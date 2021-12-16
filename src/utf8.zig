const mecha = @import("../mecha.zig");
const std = @import("std");

const math = std.math;
const mem = std.mem;
const testing = std.testing;
const unicode = std.unicode;

/// Constructs a parser that parses a single utf8 codepoint based on
/// a `predicate`. If the `predicate` returns true, the parser will
/// return the codepoint parsed and the rest of the string. Otherwise
/// the parser will fail.
pub fn wrap(comptime predicate: fn (u21) bool) mecha.Parser(u21) {
    const Res = mecha.Result(u21);
    return struct {
        fn func(_: mem.Allocator, str: []const u8) mecha.Error!Res {
            if (str.len == 0)
                return error.ParserFailed;
            const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch return error.ParserFailed;
            if (cp_len > str.len)
                return error.ParserFailed;

            const cp = unicode.utf8Decode(str[0..cp_len]) catch return error.ParserFailed;
            if (!predicate(cp))
                return error.ParserFailed;
            return Res{ .value = cp, .rest = str[cp_len..] };
        }
    }.func;
}

/// Constructs a parser that only succeeds if the string starts with `c`.
pub fn char(comptime c: u21) mecha.Parser(void) {
    comptime {
        var array: [4]u8 = undefined;
        const len = unicode.utf8Encode(c, array[0..]) catch unreachable;
        return mecha.string(array[0..len]);
    }
}

test "char" {
    const allocator = testing.failing_allocator;
    try mecha.expectResult(void, .{ .value = {}, .rest = "" }, char('a')(allocator, "a"));
    try mecha.expectResult(void, .{ .value = {}, .rest = "a" }, char('a')(allocator, "aa"));
    try mecha.expectResult(void, error.ParserFailed, char('a')(allocator, "ba"));
    try mecha.expectResult(void, error.ParserFailed, char('a')(allocator, ""));
    try mecha.expectResult(void, .{ .value = {}, .rest = "ā" }, char(0x100)(allocator, "Āā"));
    try mecha.expectResult(void, error.ParserFailed, char(0x100)(allocator, ""));
    try mecha.expectResult(void, error.ParserFailed, char(0x100)(allocator, "\xc0"));
}

/// Constructs a parser that only succeeds if the string starts with
/// a codepoint that is in between `start` and `end` inclusively.
/// The parser's result will be the codepoint parsed.
pub fn range(comptime start: u21, comptime end: u21) mecha.Parser(u21) {
    return wrap(struct {
        fn pred(cp: u21) bool {
            return switch (cp) {
                start...end => true,
                else => false,
            };
        }
    }.pred);
}

test "range" {
    const allocator = testing.failing_allocator;
    try mecha.expectResult(u21, .{ .value = 'a', .rest = "" }, range('a', 'z')(allocator, "a"));
    try mecha.expectResult(u21, .{ .value = 'c', .rest = "" }, range('a', 'z')(allocator, "c"));
    try mecha.expectResult(u21, .{ .value = 'z', .rest = "" }, range('a', 'z')(allocator, "z"));
    try mecha.expectResult(u21, .{ .value = 'a', .rest = "a" }, range('a', 'z')(allocator, "aa"));
    try mecha.expectResult(u21, .{ .value = 'c', .rest = "a" }, range('a', 'z')(allocator, "ca"));
    try mecha.expectResult(u21, .{ .value = 'z', .rest = "a" }, range('a', 'z')(allocator, "za"));
    try mecha.expectResult(u21, error.ParserFailed, range('a', 'z')(allocator, "1"));
    try mecha.expectResult(u21, error.ParserFailed, range('a', 'z')(allocator, ""));
    try mecha.expectResult(u21, .{ .value = 0x100, .rest = "ā" }, range(0x100, 0x100)(allocator, "Āā"));
    try mecha.expectResult(u21, error.ParserFailed, range(0x100, 0x100)(allocator, "aa"));
    try mecha.expectResult(u21, error.ParserFailed, range(0x100, 0x100)(allocator, "\xc0"));
}

/// Creates a parser that succeeds and parses one utf8 codepoint if
/// `parser` fails to parse the input string.
pub fn not(comptime parser: anytype) mecha.Parser(u21) {
    const Res = mecha.Result(u21);
    return struct {
        fn res(allocator: mem.Allocator, str: []const u8) mecha.Error!Res {
            if (str.len == 0)
                return error.ParserFailed;
            if (parser(allocator, str)) |_| {
                return error.ParserFailed;
            } else |e| switch (e) {
                error.ParserFailed => {},
                else => return e,
            }

            const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch return error.ParserFailed;
            if (cp_len > str.len)
                return error.ParserFailed;

            const cp = unicode.utf8Decode(str[0..cp_len]) catch return error.ParserFailed;
            return Res{ .value = cp, .rest = str[cp_len..] };
        }
    }.res;
}

test "not" {
    const allocator = testing.failing_allocator;
    const p = not(comptime range('a', 'z'));
    var i: u16 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        const c = @intCast(u8, i);
        switch (c) {
            'a'...'z' => try mecha.expectResult(u21, error.ParserFailed, p(allocator, &[_]u8{c})),
            else => try mecha.expectResult(u21, .{ .value = c, .rest = "" }, p(allocator, &[_]u8{c})),
        }
    }
}
