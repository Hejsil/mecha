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
pub fn wrap(comptime predicate: *const fn (u21) bool) mecha.Parser(u21) {
    const Res = mecha.Result(u21);
    return .{ .parse = struct {
        fn parse(_: mem.Allocator, ctx: *mecha.Context, str: []const u8) mecha.Error!Res {
            if (str.len == 0)
                return error.ParserFailed;
            const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch return error.ParserFailed;
            if (cp_len > str.len)
                return error.ParserFailed;

            const cp = unicode.utf8Decode(str[0..cp_len]) catch return error.ParserFailed;
            if (!predicate(cp))
                return error.ParserFailed;
            return Res{ .value = cp, .rest = str[cp_len..], .span = ctx.bump(cp_len) };
        }
    }.parse };
}

/// Constructs a parser that only succeeds if the string starts with `c`.
pub fn char(comptime c: u21) mecha.Parser(u21) {
    return wrap(struct {
        fn pred(cp: u21) bool {
            return c == cp;
        }
    }.pred);
}

test "char" {
    const allocator = testing.failing_allocator;
    var ctx = mecha.Context{};
    try mecha.expectResult(u21, .{ .value = 'a', .rest = "", .span = mecha.span(0, 1) }, char('a').parse(allocator, &ctx, "a"));
    try testing.expectEqual(1, ctx.pos);
    ctx = mecha.Context{};
    try mecha.expectResult(u21, .{ .value = 'a', .rest = "a", .span = mecha.span(0, 1) }, char('a').parse(allocator, &ctx, "aa"));
    try testing.expectEqual(1, ctx.pos);
    ctx = mecha.Context{};
    try mecha.expectResult(u21, error.ParserFailed, char('a').parse(allocator, &ctx, "ba"));
    try testing.expectEqual(0, ctx.pos);
    ctx = mecha.Context{};
    try mecha.expectResult(u21, error.ParserFailed, char('a').parse(allocator, &ctx, ""));
    try testing.expectEqual(0, ctx.pos);
    ctx = mecha.Context{};
    try mecha.expectResult(u21, .{ .value = 'Ā', .rest = "ā", .span = mecha.span(0, 1) }, char(0x100).parse(allocator, &ctx, "Āā"));
    try testing.expectEqual(2, ctx.pos);
    ctx = mecha.Context{};
    try mecha.expectResult(u21, error.ParserFailed, char(0x100).parse(allocator, &ctx, ""));
    try testing.expectEqual(0, ctx.pos);
    ctx = mecha.Context{};
    try mecha.expectResult(u21, error.ParserFailed, char(0x100).parse(allocator, &ctx, "\xc0"));
    try testing.expectEqual(0, ctx.pos);
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
    var ctx = mecha.Context{};
    try mecha.expectResult(u21, .{ .value = 'a', .rest = "" }, range('a', 'z').parse(allocator, &ctx, "a"));
    try mecha.expectResult(u21, .{ .value = 'c', .rest = "" }, range('a', 'z').parse(allocator, &ctx, "c"));
    try mecha.expectResult(u21, .{ .value = 'z', .rest = "" }, range('a', 'z').parse(allocator, &ctx, "z"));
    try mecha.expectResult(u21, .{ .value = 'a', .rest = "a" }, range('a', 'z').parse(allocator, &ctx, "aa"));
    try mecha.expectResult(u21, .{ .value = 'c', .rest = "a" }, range('a', 'z').parse(allocator, &ctx, "ca"));
    try mecha.expectResult(u21, .{ .value = 'z', .rest = "a" }, range('a', 'z').parse(allocator, &ctx, "za"));
    try mecha.expectResult(u21, error.ParserFailed, range('a', 'z').parse(allocator, &ctx, "1"));
    try mecha.expectResult(u21, error.ParserFailed, range('a', 'z').parse(allocator, &ctx, ""));
    try mecha.expectResult(u21, .{ .value = 0x100, .rest = "ā" }, range(0x100, 0x100).parse(allocator, &ctx, "Āā"));
    try mecha.expectResult(u21, error.ParserFailed, range(0x100, 0x100).parse(allocator, &ctx, "aa"));
    try mecha.expectResult(u21, error.ParserFailed, range(0x100, 0x100).parse(allocator, &ctx, "\xc0"));
}

/// Creates a parser that succeeds and parses one utf8 codepoint if
/// `parser` fails to parse the input string.
pub fn not(comptime parser: anytype) mecha.Parser(u21) {
    const Res = mecha.Result(u21);
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, ctx: *mecha.Context, str: []const u8) mecha.Error!Res {
            if (str.len == 0)
                return error.ParserFailed;
            const pos = ctx.pos;
            if (parser.parse(allocator, ctx, str)) |_| {
                return error.ParserFailed;
            } else |e| switch (e) {
                error.ParserFailed => {},
                else => return e,
            }

            const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch return error.ParserFailed;
            if (cp_len > str.len)
                return error.ParserFailed;

            const cp = unicode.utf8Decode(str[0..cp_len]) catch return error.ParserFailed;
            ctx.pos = pos;
            return Res{ .value = cp, .rest = str[cp_len..], .span = ctx.bump(cp_len) };
        }
    }.parse };
}

test "not" {
    const allocator = testing.failing_allocator;
    var ctx = mecha.Context{};
    const p = not(comptime range('a', 'z'));
    var i: u16 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        const c: u8 = @intCast(i);
        switch (c) {
            'a'...'z' => try mecha.expectResult(u21, error.ParserFailed, p.parse(allocator, &ctx, &[_]u8{c})),
            else => try mecha.expectResult(u21, .{ .value = c, .rest = "" }, p.parse(allocator, &ctx, &[_]u8{c})),
        }
    }
}
