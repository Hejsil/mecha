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
        fn parse(_: mem.Allocator, str: []const u8) mecha.Error!Res {
            if (str.len == 0)
                return Res.fail(@src(), 0);
            const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch
                return Res.fail(@src(), 0);
            if (cp_len > str.len)
                return Res.fail(@src(), 0);
            const cp = unicode.utf8Decode(str[0..cp_len]) catch
                return Res.fail(@src(), 0);
            if (!predicate(cp))
                return Res.fail(@src(), 0);
            return Res.pass(cp, str[cp_len..], mecha.span(0, cp_len));
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
    const fa = testing.failing_allocator;

    const p1 = char('a');
    try p1.match(fa, "a", .{ .value = 'a', .rest = "", .span = mecha.span(0, 1) });
    try p1.match(fa, "aa", .{ .value = 'a', .rest = "a", .span = mecha.span(0, 1) });
    try p1.match(fa, "aa", .{ .value = 'a', .rest = "a", .span = mecha.span(0, 1) });
    try p1.fail(fa, "ba", 0);
    try p1.fail(fa, "", 0);

    const p2 = char(0x100);
    try p2.match(fa, "Āā", .{ .value = 'Ā', .rest = "ā", .span = mecha.span(0, 2) });
    try p2.fail(fa, "", 0);
    try p2.fail(fa, "\xc0", 0);
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
    const fa = testing.failing_allocator;

    const p1 = range('a', 'z');
    try p1.match(fa, "a", .{ .value = 'a', .rest = "", .span = mecha.span(0, 1) });
    try p1.match(fa, "c", .{ .value = 'c', .rest = "", .span = mecha.span(0, 1) });
    try p1.match(fa, "aa", .{ .value = 'a', .rest = "a", .span = mecha.span(0, 1) });
    try p1.match(fa, "ca", .{ .value = 'c', .rest = "a", .span = mecha.span(0, 1) });
    try p1.match(fa, "za", .{ .value = 'z', .rest = "a", .span = mecha.span(0, 1) });
    try p1.fail(fa, "1", 0);
    try p1.fail(fa, "", 0);

    const p2 = range(0x100, 0x100);
    try p2.match(fa, "Āā", .{ .value = 0x100, .rest = "ā", .span = mecha.span(0, 2) });
    try p2.fail(fa, "aa", 0);
    try p2.fail(fa, "\xc0", 0);
}

/// Creates a parser that succeeds and parses one utf8 codepoint if
/// `parser` fails to parse the input string.
pub fn not(comptime parser: anytype) mecha.Parser(u21) {
    const Res = mecha.Result(u21);
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) mecha.Error!Res {
            if (str.len == 0)
                return Res.fail(@src(), 0);
            const r = try parser.parse(allocator, str);
            switch (r) {
                .ok => return Res.fail(@src(), 0),
                .err => {},
            }
            const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch
                return Res.fail(@src(), 0);
            if (cp_len > str.len)
                return Res.fail(@src(), 0);
            const cp = unicode.utf8Decode(str[0..cp_len]) catch
                return Res.fail(@src(), 0);
            return Res{ .ok = .{
                .value = cp,
                .rest = str[cp_len..],
                .span = mecha.span(0, cp_len),
            } };
        }
    }.parse };
}

test "not" {
    const fa = testing.failing_allocator;
    const p = not(comptime range('a', 'z'));
    var i: u16 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        const c: u8 = @intCast(i);
        switch (c) {
            'a'...'z' => try p.fail(fa, &[_]u8{c}, 0),
            else => try p.match(fa, &[_]u8{c}, .{ .value = c, .span = mecha.span(0, 1) }),
        }
    }
}
