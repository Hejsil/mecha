const mecha = @import("../mecha.zig");
const std = @import("std");

const math = std.math;
const mem = std.mem;
const testing = std.testing;
const unicode = std.unicode;

/// Constructs a parser that parses a single utf8 codepoint based on a `predicate`. If the
/// `predicate` returns true, the parser will return the codepoint parsed and the rest of the
/// string. Otherwise the parser will fail.
pub fn wrap(comptime predicate: *const fn (u21) bool) mecha.Parser(u21) {
    const Res = mecha.Result(u21);
    return .{ .parse = struct {
        fn parse(_: mem.Allocator, str: []const u8) mecha.Error!Res {
            if (str.len == 0)
                return Res.err(0);

            const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch return Res.err(0);
            if (cp_len > str.len)
                return Res.err(0);

            const cp = unicode.utf8Decode(str[0..cp_len]) catch return Res.err(0);
            if (!predicate(cp))
                return Res.err(0);

            return Res.ok(cp_len, cp);
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
    try mecha.expectOk(u21, 1, 'a', try p1.parse(fa, "a"));
    try mecha.expectOk(u21, 1, 'a', try p1.parse(fa, "aa"));
    try mecha.expectOk(u21, 1, 'a', try p1.parse(fa, "aa"));
    try mecha.expectErr(u21, 0, try p1.parse(fa, "ba"));
    try mecha.expectErr(u21, 0, try p1.parse(fa, ""));

    const p2 = char(0x100);
    try mecha.expectOk(u21, 2, 'Ā', try p2.parse(fa, "Āā"));
    try mecha.expectErr(u21, 0, try p2.parse(fa, ""));
    try mecha.expectErr(u21, 0, try p2.parse(fa, "\xc0"));
}

/// Constructs a parser that only succeeds if the string starts with a codepoint that is in between
/// `start` and `end` inclusively. The parser's result will be the codepoint parsed.
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
    try mecha.expectOk(u21, 1, 'a', try p1.parse(fa, "a"));
    try mecha.expectOk(u21, 1, 'c', try p1.parse(fa, "c"));
    try mecha.expectOk(u21, 1, 'a', try p1.parse(fa, "aa"));
    try mecha.expectOk(u21, 1, 'c', try p1.parse(fa, "ca"));
    try mecha.expectOk(u21, 1, 'z', try p1.parse(fa, "za"));
    try mecha.expectErr(u21, 0, try p1.parse(fa, "1"));
    try mecha.expectErr(u21, 0, try p1.parse(fa, ""));

    const p2 = range(0x100, 0x100);
    try mecha.expectOk(u21, 2, 0x100, try p2.parse(fa, "Āā"));
    try mecha.expectErr(u21, 0, try p2.parse(fa, "aa"));
    try mecha.expectErr(u21, 0, try p2.parse(fa, "\xc0"));
}

/// Creates a parser that succeeds and parses one utf8 codepoint if `parser` fails to parse the
/// input string.
pub fn not(comptime parser: anytype) mecha.Parser(u21) {
    const Res = mecha.Result(u21);
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) mecha.Error!Res {
            if (str.len == 0)
                return Res.err(0);

            const r = try parser.parse(allocator, str);
            switch (r.value) {
                .ok => return Res.err(0),
                .err => {},
            }
            const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch return Res.err(0);
            if (cp_len > str.len)
                return Res.err(0);

            const cp = unicode.utf8Decode(str[0..cp_len]) catch return Res.err(0);
            return Res.ok(cp_len, cp);
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
            'a'...'z' => try mecha.expectErr(u21, 0, try p.parse(fa, &[_]u8{c})),
            else => try mecha.expectOk(u21, 1, c, try p.parse(fa, &[_]u8{c})),
        }
    }
}
