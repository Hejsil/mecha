const std = @import("std");
const mecha = @import("../mecha.zig");

const math = std.math;
const unicode = std.unicode;

// Constructs a parser that only succeeds if the string starts with `c`.
pub fn char(comptime c: u21) mecha.Parser(void) {
    comptime {
        var array: [4]u8 = undefined;
        const len = unicode.utf8Encode(c, array[0..]) catch unreachable;
        return mecha.string(array[0..len]);
    }
}

test "char" {
    mecha.expectResult(void, .{ .value = {}, .rest = "" }, char('a')("a"));
    mecha.expectResult(void, .{ .value = {}, .rest = "a" }, char('a')("aa"));
    mecha.expectResult(void, null, char('a')("ba"));
    mecha.expectResult(void, null, char('a')(""));
    mecha.expectResult(void, .{ .value = {}, .rest = "ā" }, char(0x100)("Āā"));
    mecha.expectResult(void, null, char(0x100)(""));
    mecha.expectResult(void, null, char(0x100)("\xc0"));
}

/// Constructs a parser that only succeeds if the string starts with
/// a codepoint that is in between `start` and `end` inclusively.
/// The parsers result will be the codepoint parsed.
pub fn range(comptime start: u21, comptime end: u21) mecha.Parser(u21) {
    return struct {
        const Res = mecha.Result(u21);
        fn func(str: []const u8) ?Res {
            if (str.len == 0)
                return null;

            if (end <= math.maxInt(u7)) {
                switch (str[0]) {
                    start...end => return Res.init(str[0], str[1..]),
                    else => return null,
                }
            } else {
                const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch return null;
                if (cp_len > str.len)
                    return null;

                const cp = unicode.utf8Decode(str[0..cp_len]) catch return null;
                switch (cp) {
                    start...end => return Res.init(cp, str[cp_len..]),
                    else => return null,
                }
            }
        }
    }.func;
}

test "range" {
    mecha.expectResult(u21, .{ .value = 'a', .rest = "" }, range('a', 'z')("a"));
    mecha.expectResult(u21, .{ .value = 'c', .rest = "" }, range('a', 'z')("c"));
    mecha.expectResult(u21, .{ .value = 'z', .rest = "" }, range('a', 'z')("z"));
    mecha.expectResult(u21, .{ .value = 'a', .rest = "a" }, range('a', 'z')("aa"));
    mecha.expectResult(u21, .{ .value = 'c', .rest = "a" }, range('a', 'z')("ca"));
    mecha.expectResult(u21, .{ .value = 'z', .rest = "a" }, range('a', 'z')("za"));
    mecha.expectResult(u21, null, range('a', 'z')("1"));
    mecha.expectResult(u21, null, range('a', 'z')(""));
    mecha.expectResult(u21, .{ .value = 0x100, .rest = "ā" }, range(0x100, 0x100)("Āā"));
    mecha.expectResult(u21, null, range(0x100, 0x100)("aa"));
    mecha.expectResult(u21, null, range(0x100, 0x100)("\xc0"));
}

/// Creates a parser that succeeds and parses one utf8 codepoint if
/// `parser` fails to parse the input string.
pub fn not(comptime parser: anytype) mecha.Parser(u21) {
    return struct {
        const Res = mecha.Result(u21);
        fn res(str: []const u8) ?Res {
            if (str.len == 0)
                return null;
            if (parser(str)) |_|
                return null;

            const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch return null;
            if (cp_len > str.len)
                return null;

            const cp = unicode.utf8Decode(str[0..cp_len]) catch return null;
            return Res.init(cp, str[cp_len..]);
        }
    }.res;
}

test "not" {
    const p = not(comptime range('a', 'z'));
    var i: u16 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        const c = @intCast(u8, i);
        switch (c) {
            'a'...'z' => mecha.expectResult(u21, null, p(&[_]u8{c})),
            else => mecha.expectResult(u21, .{ .value = c, .rest = "" }, p(&[_]u8{c})),
        }
    }
}
