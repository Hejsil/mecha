const std = @import("std");
const mecha = @import("../mecha.zig");

const mem = std.mem;
const math = std.math;
const unicode = std.unicode;

/// Constructs a parser that only succeeds if the string starts with `c`.
pub fn char(comptime c: u21) mecha.Parser(void) {
    comptime {
        var array: [4]u8 = undefined;
        const len = unicode.utf8Encode(c, array[0..]) catch unreachable;
        return mecha.string(array[0..len]);
    }
}

test "char" {
    var allocator = &failingAllocator();
    mecha.expectResult(void, .{ .value = {}, .rest = "" }, char('a')(allocator, "a"));
    mecha.expectResult(void, .{ .value = {}, .rest = "a" }, char('a')(allocator, "aa"));
    mecha.expectResult(void, error.ParserFailed, char('a')(allocator, "ba"));
    mecha.expectResult(void, error.ParserFailed, char('a')(allocator, ""));
    mecha.expectResult(void, .{ .value = {}, .rest = "ā" }, char(0x100)(allocator, "Āā"));
    mecha.expectResult(void, error.ParserFailed, char(0x100)(allocator, ""));
    mecha.expectResult(void, error.ParserFailed, char(0x100)(allocator, "\xc0"));
}

/// Constructs a parser that only succeeds if the string starts with
/// a codepoint that is in between `start` and `end` inclusively.
/// The parser's result will be the codepoint parsed.
pub fn range(comptime start: u21, comptime end: u21) mecha.Parser(u21) {
    return struct {
        const Res = mecha.Result(u21);
        fn func(_: *mem.Allocator, str: []const u8) mecha.Error!Res {
            if (str.len == 0)
                return error.ParserFailed;

            if (end <= math.maxInt(u7)) {
                switch (str[0]) {
                    start...end => return Res.init(str[0], str[1..]),
                    else => return error.ParserFailed,
                }
            } else {
                const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch return error.ParserFailed;
                if (cp_len > str.len)
                    return error.ParserFailed;

                const cp = unicode.utf8Decode(str[0..cp_len]) catch return error.ParserFailed;
                switch (cp) {
                    start...end => return Res.init(cp, str[cp_len..]),
                    else => return error.ParserFailed,
                }
            }
        }
    }.func;
}

test "range" {
    var allocator = &failingAllocator();
    mecha.expectResult(u21, .{ .value = 'a', .rest = "" }, range('a', 'z')(allocator, "a"));
    mecha.expectResult(u21, .{ .value = 'c', .rest = "" }, range('a', 'z')(allocator, "c"));
    mecha.expectResult(u21, .{ .value = 'z', .rest = "" }, range('a', 'z')(allocator, "z"));
    mecha.expectResult(u21, .{ .value = 'a', .rest = "a" }, range('a', 'z')(allocator, "aa"));
    mecha.expectResult(u21, .{ .value = 'c', .rest = "a" }, range('a', 'z')(allocator, "ca"));
    mecha.expectResult(u21, .{ .value = 'z', .rest = "a" }, range('a', 'z')(allocator, "za"));
    mecha.expectResult(u21, error.ParserFailed, range('a', 'z')(allocator, "1"));
    mecha.expectResult(u21, error.ParserFailed, range('a', 'z')(allocator, ""));
    mecha.expectResult(u21, .{ .value = 0x100, .rest = "ā" }, range(0x100, 0x100)(allocator, "Āā"));
    mecha.expectResult(u21, error.ParserFailed, range(0x100, 0x100)(allocator, "aa"));
    mecha.expectResult(u21, error.ParserFailed, range(0x100, 0x100)(allocator, "\xc0"));
}

/// Creates a parser that succeeds and parses one utf8 codepoint if
/// `parser` fails to parse the input string.
pub fn not(comptime parser: anytype) mecha.Parser(u21) {
    return struct {
        const Res = mecha.Result(u21);
        fn res(allocator: *mem.Allocator, str: []const u8) mecha.Error!Res {
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
            return Res.init(cp, str[cp_len..]);
        }
    }.res;
}

test "not" {
    var allocator = &failingAllocator();
    const p = not(comptime range('a', 'z'));
    var i: u16 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        const c = @intCast(u8, i);
        switch (c) {
            'a'...'z' => mecha.expectResult(u21, error.ParserFailed, p(allocator, &[_]u8{c})),
            else => mecha.expectResult(u21, .{ .value = c, .rest = "" }, p(allocator, &[_]u8{c})),
        }
    }
}

fn failingAllocator() mem.Allocator {
    return std.testing.FailingAllocator.init(std.testing.allocator, 0).allocator;
}
