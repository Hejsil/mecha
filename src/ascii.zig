const std = @import("std");
const mecha = @import("../mecha.zig");

const debug = std.debug;
const math = std.math;
const mem = std.mem;
const testing = std.testing;

/// Constructs a parser that only succeeds if the string starts with `i`.
pub fn char(comptime i: u8) mecha.Parser(void) {
    comptime {
        return mecha.string(&[_]u8{i});
    }
}

test "char" {
    const allocator = testing.failing_allocator;
    mecha.expectResult(void, .{ .value = {}, .rest = "" }, char('a')(allocator, "a"));
    mecha.expectResult(void, .{ .value = {}, .rest = "a" }, char('a')(allocator, "aa"));
    mecha.expectResult(void, error.ParserFailed, char('a')(allocator, "ba"));
    mecha.expectResult(void, error.ParserFailed, char('a')(allocator, ""));
}

/// Constructs a parser that only succeeds if the string starts with
/// a codepoint that is in between `start` and `end` inclusively.
/// The parser's result will be the codepoint parsed.
pub fn range(comptime start: u8, comptime end: u8) mecha.Parser(u8) {
    return struct {
        const Res = mecha.Result(u8);
        fn func(_: *mem.Allocator, str: []const u8) mecha.Error!Res {
            if (str.len == 0)
                return error.ParserFailed;

            switch (str[0]) {
                start...end => return Res.init(str[0], str[1..]),
                else => return error.ParserFailed,
            }
        }
    }.func;
}

test "range" {
    const allocator = testing.failing_allocator;
    mecha.expectResult(u8, .{ .value = 'a', .rest = "" }, range('a', 'z')(allocator, "a"));
    mecha.expectResult(u8, .{ .value = 'i', .rest = "" }, range('a', 'z')(allocator, "i"));
    mecha.expectResult(u8, .{ .value = 'z', .rest = "" }, range('a', 'z')(allocator, "z"));
    mecha.expectResult(u8, .{ .value = 'a', .rest = "a" }, range('a', 'z')(allocator, "aa"));
    mecha.expectResult(u8, .{ .value = 'c', .rest = "a" }, range('a', 'z')(allocator, "ca"));
    mecha.expectResult(u8, .{ .value = 'z', .rest = "a" }, range('a', 'z')(allocator, "za"));
    mecha.expectResult(u8, error.ParserFailed, range('a', 'z')(allocator, "1"));
    mecha.expectResult(u8, error.ParserFailed, range('a', 'z')(allocator, ""));
}

/// A parser that succeeds if the string starts with an upper case
/// character. The parser's result will be the character parsed.
pub const upper = range('A', 'Z');

test "upper" {
    const allocator = testing.failing_allocator;
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            'A'...'Z' => mecha.expectResult(u8, .{ .value = i, .rest = "" }, upper(allocator, &[_]u8{i})),
            else => mecha.expectResult(u8, error.ParserFailed, upper(allocator, &[_]u8{i})),
        }
    }
}

/// A parser that succeeds if the string starts with a lower case
/// character. The parser's result will be the character parsed.
pub const lower = range('a', 'z');

test "lower" {
    const allocator = testing.failing_allocator;
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            'a'...'z' => mecha.expectResult(u8, .{ .value = i, .rest = "" }, lower(allocator, &[_]u8{i})),
            else => mecha.expectResult(u8, error.ParserFailed, lower(allocator, &[_]u8{i})),
        }
    }
}

/// A parser that succeeds if the string starts with an alphabetic
/// character. The parser's result will be the character parsed.
pub const alpha = mecha.oneOf(.{ lower, upper });

test "alpha" {
    const allocator = testing.failing_allocator;
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            'a'...'z',
            'A'...'Z',
            => mecha.expectResult(u8, .{ .value = i, .rest = "" }, alpha(allocator, &[_]u8{i})),
            else => mecha.expectResult(u8, error.ParserFailed, alpha(allocator, &[_]u8{i})),
        }
    }
}

/// Construct a parser that succeeds if the string starts with a
/// character that is a digit in `base`. The parser's result will be
/// the character parsed.
pub fn digit(comptime base: u8) mecha.Parser(u8) {
    debug.assert(base != 0);
    if (base <= 10)
        return range('0', '0' + (base - 1));
    return comptime mecha.oneOf(.{
        range('0', '9'),
        range('a', 'a' + (base - 11)),
        range('A', 'A' + (base - 11)),
    });
}

test "digit" {
    const allocator = testing.failing_allocator;
    var i: u8 = 0;
    i = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            '0'...'1' => mecha.expectResult(u8, .{ .value = i, .rest = "" }, digit(2)(allocator, &[_]u8{i})),
            else => mecha.expectResult(u8, error.ParserFailed, digit(2)(allocator, &[_]u8{i})),
        }
    }

    i = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            '0'...'9' => mecha.expectResult(u8, .{ .value = i, .rest = "" }, digit(10)(allocator, &[_]u8{i})),
            else => mecha.expectResult(u8, error.ParserFailed, digit(10)(allocator, &[_]u8{i})),
        }
    }
    i = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            '0'...'9',
            'a'...'f',
            'A'...'F',
            => mecha.expectResult(u8, .{ .value = i, .rest = "" }, digit(16)(allocator, &[_]u8{i})),
            else => mecha.expectResult(u8, error.ParserFailed, digit(16)(allocator, &[_]u8{i})),
        }
    }
}

/// A parser that succeeds if the string starts with an alphabetic or
/// numeric character. The parser's result will be the character parsed.
pub const alphanum = mecha.oneOf(.{ alpha, digit(10) });

test "alphanum" {
    const allocator = testing.failing_allocator;
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            'a'...'z',
            'A'...'Z',
            '0'...'9',
            => mecha.expectResult(u8, .{ .value = i, .rest = "" }, alphanum(allocator, &[_]u8{i})),
            else => mecha.expectResult(u8, error.ParserFailed, alphanum(allocator, &[_]u8{i})),
        }
    }
}

pub const cntrl = mecha.oneOf(.{
    range(0, 0x19),
    range(127, 127),
});

test "cntrl" {
    const allocator = testing.failing_allocator;
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            0...0x19, 127 => mecha.expectResult(u8, .{ .value = i, .rest = "" }, cntrl(allocator, &[_]u8{i})),
            else => mecha.expectResult(u8, error.ParserFailed, cntrl(allocator, &[_]u8{i})),
        }
    }
}

pub const graph = range(0x21, 0x7e);

test "graph" {
    const allocator = testing.failing_allocator;
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            0x21...0x7e => mecha.expectResult(u8, .{ .value = i, .rest = "" }, graph(allocator, &[_]u8{i})),
            else => mecha.expectResult(u8, error.ParserFailed, graph(allocator, &[_]u8{i})),
        }
    }
}

pub const print = range(0x20, 0x7e);

test "print" {
    const allocator = testing.failing_allocator;
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            0x20...0x7e => mecha.expectResult(u8, .{ .value = i, .rest = "" }, print(allocator, &[_]u8{i})),
            else => mecha.expectResult(u8, error.ParserFailed, print(allocator, &[_]u8{i})),
        }
    }
}

pub const space = mecha.oneOf(.{
    range(' ', ' '),
    range('\t', 0x0c),
});

test "print" {
    const allocator = testing.failing_allocator;
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            0x20...0x7e => mecha.expectResult(u8, .{ .value = i, .rest = "" }, print(allocator, &[_]u8{i})),
            else => mecha.expectResult(u8, error.ParserFailed, print(allocator, &[_]u8{i})),
        }
    }
}

pub const punct = mecha.oneOf(.{
    range('!', '/'),
    range(':', '@'),
    range('[', '`'),
    range('{', '~'),
});

test "punct" {
    const allocator = testing.failing_allocator;
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            '!'...'/',
            ':'...'@',
            '['...'`',
            '{'...'~',
            => mecha.expectResult(u8, .{ .value = i, .rest = "" }, punct(allocator, &[_]u8{i})),
            else => mecha.expectResult(u8, error.ParserFailed, punct(allocator, &[_]u8{i})),
        }
    }
}

/// Creates a parser that succeeds and parses one ascii character if
/// `parser` fails to parse the input string.
pub fn not(comptime parser: anytype) mecha.Parser(u8) {
    return struct {
        const Res = mecha.Result(u8);
        fn res(allocator: *mem.Allocator, str: []const u8) mecha.Error!Res {
            if (str.len == 0)
                return error.ParserFailed;

            _ = parser(allocator, str) catch |e| switch (e) {
                error.ParserFailed => return Res.init(str[0], str[1..]),
                else => return e,
            };

            return error.ParserFailed;
        }
    }.res;
}

test "not" {
    const allocator = testing.failing_allocator;
    const p = not(alpha);
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            'a'...'z',
            'A'...'Z',
            => mecha.expectResult(u8, error.ParserFailed, p(allocator, &[_]u8{i})),
            else => mecha.expectResult(u8, .{ .value = i, .rest = "" }, p(allocator, &[_]u8{i})),
        }
    }
}
