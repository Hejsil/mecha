const std = @import("std");
const mecha = @import("../mecha.zig");

const debug = std.debug;
const math = std.math;

/// Constructs a parser that only succeeds if the string starts with `i`.
pub fn char(comptime i: u8) mecha.Parser(void) {
    comptime {
        return mecha.string(&[_]u8{i});
    }
}

test "char" {
    mecha.expectResult(void, .{ .value = {}, .rest = "" }, char('a')("a"));
    mecha.expectResult(void, .{ .value = {}, .rest = "a" }, char('a')("aa"));
    mecha.expectResult(void, null, char('a')("ba"));
    mecha.expectResult(void, null, char('a')(""));
}

/// Constructs a parser that only succeeds if the string starts with
/// a codepoint that is in between `start` and `end` inclusively.
/// The parsers result will be the codepoint parsed.
pub fn range(comptime start: u8, comptime end: u8) mecha.Parser(u8) {
    return struct {
        const Res = mecha.Result(u8);
        fn func(str: []const u8) ?Res {
            if (str.len == 0)
                return null;

            switch (str[0]) {
                start...end => return Res.init(str[0], str[1..]),
                else => return null,
            }
        }
    }.func;
}

test "range" {
    mecha.expectResult(u8, .{ .value = 'a', .rest = "" }, range('a', 'z')("a"));
    mecha.expectResult(u8, .{ .value = 'i', .rest = "" }, range('a', 'z')("i"));
    mecha.expectResult(u8, .{ .value = 'z', .rest = "" }, range('a', 'z')("z"));
    mecha.expectResult(u8, .{ .value = 'a', .rest = "a" }, range('a', 'z')("aa"));
    mecha.expectResult(u8, .{ .value = 'c', .rest = "a" }, range('a', 'z')("ca"));
    mecha.expectResult(u8, .{ .value = 'z', .rest = "a" }, range('a', 'z')("za"));
    mecha.expectResult(u8, null, range('a', 'z')("1"));
    mecha.expectResult(u8, null, range('a', 'z')(""));
}

/// A parser that succeeds if the string starts with an upper case
/// character. The parsers result will be the character parsed.
pub const upper = mecha.oneOf(.{range('A', 'Z')});

test "upper" {
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            'A'...'Z' => mecha.expectResult(u8, .{ .value = i, .rest = "" }, upper(&[_]u8{i})),
            else => mecha.expectResult(u8, null, upper(&[_]u8{i})),
        }
    }
}

/// A parser that succeeds if the string starts with an upper case
/// character. The parsers result will be the character parsed.
pub const lower = mecha.oneOf(.{range('a', 'z')});

test "lower" {
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            'a'...'z' => mecha.expectResult(u8, .{ .value = i, .rest = "" }, lower(&[_]u8{i})),
            else => mecha.expectResult(u8, null, lower(&[_]u8{i})),
        }
    }
}

/// A parser that succeeds if the string starts with an alphabetic
/// character. The parsers result will be the character parsed.
pub const alpha = mecha.oneOf(.{ lower, upper });

test "alpha" {
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            'a'...'z',
            'A'...'Z',
            => mecha.expectResult(u8, .{ .value = i, .rest = "" }, alpha(&[_]u8{i})),
            else => mecha.expectResult(u8, null, alpha(&[_]u8{i})),
        }
    }
}

/// Construct a parser that succeeds if the string starts with a
/// character that is a digit in `base`. The parsers result will be
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
    var i: u8 = 0;
    i = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            '0'...'1' => mecha.expectResult(u8, .{ .value = i, .rest = "" }, digit(2)(&[_]u8{i})),
            else => mecha.expectResult(u8, null, digit(2)(&[_]u8{i})),
        }
    }

    i = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            '0'...'9' => mecha.expectResult(u8, .{ .value = i, .rest = "" }, digit(10)(&[_]u8{i})),
            else => mecha.expectResult(u8, null, digit(10)(&[_]u8{i})),
        }
    }
    i = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            '0'...'9',
            'a'...'f',
            'A'...'F',
            => mecha.expectResult(u8, .{ .value = i, .rest = "" }, digit(16)(&[_]u8{i})),
            else => mecha.expectResult(u8, null, digit(16)(&[_]u8{i})),
        }
    }
}

/// A parser that succeeds if the string starts with an alphabetic
/// or numeric character. The parsers result will be the character parsed.
pub const alphanum = mecha.oneOf(.{ alpha, digit(10) });

test "alphanum" {
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            'a'...'z',
            'A'...'Z',
            '0'...'9',
            => mecha.expectResult(u8, .{ .value = i, .rest = "" }, alphanum(&[_]u8{i})),
            else => mecha.expectResult(u8, null, alphanum(&[_]u8{i})),
        }
    }
}

pub const cntrl = mecha.oneOf(.{
    range(0, 0x19),
    range(127, 127),
});

test "cntrl" {
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            0...0x19, 127 => mecha.expectResult(u8, .{ .value = i, .rest = "" }, cntrl(&[_]u8{i})),
            else => mecha.expectResult(u8, null, cntrl(&[_]u8{i})),
        }
    }
}

pub const graph = range(0x21, 0x7e);

test "graph" {
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            0x21...0x7e => mecha.expectResult(u8, .{ .value = i, .rest = "" }, graph(&[_]u8{i})),
            else => mecha.expectResult(u8, null, graph(&[_]u8{i})),
        }
    }
}

pub const print = range(0x20, 0x7e);

test "print" {
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            0x20...0x7e => mecha.expectResult(u8, .{ .value = i, .rest = "" }, print(&[_]u8{i})),
            else => mecha.expectResult(u8, null, print(&[_]u8{i})),
        }
    }
}

pub const space = mecha.oneOf(.{
    range(' ', ' '),
    range('\t', 0x0c),
});

test "print" {
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            0x20...0x7e => mecha.expectResult(u8, .{ .value = i, .rest = "" }, print(&[_]u8{i})),
            else => mecha.expectResult(u8, null, print(&[_]u8{i})),
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
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            '!'...'/',
            ':'...'@',
            '['...'`',
            '{'...'~',
            => mecha.expectResult(u8, .{ .value = i, .rest = "" }, punct(&[_]u8{i})),
            else => mecha.expectResult(u8, null, punct(&[_]u8{i})),
        }
    }
}

/// Creates a parser that succeeds and parses one ascii character if
/// `parser` fails to parse the input string.
pub fn not(comptime parser: anytype) mecha.Parser(u8) {
    return struct {
        const Res = mecha.Result(u8);
        fn res(str: []const u8) ?Res {
            if (str.len == 0)
                return null;
            if (parser(str)) |_|
                return null;
            return Res.init(str[0], str[1..]);
        }
    }.res;
}

test "not" {
    const p = not(alpha);
    var i: u8 = 0;
    while (i <= math.maxInt(u7)) : (i += 1) {
        switch (i) {
            'a'...'z',
            'A'...'Z',
            => mecha.expectResult(u8, null, p(&[_]u8{i})),
            else => mecha.expectResult(u8, .{ .value = i, .rest = "" }, p(&[_]u8{i})),
        }
    }
}
