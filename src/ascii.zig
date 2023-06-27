const mecha = @import("../mecha.zig");
const std = @import("std");

const debug = std.debug;
const math = std.math;
const mem = std.mem;
const testing = std.testing;

/// Constructs a parser that parses a single ascii bytes based on
/// a `predicate`. If the `predicate` returns true, the parser will
/// return the byte parsed and the rest of the string. Otherwise
/// the parser will fail.
pub fn wrap(comptime predicate: *const fn (u8) bool) mecha.Parser(u8) {
    const Res = mecha.Result(u8);
    return .{ .parse = struct {
        fn parse(_: mem.Allocator, str: []const u8) mecha.Error!Res {
            if (str.len == 0 or !predicate(str[0]))
                return error.ParserFailed;
            return Res{ .value = str[0], .rest = str[1..] };
        }
    }.parse };
}

pub fn charPred(comptime a: u8) *const fn (u8) bool {
    return struct {
        fn pred(b: u8) bool {
            return a == b;
        }
    }.pred;
}

/// Constructs a parser that only succeeds if the string starts with `i`.
pub fn char(comptime c: u8) mecha.Parser(u8) {
    return wrap(charPred(c));
}

test "char" {
    @setEvalBranchQuota(5000);
    inline for (0..256) |i| {
        const c: u8 = @intCast(i);
        try testWithPredicate(char(c), rangePred(c, c));
    }
}

pub fn rangePred(comptime start: u8, comptime end: u8) *const fn (u8) bool {
    return struct {
        fn pred(c: u8) bool {
            return switch (c) {
                start...end => true,
                else => false,
            };
        }
    }.pred;
}

/// Constructs a parser that only succeeds if the string starts with
/// a codepoint that is in between `start` and `end` inclusively.
/// The parser's result will be the codepoint parsed.
pub fn range(comptime start: u8, comptime end: u8) mecha.Parser(u8) {
    return wrap(rangePred(start, end));
}

/// Creates a parser that succeeds and parses one ascii character if
/// `parser` fails to parse the input string.
pub fn not(comptime parser: anytype) mecha.Parser(u8) {
    const Res = mecha.Result(u8);
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) mecha.Error!Res {
            if (str.len == 0)
                return error.ParserFailed;

            _ = parser.parse(allocator, str) catch |e| switch (e) {
                error.ParserFailed => return Res{ .value = str[0], .rest = str[1..] },
                else => return e,
            };

            return error.ParserFailed;
        }
    }.parse };
}

test "not" {
    try testWithPredicate(not(alphabetic), struct {
        fn pred(c: u8) bool {
            return !std.ascii.isAlphabetic(c);
        }
    }.pred);
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
    try testWithPredicate(digit(2), struct {
        fn pred(c: u8) bool {
            return switch (c) {
                '0'...'1' => true,
                else => false,
            };
        }
    }.pred);
    try testWithPredicate(digit(10), struct {
        fn pred(c: u8) bool {
            return switch (c) {
                '0'...'9' => true,
                else => false,
            };
        }
    }.pred);
    try testWithPredicate(digit(16), struct {
        fn pred(c: u8) bool {
            return switch (c) {
                '0'...'9', 'a'...'f', 'A'...'F' => true,
                else => false,
            };
        }
    }.pred);
}

pub const alphabetic = wrap(std.ascii.isAlphabetic);
pub const alphanumeric = wrap(std.ascii.isAlphanumeric);
pub const ascii = wrap(std.ascii.isASCII);
pub const control = wrap(std.ascii.isControl);
pub const graph = wrap(std.ascii.isGraph);
pub const lower = wrap(std.ascii.isLower);
pub const print = wrap(std.ascii.isPrint);
pub const upper = wrap(std.ascii.isUpper);
pub const whitespace = wrap(std.ascii.isWhitespace);

test "predicate" {
    try testWithPredicate(alphabetic, std.ascii.isAlphabetic);
    try testWithPredicate(alphanumeric, std.ascii.isAlphanumeric);
    try testWithPredicate(control, std.ascii.isControl);
    try testWithPredicate(lower, std.ascii.isLower);
    try testWithPredicate(print, std.ascii.isPrint);
    try testWithPredicate(upper, std.ascii.isUpper);
    try testWithPredicate(ascii, std.ascii.isASCII);
    try testWithPredicate(whitespace, std.ascii.isWhitespace);
}

fn testWithPredicate(parser: anytype, pred: *const fn (u8) bool) !void {
    const allocator = testing.failing_allocator;
    for (0..256) |i| {
        const c: u8 = @intCast(i);
        if (pred(c)) switch (@TypeOf(parser)) {
            mecha.Parser(u8) => try mecha.expectResult(u8, .{ .value = c }, parser.parse(allocator, &[_]u8{c})),
            mecha.Parser(void) => try mecha.expectResult(void, .{ .value = {} }, parser.parse(allocator, &[_]u8{c})),
            else => comptime unreachable,
        } else switch (@TypeOf(parser)) {
            mecha.Parser(u8) => try mecha.expectResult(u8, error.ParserFailed, parser.parse(allocator, &[_]u8{c})),
            mecha.Parser(void) => try mecha.expectResult(void, error.ParserFailed, parser.parse(allocator, &[_]u8{c})),
            else => comptime unreachable,
        }
    }
}
