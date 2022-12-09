const mecha = @import("../mecha.zig");
const std = @import("std");

const ascii = std.ascii;
const debug = std.debug;
const math = std.math;
const mem = std.mem;
const testing = std.testing;

/// Constructs a parser that parses a single ascii bytes based on
/// a `predicate`. If the `predicate` returns true, the parser will
/// return the byte parsed and the rest of the string. Otherwise
/// the parser will fail.
pub fn wrap(comptime predicate: fn (u8) bool) mecha.Parser(u8) {
    const Res = mecha.Result(u8);
    return struct {
        fn func(_: mem.Allocator, str: []const u8) mecha.Error!Res {
            if (str.len == 0 or !predicate(str[0]))
                return error.ParserFailed;
            return Res{ .value = str[0], .rest = str[1..] };
        }
    }.func;
}

/// Constructs a parser that only succeeds if the string starts with `i`.
pub fn char(comptime i: u8) mecha.Parser(void) {
    return comptime mecha.discard(range(i, i));
}

test "char" {
    @setEvalBranchQuota(5000);
    inline for ([_]void{{}} ** 255) |_, i| {
        const c = comptime @intCast(u8, i);
        try testWithPredicate(char(c), rangePred(c, c));
    }
}

pub fn rangePred(comptime start: u8, comptime end: u8) fn (u8) bool {
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
    return wrap(comptime rangePred(start, end));
}

/// Creates a parser that succeeds and parses one ascii character if
/// `parser` fails to parse the input string.
pub fn not(comptime parser: anytype) mecha.Parser(u8) {
    const Res = mecha.Result(u8);
    return struct {
        fn res(allocator: mem.Allocator, str: []const u8) mecha.Error!Res {
            if (str.len == 0)
                return error.ParserFailed;

            _ = parser(allocator, str) catch |e| switch (e) {
                error.ParserFailed => return Res{ .value = str[0], .rest = str[1..] },
                else => return e,
            };

            return error.ParserFailed;
        }
    }.res;
}

test "not" {
    try testWithPredicate(not(alpha), struct {
        fn pred(c: u8) bool {
            return !ascii.isAlpha(c);
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

pub const alphanum = wrap(ascii.isAlNum);
pub const alpha = wrap(ascii.isAlpha);
pub const blank = wrap(ascii.isBlank);
pub const cntrl = wrap(ascii.isCntrl);
pub const graph = wrap(ascii.isGraph);
pub const lower = wrap(ascii.isLower);
pub const print = wrap(ascii.isPrint);
pub const punct = wrap(ascii.isPunct);
pub const space = wrap(ascii.isSpace);
pub const upper = wrap(ascii.isUpper);
pub const valid = wrap(ascii.isASCII);

test "predicate" {
    try testWithPredicate(alpha, ascii.isAlpha);
    try testWithPredicate(alphanum, ascii.isAlNum);
    try testWithPredicate(blank, ascii.isBlank);
    try testWithPredicate(cntrl, ascii.isCntrl);
    try testWithPredicate(graph, ascii.isGraph);
    try testWithPredicate(lower, ascii.isLower);
    try testWithPredicate(print, ascii.isPrint);
    try testWithPredicate(punct, ascii.isPunct);
    try testWithPredicate(space, ascii.isSpace);
    try testWithPredicate(upper, ascii.isUpper);
    try testWithPredicate(valid, ascii.isASCII);
}

fn testWithPredicate(parser: anytype, pred: *const fn (u8) bool) !void {
    const allocator = testing.failing_allocator;
    for ([_]void{{}} ** 255) |_, i| {
        const c = comptime @intCast(u8, i);
        if (pred(c)) switch (@TypeOf(parser)) {
            mecha.Parser(u8) => try mecha.expectResult(u8, .{ .value = c }, parser(allocator, &[_]u8{c})),
            mecha.Parser(void) => try mecha.expectResult(void, .{ .value = {} }, parser(allocator, &[_]u8{c})),
            else => comptime unreachable,
        } else switch (@TypeOf(parser)) {
            mecha.Parser(u8) => try mecha.expectResult(u8, error.ParserFailed, parser(allocator, &[_]u8{c})),
            mecha.Parser(void) => try mecha.expectResult(void, error.ParserFailed, parser(allocator, &[_]u8{c})),
            else => comptime unreachable,
        }
    }
}
