const std = @import("std");

const debug = std.debug;
const fmt = std.fmt;
const math = std.math;
const mem = std.mem;
const meta = std.meta;
const testing = std.testing;
const unicode = std.unicode;
const builtin = std.builtin;

pub const ascii = @import("src/ascii.zig");
pub const utf8 = @import("src/utf8.zig");

const mecha = @This();

/// The type of all parser that can work with `mecha`
pub fn Parser(comptime _T: type) type {
    return struct {
        pub const T = _T;

        parse: *const fn (mem.Allocator, []const u8) Error!Result(T),

        pub const asStr = mecha.asStr;
        pub const convert = mecha.convert;
        pub const digit = mecha.digit;
        pub const discard = mecha.discard;
        pub const many = mecha.many;
        pub const manyN = mecha.manyN;
        pub const mapConst = mecha.mapConst;
        pub const map = mecha.map;
        pub const opt = mecha.opt;

        const Self = @This();

        pub fn match(
            self: Self,
            alloc: mem.Allocator,
            str: []const u8,
            result: Result(T).Pass,
        ) !void {
            const res = try self.parse(alloc, str);
            switch (res) {
                .ok => try expectResult(T, .{ .ok = result }, res),
                .err => res.reportError(),
            }
        }

        pub fn fail(
            self: Self,
            alloc: mem.Allocator,
            str: []const u8,
            pos: usize,
        ) !void {
            switch (try self.parse(alloc, str)) {
                .ok => return error.TestExpectedError,
                .err => |e| try testing.expectEqual(pos, e.pos),
            }
        }
    };
}

/// The span of the input that was covered by a parser.
pub const Span = struct {
    start: usize,
    len: usize,
};

pub inline fn span(start: usize, len: usize) Span {
    return .{ .start = start, .len = len };
}

/// The result of a parse where `ok` corresponds to a successful parse
/// and `err` denotes a failure. The result will be placed in `value`
/// and `rest` will contain the unparsed input. Result will be annotated
/// with  a `span` containing the starting position of the result in the
/// input string, as well as its length. Finally, `pos` will contain
/// the position where the parser stopped and the next parser can pick up.
pub fn Result(comptime T: type) type {
    return union(enum) {
        ok: Pass,
        err: Fail,

        const Pass = struct {
            pub const Value = T;

            value: T,
            rest: []const u8 = "",
            span: Span = span(0, 0),
        };

        const Fail = struct {
            loc: builtin.SourceLocation,
            pos: usize,
        };

        const Self = @This();

        pub inline fn pass(value: T, rem: []const u8, sp: Span) Self {
            return .{
                .ok = .{
                    .value = value,
                    .rest = rem,
                    .span = sp,
                },
            };
        }

        pub inline fn fail(loc: builtin.SourceLocation, pos: usize) Self {
            return .{ .err = .{ .loc = loc, .pos = pos } };
        }

        pub inline fn failWith(e: anytype, pos: usize) Self {
            return .{ .err = .{ .loc = e.err.loc, .pos = e.err.pos + pos } };
        }

        fn reportError(self: Self) void {
            switch (self) {
                .err => |e| {
                    std.debug.print("Parser {s} ({s}:{d}:{d}) failed at position {d}", .{
                        e.loc.fn_name,
                        e.loc.file,
                        e.loc.line,
                        e.loc.column,
                        e.pos,
                    });
                },
                .ok => {},
            }
        }
    };
}

// All the ways in which a parser can fail.
pub const Error = error{OtherError} ||
    mem.Allocator.Error ||
    fmt.ParseIntError;

fn typecheckParser(comptime P: type) void {
    const err = "expected 'mecha.Parser(T)', found '" ++ @typeName(P) ++ "'";
    const PInner = switch (@typeInfo(P)) {
        .pointer => |info| info.child,
        else => P,
    };

    if (@typeInfo(PInner) != .@"struct") @compileError(err);
    if (!@hasDecl(PInner, "T")) @compileError(err);
    if (@TypeOf(PInner.T) != type) @compileError(err);
    if (PInner != Parser(PInner.T)) @compileError(err);
}

fn ReturnType(comptime P: type) type {
    return switch (@typeInfo(P)) {
        .pointer => |p| @typeInfo(p.child).@"fn".return_type.?,
        .@"fn" => |f| f.return_type.?,
        else => @compileError(@typeName(P)),
    };
}

fn ParserResult(comptime P: type) type {
    return switch (@typeInfo(P)) {
        .pointer => |p| p.child.T,
        else => P.T,
    };
}

/// A parser that always succeeds and parses nothing. This parser
/// is only really useful for generic code. See `many`.
pub const noop = Parser(void){ .parse = struct {
    const Res = Result(void);
    fn parse(_: mem.Allocator, str: []const u8) Error!Res {
        return Res.pass({}, str, span(0, 0));
    }
}.parse };

/// A parser that only succeeds on the end of the string.
pub const eos = Parser(void){ .parse = struct {
    const Res = Result(void);
    fn parse(_: mem.Allocator, str: []const u8) Error!Res {
        if (str.len != 0)
            return Res.fail(@src(), 0);
        return Res.pass({}, str, span(0, 0));
    }
}.parse };

test "eos" {
    const fa = testing.failing_allocator;
    try eos.match(fa, "", .{ .value = {} });
    try eos.match(fa, "", .{ .value = {} });
    try eos.fail(fa, "a", 0);
}

/// A parser that always succeeds with the result being the
/// entire string. The same as the '.*$' regex.
pub const rest = Parser([]const u8){ .parse = struct {
    const Res = Result([]const u8);
    fn parse(_: mem.Allocator, str: []const u8) Error!Res {
        return Res.pass(str, str[str.len..], span(0, str.len));
    }
}.parse };

test "rest" {
    const fa = testing.failing_allocator;
    try rest.match(fa, "", .{ .value = "" });
    try rest.match(fa, "a", .{ .value = "a", .span = span(0, 1) });
}

/// Construct a parser that succeeds if the string passed in starts
/// with `str`.
pub fn string(comptime str: []const u8) Parser([]const u8) {
    const Res = Result([]const u8);
    return .{ .parse = struct {
        fn parse(_: mem.Allocator, s: []const u8) Error!Res {
            if (!mem.startsWith(u8, s, str))
                return Res.fail(@src(), 0);
            return Res.pass(str, s[str.len..], span(0, str.len));
        }
    }.parse };
}

test "string" {
    const fa = testing.failing_allocator;
    const p = string("aa");
    try p.match(fa, "aa", .{ .value = "aa", .span = span(0, 2) });
    try p.match(fa, "aaa", .{ .value = "aa", .rest = "a", .span = span(0, 2) });
    try p.fail(fa, "ba", 0);
    try p.fail(fa, "", 0);
}

pub const ManyNOptions = struct {
    /// A parser used to parse the content between each element `manyN` parses.
    /// The default is `noop`, so each element will be parsed one after another.
    separator: Parser(void) = noop,
};

/// Construct a parser that repeatedly uses `parser` until `n` iterations is reached.
/// The parser's result will be an array of the results from the repeated parser.
pub fn manyN(
    comptime parser: anytype,
    comptime n: usize,
    comptime options: ManyNOptions,
) Parser([n]ParserResult(@TypeOf(parser))) {
    const T = @TypeOf(parser);
    const Array = [n]ParserResult(T);
    const Res = Result(Array);
    return .{
        .parse = struct {
            fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
                var rem = str;
                var res: Array = undefined;
                var pos: usize = 0;
                for (&res, 0..) |*value, i| {
                    if (i != 0) {
                        const sep = try options.separator.parse(allocator, rem);
                        switch (sep) {
                            .ok => |ok| {
                                rem = ok.rest;
                                pos += ok.span.len;
                            },
                            .err => return Res.failWith(sep, pos),
                        }
                    }
                    const r = try parser.parse(allocator, rem);
                    switch (r) {
                        .ok => |ok| {
                            rem = ok.rest;
                            pos += ok.span.len;
                            value.* = ok.value;
                        },
                        .err => return Res.failWith(r, pos),
                    }
                }
                return Res.pass(res, rem, span(0, str.len - rem.len));
            }
        }.parse,
    };
}

test "manyN" {
    const fa = testing.failing_allocator;
    const p1 = comptime ascii.range('a', 'b').manyN(3, .{});
    try p1.match(fa, "ababab", .{ .value = "aba".*, .rest = "bab", .span = span(0, 3) });
    const p2 = comptime ascii.range('a', 'b')
        .manyN(3, .{ .separator = discard(ascii.char(',')) });
    try p2.match(fa, "a,b,a,b,a,b", .{ .value = "aba".*, .rest = ",b,a,b", .span = span(0, 5) });
}

pub const ManyOptions = struct {
    /// The min number of elements `many` should parse for parsing to be
    /// considered successful.
    min: usize = 0,

    /// The maximum number of elements `many` will parse. `many` will stop
    /// parsing after reaching this number of elements even if more elements
    /// could be parsed.
    max: usize = math.maxInt(usize),

    /// Have `many` collect the results of all elements in an allocated slice.
    /// Setting this to false, and `many` will instead just return the parsed
    /// string as the result without any allocation.
    collect: bool = true,

    /// A parser used to parse the content between each element `many` parses.
    /// The default is `noop`, so each element will be parsed one after another.
    separator: Parser(void) = noop,
};

fn Many(comptime parser: anytype, comptime options: ManyOptions) type {
    if (options.collect)
        return []ParserResult(@TypeOf(parser));
    return []const u8;
}

/// Construct a parser that repeatedly uses `parser` as long as it succeeds
/// or until `opt.max` is reach. See `ManyOptions` for options this function
/// exposes.
pub fn many(comptime parser: anytype, comptime options: ManyOptions) Parser(Many(parser, options)) {
    const ElementParser = @TypeOf(parser);
    const Element = ParserResult(ElementParser);
    const Res = Result(Many(parser, options));
    typecheckParser(ElementParser);

    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            var res = if (options.collect)
                try std.ArrayList(Element).initCapacity(allocator, options.min)
            else {};
            errdefer if (options.collect) res.deinit();
            var rem = str;
            var pos: usize = 0;
            var e_loc = @src();
            var e_pos: usize = 0;
            var i: usize = 0;
            while (i < options.max) : (i += 1) {
                const after_separator = if (i != 0) blk: {
                    const sep = try options.separator.parse(allocator, rem);
                    switch (sep) {
                        .ok => |ok| {
                            pos += ok.span.len;
                            break :blk ok.rest;
                        },
                        .err => |e| {
                            e_loc = e.loc;
                            e_pos = e.pos;
                            break;
                        },
                    }
                } else rem;
                const r = try parser.parse(allocator, after_separator);
                switch (r) {
                    .ok => |ok| {
                        pos += ok.span.len;
                        rem = ok.rest;
                        if (options.collect)
                            try res.append(ok.value);
                    },
                    .err => |e| {
                        e_loc = e.loc;
                        e_pos = e.pos;
                        break;
                    },
                }
            }
            if (i < options.min) {
                return Res.fail(e_loc, pos + e_pos);
            }
            const delta = str.len - rem.len;
            const value = if (options.collect)
                try res.toOwnedSlice()
            else
                str[0..delta];
            return Res.pass(value, rem, span(0, delta));
        }
    }.parse };
}

test "many" {
    const fa = testing.failing_allocator;

    const p1 = comptime string("ab")
        .many(.{ .collect = false });
    try p1.match(fa, "", .{ .value = "" });
    try p1.match(fa, "a", .{ .value = "", .rest = "a" });
    try p1.match(fa, "ab", .{ .value = "ab", .span = span(0, 2) });
    try p1.match(fa, "aba", .{ .value = "ab", .rest = "a", .span = span(0, 2) });
    try p1.match(fa, "abab", .{ .value = "abab", .span = span(0, 4) });
    try p1.match(fa, "ababa", .{ .value = "abab", .rest = "a", .span = span(0, 4) });
    try p1.match(fa, "ababab", .{ .value = "ababab", .rest = "", .span = span(0, 6) });

    const p2 = comptime string("ab")
        .many(.{ .collect = false, .min = 1, .max = 2 });
    try p2.fail(fa, "", 0);
    try p2.fail(fa, "a", 0);
    try p2.match(fa, "ab", .{ .value = "ab", .span = span(0, 2) });
    try p2.match(fa, "aba", .{ .value = "ab", .rest = "a", .span = span(0, 2) });
    try p2.match(fa, "abab", .{ .value = "abab", .span = span(0, 4) });
    try p2.match(fa, "ababa", .{ .value = "abab", .rest = "a", .span = span(0, 4) });
    try p2.match(fa, "ababab", .{ .value = "abab", .rest = "ab", .span = span(0, 4) });

    const p3 = comptime string("ab")
        .many(.{ .collect = false, .separator = discard(ascii.char(',')) });
    try p3.match(fa, "", .{ .value = "" });
    try p3.match(fa, "a", .{ .value = "", .rest = "a" });
    try p3.match(fa, "aba", .{ .value = "ab", .rest = "a", .span = span(0, 2) });
    try p3.match(fa, "abab", .{ .value = "ab", .rest = "ab", .span = span(0, 2) });
    try p3.match(fa, "ab,ab", .{ .value = "ab,ab", .span = span(0, 5) });
    try p3.match(fa, "ab,ab,", .{ .value = "ab,ab", .rest = ",", .span = span(0, 5) });

    const p4 = comptime utf8.char(0x100)
        .many(.{ .collect = false });
    try p4.match(fa, "ĀĀĀāāā", .{ .value = "ĀĀĀ", .rest = "āāā", .span = span(0, 6) });

    const a = testing.allocator;

    const p5 = comptime utf8.range(0x100, 0x100).many(.{});
    const res = try p5.parse(a, "ĀĀĀāāā");
    defer a.free(res.ok.value);
    var expect = [_]u21{ 'Ā', 'Ā', 'Ā' };
    try expectResult([]u21, .{ .ok = .{ .value = &expect, .rest = "āāā", .span = span(0, 6) } }, res);
}

/// Construct a parser that will call `parser` on the string
/// but never fails to parse. The parser's result will be the
/// result of `parser` on success and `null` on failure.
pub fn opt(comptime parser: anytype) Parser(?ParserResult(@TypeOf(parser))) {
    const Res = Result(?ParserResult(@TypeOf(parser)));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            const r = try parser.parse(allocator, str);
            switch (r) {
                .ok => {},
                .err => return Res.pass(null, str, span(0, 0)),
            }
            return Res.pass(r.ok.value, r.ok.rest, r.ok.span);
        }
    }.parse };
}

test "opt" {
    const fa = testing.failing_allocator;
    const p1 = comptime ascii.range('a', 'z').opt();
    try p1.match(fa, "a", .{ .value = 'a', .span = span(0, 1) });
    try p1.match(fa, "aa", .{ .value = 'a', .rest = "a", .span = span(0, 1) });
    try p1.match(fa, "1", .{ .value = null, .rest = "1" });
}

fn parsersTypes(comptime parsers: anytype) []const type {
    var types: []const type = &[_]type{};
    for (parsers) |parser| {
        const T = ParserResult(@TypeOf(parser));
        if (T != void)
            types = types ++ [_]type{T};
    }
    return types;
}

fn Combine(comptime parsers: anytype) type {
    const types = parsersTypes(parsers);
    if (types.len == 0)
        return void;
    if (types.len == 1)
        return types[0];
    return Tuple(types.len, types[0..types.len].*);
}

/// HACK: Zig cannot cache functions that takes pointers (slices)
///       so we have to pass the types as an array, by value.
fn Tuple(comptime n: usize, comptime types: [n]type) type {
    return meta.Tuple(&types);
}

/// Takes a tuple of `Parser(any)` and constructs a parser that
/// only succeeds if all parsers succeed to parse. The parsers
/// will be called in order and parser `N` will use the `rest`
/// from parser `N-1`. The parse result will be a `Tuple` of
/// all parsers not of type `Parser(void)`. If only one parser
/// is not of type `Parser(void)` then this parser's result is
/// returned instead of a tuple.
pub fn combine(comptime parsers: anytype) Parser(Combine(parsers)) {
    const types = parsersTypes(parsers);
    const Res = Result(Combine(parsers));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            var res: Res = undefined;
            var pos: usize = 0;
            res.ok.rest = str;
            res.ok.span = span(0, 0);
            comptime var j = 0;
            inline for (parsers) |parser| {
                const r = try parser.parse(allocator, res.ok.rest);
                const value = switch (r) {
                    .ok => |ok| brk: {
                        pos += ok.span.len;
                        res.ok.rest = ok.rest;
                        break :brk ok.value;
                    },
                    .err => |e| return Res.fail(e.loc, pos + e.pos),
                };
                if (@TypeOf(value) != void) {
                    if (types.len == 1) {
                        res.ok.value = value;
                    } else {
                        res.ok.value[j] = value;
                    }
                    j += 1;
                }
            }
            return Res.pass(res.ok.value, res.ok.rest, span(0, pos));
        }
    }.parse };
}

test "combine" {
    const fa = testing.failing_allocator;

    const p1 = comptime combine(.{
        ascii.range('a', 'b').opt(),
        ascii.range('d', 'e').opt(),
    });
    try p1.match(fa, "ad", .{ .value = .{ .@"0" = 'a', .@"1" = 'd' }, .rest = "", .span = span(0, 2) });
    try p1.match(fa, "aa", .{ .value = .{ .@"0" = 'a', .@"1" = null }, .rest = "a", .span = span(0, 1) });
    try p1.match(fa, "da", .{ .value = .{ .@"0" = null, .@"1" = 'd' }, .rest = "a", .span = span(0, 1) });
    try p1.match(fa, "qa", .{ .value = .{ .@"0" = null, .@"1" = null }, .rest = "qa" });

    const p2 = comptime combine(.{
        ascii.range('a', 'b').opt(),
        ascii.char('d'),
    });
    try p2.match(fa, "ad", .{ .value = .{ .@"0" = 'a', .@"1" = 'd' }, .rest = "", .span = span(0, 2) });
    try p2.match(fa, "ada", .{ .value = .{ .@"0" = 'a', .@"1" = 'd' }, .rest = "a", .span = span(0, 2) });
    try p2.match(fa, "da", .{ .value = .{ .@"0" = null, .@"1" = 'd' }, .rest = "a", .span = span(0, 1) });
    try p2.fail(fa, "qa", 0);

    const p3 = comptime combine(.{ascii.char(' ').discard()});
    try p3.match(fa, " ", .{ .value = {}, .span = span(0, 1) });

    const p4 = comptime combine(.{
        int(usize, .{}),
        ascii.char(' ').discard(),
    }).asStr();
    try p4.match(fa, "10 ", .{ .value = "10 ", .rest = "", .span = span(0, 3) });

    const p5 = comptime combine(.{
        int(usize, .{}),
        ascii.char(' ').discard(),
    }).manyN(2, .{}).asStr();
    try p5.match(fa, "10 10 ", .{ .value = "10 10 ", .rest = "", .span = span(0, 6) });
}

/// Takes a tuple of `Parser(T)` and constructs a parser that
/// succeeds when at least one of the child parsers succeeds.
/// Note that /// parsers will be called in order, with `str`
/// as input. The parser will return with the type of the first
// child parser and the result of the first child parser
/// that succeeds. The parser result will be `Result(T)`.
pub fn oneOf(comptime parsers: anytype) Parser(ParserResult(@TypeOf(parsers[0]))) {
    inline for (parsers) |parser|
        typecheckParser(@TypeOf(parser));
    return .{ .parse = struct {
        const Res = Result(ParserResult(@TypeOf(parsers[0])));
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            inline for (parsers) |p| {
                const r = try p.parse(allocator, str);
                switch (r) {
                    .ok => return r,
                    .err => {},
                }
            }
            return Res.fail(@src(), 0);
        }
    }.parse };
}

test "oneOf" {
    const fa = testing.failing_allocator;
    const p1 = comptime oneOf(.{
        ascii.range('a', 'b'),
        ascii.range('d', 'e'),
    });
    try p1.match(fa, "a", .{ .value = 'a', .span = span(0, 1) });
    try p1.match(fa, "b", .{ .value = 'b', .span = span(0, 1) });
    try p1.match(fa, "d", .{ .value = 'd', .span = span(0, 1) });
    try p1.match(fa, "e", .{ .value = 'e', .span = span(0, 1) });
    try p1.match(fa, "aa", .{ .value = 'a', .rest = "a", .span = span(0, 1) });
    try p1.match(fa, "ba", .{ .value = 'b', .rest = "a", .span = span(0, 1) });
    try p1.match(fa, "da", .{ .value = 'd', .rest = "a", .span = span(0, 1) });
    try p1.match(fa, "ea", .{ .value = 'e', .rest = "a", .span = span(0, 1) });
    try p1.fail(fa, "q", 0);
}

/// Takes any parser (preferable not of type `Parser([]const u8)`)
/// and converts it to a parser where the result is a string that
/// contains all characters parsed by `parser`.
pub fn asStr(comptime parser: anytype) Parser([]const u8) {
    const Res = Result([]const u8);
    typecheckParser(@TypeOf(parser));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            const r = try parser.parse(allocator, str);
            switch (r) {
                .err => return Res.failWith(r, 0),
                .ok => {},
            }
            const len = str.len - r.ok.rest.len;
            return Res.pass(str[0..len], r.ok.rest, span(0, len));
        }
    }.parse };
}

test "asStr" {
    const fa = testing.failing_allocator;
    const p1 = comptime ascii.char('a').asStr();
    try p1.match(fa, "a", .{ .value = "a", .rest = "", .span = span(0, 1) });
    try p1.match(fa, "aa", .{ .value = "a", .rest = "a", .span = span(0, 1) });
    try p1.fail(fa, "ba", 0);

    const p2 = comptime combine(.{
        ascii.range('a', 'b').opt(),
        ascii.range('d', 'e').opt(),
    }).asStr();
    try p2.match(fa, "ad", .{ .value = "ad", .rest = "", .span = span(0, 2) });
    try p2.match(fa, "aa", .{ .value = "a", .rest = "a", .span = span(0, 1) });
    try p2.match(fa, "da", .{ .value = "d", .rest = "a", .span = span(0, 1) });
    try p2.match(fa, "qa", .{ .value = "", .rest = "qa", .span = span(0, 0) });
}

fn ReturnTypeErrorPayload(comptime P: type) type {
    const return_type = ReturnType(P);
    return switch (@typeInfo(return_type)) {
        .error_union => |eu| eu.payload,
        else => return_type,
    };
}

/// Constructs a parser that has its result converted with the
/// `conv` function. The ´conv` functions signature is
/// `*const fn (mem.Allocator, ParserResult(parser)) !T`.
/// The parser constructed will fail if `conv` fails.
pub fn convert(
    comptime parser: anytype,
    comptime conv: anytype,
) Parser(ReturnTypeErrorPayload(@TypeOf(conv))) {
    const Res = Result(ReturnTypeErrorPayload(@TypeOf(conv)));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            const r = try parser.parse(allocator, str);
            switch (r) {
                .err => return Res.failWith(r, 0),
                .ok => {},
            }
            const v = conv(allocator, r.ok.value) catch |e| switch (@as(anyerror, e)) {
                error.OutOfMemory => |o| return o,
                else => return Res.fail(@src(), 0),
            };
            return Res.pass(v, r.ok.rest, r.ok.span);
        }
    }.parse };
}

/// Constructs a convert function for `convert` that takes a
/// string and parses it to an int of type `Int`.
pub fn toInt(
    comptime Int: type,
    comptime base: u8,
) *const fn (mem.Allocator, []const u8) Error!Int {
    return struct {
        fn func(_: mem.Allocator, str: []const u8) Error!Int {
            return fmt.parseInt(Int, str, base);
        }
    }.func;
}

/// Constructs a convert function for `convert` that takes a
/// string and parses it to a float of type `Float`.
pub fn toFloat(comptime Float: type) *const fn (mem.Allocator, []const u8) Error!Float {
    return struct {
        fn func(_: mem.Allocator, str: []const u8) Error!Float {
            return fmt.parseFloat(Float, str);
        }
    }.func;
}

/// A convert function for `convert` that takes a string and
/// returns the first codepoint.
pub fn toChar(_: mem.Allocator, str: []const u8) Error!u21 {
    if (str.len > 1) {
        const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch
            return error.OtherError;
        if (cp_len > str.len)
            return error.OtherError;
        return unicode.utf8Decode(str[0..cp_len]) catch
            return error.OtherError;
    }
    return @as(u21, str[0]);
}

/// Constructs a convert function for `convert` that takes a
/// string and converts it to an `Enum` with `std.meta.stringToEnum`.
pub fn toEnum(comptime Enum: type) *const fn (mem.Allocator, []const u8) Error!Enum {
    return struct {
        fn func(_: mem.Allocator, str: []const u8) Error!Enum {
            return std.meta.stringToEnum(Enum, str) orelse error.OtherError;
        }
    }.func;
}

/// A convert function for `convert` that takes a string
/// and returns `true` if it is `"true"` and `false` if it
/// is `"false"`.
pub fn toBool(allocator: mem.Allocator, str: []const u8) Error!bool {
    const r = try toEnum(enum { false, true })(allocator, str);
    return r == .true;
}

test "convert" {
    const fa = testing.failing_allocator;

    const p1 = comptime string("123")
        .asStr()
        .convert(toInt(u8, 10));
    try p1.match(fa, "123", .{ .value = 123, .rest = "", .span = span(0, 3) });
    try p1.match(fa, "123a", .{ .value = 123, .rest = "a", .span = span(0, 3) });
    try p1.fail(fa, "12", 0);

    const p2 = comptime string("a")
        .asStr()
        .convert(toChar);
    try p2.match(fa, "a", .{ .value = 'a', .rest = "", .span = span(0, 1) });
    try p2.match(fa, "aa", .{ .value = 'a', .rest = "a", .span = span(0, 1) });
    try p2.fail(fa, "b", 0);

    const p3 = comptime rest.convert(toBool);
    try p3.match(fa, "true", .{ .value = true, .rest = "", .span = span(0, 4) });
    try p3.match(fa, "false", .{ .value = false, .rest = "", .span = span(0, 5) });
    try p3.fail(fa, "b", 0);

    const p4 = comptime string("1.23")
        .asStr()
        .convert(toFloat(f32));
    try p4.match(fa, "1.23", .{ .value = 1.23, .rest = "", .span = span(0, 4) });
    try p4.match(fa, "1.23a", .{ .value = 1.23, .rest = "a", .span = span(0, 4) });
    try p4.fail(fa, "1.2", 0);

    const E = enum(u8) { a, b, _ };
    const p5 = comptime rest.convert(toEnum(E));
    try p5.match(fa, "a", .{ .value = E.a, .rest = "", .span = span(0, 1) });
    try p5.match(fa, "b", .{ .value = E.b, .rest = "", .span = span(0, 1) });
    try p5.fail(fa, "2", 0);

    const p6 = comptime string("Āā")
        .asStr()
        .convert(toChar);
    try p6.match(fa, "Āā", .{ .value = 0x100, .rest = "", .span = span(0, 4) });
}

/// Constructs a parser that has its result converted with the
/// `conv` function. The ´conv` functions signature is
/// `*const fn (ParserResult(parser)) T`, so this function should only
/// be used for conversions that cannot fail. See `convert`.
pub fn map(
    comptime parser: anytype,
    comptime conv: anytype,
) Parser(ReturnType(@TypeOf(conv))) {
    const ConvT = ReturnType(@TypeOf(conv));
    const Res = Result(ConvT);
    typecheckParser(@TypeOf(parser));
    return .{
        .parse = struct {
            fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
                const r = try parser.parse(allocator, str);
                switch (r) {
                    .err => return Res.failWith(r, 0),
                    .ok => {},
                }
                return Res.pass(conv(r.ok.value), r.ok.rest, r.ok.span);
            }
        }.parse,
    };
}

/// Constructs a parser that consumes the input with `parser`
/// and places `value` into it's result. Discarding `parser`
/// result value, but keeping it's rest. This can be used
/// to map parsers to static values, for example `\n` to
/// the newline character.
pub fn mapConst(
    comptime parser: anytype,
    comptime value: anytype,
) Parser(@TypeOf(value)) {
    const Res = Result(@TypeOf(value));
    typecheckParser(@TypeOf(parser));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            const r = try parser.parse(allocator, str);
            switch (r) {
                .err => return Res.failWith(r, 0),
                .ok => {},
            }
            return Res.pass(value, r.ok.rest, r.ok.span);
        }
    }.parse };
}

test "mapConst" {
    const fa = testing.failing_allocator;
    const p1 = comptime string("123")
        .asStr()
        .mapConst(@as(u8, 3));
    try p1.match(fa, "123", .{ .value = 3, .rest = "", .span = span(0, 3) });
}

fn ToStructResult(comptime T: type) type {
    return @TypeOf(struct {
        fn func(_: anytype) T {
            return undefined;
        }
    }.func);
}

/// Constructs a convert function for `map` that takes a tuple, array or
// single value and converts it into the struct `T`. Fields will be assigned
// in order, so `tuple[i]` will be assigned to the ith field of `T`.
// This function will give a compile error if `T` and the tuple does not have
// the same number of fields, or if the items of the tuple cannot be coerced into
/// the fields of the struct.
pub fn toStruct(comptime T: type) ToStructResult(T) {
    return struct {
        fn func(value: anytype) T {
            const struct_fields = @typeInfo(T).@"struct".fields;
            const copy_many = switch (@typeInfo(@TypeOf(value))) {
                .@"struct" => |info| info.is_tuple and info.fields.len == struct_fields.len,
                .array => |info| info.len == struct_fields.len,
                else => false,
            };
            var res: T = undefined;
            if (copy_many) {
                inline for (struct_fields, 0..) |field, i|
                    @field(res, field.name) = value[i];
                return res;
            } else {
                if (struct_fields.len != 1)
                    @compileError("Cannot map " ++ @typeName(@TypeOf(value)) ++ " to " ++ @typeName(T));
                @field(res, struct_fields[0].name) = value;
                return res;
            }
        }
    }.func;
}

/// Constructs a conversion function for `map` that initializes a union `T`
/// with the value passed to it using `@unionInit` with the tag `tag`.
pub fn unionInit(comptime T: type, comptime tag: @typeInfo(T).@"union".tag_type.?) ToStructResult(T) {
    return struct {
        fn func(x: anytype) T {
            return @unionInit(T, @tagName(tag), x);
        }
    }.func;
}

test "map" {
    const fa = testing.failing_allocator;
    const Point = struct {
        x: usize,
        y: usize,
    };
    const p1 = comptime combine(.{
        int(usize, .{}),
        ascii.char(' ').discard(),
        int(usize, .{}),
    }).map(toStruct(Point));
    try p1.match(fa, "10 10", .{ .value = .{ .x = 10, .y = 10 }, .rest = "", .span = span(0, 5) });
    try p1.match(fa, "20 20aa", .{ .value = .{ .x = 20, .y = 20 }, .rest = "aa", .span = span(0, 5) });
    try p1.fail(fa, "12", 2);

    const p2 = comptime combine(.{
        int(usize, .{}),
        ascii.char(' ').discard(),
    }).manyN(2, .{}).map(toStruct(Point));
    try p2.match(fa, "10 10 ", .{ .value = .{ .x = 10, .y = 10 }, .rest = "", .span = span(0, 6) });
    try p2.match(fa, "20 20 aa", .{ .value = .{ .x = 20, .y = 20 }, .rest = "aa", .span = span(0, 6) });
    try p2.fail(fa, "12", 2);

    const Person = struct {
        name: []const u8,
        age: u32,
    };
    const MessageType = enum {
        point,
        person,
    };
    const Message = union(MessageType) { point: Point, person: Person };
    const p3 = comptime combine(.{
        int(usize, .{}),
        ascii.char(' ').discard(),
        int(usize, .{}),
    }).map(toStruct(Point)).map(unionInit(Message, MessageType.point));
    try p3.match(fa, "20 20", .{ .value = .{ .point = .{ .x = 20, .y = 20 } }, .rest = "", .span = span(0, 5) });

    const p4 = comptime combine(.{
        many(ascii.alphabetic, .{ .min = 1, .collect = false }),
        ascii.char(' ').discard(),
        int(u32, .{}),
    }).map(toStruct(Person)).map(unionInit(Message, MessageType.person));
    const r4 = try p4.parse(fa, "Bob 24");
    try testing.expectEqualStrings("Bob", r4.ok.value.person.name);
    try testing.expectEqual(24, r4.ok.value.person.age);
    try testing.expectEqual(span(0, 6), r4.ok.span);

    const Wrapper = struct {
        value: []const u8,
    };
    const wp = comptime string("foo").map(toStruct(Wrapper));
    const wr = try wp.parse(fa, "foo");
    try testing.expectEqualStrings("foo", wr.ok.value.value);
    try testing.expectEqual(span(0, 3), wr.ok.span);
}

/// Constructs a parser that discards the result returned from the parser
/// it wraps.
pub fn discard(comptime parser: anytype) Parser(void) {
    return parser.map(struct {
        fn d(_: anytype) void {}
    }.d);
}

test "discard" {
    const fa = testing.failing_allocator;
    const p1 = comptime ascii.char(' ').many(.{ .collect = false }).discard();
    try p1.match(fa, "abc", .{ .value = {}, .rest = "abc" });
    try p1.match(fa, " abc", .{ .value = {}, .rest = "abc", .span = span(0, 1) });
    try p1.match(fa, "  abc", .{ .value = {}, .rest = "abc", .span = span(0, 2) });
}

fn digitsForBase(val: anytype, base: u8) usize {
    var res: usize = 0;
    var tmp = val;
    while (tmp != 0) : (tmp /= @intCast(base))
        res += 1;
    return math.max(1, res);
}

pub const IntOptions = struct {
    /// Parse `+/-` prefix of the int as well
    parse_sign: bool = true,
    base: u8 = 10,
    max_digits: usize = math.maxInt(usize),
};

/// Construct a parser that succeeds if it parser an integer of
/// `base`. This parser will stop parsing digits after `max_digits`
/// after the leading zeros haven been reached. The result of this
/// parser will be the string containing the match.
pub fn intToken(comptime options: IntOptions) Parser([]const u8) {
    debug.assert(options.max_digits != 0);
    const sign_parser = if (options.parse_sign)
        oneOf(.{ .ok = .{ ascii.char('-'), ascii.char('+'), noop } })
    else
        noop;
    return comptime combine(.{
        sign_parser,
        ascii.digit(options.base).many(.{
            .collect = false,
            .min = 1,
            .max = options.max_digits,
        }),
    }).asStr();
}

/// Same as `intToken` but also converts the parsed string to an
/// integer. This parser will at most parse the same number of digits
/// as the underlying integer can hold in the specified base.
pub fn int(comptime Int: type, comptime options: IntOptions) Parser(Int) {
    debug.assert(options.max_digits != 0);
    const Res = Result(Int);
    return .{ .parse = struct {
        fn parse(_: mem.Allocator, str: []const u8) Error!Res {
            if (options.parse_sign and str.len != 0) {
                switch (str[0]) {
                    '+' => return parseAfterSign(str[1..], add, true),
                    '-' => return parseAfterSign(str[1..], sub, true),
                    else => {},
                }
            }
            return parseAfterSign(str, add, false);
        }

        fn parseAfterSign(
            str: []const u8,
            add_sub: *const fn (Int, Int) Overflow!Int,
            sign: bool,
        ) Error!Res {
            if (str.len == 0)
                return Res.fail(@src(), 0);

            const max_digits = @min(str.len, options.max_digits);
            const first = fmt.charToDigit(str[0], options.base) catch
                return Res.fail(@src(), 0);
            const first_casted = math.cast(Int, first) orelse
                return Res.fail(@src(), 0);

            var res = add_sub(0, first_casted) catch
                return Res.fail(@src(), 0);
            const end = for (str[1..max_digits], 0..) |c, i| {
                const d = fmt.charToDigit(c, options.base) catch break i;
                const casted_b = math.cast(Int, options.base) orelse break i;
                const casted_d = math.cast(Int, d) orelse break i;

                const next = math.mul(Int, res, casted_b) catch break i;
                res = add_sub(next, casted_d) catch break i;
            } else max_digits - 1;

            const sp_len = if (sign)
                end + 2
            else
                end + 1;

            return Res.pass(res, str[end + 1 ..], span(0, sp_len));
        }

        const Overflow = error{Overflow};

        fn add(a: Int, b: Int) Overflow!Int {
            return math.add(Int, a, b);
        }

        fn sub(a: Int, b: Int) Overflow!Int {
            return math.sub(Int, a, b);
        }
    }.parse };
}

test "int" {
    const fa = testing.failing_allocator;
    const p1 = int(u8, .{});
    try p1.match(fa, "0", .{ .value = 0, .rest = "", .span = span(0, 1) });
    try p1.match(fa, "1", .{ .value = 1, .rest = "", .span = span(0, 1) });
    try p1.match(fa, "1a", .{ .value = 1, .rest = "a", .span = span(0, 1) });
    try p1.match(fa, "255", .{ .value = 255, .rest = "", .span = span(0, 3) });
    try p1.match(fa, "2555", .{ .value = 255, .rest = "5", .span = span(0, 3) });
    try p1.match(fa, "256", .{ .value = 25, .rest = "6", .span = span(0, 2) });
    try p1.match(fa, "+255", .{ .value = 255, .rest = "", .span = span(0, 4) });
    try p1.fail(fa, "-255", 0);

    const p2 = int(u8, .{ .base = 16 });
    try p2.match(fa, "0", .{ .value = 0x00, .rest = "", .span = span(0, 1) });
    try p2.match(fa, "1", .{ .value = 0x01, .rest = "", .span = span(0, 1) });
    try p2.match(fa, "1a", .{ .value = 0x1a, .rest = "", .span = span(0, 2) });
    try p2.match(fa, "1g", .{ .value = 0x01, .rest = "g", .span = span(0, 1) });
    try p2.match(fa, "ff", .{ .value = 0xff, .rest = "", .span = span(0, 2) });
    try p2.match(fa, "FF", .{ .value = 0xff, .rest = "", .span = span(0, 2) });
    try p2.match(fa, "00FF", .{ .value = 0xff, .rest = "", .span = span(0, 4) });
    try p2.match(fa, "100", .{ .value = 0x10, .rest = "0", .span = span(0, 2) });
    try p2.match(fa, "fg", .{ .value = 0x0f, .rest = "g", .span = span(0, 1) });
    try p2.match(fa, "+ff", .{ .value = 0xff, .rest = "", .span = span(0, 3) });
    try p2.fail(fa, "-ff", 0);

    const p3 = int(u8, .{ .base = 16, .max_digits = 2 });
    try p3.match(fa, "FF", .{ .value = 0xff, .rest = "", .span = span(0, 2) });
    try p3.match(fa, "00FF", .{ .value = 0x00, .rest = "FF", .span = span(0, 2) });

    const p4 = int(isize, .{});
    try p4.match(fa, "+255", .{ .value = 255, .rest = "", .span = span(0, 4) });
    try p4.match(fa, "-255", .{ .value = -255, .rest = "", .span = span(0, 4) });

    const p5 = int(isize, .{ .parse_sign = false });
    try p5.match(fa, "255", .{ .value = 255, .rest = "", .span = span(0, 3) });
    try p5.fail(fa, "+255", 0);
    try p5.fail(fa, "-255", 0);
}

/// Construct a parser that succeeds if it parses any tag from `Enum` as
/// a string. The longest match is always chosen, so for `enum{a,aa}` the
/// "aa" string will succeed parsing and have the result of `.aa` and not
/// `.a`.
pub fn enumeration(comptime Enum: type) Parser(Enum) {
    const Res = Result(Enum);
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            var res: Error!Res = Res.fail(@src(), 0);
            inline for (@typeInfo(Enum).@"enum".fields) |field| next: {
                const p = comptime string(field.name);
                const new = try p.parse(allocator, str);
                switch (new) {
                    .err => break :next,
                    .ok => {},
                }
                const old = .{ .ok = .{ .value = undefined, .rest = str } };
                if (new.ok.rest.len < old.ok.rest.len)
                    res = Res{ .ok = .{
                        .value = @field(Enum, field.name),
                        .rest = new.ok.rest,
                        .span = new.ok.span,
                    } };
            }
            return res;
        }
    }.parse };
}

test "enumeration" {
    const fa = testing.failing_allocator;
    const E1 = enum { a, b, aa };
    const p1 = enumeration(E1);
    try p1.match(fa, "a", .{ .value = .a, .rest = "", .span = span(0, 1) });
    try p1.match(fa, "aa", .{ .value = .aa, .rest = "", .span = span(0, 2) });
    try p1.match(fa, "b", .{ .value = .b, .rest = "", .span = span(0, 1) });
    try p1.match(fa, "ab", .{ .value = .a, .rest = "b", .span = span(0, 1) });
    try p1.match(fa, "bb", .{ .value = .b, .rest = "b", .span = span(0, 1) });
    try p1.fail(fa, "256", 0);
}

/// Creates a parser that calls a function to obtain its underlying parser.
/// This function introduces the indirection required for recursive grammars.
/// ```
/// const digit_10 = discard(digit(10));
/// const digits = oneOf(.{ .ok = .{ combine(.{ digit_10, ref(digitsRef) }), digit_10 } });
/// fn digitsRef() Parser(void) {
///     return digits;
/// };
/// ```
pub fn ref(comptime func: anytype) ReturnType(@TypeOf(func)) {
    const P = ReturnType(@TypeOf(func));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Result(ParserResult(P)) {
            return func().parse(allocator, str);
        }
    }.parse };
}

test "ref" {
    const fa = testing.failing_allocator;
    const Scope = struct {
        const digit = ascii.digit(10).discard();
        const digits = oneOf(.{
            combine(.{ digit, ref(digitsRef) }),
            digit,
        });
        fn digitsRef() Parser(void) {
            return digits;
        }
    };

    try Scope.digits.match(fa, "0", .{ .value = {}, .span = span(0, 1) });
}

test "pos on fail" {
    const fa = testing.failing_allocator;
    const p1 = comptime combine(.{
        ascii.char('[').discard(),
        combine(.{
            int(u8, .{}),
            combine(.{
                ascii.char(',').discard(),
                int(u8, .{}),
            }).many(.{ .collect = false }),
        }).opt(),
        ascii.char(']').discard(),
    }).discard();
    try p1.match(fa, "[]", .{ .value = {}, .span = span(0, 2) });
    try p1.match(fa, "[1]", .{ .value = {}, .span = span(0, 3) });
    try p1.match(fa, "[1,2]", .{ .value = {}, .span = span(0, 5) });
    try p1.fail(fa, "[1,2", 4);
}

pub fn expectResult(
    comptime T: type,
    expected: Result(T),
    actual: Result(T),
) !void {
    try testing.expectEqualStrings(expected.ok.rest, actual.ok.rest);
    try testing.expectEqual(expected.ok.span.start, actual.ok.span.start);
    try testing.expectEqual(expected.ok.span.len, actual.ok.span.len);
    switch (T) {
        []const u8 => try testing.expectEqualStrings(expected.ok.value, actual.ok.value),
        else => switch (@typeInfo(T)) {
            .pointer => |ptr| try testing.expectEqualSlices(ptr.child, expected.ok.value, actual.ok.value),
            else => try testing.expectEqual(expected.ok.value, actual.ok.value),
        },
    }
}
