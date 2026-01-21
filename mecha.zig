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
        pub const inspect = mecha.inspect;
    };
}

/// The result of a parse. where `ok` corresponds to a successful parse and `err` denotes a
/// failure. The result will be placed in `value` and `index` will indicate how much of the input
/// was parsed.
pub fn Result(comptime T: type) type {
    return struct {
        /// An index into the input string pointing to the end of what was parsed.
        index: usize,

        /// The value parsed. Can either be `ok`, meaning parsing was successful, or `err` meaning
        /// the string could not be parsed.
        value: union(enum) {
            ok: T,
            err,
        },

        pub fn ok(index: usize, value: T) @This() {
            return .{ .index = index, .value = .{ .ok = value } };
        }

        pub fn err(index: usize) @This() {
            return .{ .index = index, .value = .err };
        }
    };
}

// All the ways in which a parser can fail.
pub const Error = error{OtherError} || mem.Allocator.Error;

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

/// A parser that always succeeds and parses nothing. This parser is only really useful for
/// generic code. See `many`.
pub const noop = Parser(void){ .parse = struct {
    const Res = Result(void);
    fn parse(_: mem.Allocator, _: []const u8) Error!Res {
        return Res.ok(0, {});
    }
}.parse };

/// A parser that only succeeds on the end of the string.
pub const eos = Parser(void){ .parse = struct {
    const Res = Result(void);
    fn parse(_: mem.Allocator, str: []const u8) Error!Res {
        if (str.len != 0)
            return Res.err(0);
        return Res.ok(0, {});
    }
}.parse };

test "eos" {
    const fa = testing.failing_allocator;
    try expectOk(void, 0, {}, try eos.parse(fa, ""));
    try expectOk(void, 0, {}, try eos.parse(fa, ""));
    try expectErr(void, 0, try eos.parse(fa, "a"));
}

/// A parser that always succeeds with the result being the entire string. The same as the '.*$'
/// regex.
pub const rest = Parser([]const u8){ .parse = struct {
    const Res = Result([]const u8);
    fn parse(_: mem.Allocator, str: []const u8) Error!Res {
        return Res.ok(str.len, str);
    }
}.parse };

test "rest" {
    const fa = testing.failing_allocator;
    try expectOk([]const u8, 0, "", try rest.parse(fa, ""));
    try expectOk([]const u8, 1, "a", try rest.parse(fa, "a"));
}

/// Construct a parser that succeeds if the string passed in starts with `str`.
pub fn string(comptime str: []const u8) Parser([]const u8) {
    const Res = Result([]const u8);
    return .{ .parse = struct {
        fn parse(_: mem.Allocator, s: []const u8) Error!Res {
            if (!mem.startsWith(u8, s, str))
                return Res.err(0);
            return Res.ok(str.len, str);
        }
    }.parse };
}

test "string" {
    const fa = testing.failing_allocator;
    const p = string("aa");
    try expectOk([]const u8, 2, "aa", try p.parse(fa, "aa"));
    try expectOk([]const u8, 2, "aa", try p.parse(fa, "aaa"));
    try expectErr([]const u8, 0, try p.parse(fa, "ba"));
    try expectErr([]const u8, 0, try p.parse(fa, ""));
}

pub const ManyNOptions = struct {
    /// A parser used to parse the content between each element `manyN` parses. The default is
    /// `noop`, so each element will be parsed one after another.
    separator: Parser(void) = noop,
};

/// Construct a parser that repeatedly uses `parser` until `n` iterations is reached. The parser's
/// result will be an array of the results from the repeated parser.
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
                var res: Array = undefined;
                var index: usize = 0;
                for (&res, 0..) |*value, i| {
                    if (i != 0) {
                        const sep = try options.separator.parse(allocator, str[index..]);
                        index += sep.index;

                        switch (sep.value) {
                            .err => return Res.err(index),
                            .ok => {},
                        }
                    }

                    const r = try parser.parse(allocator, str[index..]);
                    index += r.index;

                    switch (r.value) {
                        .ok => |v| value.* = v,
                        .err => return Res.err(index),
                    }
                }
                return Res.ok(index, res);
            }
        }.parse,
    };
}

test "manyN" {
    const fa = testing.failing_allocator;
    const p1 = comptime ascii.range('a', 'b').manyN(3, .{});
    try expectOk([3]u8, 3, "aba".*, try p1.parse(fa, "ababab"));
    const p2 = comptime ascii.range('a', 'b')
        .manyN(3, .{ .separator = discard(ascii.char(',')) });
    try expectOk([3]u8, 5, "aba".*, try p2.parse(fa, "a,b,a,b,a,b"));
}

pub const ManyOptions = struct {
    /// The min number of elements `many` should parse for parsing to be considered successful.
    min: usize = 0,

    /// The maximum number of elements `many` will parse. `many` will stop parsing after reaching
    /// this number of elements even if more elements could be parsed.
    max: usize = math.maxInt(usize),

    /// Have `many` collect the results of all elements in an allocated slice. Setting this to
    /// false, and `many` will instead just return the parsed string as the result without any
    /// allocation.
    collect: bool = true,

    /// A parser used to parse the content between each element `many` parses. The default is
    /// `noop`, so each element will be parsed one after another.
    separator: Parser(void) = noop,
};

fn Many(comptime parser: anytype, comptime options: ManyOptions) type {
    if (options.collect)
        return []ParserResult(@TypeOf(parser));
    return []const u8;
}

/// Construct a parser that repeatedly uses `parser` as long as it succeeds or until `opt.max` is
/// reach. See `ManyOptions` for options this function exposes.
pub fn many(comptime parser: anytype, comptime options: ManyOptions) Parser(Many(parser, options)) {
    const ElementParser = @TypeOf(parser);
    const Element = ParserResult(ElementParser);
    const Res = Result(Many(parser, options));
    typecheckParser(ElementParser);

    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            var res = if (options.collect)
                try std.ArrayListUnmanaged(Element).initCapacity(allocator, options.min)
            else {};
            defer if (options.collect) res.deinit(allocator);

            var index: usize = 0;
            var i: usize = 0;
            while (i < options.max) : (i += 1) {
                var curr = index;
                if (i != 0) {
                    const sep = try options.separator.parse(allocator, str[curr..]);
                    curr += sep.index;

                    switch (sep.value) {
                        .ok => {},
                        .err => break,
                    }
                }

                const r = try parser.parse(allocator, str[curr..]);
                curr += r.index;

                switch (r.value) {
                    .ok => |value| {
                        if (options.collect)
                            try res.append(allocator, value);
                    },
                    .err => break,
                }

                index = curr;
            }

            if (i < options.min)
                return Res.err(index);

            const value = if (options.collect)
                try res.toOwnedSlice(allocator)
            else
                str[0..index];

            return Res.ok(index, value);
        }
    }.parse };
}

test "many" {
    const fa = testing.failing_allocator;

    const p1 = comptime string("ab")
        .many(.{ .collect = false });
    try expectOk([]const u8, 0, "", try p1.parse(fa, ""));
    try expectOk([]const u8, 0, "", try p1.parse(fa, "a"));
    try expectOk([]const u8, 2, "ab", try p1.parse(fa, "ab"));
    try expectOk([]const u8, 2, "ab", try p1.parse(fa, "aba"));
    try expectOk([]const u8, 4, "abab", try p1.parse(fa, "abab"));
    try expectOk([]const u8, 4, "abab", try p1.parse(fa, "ababa"));
    try expectOk([]const u8, 6, "ababab", try p1.parse(fa, "ababab"));

    const p2 = comptime string("ab")
        .many(.{ .collect = false, .min = 1, .max = 2 });
    try expectErr([]const u8, 0, try p2.parse(fa, ""));
    try expectErr([]const u8, 0, try p2.parse(fa, "a"));
    try expectOk([]const u8, 2, "ab", try p2.parse(fa, "ab"));
    try expectOk([]const u8, 2, "ab", try p2.parse(fa, "aba"));
    try expectOk([]const u8, 4, "abab", try p2.parse(fa, "abab"));
    try expectOk([]const u8, 4, "abab", try p2.parse(fa, "ababa"));
    try expectOk([]const u8, 4, "abab", try p2.parse(fa, "ababab"));

    const p3 = comptime string("ab")
        .many(.{ .collect = false, .separator = discard(ascii.char(',')) });
    try expectOk([]const u8, 0, "", try p3.parse(fa, ""));
    try expectOk([]const u8, 0, "", try p3.parse(fa, "a"));
    try expectOk([]const u8, 2, "ab", try p3.parse(fa, "aba"));
    try expectOk([]const u8, 2, "ab", try p3.parse(fa, "abab"));
    try expectOk([]const u8, 5, "ab,ab", try p3.parse(fa, "ab,ab"));
    try expectOk([]const u8, 5, "ab,ab", try p3.parse(fa, "ab,ab,"));

    const p4 = comptime utf8.char(0x100)
        .many(.{ .collect = false });
    try expectOk([]const u8, 6, "ĀĀĀ", try p4.parse(fa, "ĀĀĀāāā"));

    const a = testing.allocator;

    const p5 = comptime utf8.range(0x100, 0x100).many(.{});
    const res = try p5.parse(a, "ĀĀĀāāā");
    defer a.free(res.value.ok);

    var expect = [_]u21{ 'Ā', 'Ā', 'Ā' };
    try expectOk([]u21, 6, &expect, res);

    const p6 = comptime utf8.range(0x100, 0x100).many(.{ .collect = true, .min = 1 });
    try expectErr([]u21, 0, try p6.parse(a, ""));
}

/// Construct a parser that will call `parser` on the string but never fails to parse. The parser's
///  result will be the result of `parser` on success and `null` on failure.
pub fn opt(comptime parser: anytype) Parser(?ParserResult(@TypeOf(parser))) {
    const Res = Result(?ParserResult(@TypeOf(parser)));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            const res = try parser.parse(allocator, str);
            return switch (res.value) {
                .ok => |value| Res.ok(res.index, value),
                .err => Res.ok(0, null),
            };
        }
    }.parse };
}

test "opt" {
    const fa = testing.failing_allocator;
    const p1 = comptime ascii.range('a', 'z').opt();
    try expectOk(?u8, 1, 'a', try p1.parse(fa, "a"));
    try expectOk(?u8, 1, 'a', try p1.parse(fa, "aa"));
    try expectOk(?u8, 0, null, try p1.parse(fa, "1"));
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

/// Takes a tuple of `Parser(any)` and constructs a parser that only succeeds if all parsers
/// succeed to parse. The parsers will be called in order and parser `N` will use the `rest` from
/// parser `N-1`. The parse result will be a `Tuple` of all parsers not of type `Parser(void)`. If
/// only one parser is not of type `Parser(void)` then this parser's result is returned instead of
/// a tuple.
pub fn combine(comptime parsers: anytype) Parser(Combine(parsers)) {
    const types = parsersTypes(parsers);
    const Value = Combine(parsers);
    const Res = Result(Value);
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            var value: Value = undefined;
            var index: usize = 0;
            comptime var j = 0;
            inline for (parsers) |parser| {
                const res = try parser.parse(allocator, str[index..]);
                index += res.index;

                const v = switch (res.value) {
                    .ok => |v| v,
                    .err => return Res.err(index),
                };

                if (@TypeOf(v) != void) {
                    if (types.len == 1) {
                        value = v;
                    } else {
                        value[j] = v;
                    }
                    j += 1;
                }
            }
            return Res.ok(index, value);
        }
    }.parse };
}

test "combine" {
    const fa = testing.failing_allocator;

    const p1 = comptime combine(.{
        ascii.range('a', 'b').opt(),
        ascii.range('d', 'e').opt(),
    });
    const P1 = @TypeOf(p1).T;
    try expectOk(P1, 2, .{ .@"0" = 'a', .@"1" = 'd' }, try p1.parse(fa, "ad"));
    try expectOk(P1, 1, .{ .@"0" = 'a', .@"1" = null }, try p1.parse(fa, "aa"));
    try expectOk(P1, 1, .{ .@"0" = null, .@"1" = 'd' }, try p1.parse(fa, "da"));
    try expectOk(P1, 0, .{ .@"0" = null, .@"1" = null }, try p1.parse(fa, "qa"));

    const p2 = comptime combine(.{
        ascii.range('a', 'b').opt(),
        ascii.char('d'),
    });
    const P2 = @TypeOf(p2).T;
    try expectOk(P2, 2, .{ .@"0" = 'a', .@"1" = 'd' }, try p2.parse(fa, "ad"));
    try expectOk(P2, 2, .{ .@"0" = 'a', .@"1" = 'd' }, try p2.parse(fa, "ada"));
    try expectOk(P2, 1, .{ .@"0" = null, .@"1" = 'd' }, try p2.parse(fa, "da"));
    try expectErr(P2, 0, try p2.parse(fa, "qa"));

    const p3 = comptime combine(.{ascii.char(' ').discard()});
    const P3 = @TypeOf(p3).T;
    try expectOk(P3, 1, {}, try p3.parse(fa, " "));

    const p4 = comptime combine(.{
        int(usize, .{}),
        ascii.char(' ').discard(),
    }).asStr();
    try expectOk([]const u8, 3, "10 ", try p4.parse(fa, "10 "));

    const p5 = comptime combine(.{
        int(usize, .{}),
        ascii.char(' ').discard(),
    }).manyN(2, .{}).asStr();
    try expectOk([]const u8, 6, "10 10 ", try p5.parse(fa, "10 10 "));
}

/// Takes a tuple of `Parser(T)` and constructs a parser that succeeds when at least one of the
/// child parsers succeeds. Note that parsers will be called in order, with `str` as input. The
/// parser will return with the type of the first child parser and the result of the first child
/// parser that succeeds. The parser result will be `Result(T)`.
pub fn oneOf(comptime parsers: anytype) Parser(ParserResult(@TypeOf(parsers[0]))) {
    inline for (parsers) |parser|
        typecheckParser(@TypeOf(parser));
    return .{ .parse = struct {
        const Res = Result(ParserResult(@TypeOf(parsers[0])));
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            var err_index: usize = 0;
            inline for (parsers) |p| {
                const res = try p.parse(allocator, str);
                switch (res.value) {
                    .ok => return res,
                    .err => err_index = @max(err_index, res.index),
                }
            }
            return Res.err(err_index);
        }
    }.parse };
}

test "oneOf" {
    const fa = testing.failing_allocator;
    const p1 = comptime oneOf(.{
        ascii.range('a', 'b'),
        ascii.range('d', 'e'),
    });
    try expectOk(u8, 1, 'a', try p1.parse(fa, "a"));
    try expectOk(u8, 1, 'b', try p1.parse(fa, "b"));
    try expectOk(u8, 1, 'd', try p1.parse(fa, "d"));
    try expectOk(u8, 1, 'e', try p1.parse(fa, "e"));
    try expectOk(u8, 1, 'a', try p1.parse(fa, "aa"));
    try expectOk(u8, 1, 'b', try p1.parse(fa, "ba"));
    try expectOk(u8, 1, 'd', try p1.parse(fa, "da"));
    try expectOk(u8, 1, 'e', try p1.parse(fa, "ea"));
    try expectErr(u8, 0, try p1.parse(fa, "q"));
}

/// Inspector struct used with `inspect` parser combinator.
/// `State` is the type returned by `Handler.onEnter` and passed to `Handler.onExit`.
/// If `Handler.onEnter` is `null`, `State` must be set to `void`.
pub fn Inspector(comptime T: type, comptime State: type) type {
    return struct {
        onEnter: ?*const fn ([]const u8) State,
        onExit: ?*const fn ([]const u8, Result(T), State) void,
    };
}

/// Inspects the parsing process by calling `inspector.onEnter` before parsing and `inspector.onExit` after parsing.
/// See `Inspector`
pub fn inspect(
    comptime parser: anytype,
    comptime State: type,
    comptime inspector: Inspector(ParserResult(@TypeOf(parser)), State),
) Parser(ParserResult(@TypeOf(parser))) {
    const Res = Result(ParserResult(@TypeOf(parser)));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, src: []const u8) Error!Res {
            const state = if (inspector.onEnter) |onEnter|
                onEnter(src)
            else {};
            const res = try parser.parse(allocator, src);
            if (inspector.onExit) |onExit| {
                onExit(src, res, state);
            }
            return res;
        }
    }.parse };
}

test "inspect" {
    const fa = testing.failing_allocator;

    const CountingInspector = struct {
        var enter_count: usize = 0;
        var success_count: usize = 0;
        var failure_count: usize = 0;

        fn get(comptime T: type) Inspector(T, void) {
            const Functions = struct {
                fn onEnter(_: []const u8) void {
                    enter_count += 1;
                }

                fn onExit(_: []const u8, res: Result(T), _: void) void {
                    switch (res.value) {
                        .ok => success_count += 1,
                        .err => failure_count += 1,
                    }
                }
            };
            return .{
                .onEnter = Functions.onEnter,
                .onExit = Functions.onExit,
            };
        }
    };

    const p1 = comptime ascii.char('a').inspect(void, CountingInspector.get(u8));
    try expectOk(u8, 1, 'a', try p1.parse(fa, "a"));
    try expectOk(u8, 1, 'a', try p1.parse(fa, "aa"));
    try expectErr(u8, 0, try p1.parse(fa, "b"));

    try testing.expectEqual(3, CountingInspector.enter_count);
    try testing.expectEqual(2, CountingInspector.success_count);
    try testing.expectEqual(1, CountingInspector.failure_count);

    // Inspect handler without onEnter
    const CountingInspectorNoEnter = struct {
        var success_count: usize = 0;
        var failure_count: usize = 0;

        fn get(comptime T: type) Inspector(T, void) {
            const Functions = struct {
                fn onExit(_: []const u8, res: Result(T), _: void) void {
                    switch (res.value) {
                        .ok => success_count += 1,
                        .err => failure_count += 1,
                    }
                }
            };
            return .{
                .onEnter = null,
                .onExit = Functions.onExit,
            };
        }
    };
    const p2 = comptime ascii.char('a').inspect(void, CountingInspectorNoEnter.get(u8));
    try expectOk(u8, 1, 'a', try p2.parse(fa, "a"));
    try expectErr(u8, 0, try p2.parse(fa, "b"));
    try testing.expectEqual(1, CountingInspectorNoEnter.success_count);
    try testing.expectEqual(1, CountingInspectorNoEnter.failure_count);

    // Usage for State
    const CountParsedBytesInspector = struct {
        var total_parsed: usize = 0;

        fn get(comptime T: type) Inspector(T, usize) {
            const Functions = struct {
                fn onEnter(src: []const u8) usize {
                    return src.len;
                }

                fn onExit(_: []const u8, res: Result(T), state: usize) void {
                    switch (res.value) {
                        .ok => total_parsed += state,
                        .err => {},
                    }
                }
            };
            return .{
                .onEnter = Functions.onEnter,
                .onExit = Functions.onExit,
            };
        }
    };
    const p3 = comptime ascii.char('a').inspect(usize, CountParsedBytesInspector.get(u8));
    try expectOk(u8, 1, 'a', try p3.parse(fa, "a"));
    try expectOk(u8, 1, 'a', try p3.parse(fa, "aa"));
    try expectErr(u8, 0, try p3.parse(fa, "b"));
    try testing.expectEqual(3, CountParsedBytesInspector.total_parsed);
}

/// Takes any parser and converts it to a parser where the result is a string that contains all
/// characters parsed by the parser.
pub fn asStr(comptime parser: anytype) Parser([]const u8) {
    const Res = Result([]const u8);
    typecheckParser(@TypeOf(parser));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            const res = try parser.parse(allocator, str);
            return switch (res.value) {
                .ok => Res.ok(res.index, str[0..res.index]),
                .err => Res.err(0),
            };
        }
    }.parse };
}

test "asStr" {
    const fa = testing.failing_allocator;
    const p1 = comptime ascii.char('a').asStr();
    try expectOk([]const u8, 1, "a", try p1.parse(fa, "a"));
    try expectOk([]const u8, 1, "a", try p1.parse(fa, "aa"));
    try expectErr([]const u8, 0, try p1.parse(fa, "ba"));

    const p2 = comptime combine(.{
        ascii.range('a', 'b').opt(),
        ascii.range('d', 'e').opt(),
    }).asStr();
    try expectOk([]const u8, 2, "ad", try p2.parse(fa, "ad"));
    try expectOk([]const u8, 1, "a", try p2.parse(fa, "aa"));
    try expectOk([]const u8, 1, "d", try p2.parse(fa, "da"));
    try expectOk([]const u8, 0, "", try p2.parse(fa, "qa"));
}

fn ReturnTypeErrorPayload(comptime P: type) type {
    const return_type = ReturnType(P);
    return switch (@typeInfo(return_type)) {
        .error_union => |eu| eu.payload,
        else => return_type,
    };
}

pub const ConvertError = error{ConversionFailed} || Error;

/// Constructs a parser that has its result converted with the `conv` function. The ´conv`
/// functions signature is `*const fn (mem.Allocator, ParserResult(parser)) ConvertError!T`. The
/// parser constructed will fail if `conv` fails.
pub fn convert(
    comptime parser: anytype,
    comptime conv: anytype,
) Parser(ReturnTypeErrorPayload(@TypeOf(conv))) {
    const Res = Result(ReturnTypeErrorPayload(@TypeOf(conv)));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            const res = try parser.parse(allocator, str);
            switch (res.value) {
                .err => return Res.err(res.index),
                .ok => |value| {
                    const v = conv(allocator, value) catch |err| switch (@as(ConvertError, err)) {
                        error.ConversionFailed => return Res.err(0),
                        error.OtherError, error.OutOfMemory => |e| return e,
                    };
                    return Res.ok(res.index, v);
                },
            }
        }
    }.parse };
}

/// Constructs a convert function for `convert` that takes a string and parses it to an int of
/// type `Int`.
pub fn toInt(
    comptime Int: type,
    comptime base: u8,
) *const fn (mem.Allocator, []const u8) ConvertError!Int {
    return struct {
        fn func(_: mem.Allocator, str: []const u8) ConvertError!Int {
            return fmt.parseInt(Int, str, base) catch return error.ConversionFailed;
        }
    }.func;
}

/// Constructs a convert function for `convert` that takes a string and parses it to a float of
/// type `Float`.
pub fn toFloat(comptime Float: type) *const fn (mem.Allocator, []const u8) ConvertError!Float {
    return struct {
        fn func(_: mem.Allocator, str: []const u8) ConvertError!Float {
            return fmt.parseFloat(Float, str) catch return error.ConversionFailed;
        }
    }.func;
}

/// A convert function for `convert` that takes a string and returns the first codepoint.
pub fn toChar(_: mem.Allocator, str: []const u8) ConvertError!u21 {
    if (str.len == 0)
        return error.ConversionFailed;

    const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch return error.ConversionFailed;
    if (cp_len != str.len)
        return error.ConversionFailed;

    return unicode.utf8Decode(str[0..cp_len]) catch return error.ConversionFailed;
}

/// Constructs a convert function for `convert` that takes a string and converts it to an `Enum`
/// with `std.meta.stringToEnum`.
pub fn toEnum(comptime Enum: type) *const fn (mem.Allocator, []const u8) ConvertError!Enum {
    return struct {
        fn func(_: mem.Allocator, str: []const u8) ConvertError!Enum {
            return std.meta.stringToEnum(Enum, str) orelse error.ConversionFailed;
        }
    }.func;
}

/// A convert function for `convert` that takes a string and returns `true` if it is `"true"` and
/// `false` if it is `"false"`.
pub fn toBool(allocator: mem.Allocator, str: []const u8) ConvertError!bool {
    const r = try toEnum(enum { false, true })(allocator, str);
    return r == .true;
}

test "convert" {
    const fa = testing.failing_allocator;

    const p1 = comptime string("123")
        .asStr()
        .convert(toInt(u8, 10));
    try expectOk(u8, 3, 123, try p1.parse(fa, "123"));
    try expectOk(u8, 3, 123, try p1.parse(fa, "123a"));
    try expectErr(u8, 0, try p1.parse(fa, "12"));

    const p2 = comptime string("a")
        .asStr()
        .convert(toChar);
    try expectOk(u21, 1, 'a', try p2.parse(fa, "a"));
    try expectOk(u21, 1, 'a', try p2.parse(fa, "aa"));
    try expectErr(u21, 0, try p2.parse(fa, "b"));

    const p3 = comptime rest.convert(toBool);
    try expectOk(bool, 4, true, try p3.parse(fa, "true"));
    try expectOk(bool, 5, false, try p3.parse(fa, "false"));
    try expectErr(bool, 0, try p3.parse(fa, "b"));

    const p4 = comptime string("1.23")
        .asStr()
        .convert(toFloat(f32));
    try expectOk(f32, 4, 1.23, try p4.parse(fa, "1.23"));
    try expectOk(f32, 4, 1.23, try p4.parse(fa, "1.23a"));
    try expectErr(f32, 0, try p4.parse(fa, "1.2"));

    const E = enum(u8) { a, b, _ };
    const p5 = comptime rest.convert(toEnum(E));
    try expectOk(E, 1, .a, try p5.parse(fa, "a"));
    try expectOk(E, 1, .b, try p5.parse(fa, "b"));
    try expectErr(E, 0, try p5.parse(fa, "2"));

    const p6 = comptime string("Ā")
        .asStr()
        .convert(toChar);
    try expectOk(u21, 2, 0x100, try p6.parse(fa, "Āā"));
}

/// Constructs a parser that has its result converted with the `conv` function. The ´conv`
/// functions signature is `*const fn (ParserResult(parser)) T`, so this function should only be
/// used for conversions that cannot fail. See `convert`.
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
                const res = try parser.parse(allocator, str);
                return switch (res.value) {
                    .err => return Res.err(res.index),
                    .ok => |value| return Res.ok(res.index, conv(value)),
                };
            }
        }.parse,
    };
}

/// Constructs a parser that consumes the input with `parser` and places `value` into it's result.
/// Discarding `parser` result value, but keeping it's rest. This can be used to map parsers to
/// static values, for example `\n` to the newline character.
pub fn mapConst(
    comptime parser: anytype,
    comptime value: anytype,
) Parser(@TypeOf(value)) {
    const Res = Result(@TypeOf(value));
    typecheckParser(@TypeOf(parser));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            const res = try parser.parse(allocator, str);
            return switch (res.value) {
                .ok => Res.ok(res.index, value),
                .err => Res.err(res.index),
            };
        }
    }.parse };
}

test "mapConst" {
    const fa = testing.failing_allocator;
    const p1 = comptime string("123")
        .asStr()
        .mapConst(@as(u8, 3));
    try expectOk(u8, 3, 3, try p1.parse(fa, "123"));
}

fn ToStructResult(comptime T: type) type {
    return @TypeOf(struct {
        fn func(_: anytype) T {
            return undefined;
        }
    }.func);
}

/// Constructs a convert function for `map` that takes a tuple, array or single value and converts
/// it into the struct `T`. Fields will be assigned in order, so `tuple[i]` will be assigned to
/// the ith field of `T`. This function will give a compile error if `T` and the tuple does not
/// have the same number of fields, or if the items of the tuple cannot be coerced into the fields
/// of the struct.
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
                if (struct_fields.len == 0)
                    @compileError("Cannot map " ++ @typeName(@TypeOf(value)) ++ " to " ++ @typeName(T));
                @field(res, struct_fields[0].name) = value;
                return res;
            }
        }
    }.func;
}

/// Constructs a conversion function for `map` that initializes a union `T` with the value passed
/// to it using `@unionInit` with the tag `tag`.
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
    try expectOk(Point, 5, .{ .x = 10, .y = 10 }, try p1.parse(fa, "10 10"));
    try expectOk(Point, 5, .{ .x = 20, .y = 20 }, try p1.parse(fa, "20 20aa"));
    try expectErr(Point, 2, try p1.parse(fa, "12"));

    const p2 = comptime combine(.{
        int(usize, .{}),
        ascii.char(' ').discard(),
    }).manyN(2, .{}).map(toStruct(Point));
    try expectOk(Point, 6, .{ .x = 10, .y = 10 }, try p2.parse(fa, "10 10 "));
    try expectOk(Point, 6, .{ .x = 20, .y = 20 }, try p2.parse(fa, "20 20 aa"));
    try expectErr(Point, 2, try p2.parse(fa, "12"));

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
    try expectOk(Message, 5, .{ .point = .{ .x = 20, .y = 20 } }, try p3.parse(fa, "20 20"));

    const p4 = comptime combine(.{
        many(ascii.alphabetic, .{ .min = 1, .collect = false }),
        ascii.char(' ').discard(),
        int(u32, .{}),
    }).map(toStruct(Person)).map(unionInit(Message, MessageType.person));
    const r4 = try p4.parse(fa, "Bob 24");
    try testing.expect(r4.value == .ok);
    try testing.expectEqual(@as(usize, 6), r4.index);
    try testing.expectEqualStrings("Bob", r4.value.ok.person.name);
    try testing.expectEqual(24, r4.value.ok.person.age);

    const Wrapper = struct {
        value: []const u8,
    };
    const wp = comptime string("foo").map(toStruct(Wrapper));
    const wr = try wp.parse(fa, "foo");
    try testing.expect(wr.value == .ok);
    try testing.expectEqualStrings("foo", wr.value.ok.value);
}

/// Constructs a parser that discards the result returned from the parser it wraps.
pub fn discard(comptime parser: anytype) Parser(void) {
    return parser.map(struct {
        fn d(_: anytype) void {}
    }.d);
}

test "discard" {
    const fa = testing.failing_allocator;
    const p1 = comptime ascii.char(' ').many(.{ .collect = false }).discard();
    try expectOk(void, 0, {}, try p1.parse(fa, "abc"));
    try expectOk(void, 1, {}, try p1.parse(fa, " abc"));
    try expectOk(void, 2, {}, try p1.parse(fa, "  abc"));
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

/// Construct a parser that succeeds if it parser an integer of `base`. This parser will stop
/// parsing digits after `max_digits` after the leading zeros haven been reached. The result of
/// this parser will be the string containing the match.
pub fn intToken(comptime options: IntOptions) Parser([]const u8) {
    debug.assert(options.max_digits != 0);
    const sign_parser = comptime if (options.parse_sign)
        oneOf(.{ ascii.char('-').discard(), ascii.char('+').discard(), noop })
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

test "intToken" {
    const fa = testing.failing_allocator;
    const p1 = intToken(.{});
    try expectOk([]const u8, 1, "0", try p1.parse(fa, "0"));
    try expectOk([]const u8, 1, "1", try p1.parse(fa, "1"));
    try expectOk([]const u8, 1, "1", try p1.parse(fa, "1a"));
    try expectOk([]const u8, 3, "255", try p1.parse(fa, "255"));
    try expectOk([]const u8, 4, "2555", try p1.parse(fa, "2555"));
    try expectOk([]const u8, 3, "256", try p1.parse(fa, "256"));
    try expectOk([]const u8, 4, "+255", try p1.parse(fa, "+255"));
    try expectOk([]const u8, 4, "-255", try p1.parse(fa, "-255"));

    const p2 = intToken(.{ .base = 16 });
    try expectOk([]const u8, 1, "0", try p2.parse(fa, "0"));
    try expectOk([]const u8, 1, "1", try p2.parse(fa, "1"));
    try expectOk([]const u8, 2, "1a", try p2.parse(fa, "1a"));
    try expectOk([]const u8, 1, "1", try p2.parse(fa, "1g"));
    try expectOk([]const u8, 2, "ff", try p2.parse(fa, "ff"));
    try expectOk([]const u8, 2, "FF", try p2.parse(fa, "FF"));
    try expectOk([]const u8, 4, "00FF", try p2.parse(fa, "00FF"));
    try expectOk([]const u8, 3, "100", try p2.parse(fa, "100"));
    try expectOk([]const u8, 1, "f", try p2.parse(fa, "fg"));
    try expectErr([]const u8, 0, try p2.parse(fa, "gf"));
    try expectOk([]const u8, 3, "+ff", try p2.parse(fa, "+ff"));
    try expectOk([]const u8, 3, "-ff", try p2.parse(fa, "-ff"));

    const p3 = intToken(.{ .base = 16, .max_digits = 2 });
    try expectOk([]const u8, 2, "FF", try p3.parse(fa, "FF"));
    try expectOk([]const u8, 2, "00", try p3.parse(fa, "00FF"));

    const p4 = intToken(.{});
    try expectOk([]const u8, 4, "+255", try p4.parse(fa, "+255"));
    try expectOk([]const u8, 4, "-255", try p4.parse(fa, "-255"));

    const p5 = intToken(.{ .parse_sign = false });
    try expectOk([]const u8, 3, "255", try p5.parse(fa, "255"));
    try expectErr([]const u8, 0, try p5.parse(fa, "+255"));
    try expectErr([]const u8, 0, try p5.parse(fa, "-255"));
}

/// Same as `intToken` but also converts the parsed string to an integer. This parser will at most
/// parse the same number of digits as the underlying integer can hold in the specified base.
pub fn int(comptime Int: type, comptime options: IntOptions) Parser(Int) {
    debug.assert(options.max_digits != 0);
    const Res = Result(Int);
    return .{ .parse = struct {
        fn parse(_: mem.Allocator, str: []const u8) Error!Res {
            if (options.parse_sign and str.len != 0) {
                var res = switch (str[0]) {
                    '+' => try parseAfterSign(str[1..], add),
                    '-' => try parseAfterSign(str[1..], sub),
                    else => return parseAfterSign(str, add),
                };
                if (res.value == .ok)
                    res.index += 1;
                return res;
            }
            return parseAfterSign(str, add);
        }

        fn parseAfterSign(
            str: []const u8,
            add_sub: *const fn (Int, Int) Overflow!Int,
        ) Error!Res {
            if (str.len == 0)
                return Res.err(0);

            const max_digits = @min(str.len, options.max_digits);
            const first = fmt.charToDigit(str[0], options.base) catch return Res.err(0);
            const first_casted = math.cast(Int, first) orelse return Res.err(0);

            var res = add_sub(0, first_casted) catch return Res.err(0);
            const end = for (str[1..max_digits], 0..) |c, i| {
                const d = fmt.charToDigit(c, options.base) catch break i;
                const casted_b = math.cast(Int, options.base) orelse break i;
                const casted_d = math.cast(Int, d) orelse break i;

                const next = math.mul(Int, res, casted_b) catch break i;
                res = add_sub(next, casted_d) catch break i;
            } else max_digits - 1;

            return Res.ok(end + 1, res);
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
    try expectOk(u8, 1, 0, try p1.parse(fa, "0"));
    try expectOk(u8, 1, 1, try p1.parse(fa, "1"));
    try expectOk(u8, 1, 1, try p1.parse(fa, "1a"));
    try expectOk(u8, 3, 255, try p1.parse(fa, "255"));
    try expectOk(u8, 3, 255, try p1.parse(fa, "2555"));
    try expectOk(u8, 2, 25, try p1.parse(fa, "256"));
    try expectOk(u8, 4, 255, try p1.parse(fa, "+255"));
    try expectErr(u8, 0, try p1.parse(fa, "-255"));

    const p2 = int(u8, .{ .base = 16 });
    try expectOk(u8, 1, 0x00, try p2.parse(fa, "0"));
    try expectOk(u8, 1, 0x01, try p2.parse(fa, "1"));
    try expectOk(u8, 2, 0x1a, try p2.parse(fa, "1a"));
    try expectOk(u8, 1, 0x01, try p2.parse(fa, "1g"));
    try expectOk(u8, 2, 0xff, try p2.parse(fa, "ff"));
    try expectOk(u8, 2, 0xff, try p2.parse(fa, "FF"));
    try expectOk(u8, 4, 0xff, try p2.parse(fa, "00FF"));
    try expectOk(u8, 2, 0x10, try p2.parse(fa, "100"));
    try expectOk(u8, 1, 0x0f, try p2.parse(fa, "fg"));
    try expectOk(u8, 3, 0xff, try p2.parse(fa, "+ff"));
    try expectErr(u8, 0, try p2.parse(fa, "-ff"));

    const p3 = int(u8, .{ .base = 16, .max_digits = 2 });
    try expectOk(u8, 2, 0xff, try p3.parse(fa, "FF"));
    try expectOk(u8, 2, 0x00, try p3.parse(fa, "00FF"));

    const p4 = int(isize, .{});
    try expectOk(isize, 4, 255, try p4.parse(fa, "+255"));
    try expectOk(isize, 4, -255, try p4.parse(fa, "-255"));

    const p5 = int(isize, .{ .parse_sign = false });
    try expectOk(isize, 3, 255, try p5.parse(fa, "255"));
    try expectErr(isize, 0, try p5.parse(fa, "+255"));
    try expectErr(isize, 0, try p5.parse(fa, "-255"));
}

/// Construct a parser that succeeds if it parses any tag from `Enum` as a string. The longest
/// match is always chosen, so for `enum{a,aa}` the "aa" string will succeed parsing and have the
/// result of `.aa` and not `.a`.
pub fn enumeration(comptime Enum: type) Parser(Enum) {
    const Res = Result(Enum);
    return .{ .parse = struct {
        fn parse(_: mem.Allocator, str: []const u8) Error!Res {
            var res: Res = Res.err(0);
            inline for (@typeInfo(Enum).@"enum".fields) |field| next: {
                if (!std.mem.startsWith(u8, str, field.name))
                    break :next;

                if (res.index < field.name.len)
                    res = Res.ok(field.name.len, @field(Enum, field.name));
            }

            return res;
        }
    }.parse };
}

test "enumeration" {
    const fa = testing.failing_allocator;
    const E1 = enum { a, b, aa };
    const p1 = enumeration(E1);
    try expectOk(E1, 1, .a, try p1.parse(fa, "a"));
    try expectOk(E1, 2, .aa, try p1.parse(fa, "aa"));
    try expectOk(E1, 1, .b, try p1.parse(fa, "b"));
    try expectOk(E1, 1, .a, try p1.parse(fa, "ab"));
    try expectOk(E1, 1, .b, try p1.parse(fa, "bb"));
    try expectErr(E1, 0, try p1.parse(fa, "256"));
}

/// Creates a parser that calls a function to obtain its underlying parser. This function
/// introduces the indirection required for recursive grammars.
/// ```
/// const digit_10 = discard(digit(10));
/// const digits = oneOf(.{ combine(.{ digit_10, ref(digitsRef) }), digit_10 } });
/// fn digitsRef() Parser(void) {
///     return digits;
/// };
/// ```
///
/// Note: `ref` does not support [left recursion](https://en.wikipedia.org/wiki/Left_recursion).
///        Use `recursiveRef` for that
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

    try expectOk(void, 1, {}, try Scope.digit.parse(fa, "0"));
}

/// Similar to `ref`, but the passed function can accept a Parser parameter as a
/// `recursiveRef` pointing to the function's return value, and it returns this passed ref.
///
/// recursiveRef differs from a regular ref in that it internally implements a Packet parsing
/// algorithm that supports left recursion. Therefore, you can use this to express
/// left-recursive grammars that are typically not allowed. In exchange for this flexibility,
/// there is a performance cost, and it must be used with an allocator.
/// ```
/// const expr = recursiveRef(struct {
///     fn f(comptime _expr: anytype) Parser(void) {
///         return oneOf(.{
///             combine(.{ _expr, ascii.char('+').discard(), _expr }).discard(),
///             ascii.char('0').discard(),
///         });
///     }
/// }.f);
/// expr.parse("0+0");
/// ```
///
/// By design, if recursiveRef is used in an ambiguous grammar such as
/// `expr := expr "+" expr | num`, the parsing result will be right-associative. If you need
/// a left-associative result, you should modify the grammar to something like
/// `expr := expr "+" num | num` to enforce left associativity.
///
/// Unless you know what you are doing, please be cautious not to write code likes below, as
/// the function does not return a regular ref. It establishes a memoization context upon the
/// first call. You must ensure that the parser wrapped by `recursiveRef` is called first in a
/// homogeneous parsing process. Therefore, the following code will not work.
/// ```
/// const rawExpr = oneOf(.{
///     combine(.{ expr, ascii.char('+').discard(), expr }).discard(),
///     ascii.char('0').discard(),
/// });
/// const expr = recursiveRef(struct {
///     fn f(comptime _expr: anytype) Parser(void) {
///         return rawExpr;
///     }
/// }.f);
/// rawExpr.parse("0+0");
/// ```
pub fn recursiveRef(comptime func: anytype) ReturnType(@TypeOf(func)) {
    const T = ParserResult(ReturnType(@TypeOf(func)));
    const Res = Result(T);

    return struct {
        threadlocal var memo: std.AutoArrayHashMapUnmanaged(usize, Res) = .empty;

        const parser = Parser(T){ .parse = parse };
        const innerParser = func(parser);

        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            const key: usize = @intFromPtr(str.ptr);
            const entry = try memo.getOrPut(allocator, key);
            if (entry.found_existing)
                return entry.value_ptr.*;

            entry.value_ptr.* = Res.err(0);
            defer {
                if (entry.index == 0) {
                    memo.deinit(allocator);
                    memo = .empty;
                }
            }

            while (true) {
                const res = try innerParser.parse(allocator, str);

                const p = &memo.values()[entry.index];
                if (res.index <= p.index)
                    break;

                p.* = res;
            }

            return memo.values()[entry.index];
        }
    }.parser;
}

test "recursiveRef" {
    const a = testing.allocator;
    const Scope = struct {
        const num = oneOf(.{ ascii.char('0'), ascii.char('1') }).discard();
        const expr = recursiveRef(struct {
            fn f(comptime _expr: anytype) Parser(void) {
                return oneOf(.{
                    combine(.{ _expr, ascii.char('+').discard(), num }).discard(),
                    num,
                });
            }
        }.f);
    };
    const start = Scope.expr;
    try expectOk(void, 5, {}, try start.parse(a, "1+0+1"));
    try expectOk(void, 3, {}, try start.parse(a, "1+0"));
    try expectOk(void, 1, {}, try start.parse(a, "1"));
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
    try expectOk(void, 2, {}, try p1.parse(fa, "[]"));
    try expectOk(void, 3, {}, try p1.parse(fa, "[1]"));
    try expectOk(void, 5, {}, try p1.parse(fa, "[1,2]"));
    try expectErr(void, 4, try p1.parse(fa, "[1,2"));
}

pub fn expectResult(comptime T: type, expected: Result(T), actual: Result(T)) !void {
    switch (expected.value) {
        .ok => |expected_value| switch (actual.value) {
            .ok => |actual_value| switch (T) {
                []const u8 => try testing.expectEqualStrings(expected_value, actual_value),
                else => try testing.expectEqualDeep(expected_value, actual_value),
            },
            .err => try std.testing.expect(false),
        },
        .err => switch (actual.value) {
            .ok => try std.testing.expect(false),
            .err => {},
        },
    }
    try testing.expectEqual(expected.index, actual.index);
}

pub fn expectErr(comptime T: type, expected: usize, actual: Result(T)) !void {
    return try expectResult(T, Result(T).err(expected), actual);
}

pub fn expectOk(
    comptime T: type,
    expected_index: usize,
    expected_value: T,
    actual: Result(T),
) !void {
    return try expectResult(T, Result(T).ok(expected_index, expected_value), actual);
}
