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

        parse: *const fn (mem.Allocator, *mecha.Context, []const u8) Error!Result(T),

        pub const asStr = mecha.asStr;
        pub const convert = mecha.convert;
        pub const digit = mecha.digit;
        pub const discard = mecha.discard;
        pub const many = mecha.many;
        pub const manyN = mecha.manyN;
        pub const mapConst = mecha.mapConst;
        pub const map = mecha.map;
        pub const opt = mecha.opt;
    };
}

/// The result of a successful parse
pub fn Result(comptime T: type) type {
    return struct {
        pub const Value = T;

        value: T,
        rest: []const u8 = "",
        span: Span = span(0, 0),
    };
}

/// Out-of-band context for reporting successful parser spans
/// and error locations. We can't return a tagged union (result, error)
/// from a parser because it breaks `combine`. The latter requires
/// its parsing loop to be comptime. Any tagged union checks will be
/// runtime and the compiler will disallow them. Note that `pos`,
/// the parser position, will always point to the next character
/// to be parsed. This means 1 for 1-character strings since
/// the first character is at position 0.
pub const Context = struct {
    loc: builtin.SourceLocation = undefined,
    pos: usize = 0,

    const Self = @This();

    pub inline fn set(self: *Self, loc: builtin.SourceLocation, pos: usize) void {
        self.loc = loc;
        self.pos = pos;
    }

    pub inline fn bump(self: *Self, len: usize) Span {
        const sp = span(self.pos, len);
        self.pos += len;
        return sp;
    }
};

/// The span of the input that was covered by a parser.
pub const Span = struct {
    start: usize = 0,
    len: usize = 0,
};

pub inline fn span(start: usize, len: usize) Span {
    return .{ .start = start, .len = len };
}

pub const Void = Result(void);

/// All the ways in which a parser can fail.
/// ParserFailed corresponds to the string not matching the expected form.
/// BadSpan will be thrown when a child parser succeeds but parser position
/// is less than the parser position of the parent parser.
pub const Error = error{ ParserFailed, BadSpan, OtherError } || mem.Allocator.Error;

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
    fn parse(_: mem.Allocator, ctx: *Context, str: []const u8) Error!Void {
        return Void{ .value = {}, .rest = str, .span = span(ctx.pos, 0) };
    }
}.parse };

/// A parser that only succeeds on the end of the string.
pub const eos = Parser(void){ .parse = struct {
    fn parse(_: mem.Allocator, ctx: *Context, str: []const u8) Error!Void {
        if (str.len != 0) {
            ctx.set(@src(), 0);
            return error.ParserFailed;
        }
        return Void{ .value = {}, .rest = str, .span = span(ctx.pos, 0) };
    }
}.parse };

test "eos" {
    const allocator = testing.failing_allocator;
    var ctx = Context{};
    try expectResult(void, .{ .value = {}, .span = span(0, 0) }, eos.parse(allocator, &ctx, ""));
    try testing.expectEqual(0, ctx.pos);
    try expectResult(void, error.ParserFailed, eos.parse(allocator, &ctx, "a"));
    try testing.expectEqual(0, ctx.pos);
}

/// A parser that always succeeds with the result being the
/// entire string. The same as the '.*$' regex.
pub const rest = Parser([]const u8){ .parse = struct {
    fn parse(_: mem.Allocator, ctx: *Context, str: []const u8) Error!Result([]const u8) {
        return Result([]const u8){
            .value = str,
            .rest = str[str.len..],
            .span = ctx.bump(str.len),
        };
    }
}.parse };

test "rest" {
    const allocator = testing.failing_allocator;
    var ctx = Context{};
    try expectResult([]const u8, .{ .value = "", .span = span(0, 0) }, rest.parse(allocator, &ctx, ""));
    try testing.expectEqual(0, ctx.pos);
    try expectResult([]const u8, .{ .value = "a", .span = span(0, 1) }, rest.parse(allocator, &ctx, "a"));
    try testing.expectEqual(1, ctx.pos);
}

/// Construct a parser that succeeds if the string passed in starts with `str`.
pub fn string(comptime str: []const u8) Parser([]const u8) {
    return .{ .parse = struct {
        fn parse(_: mem.Allocator, ctx: *Context, s: []const u8) Error!Result([]const u8) {
            if (!mem.startsWith(u8, s, str)) {
                ctx.set(@src(), ctx.pos);
                return error.ParserFailed;
            }
            return Result([]const u8){
                .value = str,
                .rest = s[str.len..],
                .span = ctx.bump(str.len),
            };
        }
    }.parse };
}

test "string" {
    const allocator = testing.failing_allocator;
    var ctx = Context{};
    try expectResult([]const u8, .{ .value = "aa", .span = span(0, 2) }, string("aa").parse(allocator, &ctx, "aa"));
    try testing.expectEqual(2, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "aa", .rest = "a", .span = span(0, 2) }, string("aa").parse(allocator, &ctx, "aaa"));
    try testing.expectEqual(2, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, error.ParserFailed, string("aa").parse(allocator, &ctx, "ba"));
    try testing.expectEqual(0, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, error.ParserFailed, string("aa").parse(allocator, &ctx, ""));
    try testing.expectEqual(0, ctx.pos);
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
    const Array = [n]ParserResult(@TypeOf(parser));
    const Res = Result(Array);
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, ctx: *Context, str: []const u8) Error!Res {
            var rem = str;
            var res: Array = undefined;
            const pos = ctx.pos;
            for (&res, 0..) |*value, i| {
                if (i != 0)
                    rem = (try options.separator.parse(allocator, ctx, rem)).rest;

                const r = try parser.parse(allocator, ctx, rem);
                rem = r.rest;
                value.* = r.value;
            }

            if (ctx.pos < pos) {
                return Error.BadSpan;
            }

            return Res{ .value = res, .rest = rem, .span = span(pos, ctx.pos - pos) };
        }
    }.parse };
}

test "manyN" {
    const allocator = testing.failing_allocator;
    var ctx = Context{};
    const parser1 = comptime ascii.range('a', 'b')
        .manyN(3, .{});
    try expectResult([3]u8, .{ .value = "aba".*, .rest = "bab", .span = span(0, 3) }, parser1.parse(allocator, &ctx, "ababab"));
    try testing.expectEqual(3, ctx.pos);
    ctx = Context{};
    const parser2 = comptime ascii.range('a', 'b')
        .manyN(3, .{ .separator = discard(ascii.char(',')) });
    try expectResult([3]u8, .{ .value = "aba".*, .rest = ",b,a,b", .span = span(0, 5) }, parser2.parse(allocator, &ctx, "a,b,a,b,a,b"));
    try testing.expectEqual(5, ctx.pos);
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
        fn parse(allocator: mem.Allocator, ctx: *Context, str: []const u8) Error!Res {
            var res = if (options.collect)
                try std.ArrayList(Element).initCapacity(allocator, options.min)
            else {};
            errdefer if (options.collect) res.deinit();

            var rem = str;
            var i: usize = 0;
            const pos = ctx.pos;
            while (i < options.max) : (i += 1) {
                const after_seperator = if (i != 0)
                    (options.separator.parse(allocator, ctx, rem) catch break).rest
                else
                    rem;

                const r = parser.parse(allocator, ctx, after_seperator) catch |e| switch (e) {
                    error.ParserFailed => break,
                    else => return e,
                };
                rem = r.rest;
                if (options.collect)
                    try res.append(r.value);
            }
            if (i < options.min)
                return error.ParserFailed;

            if (ctx.pos < pos) {
                return Error.BadSpan;
            }

            return Res{
                .value = if (options.collect) try res.toOwnedSlice() else str[0 .. str.len - rem.len],
                .rest = rem,
                .span = span(pos, ctx.pos - pos),
            };
        }
    }.parse };
}

test "many" {
    const allocator = testing.failing_allocator;
    var ctx = Context{};
    const parser1 = comptime string("ab")
        .many(.{ .collect = false });
    try expectResult([]const u8, .{ .value = "", .span = span(0, 0) }, parser1.parse(allocator, &ctx, ""));
    try testing.expectEqual(0, ctx.pos);
    try expectResult([]const u8, .{ .value = "", .rest = "a", .span = span(0, 0) }, parser1.parse(allocator, &ctx, "a"));
    try testing.expectEqual(0, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "ab", .span = span(0, 2) }, parser1.parse(allocator, &ctx, "ab"));
    try testing.expectEqual(2, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "ab", .rest = "a", .span = span(0, 2) }, parser1.parse(allocator, &ctx, "aba"));
    try testing.expectEqual(2, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "abab", .span = span(0, 4) }, parser1.parse(allocator, &ctx, "abab"));
    try testing.expectEqual(4, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "abab", .rest = "a", .span = span(0, 4) }, parser1.parse(allocator, &ctx, "ababa"));
    try testing.expectEqual(4, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "ababab", .span = span(0, 6) }, parser1.parse(allocator, &ctx, "ababab"));
    try testing.expectEqual(6, ctx.pos);

    const parser2 = comptime string("ab")
        .many(.{ .collect = false, .min = 1, .max = 2 });
    ctx = Context{};
    try expectResult([]const u8, error.ParserFailed, parser2.parse(allocator, &ctx, ""));
    try testing.expectEqual(0, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, error.ParserFailed, parser2.parse(allocator, &ctx, "a"));
    try testing.expectEqual(0, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "ab", .span = span(0, 2) }, parser2.parse(allocator, &ctx, "ab"));
    try testing.expectEqual(2, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "ab", .rest = "a", .span = span(0, 2) }, parser2.parse(allocator, &ctx, "aba"));
    try testing.expectEqual(2, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "abab", .span = span(0, 4) }, parser2.parse(allocator, &ctx, "abab"));
    try testing.expectEqual(4, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "abab", .rest = "a", .span = span(0, 4) }, parser2.parse(allocator, &ctx, "ababa"));
    try testing.expectEqual(4, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "abab", .rest = "ab", .span = span(0, 4) }, parser2.parse(allocator, &ctx, "ababab"));
    try testing.expectEqual(4, ctx.pos);

    const parser3 = comptime string("ab")
        .many(.{ .collect = false, .separator = discard(ascii.char(',')) });
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "", .span = span(0, 0) }, parser3.parse(allocator, &ctx, ""));
    try testing.expectEqual(0, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "", .rest = "a", .span = span(0, 0) }, parser3.parse(allocator, &ctx, "a"));
    try testing.expectEqual(0, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "ab", .span = span(0, 2) }, parser3.parse(allocator, &ctx, "ab"));
    try testing.expectEqual(2, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "ab", .rest = "a", .span = span(0, 2) }, parser3.parse(allocator, &ctx, "aba"));
    try testing.expectEqual(2, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "ab", .rest = "ab", .span = span(0, 2) }, parser3.parse(allocator, &ctx, "abab"));
    try testing.expectEqual(2, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "ab,ab", .span = span(0, 5) }, parser3.parse(allocator, &ctx, "ab,ab"));
    try testing.expectEqual(5, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "ab,ab", .rest = ",", .span = span(0, 5) }, parser3.parse(allocator, &ctx, "ab,ab,"));
    try testing.expectEqual(6, ctx.pos);

    const parser4 = comptime utf8.char(0x100)
        .many(.{ .collect = false });
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "ĀĀĀ", .rest = "āāā", .span = span(0, 3) }, parser4.parse(allocator, &ctx, "ĀĀĀāāā"));
    try testing.expectEqual(6, ctx.pos);

    const parser5 = comptime utf8.range(0x100, 0x100)
        .many(.{});
    ctx = Context{};
    const res = try parser5.parse(testing.allocator, &ctx, "ĀĀĀāāā");
    defer testing.allocator.free(res.value);

    var expect = [_]u21{ 'Ā', 'Ā', 'Ā' };
    try expectResult([]u21, .{ .value = &expect, .rest = "āāā", .span = span(0, 3) }, res);
    try testing.expectEqual(6, ctx.pos);
}

/// Construct a parser that will call `parser` on the string
/// but never fails to parse. The parser's result will be the
/// result of `parser` on success and `null` on failure.
pub fn opt(comptime parser: anytype) Parser(?ParserResult(@TypeOf(parser))) {
    const Res = Result(?ParserResult(@TypeOf(parser)));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, ctx: *Context, str: []const u8) Error!Res {
            const pos = ctx.pos;
            const r = parser.parse(allocator, ctx, str) catch |e| switch (e) {
                error.ParserFailed => return Res{
                    .value = null,
                    .rest = str,
                    .span = span(ctx.pos, 0),
                },
                else => return e,
            };

            if (ctx.pos < pos) {
                return Error.BadSpan;
            }

            return Res{
                .value = r.value,
                .rest = r.rest,
                .span = span(pos, ctx.pos - pos),
            };
        }
    }.parse };
}

test "opt" {
    const allocator = testing.failing_allocator;
    var ctx = Context{};
    const parser1 = comptime ascii.range('a', 'z')
        .opt();
    try expectResult(?u8, .{ .value = 'a', .span = span(0, 1) }, parser1.parse(allocator, &ctx, "a"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(?u8, .{ .value = 'a', .rest = "a", .span = span(0, 1) }, parser1.parse(allocator, &ctx, "aa"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(?u8, .{ .value = null, .rest = "1", .span = span(0, 0) }, parser1.parse(allocator, &ctx, "1"));
    try testing.expectEqual(0, ctx.pos);
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
///       so we have to passed the types as an array by value.
fn Tuple(comptime n: usize, comptime types: [n]type) type {
    return meta.Tuple(&types);
}

/// Takes a tuple of `Parser(any)` and constructs a parser that
/// only succeeds if all parsers succeed to parse. The parsers
/// will be called in order and parser `N` will use the `rest`
/// from parser `N-1`. The parsers result will be a `Tuple` of
/// all parser not of type `Parser(void)`. If only one parser
/// is not of type `Parser(void)` then this parsers result is
/// returned instead of a tuple.
pub fn combine(comptime parsers: anytype) Parser(Combine(parsers)) {
    const types = parsersTypes(parsers);
    const Res = Result(Combine(parsers));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, ctx: *Context, str: []const u8) Error!Res {
            const pos = ctx.pos;
            var res: Res = undefined;
            res.rest = str;

            comptime var j = 0;
            inline for (parsers) |parser| {
                const r = parser.parse(allocator, ctx, res.rest) catch |e| {
                    if (e == error.ParserFailed)
                        ctx.pos = pos;
                    return e;
                };
                res.rest = r.rest;

                if (@TypeOf(r.value) != void) {
                    if (types.len == 1) {
                        res.value = r.value;
                    } else {
                        res.value[j] = r.value;
                    }
                    j += 1;
                }
            }

            if (ctx.pos < pos) {
                return Error.BadSpan;
            }

            res.span = span(pos, ctx.pos - pos);

            return res;
        }
    }.parse };
}

test "combine" {
    const allocator = testing.failing_allocator;
    var ctx = Context{};
    const parser1 = comptime combine(.{
        ascii.range('a', 'b').opt(),
        ascii.range('d', 'e').opt(),
    });
    const Res = ParserResult(@TypeOf(parser1));
    try expectResult(Res, .{ .value = .{ .@"0" = 'a', .@"1" = 'd' }, .span = span(0, 2) }, parser1.parse(allocator, &ctx, "ad"));
    try testing.expectEqual(2, ctx.pos);
    ctx = Context{};
    try expectResult(Res, .{ .value = .{ .@"0" = 'a', .@"1" = null }, .rest = "a", .span = span(0, 1) }, parser1.parse(allocator, &ctx, "aa"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(Res, .{ .value = .{ .@"0" = null, .@"1" = 'd' }, .rest = "a", .span = span(0, 1) }, parser1.parse(allocator, &ctx, "da"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(Res, .{ .value = .{ .@"0" = null, .@"1" = null }, .rest = "qa", .span = span(0, 0) }, parser1.parse(allocator, &ctx, "qa"));
    try testing.expectEqual(0, ctx.pos);

    const parser2 = comptime combine(.{
        ascii.range('a', 'b').opt(),
        ascii.char('d'),
    });
    const Res2 = ParserResult(@TypeOf(parser2));
    ctx = Context{};
    try expectResult(Res2, .{ .value = .{ .@"0" = 'a', .@"1" = 'd' }, .span = span(0, 2) }, parser2.parse(allocator, &ctx, "ad"));
    try testing.expectEqual(2, ctx.pos);
    ctx = Context{};
    try expectResult(Res2, .{ .value = .{ .@"0" = 'a', .@"1" = 'd' }, .rest = "a", .span = span(0, 2) }, parser2.parse(allocator, &ctx, "ada"));
    try testing.expectEqual(2, ctx.pos);
    ctx = Context{};
    try expectResult(Res2, .{ .value = .{ .@"0" = null, .@"1" = 'd' }, .rest = "a", .span = span(0, 1) }, parser2.parse(allocator, &ctx, "da"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(Res2, error.ParserFailed, parser2.parse(allocator, &ctx, "qa"));
    try testing.expectEqual(0, ctx.pos);
}

/// Takes a tuple of `Parser(T)` and constructs a parser that
/// only succeeds if one of the parsers succeed to parse. The
/// parsers will be called in order all with `str` as input.
/// The parser will return with the result of the first parser
/// that succeeded. The parsers result will be `Result(T)`
pub fn oneOf(comptime parsers: anytype) Parser(ParserResult(@TypeOf(parsers[0]))) {
    inline for (parsers) |parser|
        typecheckParser(@TypeOf(parser));

    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, ctx: *Context, str: []const u8) Error!Result(ParserResult(@TypeOf(parsers[0]))) {
            const pos = ctx.pos;
            inline for (parsers) |p| {
                ctx.pos = pos;
                if (p.parse(allocator, ctx, str)) |res| {
                    return res;
                } else |e| {
                    switch (e) {
                        error.ParserFailed => {},
                        else => return e,
                    }
                }
            }
            return error.ParserFailed;
        }
    }.parse };
}

test "oneOf" {
    const allocator = testing.failing_allocator;
    var ctx = Context{};
    const parser1 = comptime oneOf(.{
        ascii.range('a', 'b'),
        ascii.range('d', 'e'),
    });
    try expectResult(u8, .{ .value = 'a', .span = span(0, 1) }, parser1.parse(allocator, &ctx, "a"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(u8, .{ .value = 'b', .span = span(0, 1) }, parser1.parse(allocator, &ctx, "b"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(u8, .{ .value = 'd', .span = span(0, 1) }, parser1.parse(allocator, &ctx, "d"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(u8, .{ .value = 'e', .span = span(0, 1) }, parser1.parse(allocator, &ctx, "e"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(u8, .{ .value = 'a', .rest = "a", .span = span(0, 1) }, parser1.parse(allocator, &ctx, "aa"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(u8, .{ .value = 'b', .rest = "a", .span = span(0, 1) }, parser1.parse(allocator, &ctx, "ba"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(u8, .{ .value = 'd', .rest = "a", .span = span(0, 1) }, parser1.parse(allocator, &ctx, "da"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(u8, .{ .value = 'e', .rest = "a", .span = span(0, 1) }, parser1.parse(allocator, &ctx, "ea"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(u8, error.ParserFailed, parser1.parse(allocator, &ctx, "q"));
    try testing.expectEqual(0, ctx.pos);
}

/// Takes any parser (preferable not of type `Parser([]const u8)`)
/// and converts it to a parser where the result is a string that
/// contains all characters parsed by `parser`.
pub fn asStr(comptime parser: anytype) Parser([]const u8) {
    const Res = Result([]const u8);
    typecheckParser(@TypeOf(parser));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, ctx: *Context, str: []const u8) Error!Res {
            const pos = ctx.pos;
            const r = try parser.parse(allocator, ctx, str);

            if (ctx.pos < pos) {
                return Error.BadSpan;
            }

            return Res{
                .value = str[0 .. str.len - r.rest.len],
                .rest = r.rest,
                .span = span(pos, ctx.pos - pos),
            };
        }
    }.parse };
}

test "asStr" {
    const allocator = testing.failing_allocator;
    var ctx = Context{};
    const parser1 = comptime ascii.char('a').asStr();
    try expectResult([]const u8, .{ .value = "a", .span = span(0, 1) }, parser1.parse(allocator, &ctx, "a"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "a", .rest = "a", .span = span(0, 1) }, parser1.parse(allocator, &ctx, "aa"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, error.ParserFailed, parser1.parse(allocator, &ctx, "ba"));
    try testing.expectEqual(0, ctx.pos);

    const parser2 = comptime combine(.{
        ascii.range('a', 'b').opt(),
        ascii.range('d', 'e').opt(),
    }).asStr();
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "ad", .span = span(0, 2) }, parser2.parse(allocator, &ctx, "ad"));
    try testing.expectEqual(2, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "a", .rest = "a", .span = span(0, 1) }, parser2.parse(allocator, &ctx, "aa"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "d", .rest = "a", .span = span(0, 1) }, parser2.parse(allocator, &ctx, "da"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult([]const u8, .{ .value = "", .rest = "qa" }, parser2.parse(allocator, &ctx, "qa"));
    try testing.expectEqual(0, ctx.pos);
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
        fn parse(allocator: mem.Allocator, ctx: *Context, str: []const u8) Error!Res {
            const r = try parser.parse(allocator, ctx, str);
            const v = conv(allocator, r.value) catch |e| switch (@as(anyerror, e)) {
                error.ParserFailed => return error.ParserFailed,
                error.OutOfMemory => return error.OutOfMemory,
                else => return error.OtherError,
            };
            return Res{ .value = v, .rest = r.rest, .span = r.span };
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
            return fmt.parseInt(Int, str, base) catch error.ParserFailed;
        }
    }.func;
}

/// Constructs a convert function for `convert` that takes a
/// string and parses it to a float of type `Float`.
pub fn toFloat(comptime Float: type) *const fn (mem.Allocator, []const u8) Error!Float {
    return struct {
        fn func(_: mem.Allocator, str: []const u8) Error!Float {
            return fmt.parseFloat(Float, str) catch error.ParserFailed;
        }
    }.func;
}

/// A convert function for `convert` that takes a string and
/// returns the first codepoint.
pub fn toChar(_: mem.Allocator, str: []const u8) Error!u21 {
    if (str.len > 1) {
        const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch return error.ParserFailed;
        if (cp_len > str.len)
            return error.ParserFailed;
        return unicode.utf8Decode(str[0..cp_len]) catch error.ParserFailed;
    }
    return @as(u21, str[0]);
}

/// Constructs a convert function for `convert` that takes a
/// string and converts it to an `Enum` with `std.meta.stringToEnum`.
pub fn toEnum(comptime Enum: type) *const fn (mem.Allocator, []const u8) Error!Enum {
    return struct {
        fn func(_: mem.Allocator, str: []const u8) Error!Enum {
            return std.meta.stringToEnum(Enum, str) orelse error.ParserFailed;
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
    const allocator = testing.failing_allocator;
    var ctx = Context{};
    const parser1 = comptime string("123")
        .asStr()
        .convert(toInt(u8, 10));
    try expectResult(u8, .{ .value = 123, .span = span(0, 3) }, parser1.parse(allocator, &ctx, "123"));
    try testing.expectEqual(3, ctx.pos);
    ctx = Context{};
    try expectResult(u8, .{ .value = 123, .rest = "a", .span = span(0, 3) }, parser1.parse(allocator, &ctx, "123a"));
    try testing.expectEqual(3, ctx.pos);
    ctx = Context{};
    try expectResult(u8, error.ParserFailed, parser1.parse(allocator, &ctx, "12"));
    try testing.expectEqual(0, ctx.pos);

    const parser2 = comptime string("a")
        .asStr()
        .convert(toChar);
    try expectResult(u21, .{ .value = 'a' }, parser2.parse(allocator, &ctx, "a"));
    try expectResult(u21, .{ .value = 'a', .rest = "a" }, parser2.parse(allocator, &ctx, "aa"));
    try expectResult(u21, error.ParserFailed, parser2.parse(allocator, &ctx, "b"));

    const parser3 = comptime rest.convert(toBool);
    try expectResult(bool, .{ .value = true }, parser3.parse(allocator, &ctx, "true"));
    try expectResult(bool, .{ .value = false }, parser3.parse(allocator, &ctx, "false"));
    try expectResult(bool, error.ParserFailed, parser3.parse(allocator, &ctx, "b"));

    const parser4 = comptime string("1.23")
        .asStr()
        .convert(toFloat(f32));
    ctx = Context{};
    try expectResult(f32, .{ .value = 1.23, .span = span(0, 4) }, parser4.parse(allocator, &ctx, "1.23"));
    try testing.expectEqual(4, ctx.pos);
    try expectResult(f32, .{ .value = 1.23, .rest = "a" }, parser4.parse(allocator, &ctx, "1.23a"));
    try expectResult(f32, error.ParserFailed, parser4.parse(allocator, &ctx, "1.2"));

    const E = enum(u8) { a, b, _ };
    const parser5 = comptime rest.convert(toEnum(E));
    try expectResult(E, .{ .value = E.a }, parser5.parse(allocator, &ctx, "a"));
    try expectResult(E, .{ .value = E.b }, parser5.parse(allocator, &ctx, "b"));
    try expectResult(E, error.ParserFailed, parser5.parse(allocator, &ctx, "2"));

    const parser6 = comptime string("Āā")
        .asStr()
        .convert(toChar);
    try expectResult(u21, .{ .value = 0x100 }, parser6.parse(allocator, &ctx, "Āā"));
}

/// Constructs a parser that has its result converted with the
/// `conv` function. The ´conv` functions signature is
/// `*const fn (ParserResult(parser)) T`, so this function should only
/// be used for conversions that cannot fail. See `convert`.
pub fn map(
    comptime parser: anytype,
    comptime conv: anytype,
) Parser(ReturnType(@TypeOf(conv))) {
    const Res = Result(ReturnType(@TypeOf(conv)));
    typecheckParser(@TypeOf(parser));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, ctx: *Context, str: []const u8) Error!Res {
            const r = try parser.parse(allocator, ctx, str);
            return Res{
                .value = conv(r.value),
                .rest = r.rest,
                .span = r.span,
            };
        }
    }.parse };
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
        fn parse(allocator: mem.Allocator, ctx: *Context, str: []const u8) Error!Res {
            const r = try parser.parse(allocator, ctx, str);
            return Res{
                .value = value,
                .rest = r.rest,
                .span = r.span,
            };
        }
    }.parse };
}

test "mapConst" {
    const allocator = testing.failing_allocator;
    var ctx = Context{};
    const parser1 = comptime string("123")
        .asStr()
        .mapConst(@as(u8, 3));
    try expectResult(u8, .{ .value = 3, .span = span(0, 3) }, parser1.parse(allocator, &ctx, "123"));
    try testing.expectEqual(3, ctx.pos);
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
    const allocator = testing.failing_allocator;
    var ctx = Context{};
    const Point = struct {
        x: usize,
        y: usize,
    };
    const parser1 = comptime combine(.{
        int(usize, .{}),
        ascii.char(' ').discard(),
        int(usize, .{}),
    }).map(toStruct(Point));
    try expectResult(Point, .{ .value = .{ .x = 10, .y = 10 }, .span = span(0, 5) }, parser1.parse(allocator, &ctx, "10 10"));
    try testing.expectEqual(5, ctx.pos);
    ctx = Context{};
    try expectResult(Point, .{ .value = .{ .x = 20, .y = 20 }, .rest = "aa", .span = span(0, 5) }, parser1.parse(allocator, &ctx, "20 20aa"));
    try testing.expectEqual(5, ctx.pos);
    ctx = Context{};
    try expectResult(Point, error.ParserFailed, parser1.parse(allocator, &ctx, "12"));
    try testing.expectEqual(0, ctx.pos);

    const parser2 = comptime combine(.{
        int(usize, .{}),
        ascii.char(' ').discard(),
    })
        .manyN(2, .{})
        .map(toStruct(Point));
    ctx = Context{};
    try expectResult(Point, .{ .value = .{ .x = 10, .y = 10 }, .span = span(0, 5) }, parser2.parse(allocator, &ctx, "10 10 "));
    try testing.expectEqual(6, ctx.pos);
    ctx = Context{};
    try expectResult(Point, .{ .value = .{ .x = 20, .y = 20 }, .rest = "aa", .span = span(0, 5) }, parser2.parse(allocator, &ctx, "20 20 aa"));
    try testing.expectEqual(6, ctx.pos);
    ctx = Context{};
    try expectResult(Point, error.ParserFailed, parser2.parse(allocator, &ctx, "12"));
    try testing.expectEqual(0, ctx.pos);

    const Person = struct {
        name: []const u8,
        age: u32,
    };
    const MessageType = enum {
        point,
        person,
    };
    const Message = union(MessageType) { point: Point, person: Person };
    const point_parser = comptime combine(.{
        int(usize, .{}),
        ascii.char(' ').discard(),
        int(usize, .{}),
    }).map(toStruct(Point)).map(unionInit(Message, MessageType.point));
    ctx = Context{};
    try expectResult(Message, .{ .value = .{ .point = .{ .x = 20, .y = 20 } }, .span = span(0, 5) }, point_parser.parse(allocator, &ctx, "20 20"));
    try testing.expectEqual(5, ctx.pos);

    const person_parser = comptime combine(.{
        many(ascii.alphabetic, .{ .min = 1, .collect = false }),
        ascii.char(' ').discard(),
        int(u32, .{}),
    }).map(toStruct(Person)).map(unionInit(Message, MessageType.person));
    ctx = Context{};
    const person_result = try person_parser.parse(allocator, &ctx, "Bob 24");
    try testing.expectEqualStrings("Bob", person_result.value.person.name);
    try testing.expectEqual(24, person_result.value.person.age);
    try testing.expectEqual(span(0, 6), person_result.span);
    try testing.expectEqual(6, ctx.pos);

    const Wrapper = struct {
        value: []const u8,
    };
    const wrapper_parser = comptime string("foo").map(toStruct(Wrapper));
    ctx = Context{};
    const wrapper_result = try wrapper_parser.parse(allocator, &ctx, "foo");
    try testing.expectEqualStrings("foo", wrapper_result.value.value);
    try testing.expectEqual(span(0, 3), wrapper_result.span);
    try testing.expectEqual(3, ctx.pos);
}

/// Constructs a parser that discards the result returned from the parser
/// it wraps.
pub fn discard(comptime parser: anytype) Parser(void) {
    return parser.map(struct {
        fn d(_: anytype) void {}
    }.d);
}

test "discard" {
    const allocator = testing.failing_allocator;
    var ctx = Context{};
    const parser = comptime ascii.char(' ').many(.{ .collect = false }).discard();
    try expectResult(void, .{ .value = {}, .rest = "abc", .span = span(0, 0) }, parser.parse(allocator, &ctx, "abc"));
    try testing.expectEqual(0, ctx.pos);
    ctx = Context{};
    try expectResult(void, .{ .value = {}, .rest = "abc", .span = span(0, 2) }, parser.parse(allocator, &ctx, " abc"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(void, .{ .value = {}, .rest = "abc", .span = span(0, 3) }, parser.parse(allocator, &ctx, "  abc"));
    try testing.expectEqual(2, ctx.pos);
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
        oneOf(.{ ascii.char('-'), ascii.char('+'), noop })
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
        fn parse(_: mem.Allocator, ctx: *Context, str: []const u8) Error!Res {
            if (options.parse_sign and str.len != 0) {
                switch (str[0]) {
                    '+' => return parseAfterSign(ctx, str[1..], add, true),
                    '-' => return parseAfterSign(ctx, str[1..], sub, true),
                    else => {},
                }
            }

            return parseAfterSign(ctx, str, add, false);
        }

        fn parseAfterSign(
            ctx: *Context,
            str: []const u8,
            add_sub: *const fn (Int, Int) Overflow!Int,
            sign: bool,
        ) Error!Res {
            if (str.len == 0)
                return error.ParserFailed;

            const max_digits = @min(str.len, options.max_digits);
            const first = fmt.charToDigit(str[0], options.base) catch return error.ParserFailed;
            const first_casted = math.cast(Int, first) orelse return error.ParserFailed;

            var res = add_sub(0, first_casted) catch return error.ParserFailed;
            const end = for (str[1..max_digits], 0..) |c, i| {
                const d = fmt.charToDigit(c, options.base) catch break i;
                const casted_b = math.cast(Int, options.base) orelse break i;
                const casted_d = math.cast(Int, d) orelse break i;

                const next = math.mul(Int, res, casted_b) catch break i;
                res = add_sub(next, casted_d) catch break i;
            } else max_digits - 1;

            if (sign)
                ctx.pos += 1;

            return Res{ .value = res, .rest = str[end + 1 ..], .span = ctx.bump(end + 1) };
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
    const allocator = testing.failing_allocator;
    var ctx = Context{};
    const parser1 = int(u8, .{});
    try expectResult(u8, .{ .value = 0, .span = span(0, 1) }, parser1.parse(allocator, &ctx, "0"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(u8, .{ .value = 1, .span = span(0, 1) }, parser1.parse(allocator, &ctx, "1"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(u8, .{ .value = 1, .rest = "a", .span = span(0, 1) }, parser1.parse(allocator, &ctx, "1a"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(u8, .{ .value = 255, .span = span(0, 3) }, parser1.parse(allocator, &ctx, "255"));
    try testing.expectEqual(3, ctx.pos);
    ctx = Context{};
    try expectResult(u8, .{ .value = 255, .rest = "5", .span = span(0, 3) }, parser1.parse(allocator, &ctx, "2555"));
    try testing.expectEqual(3, ctx.pos);
    ctx = Context{};
    try expectResult(u8, .{ .value = 25, .rest = "6", .span = span(0, 2) }, parser1.parse(allocator, &ctx, "256"));
    try testing.expectEqual(2, ctx.pos);
    ctx = Context{};
    try expectResult(u8, .{ .value = 255, .span = span(0, 4) }, parser1.parse(allocator, &ctx, "+255"));
    try testing.expectEqual(4, ctx.pos);
    ctx = Context{};
    try expectResult(u8, error.ParserFailed, parser1.parse(allocator, &ctx, "-255"));
    try testing.expectEqual(0, ctx.pos);

    const parser2 = int(u8, .{ .base = 16 });
    try expectResult(u8, .{ .value = 0x00 }, parser2.parse(allocator, &ctx, "0"));
    try expectResult(u8, .{ .value = 0x01 }, parser2.parse(allocator, &ctx, "1"));
    try expectResult(u8, .{ .value = 0x1a }, parser2.parse(allocator, &ctx, "1a"));
    try expectResult(u8, .{ .value = 0x01, .rest = "g" }, parser2.parse(allocator, &ctx, "1g"));
    ctx = Context{};
    try expectResult(u8, .{ .value = 0xff, .span = span(0, 2) }, parser2.parse(allocator, &ctx, "ff"));
    try testing.expectEqual(2, ctx.pos);
    try expectResult(u8, .{ .value = 0xff }, parser2.parse(allocator, &ctx, "FF"));
    ctx = Context{};
    try expectResult(u8, .{ .value = 0xff, .span = span(0, 4) }, parser2.parse(allocator, &ctx, "00FF"));
    try testing.expectEqual(4, ctx.pos);
    try expectResult(u8, .{ .value = 0x10, .rest = "0" }, parser2.parse(allocator, &ctx, "100"));
    try expectResult(u8, .{ .value = 0xf, .rest = "g" }, parser2.parse(allocator, &ctx, "fg"));
    ctx = Context{};
    try expectResult(u8, .{ .value = 0xff, .span = span(0, 3) }, parser2.parse(allocator, &ctx, "+ff"));
    try testing.expectEqual(3, ctx.pos);
    ctx = Context{};
    try expectResult(u8, error.ParserFailed, parser2.parse(allocator, &ctx, "-ff"));
    try testing.expectEqual(0, ctx.pos);

    const parser3 = int(u8, .{ .base = 16, .max_digits = 2 });
    try expectResult(u8, .{ .value = 0xff }, parser3.parse(allocator, &ctx, "FF"));
    try expectResult(u8, .{ .value = 0x00, .rest = "FF" }, parser3.parse(allocator, &ctx, "00FF"));

    const parser4 = int(isize, .{});
    ctx = Context{};
    try expectResult(isize, .{ .value = 255, .span = span(0, 4) }, parser4.parse(allocator, &ctx, "+255"));
    try testing.expectEqual(4, ctx.pos);
    ctx = Context{};
    try expectResult(isize, .{ .value = -255, .span = span(0, 4) }, parser4.parse(allocator, &ctx, "-255"));
    try testing.expectEqual(4, ctx.pos);

    const parser5 = int(isize, .{ .parse_sign = false });
    try expectResult(isize, .{ .value = 255 }, parser5.parse(allocator, &ctx, "255"));
    ctx = Context{};
    try expectResult(isize, error.ParserFailed, parser5.parse(allocator, &ctx, "+255"));
    try testing.expectEqual(0, ctx.pos);
    ctx = Context{};
    try expectResult(isize, error.ParserFailed, parser5.parse(allocator, &ctx, "-255"));
    try testing.expectEqual(0, ctx.pos);
}

/// Construct a parser that succeeds if it parses any tag from `Enum` as
/// a string. The longest match is always chosen, so for `enum{a,aa}` the
/// "aa" string will succeed parsing and have the result of `.aa` and not
/// `.a`.
pub fn enumeration(comptime Enum: type) Parser(Enum) {
    const Res = Result(Enum);
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, ctx: *Context, str: []const u8) Error!Res {
            var res: Error!Res = error.ParserFailed;
            const pos = ctx.pos;
            inline for (@typeInfo(Enum).@"enum".fields) |field| next: {
                const p = comptime string(field.name);
                ctx.pos = pos;
                const new = p.parse(allocator, ctx, str) catch |err| switch (err) {
                    error.ParserFailed => break :next,
                    else => |e| return e,
                };
                const old = res catch Res{ .value = undefined, .rest = str };
                if (new.rest.len < old.rest.len)
                    res = Res{
                        .value = @field(Enum, field.name),
                        .rest = new.rest,
                        .span = new.span,
                    };
            }

            const temp = res catch Res{ .value = undefined };
            ctx.pos = temp.span.start + temp.span.len;
            return res;
        }
    }.parse };
}

test "enumeration" {
    const allocator = testing.failing_allocator;
    var ctx = Context{};
    const E1 = enum { a, b, aa };
    const parser1 = enumeration(E1);
    try expectResult(E1, .{ .value = .a, .span = span(0, 1) }, parser1.parse(allocator, &ctx, "a"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(E1, .{ .value = .aa, .span = span(0, 2) }, parser1.parse(allocator, &ctx, "aa"));
    try testing.expectEqual(2, ctx.pos);
    ctx = Context{};
    try expectResult(E1, .{ .value = .b, .span = span(0, 1) }, parser1.parse(allocator, &ctx, "b"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(E1, .{ .value = .a, .rest = "b", .span = span(1, 1) }, parser1.parse(allocator, &ctx, "ab"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(E1, .{ .value = .b, .rest = "b", .span = span(0, 1) }, parser1.parse(allocator, &ctx, "bb"));
    try testing.expectEqual(1, ctx.pos);
    ctx = Context{};
    try expectResult(E1, error.ParserFailed, parser1.parse(allocator, &ctx, "256"));
    try testing.expectEqual(0, ctx.pos);
}

/// Creates a parser that calls a function to obtain its underlying parser.
/// This function introduces the indirection required for recursive grammars.
/// ```
/// const digit_10 = discard(digit(10));
/// const digits = oneOf(.{ combine(.{ digit_10, ref(digitsRef) }), digit_10 });
/// fn digitsRef() Parser(void) {
///     return digits;
/// };
/// ```
pub fn ref(comptime func: anytype) ReturnType(@TypeOf(func)) {
    const P = ReturnType(@TypeOf(func));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, ctx: *Context, str: []const u8) Error!Result(ParserResult(P)) {
            return func().parse(allocator, ctx, str);
        }
    }.parse };
}

test "ref" {
    const allocator = testing.failing_allocator;
    var ctx = Context{};
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
    try expectResult(void, .{ .value = {} }, Scope.digits.parse(allocator, &ctx, "0"));
}

pub fn expectResult(
    comptime T: type,
    m_expect: Error!Result(T),
    m_actual: Error!Result(T),
) !void {
    const expect = m_expect catch |err| {
        try testing.expectError(err, m_actual);
        return;
    };

    const actual = try m_actual;

    try testing.expectEqualStrings(expect.rest, actual.rest);
    switch (T) {
        []const u8 => try testing.expectEqualStrings(expect.value, actual.value),
        else => switch (@typeInfo(T)) {
            .pointer => |ptr| try testing.expectEqualSlices(ptr.child, expect.value, actual.value),
            else => try testing.expectEqual(expect.value, actual.value),
        },
    }
}
