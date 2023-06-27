const std = @import("std");

const debug = std.debug;
const fmt = std.fmt;
const math = std.math;
const mem = std.mem;
const meta = std.meta;
const testing = std.testing;
const unicode = std.unicode;

pub const ascii = @import("src/ascii.zig");
pub const utf8 = @import("src/utf8.zig");

const mecha = @This();

/// The type of all parser that can work with `mecha`
pub fn Parser(comptime _T: type) type {
    return struct {
        pub const T = _T;

        parse: *const fn (mem.Allocator, []const u8) Error!Result(T),

        pub usingnamespace mecha;
    };
}

/// The result of a successful parse
pub fn Result(comptime T: type) type {
    return struct {
        pub const Value = T;

        value: T,
        rest: []const u8 = "",
    };
}

pub const Void = Result(void);

/// All the ways in which a parser can fail.
/// ParserFailed corresponds to the string not matching the expected form and is
/// the only one `mecha` intrinsically deals with.
pub const Error = error{ ParserFailed, OtherError } || mem.Allocator.Error;

fn typecheckParser(comptime P: type) void {
    const err = "expected 'mecha.Parser(T)', found '" ++ @typeName(P) ++ "'";
    const PInner = switch (@typeInfo(P)) {
        .Pointer => |info| info.child,
        else => P,
    };

    if (@typeInfo(PInner) != .Struct) @compileError(err);
    if (!@hasDecl(PInner, "T")) @compileError(err);
    if (@TypeOf(PInner.T) != type) @compileError(err);
    if (PInner != Parser(PInner.T)) @compileError(err);
}

fn ReturnType(comptime P: type) type {
    return switch (@typeInfo(P)) {
        .Pointer => |p| @typeInfo(p.child).Fn.return_type.?,
        .Fn => |f| f.return_type.?,
        else => @compileError(@typeName(P)),
    };
}

fn ParserResult(comptime P: type) type {
    return switch (@typeInfo(P)) {
        .Pointer => |p| p.child.T,
        else => P.T,
    };
}

/// A parser that always succeeds and parses nothing. This parser
/// is only really useful for generic code. See `many`.
pub const noop = Parser(void){ .parse = struct {
    fn parse(_: mem.Allocator, str: []const u8) Error!Void {
        return Void{ .value = {}, .rest = str };
    }
}.parse };

/// A parser that only succeeds on the end of the string.
pub const eos = Parser(void){ .parse = struct {
    fn parse(_: mem.Allocator, str: []const u8) Error!Void {
        if (str.len != 0)
            return error.ParserFailed;
        return Void{ .value = {}, .rest = str };
    }
}.parse };

test "eos" {
    const allocator = testing.failing_allocator;
    try expectResult(void, .{ .value = {} }, eos.parse(allocator, ""));
    try expectResult(void, error.ParserFailed, eos.parse(allocator, "a"));
}

/// A parser that always succeeds with the result being the
/// entire string. The same as the '.*$' regex.
pub const rest = Parser([]const u8){ .parse = struct {
    fn parse(_: mem.Allocator, str: []const u8) Error!Result([]const u8) {
        return Result([]const u8){ .value = str, .rest = str[str.len..] };
    }
}.parse };

test "rest" {
    const allocator = testing.failing_allocator;
    try expectResult([]const u8, .{ .value = "" }, rest.parse(allocator, ""));
    try expectResult([]const u8, .{ .value = "a" }, rest.parse(allocator, "a"));
}

/// Construct a parser that succeeds if the string passed in starts
/// with `str`.
pub fn string(comptime str: []const u8) Parser([]const u8) {
    return .{ .parse = struct {
        fn parse(_: mem.Allocator, s: []const u8) Error!Result([]const u8) {
            if (!mem.startsWith(u8, s, str))
                return error.ParserFailed;
            return Result([]const u8){ .value = str, .rest = s[str.len..] };
        }
    }.parse };
}

test "string" {
    const allocator = testing.failing_allocator;
    try expectResult([]const u8, .{ .value = "aa" }, string("aa").parse(allocator, "aa"));
    try expectResult([]const u8, .{ .value = "aa", .rest = "a" }, string("aa").parse(allocator, "aaa"));
    try expectResult([]const u8, error.ParserFailed, string("aa").parse(allocator, "ba"));
    try expectResult([]const u8, error.ParserFailed, string("aa").parse(allocator, ""));
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
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            var rem = str;
            var res: Array = undefined;
            for (&res, 0..) |*value, i| {
                if (i != 0)
                    rem = (try options.separator.parse(allocator, rem)).rest;

                const r = try parser.parse(allocator, rem);
                rem = r.rest;
                value.* = r.value;
            }

            return Res{ .value = res, .rest = rem };
        }
    }.parse };
}

test "manyN" {
    const allocator = testing.failing_allocator;
    const parser1 = comptime ascii.range('a', 'b')
        .manyN(3, .{});
    try expectResult([3]u8, .{ .value = "aba".*, .rest = "bab" }, parser1.parse(allocator, "ababab"));

    const parser2 = comptime ascii.range('a', 'b')
        .manyN(3, .{ .separator = discard(ascii.char(',')) });
    try expectResult([3]u8, .{ .value = "aba".*, .rest = ",b,a,b" }, parser2.parse(allocator, "a,b,a,b,a,b"));
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
            var i: usize = 0;
            while (i < options.max) : (i += 1) {
                const after_seperator = if (i != 0)
                    (options.separator.parse(allocator, rem) catch break).rest
                else
                    rem;

                const r = parser.parse(allocator, after_seperator) catch |e| switch (e) {
                    error.ParserFailed => break,
                    else => return e,
                };
                rem = r.rest;
                if (options.collect)
                    try res.append(r.value);
            }
            if (i < options.min)
                return error.ParserFailed;

            return Res{
                .value = if (options.collect) try res.toOwnedSlice() else str[0 .. str.len - rem.len],
                .rest = rem,
            };
        }
    }.parse };
}

test "many" {
    const allocator = testing.failing_allocator;
    const parser1 = comptime string("ab")
        .many(.{ .collect = false });
    try expectResult([]const u8, .{ .value = "" }, parser1.parse(allocator, ""));
    try expectResult([]const u8, .{ .value = "", .rest = "a" }, parser1.parse(allocator, "a"));
    try expectResult([]const u8, .{ .value = "ab" }, parser1.parse(allocator, "ab"));
    try expectResult([]const u8, .{ .value = "ab", .rest = "a" }, parser1.parse(allocator, "aba"));
    try expectResult([]const u8, .{ .value = "abab" }, parser1.parse(allocator, "abab"));
    try expectResult([]const u8, .{ .value = "abab", .rest = "a" }, parser1.parse(allocator, "ababa"));
    try expectResult([]const u8, .{ .value = "ababab" }, parser1.parse(allocator, "ababab"));

    const parser2 = comptime string("ab")
        .many(.{ .collect = false, .min = 1, .max = 2 });
    try expectResult([]const u8, error.ParserFailed, parser2.parse(allocator, ""));
    try expectResult([]const u8, error.ParserFailed, parser2.parse(allocator, "a"));
    try expectResult([]const u8, .{ .value = "ab" }, parser2.parse(allocator, "ab"));
    try expectResult([]const u8, .{ .value = "ab", .rest = "a" }, parser2.parse(allocator, "aba"));
    try expectResult([]const u8, .{ .value = "abab" }, parser2.parse(allocator, "abab"));
    try expectResult([]const u8, .{ .value = "abab", .rest = "a" }, parser2.parse(allocator, "ababa"));
    try expectResult([]const u8, .{ .value = "abab", .rest = "ab" }, parser2.parse(allocator, "ababab"));

    const parser3 = comptime string("ab")
        .many(.{ .collect = false, .separator = discard(ascii.char(',')) });
    try expectResult([]const u8, .{ .value = "" }, parser3.parse(allocator, ""));
    try expectResult([]const u8, .{ .value = "", .rest = "a" }, parser3.parse(allocator, "a"));
    try expectResult([]const u8, .{ .value = "ab" }, parser3.parse(allocator, "ab"));
    try expectResult([]const u8, .{ .value = "ab", .rest = "a" }, parser3.parse(allocator, "aba"));
    try expectResult([]const u8, .{ .value = "ab", .rest = "ab" }, parser3.parse(allocator, "abab"));
    try expectResult([]const u8, .{ .value = "ab,ab" }, parser3.parse(allocator, "ab,ab"));
    try expectResult([]const u8, .{ .value = "ab,ab", .rest = "," }, parser3.parse(allocator, "ab,ab,"));

    const parser4 = comptime utf8.char(0x100)
        .many(.{ .collect = false });
    try expectResult([]const u8, .{ .value = "ĀĀĀ", .rest = "āāā" }, parser4.parse(allocator, "ĀĀĀāāā"));

    const parser5 = comptime utf8.range(0x100, 0x100)
        .many(.{});
    const res = try parser5.parse(testing.allocator, "ĀĀĀāāā");
    defer testing.allocator.free(res.value);

    var expect = [_]u21{ 'Ā', 'Ā', 'Ā' };
    try expectResult([]u21, .{ .value = &expect, .rest = "āāā" }, res);
}

/// Construct a parser that will call `parser` on the string
/// but never fails to parse. The parser's result will be the
/// result of `parser` on success and `null` on failure.
pub fn opt(comptime parser: anytype) Parser(?ParserResult(@TypeOf(parser))) {
    const Res = Result(?ParserResult(@TypeOf(parser)));
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            const r = parser.parse(allocator, str) catch |e| switch (e) {
                error.ParserFailed => return Res{ .value = null, .rest = str },
                else => return e,
            };
            return Res{ .value = r.value, .rest = r.rest };
        }
    }.parse };
}

test "opt" {
    const allocator = testing.failing_allocator;
    const parser1 = comptime ascii.range('a', 'z')
        .opt();
    try expectResult(?u8, .{ .value = 'a' }, parser1.parse(allocator, "a"));
    try expectResult(?u8, .{ .value = 'a', .rest = "a" }, parser1.parse(allocator, "aa"));
    try expectResult(?u8, .{ .value = null, .rest = "1" }, parser1.parse(allocator, "1"));
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
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            var res: Res = undefined;
            res.rest = str;

            comptime var j = 0;
            inline for (parsers) |parser| {
                const r = try parser.parse(allocator, res.rest);
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
            return res;
        }
    }.parse };
}

test "combine" {
    const allocator = testing.failing_allocator;
    const parser1 = comptime combine(.{
        ascii.range('a', 'b').opt(),
        ascii.range('d', 'e').opt(),
    });
    const Res = ParserResult(@TypeOf(parser1));
    try expectResult(Res, .{ .value = .{ .@"0" = 'a', .@"1" = 'd' } }, parser1.parse(allocator, "ad"));
    try expectResult(Res, .{ .value = .{ .@"0" = 'a', .@"1" = null }, .rest = "a" }, parser1.parse(allocator, "aa"));
    try expectResult(Res, .{ .value = .{ .@"0" = null, .@"1" = 'd' }, .rest = "a" }, parser1.parse(allocator, "da"));
    try expectResult(Res, .{ .value = .{ .@"0" = null, .@"1" = null }, .rest = "qa" }, parser1.parse(allocator, "qa"));

    const parser2 = comptime combine(.{
        ascii.range('a', 'b').opt(),
        ascii.char('d'),
    });
    const Res2 = ParserResult(@TypeOf(parser2));
    try expectResult(Res2, .{ .value = .{ .@"0" = 'a', .@"1" = 'd' } }, parser2.parse(allocator, "ad"));
    try expectResult(Res2, .{ .value = .{ .@"0" = 'a', .@"1" = 'd' }, .rest = "a" }, parser2.parse(allocator, "ada"));
    try expectResult(Res2, .{ .value = .{ .@"0" = null, .@"1" = 'd' }, .rest = "a" }, parser2.parse(allocator, "da"));
    try expectResult(Res2, error.ParserFailed, parser2.parse(allocator, "qa"));
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
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Result(ParserResult(@TypeOf(parsers[0]))) {
            inline for (parsers) |p| {
                if (p.parse(allocator, str)) |res| {
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
    const parser1 = comptime oneOf(.{
        ascii.range('a', 'b'),
        ascii.range('d', 'e'),
    });
    try expectResult(u8, .{ .value = 'a' }, parser1.parse(allocator, "a"));
    try expectResult(u8, .{ .value = 'b' }, parser1.parse(allocator, "b"));
    try expectResult(u8, .{ .value = 'd' }, parser1.parse(allocator, "d"));
    try expectResult(u8, .{ .value = 'e' }, parser1.parse(allocator, "e"));
    try expectResult(u8, .{ .value = 'a', .rest = "a" }, parser1.parse(allocator, "aa"));
    try expectResult(u8, .{ .value = 'b', .rest = "a" }, parser1.parse(allocator, "ba"));
    try expectResult(u8, .{ .value = 'd', .rest = "a" }, parser1.parse(allocator, "da"));
    try expectResult(u8, .{ .value = 'e', .rest = "a" }, parser1.parse(allocator, "ea"));
    try expectResult(u8, error.ParserFailed, parser1.parse(allocator, "q"));
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
            return Res{ .value = str[0 .. str.len - r.rest.len], .rest = r.rest };
        }
    }.parse };
}

test "asStr" {
    const allocator = testing.failing_allocator;
    const parser1 = comptime ascii.char('a').asStr();
    try expectResult([]const u8, .{ .value = "a" }, parser1.parse(allocator, "a"));
    try expectResult([]const u8, .{ .value = "a", .rest = "a" }, parser1.parse(allocator, "aa"));
    try expectResult([]const u8, error.ParserFailed, parser1.parse(allocator, "ba"));

    const parser2 = comptime combine(.{
        ascii.range('a', 'b').opt(),
        ascii.range('d', 'e').opt(),
    }).asStr();
    try expectResult([]const u8, .{ .value = "ad" }, parser2.parse(allocator, "ad"));
    try expectResult([]const u8, .{ .value = "a", .rest = "a" }, parser2.parse(allocator, "aa"));
    try expectResult([]const u8, .{ .value = "d", .rest = "a" }, parser2.parse(allocator, "da"));
    try expectResult([]const u8, .{ .value = "", .rest = "qa" }, parser2.parse(allocator, "qa"));
}

fn ReturnTypeErrorPayload(comptime P: type) type {
    const return_type = ReturnType(P);
    return switch (@typeInfo(return_type)) {
        .ErrorUnion => |eu| eu.payload,
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
            const v = conv(allocator, r.value) catch |e| switch (@as(anyerror, e)) {
                error.ParserFailed => return error.ParserFailed,
                error.OutOfMemory => return error.OutOfMemory,
                else => return error.OtherError,
            };
            return Res{ .value = v, .rest = r.rest };
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
    const parser1 = comptime string("123")
        .asStr()
        .convert(toInt(u8, 10));
    try expectResult(u8, .{ .value = 123 }, parser1.parse(allocator, "123"));
    try expectResult(u8, .{ .value = 123, .rest = "a" }, parser1.parse(allocator, "123a"));
    try expectResult(u8, error.ParserFailed, parser1.parse(allocator, "12"));

    const parser2 = comptime string("a")
        .asStr()
        .convert(toChar);
    try expectResult(u21, .{ .value = 'a' }, parser2.parse(allocator, "a"));
    try expectResult(u21, .{ .value = 'a', .rest = "a" }, parser2.parse(allocator, "aa"));
    try expectResult(u21, error.ParserFailed, parser2.parse(allocator, "b"));

    const parser3 = comptime rest.convert(toBool);
    try expectResult(bool, .{ .value = true }, parser3.parse(allocator, "true"));
    try expectResult(bool, .{ .value = false }, parser3.parse(allocator, "false"));
    try expectResult(bool, error.ParserFailed, parser3.parse(allocator, "b"));

    const parser4 = comptime string("1.23")
        .asStr()
        .convert(toFloat(f32));
    try expectResult(f32, .{ .value = 1.23 }, parser4.parse(allocator, "1.23"));
    try expectResult(f32, .{ .value = 1.23, .rest = "a" }, parser4.parse(allocator, "1.23a"));
    try expectResult(f32, error.ParserFailed, parser4.parse(allocator, "1.2"));

    const E = enum(u8) { a, b, _ };
    const parser5 = comptime rest.convert(toEnum(E));
    try expectResult(E, .{ .value = E.a }, parser5.parse(allocator, "a"));
    try expectResult(E, .{ .value = E.b }, parser5.parse(allocator, "b"));
    try expectResult(E, error.ParserFailed, parser5.parse(allocator, "2"));

    const parser6 = comptime string("Āā")
        .asStr()
        .convert(toChar);
    try expectResult(u21, .{ .value = 0x100 }, parser6.parse(allocator, "Āā"));
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
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            const r = try parser.parse(allocator, str);
            return Res{ .value = conv(r.value), .rest = r.rest };
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
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            const r = try parser.parse(allocator, str);
            return Res{ .value = value, .rest = r.rest };
        }
    }.parse };
}

test "mapConst" {
    const allocator = testing.failing_allocator;
    const parser1 = comptime string("123")
        .asStr()
        .mapConst(@as(u8, 3));
    try expectResult(u8, .{ .value = 3 }, parser1.parse(allocator, "123"));
}

fn ToStructResult(comptime T: type) type {
    return @TypeOf(struct {
        fn func(_: anytype) T {
            return undefined;
        }
    }.func);
}

/// Constructs a convert function for `map` that takes a tuple or an array and
/// converts it into the struct `T`. Fields will be assigned in order,
/// so `tuple[i]` will be assigned to the ith field of `T`. This function
/// will give a compile error if `T` and the tuple does not have the same
/// number of fields, or if the items of the tuple cannot be coerced into
/// the fields of the struct.
pub fn toStruct(comptime T: type) ToStructResult(T) {
    return struct {
        fn func(tuple: anytype) T {
            const struct_fields = @typeInfo(T).Struct.fields;
            if (struct_fields.len != tuple.len)
                @compileError(@typeName(T) ++ " and " ++ @typeName(@TypeOf(tuple)) ++ " does not have " ++
                    "same number of fields. Conversion is not possible.");

            var res: T = undefined;
            inline for (struct_fields, 0..) |field, i|
                @field(res, field.name) = tuple[i];

            return res;
        }
    }.func;
}

test "map" {
    const allocator = testing.failing_allocator;
    const Point = struct {
        x: usize,
        y: usize,
    };
    const parser1 = comptime combine(.{
        int(usize, .{}),
        ascii.char(' ').discard(),
        int(usize, .{}),
    }).map(toStruct(Point));
    try expectResult(Point, .{ .value = .{ .x = 10, .y = 10 } }, parser1.parse(allocator, "10 10"));
    try expectResult(Point, .{ .value = .{ .x = 20, .y = 20 }, .rest = "aa" }, parser1.parse(allocator, "20 20aa"));
    try expectResult(Point, error.ParserFailed, parser1.parse(allocator, "12"));

    const parser2 = comptime combine(.{
        int(usize, .{}),
        ascii.char(' ').discard(),
    })
        .manyN(2, .{})
        .map(toStruct(Point));
    try expectResult(Point, .{ .value = .{ .x = 10, .y = 10 } }, parser2.parse(allocator, "10 10 "));
    try expectResult(Point, .{ .value = .{ .x = 20, .y = 20 }, .rest = "aa" }, parser2.parse(allocator, "20 20 aa"));
    try expectResult(Point, error.ParserFailed, parser2.parse(allocator, "12"));
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
    const parser = comptime ascii.char(' ').many(.{ .collect = false }).discard();
    try expectResult(void, .{ .value = {}, .rest = "abc" }, parser.parse(allocator, "abc"));
    try expectResult(void, .{ .value = {}, .rest = "abc" }, parser.parse(allocator, " abc"));
    try expectResult(void, .{ .value = {}, .rest = "abc" }, parser.parse(allocator, "  abc"));
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
        fn parse(_: mem.Allocator, str: []const u8) Error!Res {
            if (options.parse_sign and str.len != 0) {
                switch (str[0]) {
                    '+' => return parseAfterSign(str[1..], add),
                    '-' => return parseAfterSign(str[1..], sub),
                    else => {},
                }
            }

            return parseAfterSign(str, add);
        }

        fn parseAfterSign(
            str: []const u8,
            add_sub: *const fn (Int, Int) Overflow!Int,
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

            return Res{ .value = res, .rest = str[end + 1 ..] };
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
    const parser1 = int(u8, .{});
    try expectResult(u8, .{ .value = 0 }, parser1.parse(allocator, "0"));
    try expectResult(u8, .{ .value = 1 }, parser1.parse(allocator, "1"));
    try expectResult(u8, .{ .value = 1, .rest = "a" }, parser1.parse(allocator, "1a"));
    try expectResult(u8, .{ .value = 255 }, parser1.parse(allocator, "255"));
    try expectResult(u8, .{ .value = 255, .rest = "5" }, parser1.parse(allocator, "2555"));
    try expectResult(u8, .{ .value = 25, .rest = "6" }, parser1.parse(allocator, "256"));
    try expectResult(u8, .{ .value = 255 }, parser1.parse(allocator, "+255"));
    try expectResult(u8, error.ParserFailed, parser1.parse(allocator, "-255"));

    const parser2 = int(u8, .{ .base = 16 });
    try expectResult(u8, .{ .value = 0x00 }, parser2.parse(allocator, "0"));
    try expectResult(u8, .{ .value = 0x01 }, parser2.parse(allocator, "1"));
    try expectResult(u8, .{ .value = 0x1a }, parser2.parse(allocator, "1a"));
    try expectResult(u8, .{ .value = 0x01, .rest = "g" }, parser2.parse(allocator, "1g"));
    try expectResult(u8, .{ .value = 0xff }, parser2.parse(allocator, "ff"));
    try expectResult(u8, .{ .value = 0xff }, parser2.parse(allocator, "FF"));
    try expectResult(u8, .{ .value = 0xff }, parser2.parse(allocator, "00FF"));
    try expectResult(u8, .{ .value = 0x10, .rest = "0" }, parser2.parse(allocator, "100"));
    try expectResult(u8, .{ .value = 0xf, .rest = "g" }, parser2.parse(allocator, "fg"));
    try expectResult(u8, .{ .value = 0xff }, parser2.parse(allocator, "+ff"));
    try expectResult(u8, error.ParserFailed, parser2.parse(allocator, "-ff"));

    const parser3 = int(u8, .{ .base = 16, .max_digits = 2 });
    try expectResult(u8, .{ .value = 0xff }, parser3.parse(allocator, "FF"));
    try expectResult(u8, .{ .value = 0x00, .rest = "FF" }, parser3.parse(allocator, "00FF"));

    const parser4 = int(isize, .{});
    try expectResult(isize, .{ .value = 255 }, parser4.parse(allocator, "+255"));
    try expectResult(isize, .{ .value = -255 }, parser4.parse(allocator, "-255"));

    const parser5 = int(isize, .{ .parse_sign = false });
    try expectResult(isize, .{ .value = 255 }, parser5.parse(allocator, "255"));
    try expectResult(isize, error.ParserFailed, parser5.parse(allocator, "+255"));
    try expectResult(isize, error.ParserFailed, parser5.parse(allocator, "-255"));
}

/// Construct a parser that succeeds if it parses any tag from `Enum` as
/// a string. The longest match is always chosen, so for `enum{a,aa}` the
/// "aa" string will succeed parsing and have the result of `.aa` and not
/// `.a`.
pub fn enumeration(comptime Enum: type) Parser(Enum) {
    const Res = Result(Enum);
    return .{ .parse = struct {
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Res {
            var res: Error!Res = error.ParserFailed;
            inline for (@typeInfo(Enum).Enum.fields) |field| next: {
                const p = comptime string(field.name);
                const new = p.parse(allocator, str) catch |err| switch (err) {
                    error.ParserFailed => break :next,
                    else => |e| return e,
                };
                const old = res catch Res{ .value = undefined, .rest = str };
                if (new.rest.len < old.rest.len)
                    res = Res{ .value = @field(Enum, field.name), .rest = new.rest };
            }

            return res;
        }
    }.parse };
}

test "enumeration" {
    const allocator = testing.failing_allocator;
    const E1 = enum { a, b, aa };
    const parser1 = enumeration(E1);
    try expectResult(E1, .{ .value = .a }, parser1.parse(allocator, "a"));
    try expectResult(E1, .{ .value = .aa }, parser1.parse(allocator, "aa"));
    try expectResult(E1, .{ .value = .b }, parser1.parse(allocator, "b"));
    try expectResult(E1, .{ .value = .a, .rest = "b" }, parser1.parse(allocator, "ab"));
    try expectResult(E1, .{ .value = .b, .rest = "b" }, parser1.parse(allocator, "bb"));
    try expectResult(E1, error.ParserFailed, parser1.parse(allocator, "256"));
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
        fn parse(allocator: mem.Allocator, str: []const u8) Error!Result(ParserResult(P)) {
            return func().parse(allocator, str);
        }
    }.parse };
}

test "ref" {
    const allocator = testing.failing_allocator;
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
    try expectResult(void, .{ .value = {} }, Scope.digits.parse(allocator, "0"));
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
            .Pointer => |ptr| try testing.expectEqualSlices(ptr.child, expect.value, actual.value),
            else => try testing.expectEqual(expect.value, actual.value),
        },
    }
}
