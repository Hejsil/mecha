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

/// All the ways in which a parser can fail.
/// ParserFailed corresponds to the string not matching the expected form and is
/// the only one `mecha` intrinsically deals with.
pub const Error = error{ ParserFailed, OtherError } || mem.Allocator.Error;

pub const Void = Result(void);

/// The result of a successful parse
pub fn Result(comptime T: type) type {
    return struct {
        pub const Value = T;

        value: T,
        rest: []const u8 = "",
    };
}

/// The type of all parser that can work with `mecha`
pub fn Parser(comptime T: type) type {
    return ParserWithCC(T, .Unspecified);
}

pub fn ParserWithCC(comptime T: type, comptime cc: std.builtin.CallingConvention) type {
    return *const fn (mem.Allocator, []const u8) callconv(cc) Error!Result(T);
}

fn typecheckParser(comptime P: type) void {
    const Fn = switch (@typeInfo(P)) {
        .Pointer => |p| p.child,
        .Fn => P,
        else => @compileError("expected 'mecha.Parser(T)', found '" ++ @typeName(P) ++ "'"),
    };
    switch (@typeInfo(Fn)) {
        .Fn => |func| {
            const R = func.return_type orelse
                @compileError("expected 'mecha.Parser(T)', found '" ++ @typeName(P) ++ "'");
            const T = switch (@typeInfo(R)) {
                .ErrorUnion => |e| e.payload.Value,
                else => @compileError("expected 'mecha.Parser(T)', found '" ++ @typeName(P) ++ "'"),
            };
            if (P != ParserWithCC(T, func.calling_convention))
                @compileError("expected 'mecha.Parser(" ++ @typeName(T) ++ ")', found '" ++ @typeName(P) ++ "'");
        },
        else => @compileError("expected 'mecha.Parser(T)', found '" ++ @typeName(P) ++ "'"),
    }
}

fn ReturnType(comptime P: type) type {
    return switch (@typeInfo(P)) {
        .Pointer => |p| @typeInfo(p.child).Fn.return_type.?,
        .Fn => |f| f.return_type.?,
        else => unreachable,
    };
}

/// The reverse of `Parser`. Give it a `Parser` type
/// and this function will give you `T`.
pub fn ParserResult(comptime P: type) type {
    typecheckParser(P);
    return @typeInfo(ReturnType(P)).ErrorUnion.payload.Value;
}

/// A parser that always succeeds and parses nothing. This parser
/// is only really useful for generic code. See `many`.
pub fn noop(_: mem.Allocator, str: []const u8) Error!Void {
    return Void{ .value = {}, .rest = str };
}

/// A parser that only succeeds on the end of the string.
pub fn eos(_: mem.Allocator, str: []const u8) Error!Void {
    if (str.len != 0)
        return error.ParserFailed;
    return Void{ .value = {}, .rest = str };
}

test "eos" {
    const allocator = testing.failing_allocator;
    try expectResult(void, .{ .value = {} }, eos(allocator, ""));
    try expectResult(void, error.ParserFailed, eos(allocator, "a"));
}

/// A parser that always succeeds with the result being the
/// entire string. The same as the '.*$' regex.
pub fn rest(_: mem.Allocator, str: []const u8) Error!Result([]const u8) {
    return Result([]const u8){ .value = str, .rest = str[str.len..] };
}

test "rest" {
    const allocator = testing.failing_allocator;
    try expectResult([]const u8, .{ .value = "" }, rest(allocator, ""));
    try expectResult([]const u8, .{ .value = "a" }, rest(allocator, "a"));
}

/// Construct a parser that succeeds if the string passed in starts
/// with `str`.
pub fn string(comptime str: []const u8) Parser(void) {
    return struct {
        fn func(_: mem.Allocator, s: []const u8) Error!Void {
            if (!mem.startsWith(u8, s, str))
                return error.ParserFailed;
            return Void{ .value = {}, .rest = s[str.len..] };
        }
    }.func;
}

test "string" {
    const allocator = testing.failing_allocator;
    try expectResult(void, .{ .value = {} }, string("aa")(allocator, "aa"));
    try expectResult(void, .{ .value = {}, .rest = "a" }, string("aa")(allocator, "aaa"));
    try expectResult(void, error.ParserFailed, string("aa")(allocator, "ba"));
    try expectResult(void, error.ParserFailed, string("aa")(allocator, ""));
}

pub const ManyNOptions = struct {
    /// A parser used to parse the content between each element `manyN` parses.
    /// The default is `noop`, so each element will be parsed one after another.
    separator: *const fn (mem.Allocator, []const u8) Error!Void = noop,
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
    return struct {
        fn func(allocator: mem.Allocator, str: []const u8) Error!Res {
            var rem = str;
            var res: Array = undefined;
            for (res) |*value, i| {
                if (i != 0)
                    rem = (try options.separator(allocator, rem)).rest;

                const r = try parser(allocator, rem);
                rem = r.rest;
                value.* = r.value;
            }

            return Res{ .value = res, .rest = rem };
        }
    }.func;
}

test "manyN" {
    const allocator = testing.failing_allocator;
    const parser1 = comptime manyN(ascii.range('a', 'b'), 3, .{});
    try expectResult([3]u8, .{ .value = "aba".*, .rest = "bab" }, parser1(allocator, "ababab"));

    const parser2 = comptime manyN(ascii.range('a', 'b'), 3, .{ .separator = ascii.char(',') });
    try expectResult([3]u8, .{ .value = "aba".*, .rest = ",b,a,b" }, parser2(allocator, "a,b,a,b,a,b"));
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
    separator: *const fn (mem.Allocator, []const u8) Error!Void = noop,
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

    return struct {
        fn func(allocator: mem.Allocator, str: []const u8) Error!Res {
            var res = if (options.collect)
                try std.ArrayList(Element).initCapacity(allocator, options.min)
            else {};
            errdefer if (options.collect) res.deinit();

            var rem = str;
            var i: usize = 0;
            while (i < options.max) : (i += 1) {
                const after_seperator = if (i != 0)
                    (options.separator(allocator, rem) catch break).rest
                else
                    rem;

                const r = parser(allocator, after_seperator) catch |e| switch (e) {
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
    }.func;
}

test "many" {
    const allocator = testing.failing_allocator;
    const parser1 = comptime many(string("ab"), .{ .collect = false });
    try expectResult([]const u8, .{ .value = "" }, parser1(allocator, ""));
    try expectResult([]const u8, .{ .value = "", .rest = "a" }, parser1(allocator, "a"));
    try expectResult([]const u8, .{ .value = "ab" }, parser1(allocator, "ab"));
    try expectResult([]const u8, .{ .value = "ab", .rest = "a" }, parser1(allocator, "aba"));
    try expectResult([]const u8, .{ .value = "abab" }, parser1(allocator, "abab"));
    try expectResult([]const u8, .{ .value = "abab", .rest = "a" }, parser1(allocator, "ababa"));
    try expectResult([]const u8, .{ .value = "ababab" }, parser1(allocator, "ababab"));

    const parser2 = comptime many(string("ab"), .{ .collect = false, .min = 1, .max = 2 });
    try expectResult([]const u8, error.ParserFailed, parser2(allocator, ""));
    try expectResult([]const u8, error.ParserFailed, parser2(allocator, "a"));
    try expectResult([]const u8, .{ .value = "ab" }, parser2(allocator, "ab"));
    try expectResult([]const u8, .{ .value = "ab", .rest = "a" }, parser2(allocator, "aba"));
    try expectResult([]const u8, .{ .value = "abab" }, parser2(allocator, "abab"));
    try expectResult([]const u8, .{ .value = "abab", .rest = "a" }, parser2(allocator, "ababa"));
    try expectResult([]const u8, .{ .value = "abab", .rest = "ab" }, parser2(allocator, "ababab"));

    const parser3 = comptime many(string("ab"), .{ .collect = false, .separator = ascii.char(',') });
    try expectResult([]const u8, .{ .value = "" }, parser3(allocator, ""));
    try expectResult([]const u8, .{ .value = "", .rest = "a" }, parser3(allocator, "a"));
    try expectResult([]const u8, .{ .value = "ab" }, parser3(allocator, "ab"));
    try expectResult([]const u8, .{ .value = "ab", .rest = "a" }, parser3(allocator, "aba"));
    try expectResult([]const u8, .{ .value = "ab", .rest = "ab" }, parser3(allocator, "abab"));
    try expectResult([]const u8, .{ .value = "ab,ab" }, parser3(allocator, "ab,ab"));
    try expectResult([]const u8, .{ .value = "ab,ab", .rest = "," }, parser3(allocator, "ab,ab,"));

    const parser4 = comptime many(utf8.char(0x100), .{ .collect = false });
    try expectResult([]const u8, .{ .value = "ĀĀĀ", .rest = "āāā" }, parser4(allocator, "ĀĀĀāāā"));

    const parser5 = comptime many(utf8.range(0x100, 0x100), .{});
    const res = try parser5(testing.allocator, "ĀĀĀāāā");
    defer testing.allocator.free(res.value);

    var expect = [_]u21{ 'Ā', 'Ā', 'Ā' };
    try expectResult([]u21, .{ .value = &expect, .rest = "āāā" }, res);
}

/// Construct a parser that will call `parser` on the string
/// but never fails to parse. The parser's result will be the
/// result of `parser` on success and `null` on failure.
pub fn opt(comptime parser: anytype) Parser(?ParserResult(@TypeOf(parser))) {
    const Res = Result(?ParserResult(@TypeOf(parser)));
    return struct {
        fn func(allocator: mem.Allocator, str: []const u8) Error!Res {
            const r = parser(allocator, str) catch |e| switch (e) {
                error.ParserFailed => return Res{ .value = null, .rest = str },
                else => return e,
            };
            return Res{ .value = r.value, .rest = r.rest };
        }
    }.func;
}

test "opt" {
    const allocator = testing.failing_allocator;
    const parser1 = comptime opt(ascii.range('a', 'z'));
    try expectResult(?u8, .{ .value = 'a' }, parser1(allocator, "a"));
    try expectResult(?u8, .{ .value = 'a', .rest = "a" }, parser1(allocator, "aa"));
    try expectResult(?u8, .{ .value = null, .rest = "1" }, parser1(allocator, "1"));
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
    return struct {
        fn func(allocator: mem.Allocator, str: []const u8) Error!Res {
            var res: Res = undefined;
            res.rest = str;

            comptime var j = 0;
            inline for (parsers) |parser| {
                const r = try parser(allocator, res.rest);
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
    }.func;
}

test "combine" {
    const allocator = testing.failing_allocator;
    const parser1 = comptime combine(.{ opt(ascii.range('a', 'b')), opt(ascii.range('d', 'e')) });
    const Res = ParserResult(@TypeOf(parser1));
    try expectResult(Res, .{ .value = .{ .@"0" = 'a', .@"1" = 'd' } }, parser1(allocator, "ad"));
    try expectResult(Res, .{ .value = .{ .@"0" = 'a', .@"1" = null }, .rest = "a" }, parser1(allocator, "aa"));
    try expectResult(Res, .{ .value = .{ .@"0" = null, .@"1" = 'd' }, .rest = "a" }, parser1(allocator, "da"));
    try expectResult(Res, .{ .value = .{ .@"0" = null, .@"1" = null }, .rest = "qa" }, parser1(allocator, "qa"));

    const parser2 = comptime combine(.{ opt(ascii.range('a', 'b')), ascii.char('d') });
    try expectResult(?u8, .{ .value = 'a' }, parser2(allocator, "ad"));
    try expectResult(?u8, .{ .value = 'a', .rest = "a" }, parser2(allocator, "ada"));
    try expectResult(?u8, .{ .value = null, .rest = "a" }, parser2(allocator, "da"));
    try expectResult(?u8, error.ParserFailed, parser2(allocator, "qa"));
}

/// Takes a tuple of `Parser(T)` and constructs a parser that
/// only succeeds if one of the parsers succeed to parse. The
/// parsers will be called in order all with `str` as input.
/// The parser will return with the result of the first parser
/// that succeeded. The parsers result will be `Result(T)`
pub fn oneOf(comptime parsers: anytype) Parser(ParserResult(@TypeOf(parsers[0]))) {
    inline for (parsers) |parser|
        typecheckParser(@TypeOf(parser));

    return struct {
        fn func(allocator: mem.Allocator, str: []const u8) Error!Result(ParserResult(@TypeOf(parsers[0]))) {
            inline for (parsers) |p| {
                if (p(allocator, str)) |res| {
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
    }.func;
}

test "oneOf" {
    const allocator = testing.failing_allocator;
    const parser1 = comptime oneOf(.{ ascii.range('a', 'b'), ascii.range('d', 'e') });
    try expectResult(u8, .{ .value = 'a' }, parser1(allocator, "a"));
    try expectResult(u8, .{ .value = 'b' }, parser1(allocator, "b"));
    try expectResult(u8, .{ .value = 'd' }, parser1(allocator, "d"));
    try expectResult(u8, .{ .value = 'e' }, parser1(allocator, "e"));
    try expectResult(u8, .{ .value = 'a', .rest = "a" }, parser1(allocator, "aa"));
    try expectResult(u8, .{ .value = 'b', .rest = "a" }, parser1(allocator, "ba"));
    try expectResult(u8, .{ .value = 'd', .rest = "a" }, parser1(allocator, "da"));
    try expectResult(u8, .{ .value = 'e', .rest = "a" }, parser1(allocator, "ea"));
    try expectResult(u8, error.ParserFailed, parser1(allocator, "q"));
}

/// Takes any parser (preferable not of type `Parser([]const u8)`)
/// and converts it to a parser where the result is a string that
/// contains all characters parsed by `parser`.
pub fn asStr(comptime parser: anytype) Parser([]const u8) {
    const Res = Result([]const u8);
    typecheckParser(@TypeOf(parser));
    return struct {
        fn func(allocator: mem.Allocator, str: []const u8) Error!Res {
            const r = try parser(allocator, str);
            return Res{ .value = str[0 .. str.len - r.rest.len], .rest = r.rest };
        }
    }.func;
}

test "asStr" {
    const allocator = testing.failing_allocator;
    const parser1 = comptime asStr(ascii.char('a'));
    try expectResult([]const u8, .{ .value = "a" }, parser1(allocator, "a"));
    try expectResult([]const u8, .{ .value = "a", .rest = "a" }, parser1(allocator, "aa"));
    try expectResult([]const u8, error.ParserFailed, parser1(allocator, "ba"));

    const parser2 = comptime asStr(combine(.{ opt(ascii.range('a', 'b')), opt(ascii.range('d', 'e')) }));
    try expectResult([]const u8, .{ .value = "ad" }, parser2(allocator, "ad"));
    try expectResult([]const u8, .{ .value = "a", .rest = "a" }, parser2(allocator, "aa"));
    try expectResult([]const u8, .{ .value = "d", .rest = "a" }, parser2(allocator, "da"));
    try expectResult([]const u8, .{ .value = "", .rest = "qa" }, parser2(allocator, "qa"));
}

/// Constructs a parser that has its result converted with the
/// `conv` function. The ´conv` functions signature is
/// `fn (mem.Allocator, ParserResult(parser)) !T`.
/// The parser constructed will fail if `conv` fails.
pub fn convert(
    comptime T: type,
    comptime conv: anytype,
    comptime parser: anytype,
) Parser(T) {
    const Res = Result(T);
    return struct {
        fn func(allocator: mem.Allocator, str: []const u8) Error!Res {
            const r = try parser(allocator, str);
            const v = conv(allocator, r.value) catch |e| switch (@as(anyerror, e)) {
                error.ParserFailed => return error.ParserFailed,
                error.OutOfMemory => return error.OutOfMemory,
                else => return error.OtherError,
            };
            return Res{ .value = v, .rest = r.rest };
        }
    }.func;
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
pub fn toChar(_: mem.Allocator, str: []const u8) anyerror!u21 {
    if (str.len > 1) {
        const cp_len = try unicode.utf8ByteSequenceLength(str[0]);
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
    const parser1 = comptime convert(u8, toInt(u8, 10), asStr(string("123")));
    try expectResult(u8, .{ .value = 123 }, parser1(allocator, "123"));
    try expectResult(u8, .{ .value = 123, .rest = "a" }, parser1(allocator, "123a"));
    try expectResult(u8, error.ParserFailed, parser1(allocator, "12"));

    const parser2 = comptime convert(u21, toChar, asStr(string("a")));
    try expectResult(u21, .{ .value = 'a' }, parser2(allocator, "a"));
    try expectResult(u21, .{ .value = 'a', .rest = "a" }, parser2(allocator, "aa"));
    try expectResult(u21, error.ParserFailed, parser2(allocator, "b"));

    const parser3 = comptime convert(bool, toBool, rest);
    try expectResult(bool, .{ .value = true }, parser3(allocator, "true"));
    try expectResult(bool, .{ .value = false }, parser3(allocator, "false"));
    try expectResult(bool, error.ParserFailed, parser3(allocator, "b"));

    const parser4 = comptime convert(f32, toFloat(f32), asStr(string("1.23")));
    try expectResult(f32, .{ .value = 1.23 }, parser4(allocator, "1.23"));
    try expectResult(f32, .{ .value = 1.23, .rest = "a" }, parser4(allocator, "1.23a"));
    try expectResult(f32, error.ParserFailed, parser4(allocator, "1.2"));

    const E = enum(u8) { a, b, _ };
    const parser5 = comptime convert(E, toEnum(E), rest);
    try expectResult(E, .{ .value = E.a }, parser5(allocator, "a"));
    try expectResult(E, .{ .value = E.b }, parser5(allocator, "b"));
    try expectResult(E, error.ParserFailed, parser5(allocator, "2"));

    const parser6 = comptime convert(u21, toChar, asStr(string("Āā")));
    try expectResult(u21, .{ .value = 0x100 }, parser6(allocator, "Āā"));
}

/// Constructs a parser that has its result converted with the
/// `conv` function. The ´conv` functions signature is
/// `fn (ParserResult(parser)) T`, so this function should only
/// be used for conversions that cannot fail. See `convert`.
pub fn map(
    comptime T: type,
    comptime conv: anytype,
    comptime parser: anytype,
) Parser(T) {
    const Res = Result(T);
    typecheckParser(@TypeOf(parser));
    return struct {
        fn func(allocator: mem.Allocator, str: []const u8) Error!Res {
            const r = try parser(allocator, str);
            return Res{ .value = conv(r.value), .rest = r.rest };
        }
    }.func;
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
            inline for (struct_fields) |field, i|
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
    const parser1 = comptime map(Point, toStruct(Point), combine(.{ int(usize, .{}), ascii.char(' '), int(usize, .{}) }));
    try expectResult(Point, .{ .value = .{ .x = 10, .y = 10 } }, parser1(allocator, "10 10"));
    try expectResult(Point, .{ .value = .{ .x = 20, .y = 20 }, .rest = "aa" }, parser1(allocator, "20 20aa"));
    try expectResult(Point, error.ParserFailed, parser1(allocator, "12"));

    const parser2 = comptime map(Point, toStruct(Point), manyN(combine(.{ int(usize, .{}), ascii.char(' ') }), 2, .{}));
    try expectResult(Point, .{ .value = .{ .x = 10, .y = 10 } }, parser2(allocator, "10 10 "));
    try expectResult(Point, .{ .value = .{ .x = 20, .y = 20 }, .rest = "aa" }, parser2(allocator, "20 20 aa"));
    try expectResult(Point, error.ParserFailed, parser2(allocator, "12"));
}

/// Constructs a parser that discards the result returned from the parser
/// it wraps.
pub fn discard(comptime parser: anytype) Parser(void) {
    return map(void, struct {
        fn d(_: anytype) void {}
    }.d, parser);
}

test "discard" {
    const allocator = testing.failing_allocator;
    const parser = comptime discard(many(ascii.char(' '), .{ .collect = false }));
    try expectResult(void, .{ .value = {}, .rest = "abc" }, parser(allocator, "abc"));
    try expectResult(void, .{ .value = {}, .rest = "abc" }, parser(allocator, " abc"));
    try expectResult(void, .{ .value = {}, .rest = "abc" }, parser(allocator, "  abc"));
}

fn digitsForBase(val: anytype, base: u8) usize {
    var res: usize = 0;
    var tmp = val;
    while (tmp != 0) : (tmp /= @intCast(@TypeOf(val), base))
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

    return comptime asStr(combine(.{
        sign_parser,
        many(ascii.digit(options.base), .{
            .collect = false,
            .min = 1,
            .max = options.max_digits,
        }),
    }));
}

/// Same as `intToken` but also converts the parsed string to an
/// integer. This parser will at most parse the same number of digits
/// as the underlying interger can hold in the specified base.
pub fn int(comptime Int: type, comptime options: IntOptions) Parser(Int) {
    debug.assert(options.max_digits != 0);
    const Res = Result(Int);

    return struct {
        fn intParser(_: mem.Allocator, str: []const u8) Error!Res {
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

            const max_digits = math.min(str.len, options.max_digits);
            const first = fmt.charToDigit(str[0], options.base) catch return error.ParserFailed;
            const first_casted = math.cast(Int, first) orelse return error.ParserFailed;

            var res = add_sub(0, first_casted) catch return error.ParserFailed;
            const end = for (str[1..max_digits]) |c, i| {
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
    }.intParser;
}

test "int" {
    const allocator = testing.failing_allocator;
    const parser1 = int(u8, .{});
    try expectResult(u8, .{ .value = 0 }, parser1(allocator, "0"));
    try expectResult(u8, .{ .value = 1 }, parser1(allocator, "1"));
    try expectResult(u8, .{ .value = 1, .rest = "a" }, parser1(allocator, "1a"));
    try expectResult(u8, .{ .value = 255 }, parser1(allocator, "255"));
    try expectResult(u8, .{ .value = 255, .rest = "5" }, parser1(allocator, "2555"));
    try expectResult(u8, .{ .value = 25, .rest = "6" }, parser1(allocator, "256"));
    try expectResult(u8, .{ .value = 255 }, parser1(allocator, "+255"));
    try expectResult(u8, error.ParserFailed, parser1(allocator, "-255"));

    const parser2 = int(u8, .{ .base = 16 });
    try expectResult(u8, .{ .value = 0x00 }, parser2(allocator, "0"));
    try expectResult(u8, .{ .value = 0x01 }, parser2(allocator, "1"));
    try expectResult(u8, .{ .value = 0x1a }, parser2(allocator, "1a"));
    try expectResult(u8, .{ .value = 0x01, .rest = "g" }, parser2(allocator, "1g"));
    try expectResult(u8, .{ .value = 0xff }, parser2(allocator, "ff"));
    try expectResult(u8, .{ .value = 0xff }, parser2(allocator, "FF"));
    try expectResult(u8, .{ .value = 0xff }, parser2(allocator, "00FF"));
    try expectResult(u8, .{ .value = 0x10, .rest = "0" }, parser2(allocator, "100"));
    try expectResult(u8, .{ .value = 0xf, .rest = "g" }, parser2(allocator, "fg"));
    try expectResult(u8, .{ .value = 0xff }, parser2(allocator, "+ff"));
    try expectResult(u8, error.ParserFailed, parser2(allocator, "-ff"));

    const parser3 = int(u8, .{ .base = 16, .max_digits = 2 });
    try expectResult(u8, .{ .value = 0xff }, parser3(allocator, "FF"));
    try expectResult(u8, .{ .value = 0x00, .rest = "FF" }, parser3(allocator, "00FF"));

    const parser4 = int(isize, .{});
    try expectResult(isize, .{ .value = 255 }, parser4(allocator, "+255"));
    try expectResult(isize, .{ .value = -255 }, parser4(allocator, "-255"));

    const parser5 = int(isize, .{ .parse_sign = false });
    try expectResult(isize, .{ .value = 255 }, parser5(allocator, "255"));
    try expectResult(isize, error.ParserFailed, parser5(allocator, "+255"));
    try expectResult(isize, error.ParserFailed, parser5(allocator, "-255"));
}

/// Construct a parser that succeeds if it parses any tag from `Enum` as
/// a string. The longest match is always chosen, so for `enum{a,aa}` the
/// "aa" string will succeed parsing and have the result of `.aa` and not
/// `.a`.
pub fn enumeration(comptime Enum: type) Parser(Enum) {
    const Res = Result(Enum);
    return struct {
        fn func(allocator: mem.Allocator, str: []const u8) Error!Res {
            var res: Error!Res = error.ParserFailed;
            inline for (@typeInfo(Enum).Enum.fields) |field| next: {
                const p = comptime string(field.name);
                const new = p(allocator, str) catch |err| switch (err) {
                    error.ParserFailed => break :next,
                    else => |e| return e,
                };
                const old = res catch Res{ .value = undefined, .rest = str };
                if (new.rest.len < old.rest.len)
                    res = Res{ .value = @field(Enum, field.name), .rest = new.rest };
            }

            return res;
        }
    }.func;
}

test "enumeration" {
    const allocator = testing.failing_allocator;
    const E1 = enum { a, b, aa };
    const parser1 = enumeration(E1);
    try expectResult(E1, .{ .value = .a }, parser1(allocator, "a"));
    try expectResult(E1, .{ .value = .aa }, parser1(allocator, "aa"));
    try expectResult(E1, .{ .value = .b }, parser1(allocator, "b"));
    try expectResult(E1, .{ .value = .a, .rest = "b" }, parser1(allocator, "ab"));
    try expectResult(E1, .{ .value = .b, .rest = "b" }, parser1(allocator, "bb"));
    try expectResult(E1, error.ParserFailed, parser1(allocator, "256"));
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
pub fn ref(comptime func: anytype) Parser(ParserResult(ReturnType(@TypeOf(func)))) {
    const P = ReturnType(@TypeOf(func));
    const T = ParserResult(P);
    return struct {
        fn res(allocator: mem.Allocator, str: []const u8) Error!Result(T) {
            return func()(allocator, str);
        }
    }.res;
}

test "ref" {
    const allocator = testing.failing_allocator;
    const Scope = struct {
        const digit = discard(ascii.digit(10));
        const digits = oneOf(.{ combine(.{ digit, ref(digitsRef) }), digit });
        fn digitsRef() Parser(void) {
            return digits;
        }
    };
    try expectResult(void, .{ .value = {} }, Scope.digits(allocator, "0"));
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
