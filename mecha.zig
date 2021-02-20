const std = @import("std");

const debug = std.debug;
const fmt = std.fmt;
const math = std.math;
const mem = std.mem;
const unicode = std.unicode;
const testing = std.testing;

pub const ascii = @import("src/ascii.zig");
pub const utf8 = @import("src/utf8.zig");

/// All the ways in which a parser can fail.
/// ParserFailed corresponds to the string not matching the expected form and is
/// the only one `mecha` intrinsically deals with.
pub const Error = error{ ParserFailed, OtherError } || mem.Allocator.Error;

/// The result of a successful parse
pub fn Result(comptime T: type) type {
    return struct {
        const Value = T;

        value: T,
        rest: []const u8,

        pub fn init(v: T, _rest: []const u8) @This() {
            return .{ .value = v, .rest = _rest };
        }
    };
}

/// The type of all parser that can work with `mecha`
pub fn Parser(comptime T: type) type {
    return fn (*mem.Allocator, []const u8) Error!Result(T);
}

fn typecheckParser(comptime P: type) void {
    switch (@typeInfo(P)) {
        .Fn => |func| {
            const R = func.return_type orelse
                @compileError("expected 'mecha.Parser(T)', found '" ++ @typeName(P) ++ "'");
            const T = switch (@typeInfo(R)) {
                .ErrorUnion => |e| e.payload.Value,
                else => @compileError("expected 'mecha.Parser(T)', found '" ++ @typeName(P) ++ "'"),
            };
            if (P != Parser(T))
                @compileError("expected 'mecha.Parser(" ++ @typeName(T) ++ ")', found '" ++ @typeName(P) ++ "'");
        },
        else => @compileError("expected 'mecha.Parser(T)', found '" ++ @typeName(P) ++ "'"),
    }
}

fn ReturnType(comptime P: type) type {
    return @typeInfo(P).Fn.return_type.?;
}

/// The reverse of `Parser`. Give it a `Parser` type
/// and this function will give you `T`.
pub fn ParserResult(comptime P: type) type {
    typecheckParser(P);
    return @typeInfo(ReturnType(P)).ErrorUnion.payload.Value;
}

/// A parser that only succeeds on the end of the string.
pub fn eos(_: *mem.Allocator, str: []const u8) Error!Result(void) {
    if (str.len != 0)
        return error.ParserFailed;
    return Result(void).init({}, str);
}

test "eos" {
    var allocator = &failingAllocator();
    expectResult(void, .{ .value = {}, .rest = "" }, eos(allocator, ""));
    expectResult(void, error.ParserFailed, eos(allocator, "a"));
}

/// A parser that always succeeds with the result being the
/// entire string. The same as the '.*$' regex.
pub fn rest(_: *mem.Allocator, str: []const u8) Error!Result([]const u8) {
    return Result([]const u8).init(str, str[str.len..]);
}

test "rest" {
    var allocator = &failingAllocator();
    expectResult([]const u8, .{ .value = "", .rest = "" }, rest(allocator, ""));
    expectResult([]const u8, .{ .value = "a", .rest = "" }, rest(allocator, "a"));
}

/// Construct a parser that succeeds if the string passed in starts
/// with `str`.
pub fn string(comptime str: []const u8) Parser(void) {
    return struct {
        const Res = Result(void);
        fn func(_: *mem.Allocator, s: []const u8) Error!Res {
            if (!mem.startsWith(u8, s, str))
                return error.ParserFailed;
            return Res.init({}, s[str.len..]);
        }
    }.func;
}

test "string" {
    var allocator = &failingAllocator();
    expectResult(void, .{ .value = {}, .rest = "" }, string("aa")(allocator, "aa"));
    expectResult(void, .{ .value = {}, .rest = "a" }, string("aa")(allocator, "aaa"));
    expectResult(void, error.ParserFailed, string("aa")(allocator, "ba"));
    expectResult(void, error.ParserFailed, string("aa")(allocator, ""));
}

/// Construct a parser that repeatedly uses `parser` until `n` iterations is reached.
/// The parser's result will be an array of the results from the repeated parser.
pub fn manyN(
    comptime n: usize,
    comptime parser: anytype,
) Parser([n]ParserResult(@TypeOf(parser))) {
    return struct {
        const Array = [n]ParserResult(@TypeOf(parser));
        const Res = Result(Array);
        fn func(allocator: *mem.Allocator, str: []const u8) Error!Res {
            var rem = str;
            var res: Array = undefined;
            for (res) |*value| {
                const r = try parser(allocator, rem);
                rem = r.rest;
                value.* = r.value;
            }

            return Res.init(res, rem);
        }
    }.func;
}

/// Construct a parser that repeatedly uses `parser` until it fails
/// or `m` iterations is reached. The parser constructed will only
/// succeed if `parser` succeeded at least `n` times. The parser's
/// result will be a string containing everything parsed.
pub fn manyRange(
    comptime n: usize,
    comptime m: usize,
    comptime parser: anytype,
) Parser([]const u8) {
    typecheckParser(@TypeOf(parser));
    return struct {
        const Res = Result([]const u8);
        fn func(allocator: *mem.Allocator, str: []const u8) Error!Res {
            const first_n = try manyN(n, parser)(allocator, str);
            var rem = first_n.rest;

            var i: usize = n;
            while (i < m) : (i += 1) {
                const r = parser(allocator, rem) catch |e| {
                    switch (e) {
                        error.ParserFailed => break,
                        else => return e,
                    }
                };
                rem = r.rest;
            }
            return Res.init(str[0 .. str.len - rem.len], rem);
        }
    }.func;
}

/// Construct a parser that repeatedly uses `parser` until it fails.
/// The parser's result will be a string containing everything parsed.
pub fn many(comptime parser: anytype) Parser([]const u8) {
    return manyRange(0, math.maxInt(usize), parser);
}

test "many" {
    var allocator = &failingAllocator();
    const parser1 = comptime many(string("ab"));
    expectResult([]const u8, .{ .value = "", .rest = "" }, parser1(allocator, ""));
    expectResult([]const u8, .{ .value = "", .rest = "a" }, parser1(allocator, "a"));
    expectResult([]const u8, .{ .value = "ab", .rest = "" }, parser1(allocator, "ab"));
    expectResult([]const u8, .{ .value = "ab", .rest = "a" }, parser1(allocator, "aba"));
    expectResult([]const u8, .{ .value = "abab", .rest = "" }, parser1(allocator, "abab"));
    expectResult([]const u8, .{ .value = "abab", .rest = "a" }, parser1(allocator, "ababa"));
    expectResult([]const u8, .{ .value = "ababab", .rest = "" }, parser1(allocator, "ababab"));

    const parser2 = comptime manyRange(1, 2, string("ab"));
    expectResult([]const u8, error.ParserFailed, parser2(allocator, ""));
    expectResult([]const u8, error.ParserFailed, parser2(allocator, "a"));
    expectResult([]const u8, .{ .value = "ab", .rest = "" }, parser2(allocator, "ab"));
    expectResult([]const u8, .{ .value = "ab", .rest = "a" }, parser2(allocator, "aba"));
    expectResult([]const u8, .{ .value = "abab", .rest = "" }, parser2(allocator, "abab"));
    expectResult([]const u8, .{ .value = "abab", .rest = "a" }, parser2(allocator, "ababa"));
    expectResult([]const u8, .{ .value = "abab", .rest = "ab" }, parser2(allocator, "ababab"));

    const parser3 = comptime many(utf8.char(0x100));
    expectResult([]const u8, .{ .value = "ĀĀĀ", .rest = "āāā" }, parser3(allocator, "ĀĀĀāāā"));

    const parser4 = comptime manyN(3, ascii.range('a', 'b'));
    expectResult([3]u8, .{ .value = "aba".*, .rest = "bab" }, parser4(allocator, "ababab"));
}

/// Construct a parser that will call `parser` on the string
/// but never fails to parse. The parser's result will be the
/// result of `parser` on success and `null` on failure.
pub fn opt(comptime parser: anytype) Parser(?ParserResult(@TypeOf(parser))) {
    return struct {
        const Res = Result(?ParserResult(@TypeOf(parser)));
        fn func(allocator: *mem.Allocator, str: []const u8) Error!Res {
            const r = parser(allocator, str) catch |e| {
                switch (e) {
                    error.ParserFailed => return Res.init(null, str),
                    else => return e,
                }
            };
            return Res.init(r.value, r.rest);
        }
    }.func;
}

test "opt" {
    var allocator = &failingAllocator();
    const parser1 = comptime opt(ascii.range('a', 'z'));
    expectResult(?u8, .{ .value = 'a', .rest = "" }, parser1(allocator, "a"));
    expectResult(?u8, .{ .value = 'a', .rest = "a" }, parser1(allocator, "aa"));
    expectResult(?u8, .{ .value = null, .rest = "1" }, parser1(allocator, "1"));
}

fn ParsersTypes(comptime parsers: anytype) []const type {
    var types: []const type = &[_]type{};
    for (parsers) |parser| {
        const T = ParserResult(@TypeOf(parser));
        if (T != void)
            types = types ++ [_]type{T};
    }
    return types;
}

fn Combine(comptime parsers: anytype) type {
    const types = ParsersTypes(parsers);
    if (types.len == 0)
        return void;
    if (types.len == 1)
        return types[0];
    return Tuple(types.len, types[0..types.len].*);
}

/// HACK: Zig cannot cache functions that takes pointers (slices)
///       so we have to passed the types as an array by value.
fn Tuple(comptime n: usize, comptime types: [n]type) type {
    return std.meta.Tuple(&types);
}

/// Takes a tuple of `Parser(any)` and constructs a parser that
/// only succeeds if all parsers succeed to parse. The parsers
/// will be called in order and parser `N` will use the `rest`
/// from parser `N-1`. The parsers result will be a `Tuple` of
/// all parser not of type `Parser(void)`. If only one parser
/// is not of type `Parser(void)` then this parsers result is
/// returned instead of a tuple.
pub fn combine(comptime parsers: anytype) Parser(Combine(parsers)) {
    return struct {
        const types = ParsersTypes(parsers);
        const Res = Result(Combine(parsers));
        fn func(allocator: *mem.Allocator, str: []const u8) Error!Res {
            var res: Res = undefined;
            res.rest = str;

            comptime var i = 0;
            comptime var j = 0;
            inline while (i < parsers.len) : (i += 1) {
                const r = try parsers[i](allocator, res.rest);
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
    var allocator = &failingAllocator();
    const parser1 = comptime combine(.{ opt(ascii.range('a', 'b')), opt(ascii.range('d', 'e')) });
    const Res = ParserResult(@TypeOf(parser1));
    expectResult(Res, .{ .value = .{ .@"0" = 'a', .@"1" = 'd' }, .rest = "" }, parser1(allocator, "ad"));
    expectResult(Res, .{ .value = .{ .@"0" = 'a', .@"1" = null }, .rest = "a" }, parser1(allocator, "aa"));
    expectResult(Res, .{ .value = .{ .@"0" = null, .@"1" = 'd' }, .rest = "a" }, parser1(allocator, "da"));
    expectResult(Res, .{ .value = .{ .@"0" = null, .@"1" = null }, .rest = "qa" }, parser1(allocator, "qa"));

    const parser2 = comptime combine(.{ opt(ascii.range('a', 'b')), ascii.char('d') });
    expectResult(?u8, .{ .value = 'a', .rest = "" }, parser2(allocator, "ad"));
    expectResult(?u8, .{ .value = 'a', .rest = "a" }, parser2(allocator, "ada"));
    expectResult(?u8, .{ .value = null, .rest = "a" }, parser2(allocator, "da"));
    expectResult(?u8, error.ParserFailed, parser2(allocator, "qa"));
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
        fn func(allocator: *mem.Allocator, str: []const u8) Error!Result(ParserResult(@TypeOf(parsers[0]))) {
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
    var allocator = &failingAllocator();
    const parser1 = comptime oneOf(.{ ascii.range('a', 'b'), ascii.range('d', 'e') });
    expectResult(u8, .{ .value = 'a', .rest = "" }, parser1(allocator, "a"));
    expectResult(u8, .{ .value = 'b', .rest = "" }, parser1(allocator, "b"));
    expectResult(u8, .{ .value = 'd', .rest = "" }, parser1(allocator, "d"));
    expectResult(u8, .{ .value = 'e', .rest = "" }, parser1(allocator, "e"));
    expectResult(u8, .{ .value = 'a', .rest = "a" }, parser1(allocator, "aa"));
    expectResult(u8, .{ .value = 'b', .rest = "a" }, parser1(allocator, "ba"));
    expectResult(u8, .{ .value = 'd', .rest = "a" }, parser1(allocator, "da"));
    expectResult(u8, .{ .value = 'e', .rest = "a" }, parser1(allocator, "ea"));
    expectResult(u8, error.ParserFailed, parser1(allocator, "q"));
}

/// Takes any parser (preferable not of type `Parser([]const u8)`)
/// and converts it to a parser where the result is a string that
/// contains all characters parsed by `parser`.
pub fn asStr(comptime parser: anytype) Parser([]const u8) {
    typecheckParser(@TypeOf(parser));
    return struct {
        const Res = Result([]const u8);
        fn func(allocator: *mem.Allocator, str: []const u8) Error!Res {
            const r = try parser(allocator, str);
            return Res.init(str[0 .. str.len - r.rest.len], r.rest);
        }
    }.func;
}

test "asStr" {
    var allocator = &failingAllocator();
    const parser1 = comptime asStr(ascii.char('a'));
    expectResult([]const u8, .{ .value = "a", .rest = "" }, parser1(allocator, "a"));
    expectResult([]const u8, .{ .value = "a", .rest = "a" }, parser1(allocator, "aa"));
    expectResult([]const u8, error.ParserFailed, parser1(allocator, "ba"));

    const parser2 = comptime asStr(combine(.{ opt(ascii.range('a', 'b')), opt(ascii.range('d', 'e')) }));
    expectResult([]const u8, .{ .value = "ad", .rest = "" }, parser2(allocator, "ad"));
    expectResult([]const u8, .{ .value = "a", .rest = "a" }, parser2(allocator, "aa"));
    expectResult([]const u8, .{ .value = "d", .rest = "a" }, parser2(allocator, "da"));
    expectResult([]const u8, .{ .value = "", .rest = "qa" }, parser2(allocator, "qa"));
}

/// Constructs a parser that has its result converted with the
/// `conv` function. The ´conv` functions signature is
/// `fn (ParserResult(parser)) ?T`. The parser constructed will
/// fail if `conv` fails.
pub fn convert(
    comptime T: type,
    comptime conv: anytype,
    comptime parser: anytype,
) Parser(T) {
    return struct {
        const Res = Result(T);
        fn func(allocator: *mem.Allocator, str: []const u8) Error!Res {
            const r = try parser(allocator, str);
            const v = conv(r.value) orelse return error.ParserFailed;
            return Res.init(v, r.rest);
        }
    }.func;
}

/// Constructs a convert function for `convert` that takes a
/// string and parses it to an int of type `Int`.
pub fn toInt(comptime Int: type, comptime base: u8) fn ([]const u8) ?Int {
    return struct {
        fn func(str: []const u8) ?Int {
            return fmt.parseInt(Int, str, base) catch return null;
        }
    }.func;
}

/// Constructs a convert function for `convert` that takes a
/// string and parses it to a float of type `Float`.
pub fn toFloat(comptime Float: type) fn ([]const u8) ?Float {
    return struct {
        fn func(str: []const u8) ?Float {
            return fmt.parseFloat(Float, str) catch return null;
        }
    }.func;
}

/// A convert function for `convert` that takes a string and
/// returns the first codepoint.
pub fn toChar(str: []const u8) ?u21 {
    if (str.len > 1) {
        const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch return null;
        if (cp_len > str.len)
            return null;
        return unicode.utf8Decode(str[0..cp_len]) catch null;
    }
    return @as(u21, str[0]);
}

/// Constructs a convert function for `convert` that takes a
/// string and converts it to an `Enum` with `std.meta.stringToEnum`.
pub fn toEnum(comptime Enum: type) fn ([]const u8) ?Enum {
    return struct {
        fn func(str: []const u8) ?Enum {
            return std.meta.stringToEnum(Enum, str);
        }
    }.func;
}

/// A convert function for `convert` that takes a string
/// and returns `true` if it is `"true"` and `false` if it
/// is `"false"`.
pub fn toBool(str: []const u8) ?bool {
    const r = toEnum(enum { @"false", @"true" })(str) orelse return null;
    return r == .@"true";
}

test "convert" {
    var allocator = &failingAllocator();
    const parser1 = comptime convert(u8, toInt(u8, 10), asStr(string("123")));
    expectResult(u8, .{ .value = 123, .rest = "" }, parser1(allocator, "123"));
    expectResult(u8, .{ .value = 123, .rest = "a" }, parser1(allocator, "123a"));
    expectResult(u8, error.ParserFailed, parser1(allocator, "12"));

    const parser2 = comptime convert(u21, toChar, asStr(string("a")));
    expectResult(u21, .{ .value = 'a', .rest = "" }, parser2(allocator, "a"));
    expectResult(u21, .{ .value = 'a', .rest = "a" }, parser2(allocator, "aa"));
    expectResult(u21, error.ParserFailed, parser2(allocator, "b"));

    const parser3 = comptime convert(bool, toBool, rest);
    expectResult(bool, .{ .value = true, .rest = "" }, parser3(allocator, "true"));
    expectResult(bool, .{ .value = false, .rest = "" }, parser3(allocator, "false"));
    expectResult(bool, error.ParserFailed, parser3(allocator, "b"));

    const parser4 = comptime convert(f32, toFloat(f32), asStr(string("1.23")));
    expectResult(f32, .{ .value = 1.23, .rest = "" }, parser4(allocator, "1.23"));
    expectResult(f32, .{ .value = 1.23, .rest = "a" }, parser4(allocator, "1.23a"));
    expectResult(f32, error.ParserFailed, parser4(allocator, "1.2"));

    const E = packed enum(u8) { a, b, _ };
    const parser5 = comptime convert(E, toEnum(E), rest);
    expectResult(E, .{ .value = E.a, .rest = "" }, parser5(allocator, "a"));
    expectResult(E, .{ .value = E.b, .rest = "" }, parser5(allocator, "b"));
    expectResult(E, error.ParserFailed, parser5(allocator, "2"));

    const parser6 = comptime convert(u21, toChar, asStr(string("Āā")));
    expectResult(u21, .{ .value = 0x100, .rest = "" }, parser6(allocator, "Āā"));
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
    typecheckParser(@TypeOf(parser));
    return struct {
        const Res = Result(T);
        fn func(allocator: *mem.Allocator, str: []const u8) Error!Res {
            const r = try parser(allocator, str);
            return Res.init(conv(r.value), r.rest);
        }
    }.func;
}

fn ToStructResult(comptime T: type) type {
    return @TypeOf(struct {
        fn func(tuple: anytype) T {
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
    var allocator = &failingAllocator();
    const Point = struct {
        x: usize,
        y: usize,
    };
    const parser1 = comptime map(Point, toStruct(Point), combine(.{ int(usize, 10), ascii.char(' '), int(usize, 10) }));
    expectResult(Point, .{ .value = .{ .x = 10, .y = 10 }, .rest = "" }, parser1(allocator, "10 10"));
    expectResult(Point, .{ .value = .{ .x = 20, .y = 20 }, .rest = "aa" }, parser1(allocator, "20 20aa"));
    expectResult(Point, error.ParserFailed, parser1(allocator, "12"));

    const parser2 = comptime map(Point, toStruct(Point), manyN(2, combine(.{ int(usize, 10), ascii.char(' ') })));
    expectResult(Point, .{ .value = .{ .x = 10, .y = 10 }, .rest = "" }, parser2(allocator, "10 10 "));
    expectResult(Point, .{ .value = .{ .x = 20, .y = 20 }, .rest = "aa" }, parser2(allocator, "20 20 aa"));
    expectResult(Point, error.ParserFailed, parser2(allocator, "12"));
}

/// Constructs a parser that discards the result returned from the parser
/// it wraps.
pub fn discard(comptime parser: anytype) Parser(void) {
    return convert(void, struct {
        fn d(_: anytype) ?void {}
    }.d, parser);
}

test "discard" {
    var allocator = &failingAllocator();
    const parser = comptime discard(many(ascii.char(' ')));
    expectResult(void, .{ .value = {}, .rest = "abc" }, parser(allocator, "abc"));
    expectResult(void, .{ .value = {}, .rest = "abc" }, parser(allocator, " abc"));
    expectResult(void, .{ .value = {}, .rest = "abc" }, parser(allocator, "  abc"));
}

/// Construct a parser that succeeds if it parser an integer of
/// `base`. The result of this parser will be the string containing
/// the match.
pub fn intToken(comptime base: u8) Parser([]const u8) {
    return comptime asStr(combine(.{
        opt(ascii.char('-')),
        manyRange(1, math.maxInt(usize), ascii.digit(base)),
    }));
}

/// Same as `intToken` but also converts the parsed string
/// to an integer.
pub fn int(comptime Int: type, comptime base: u8) Parser(Int) {
    return comptime convert(Int, toInt(Int, base), intToken(base));
}

test "int" {
    var allocator = &failingAllocator();
    const parser1 = int(u8, 10);
    expectResult(u8, .{ .value = 0, .rest = "" }, parser1(allocator, "0"));
    expectResult(u8, .{ .value = 1, .rest = "" }, parser1(allocator, "1"));
    expectResult(u8, .{ .value = 1, .rest = "a" }, parser1(allocator, "1a"));
    expectResult(u8, .{ .value = 255, .rest = "" }, parser1(allocator, "255"));
    expectResult(u8, error.ParserFailed, parser1(allocator, "256"));

    const parser2 = int(u8, 16);
    expectResult(u8, .{ .value = 0x00, .rest = "" }, parser2(allocator, "0"));
    expectResult(u8, .{ .value = 0x01, .rest = "" }, parser2(allocator, "1"));
    expectResult(u8, .{ .value = 0x1a, .rest = "" }, parser2(allocator, "1a"));
    expectResult(u8, .{ .value = 0x01, .rest = "g" }, parser2(allocator, "1g"));
    expectResult(u8, .{ .value = 0xff, .rest = "" }, parser2(allocator, "ff"));
    expectResult(u8, .{ .value = 0xff, .rest = "" }, parser2(allocator, "FF"));
    expectResult(u8, error.ParserFailed, parser2(allocator, "100"));
}

/// Creates a parser that calls a function to obtain its underlying parser.
/// This function introduces the indirection required for recursive grammars.
/// ```
/// const digit_10 = discard(digit(10));
/// const digits = oneOf(.{ combine(.{ digit_10, ref(digits_ref) }), digit_10 });
/// fn digits_ref() Parser(void) {
///     return digits;
/// };
/// ```
pub fn ref(comptime func: anytype) Parser(ParserResult(ReturnType(@TypeOf(func)))) {
    return struct {
        const P = ReturnType(@TypeOf(func));
        const T = ParserResult(P);
        fn res(allocator: *mem.Allocator, str: []const u8) Error!Result(T) {
            return func()(allocator, str);
        }
    }.res;
}

test "ref" {
    const allocator = &failingAllocator();
    const Scope = struct {
        const digit = discard(ascii.digit(10));
        const digits = oneOf(.{ combine(.{ digit, ref(digits_ref) }), digit });
        fn digits_ref() Parser(void) {
            return digits;
        }
    };
    expectResult(void, .{ .value = {}, .rest = "" }, Scope.digits(allocator, "0"));
}

pub fn expectResult(
    comptime T: type,
    m_expect: Error!Result(T),
    m_actual: Error!Result(T),
) void {
    const expect = m_expect catch |err| {
        testing.expectError(err, m_actual);
        return;
    };

    const actual = m_actual catch |err| std.debug.panic("expected {}, found {} ", .{ expect.value, err });

    testing.expectEqualStrings(expect.rest, actual.rest);
    switch (T) {
        []const u8 => testing.expectEqualStrings(expect.value, actual.value),
        else => testing.expectEqual(expect.value, actual.value),
    }
}

fn failingAllocator() mem.Allocator {
    return testing.FailingAllocator.init(testing.allocator, 0).allocator;
}
