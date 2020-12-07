const std = @import("std");

const debug = std.debug;
const fmt = std.fmt;
const math = std.math;
const mem = std.mem;
const unicode = std.unicode;
const testing = std.testing;

/// The result of a successful parse
pub fn Result(comptime T: type) type {
    return struct {
        const Value = T;

        value: T,
        rest: []const u8,

        pub fn init(v: T, rest: []const u8) @This() {
            return .{ .value = v, .rest = rest };
        }
    };
}

/// The type of all parser that can work with `mecha`
pub fn Parser(comptime T: type) type {
    return fn ([]const u8) ?Result(T);
}

fn ReturnType(comptime P: type) type {
    return @typeInfo(P).Fn.return_type.?;
}

/// The reverse of `Parser`. Give it a `Parser` type
/// and this function will give you `T`.
pub fn ParserResult(comptime P: type) type {
    return @typeInfo(ReturnType(P)).Optional.child.Value;
}

/// A parser that only succeeds on the end of the string.
pub fn eos(str: []const u8) ?Result(void) {
    if (str.len != 0)
        return null;
    return Result(void).init({}, str);
}

test "eos" {
    expectResult(void, .{ .value = {}, .rest = "" }, eos(""));
    expectResult(void, null, eos("a"));
}

/// A parser that always succeeds with the result being the
/// entire string. The same as the '.*$' regex.
pub fn any(str: []const u8) ?Result([]const u8) {
    return Result([]const u8).init(str, str[str.len..]);
}

test "any" {
    expectResult([]const u8, .{ .value = "", .rest = "" }, any(""));
    expectResult([]const u8, .{ .value = "a", .rest = "" }, any("a"));
}

/// Constructs a parser that only succeeds if the string starts with `c`.
pub fn char(comptime c: u21) Parser(void) {
    comptime {
        var array: [4]u8 = undefined;
        const len = unicode.utf8Encode(c, array[0..]) catch unreachable;
        return string(array[0..len]);
    }
}

test "char" {
    expectResult(void, .{ .value = {}, .rest = "" }, char('a')("a"));
    expectResult(void, .{ .value = {}, .rest = "a" }, char('a')("aa"));
    expectResult(void, null, char('a')("ba"));
    expectResult(void, null, char('a')(""));
    expectResult(void, .{ .value = {}, .rest = "ā" }, char(0x100)("Āā"));
    expectResult(void, null, char(0x100)(""));
    expectResult(void, null, char(0x100)("\xc0"));
}

/// Constructs a parser that only succeeds if the string starts with
/// a codepoint that is in between `start` and `end` inclusively.
/// The parsers result will be the codepoint parsed.
pub fn range(comptime start: u21, comptime end: u21) Parser(u21) {
    return struct {
        const Res = Result(u21);
        fn func(str: []const u8) ?Res {
            if (str.len == 0)
                return null;

            if (end <= math.maxInt(u7)) {
                switch (str[0]) {
                    start...end => return Res.init(str[0], str[1..]),
                    else => return null,
                }
            } else {
                const cp_len = unicode.utf8ByteSequenceLength(str[0]) catch return null;
                if (cp_len > str.len)
                    return null;

                const cp = unicode.utf8Decode(str[0..cp_len]) catch return null;
                switch (cp) {
                    start...end => return Res.init(cp, str[cp_len..]),
                    else => return null,
                }
            }
        }
    }.func;
}

test "range" {
    expectResult(u21, .{ .value = 'a', .rest = "" }, range('a', 'z')("a"));
    expectResult(u21, .{ .value = 'c', .rest = "" }, range('a', 'z')("c"));
    expectResult(u21, .{ .value = 'z', .rest = "" }, range('a', 'z')("z"));
    expectResult(u21, .{ .value = 'a', .rest = "a" }, range('a', 'z')("aa"));
    expectResult(u21, .{ .value = 'c', .rest = "a" }, range('a', 'z')("ca"));
    expectResult(u21, .{ .value = 'z', .rest = "a" }, range('a', 'z')("za"));
    expectResult(u21, null, range('a', 'z')("1"));
    expectResult(u21, null, range('a', 'z')(""));
    expectResult(u21, .{ .value = 0x100, .rest = "ā" }, range(0x100, 0x100)("Āā"));
    expectResult(u21, null, range(0x100, 0x100)("aa"));
    expectResult(u21, null, range(0x100, 0x100)("\xc0"));
}

/// A parser that succeeds if the string starts with an alphabetic
/// character. The parsers result will be the character parsed.
pub const alpha = oneOf(.{ range('a', 'z'), range('A', 'Z') });

test "alpha" {
    var i: u16 = 0;
    while (i <= 255) : (i += 1) {
        const c = @intCast(u8, i);
        switch (c) {
            'a'...'z',
            'A'...'Z',
            => expectResult(u21, .{ .value = c, .rest = "" }, alpha(&[_]u8{c})),
            else => expectResult(u21, null, alpha(&[_]u8{c})),
        }
    }
}

/// Construct a parser that succeeds if the string starts with a
/// character that is a digit in `base`. The parsers result will be
/// the character parsed.
pub fn digit(comptime base: u8) Parser(u21) {
    debug.assert(base != 0);
    if (base <= 10)
        return range('0', '0' + (base - 1));
    return comptime oneOf(.{
        range('0', '9'),
        range('a', 'a' + (base - 11)),
        range('A', 'A' + (base - 11)),
    });
}

test "alpha" {
    var i: u16 = 0;
    i = 0;
    while (i <= 255) : (i += 1) {
        const c = @intCast(u8, i);
        switch (c) {
            '0'...'1' => expectResult(u21, .{ .value = c, .rest = "" }, digit(2)(&[_]u8{c})),
            else => expectResult(u21, null, digit(2)(&[_]u8{c})),
        }
    }

    i = 0;
    while (i <= 255) : (i += 1) {
        const c = @intCast(u8, i);
        switch (c) {
            '0'...'9' => expectResult(u21, .{ .value = c, .rest = "" }, digit(10)(&[_]u8{c})),
            else => expectResult(u21, null, digit(10)(&[_]u8{c})),
        }
    }
    i = 0;
    while (i <= 255) : (i += 1) {
        const c = @intCast(u8, i);
        switch (c) {
            '0'...'9',
            'a'...'f',
            'A'...'F',
            => expectResult(u21, .{ .value = c, .rest = "" }, digit(16)(&[_]u8{c})),
            else => expectResult(u21, null, digit(16)(&[_]u8{c})),
        }
    }
}

/// Construct a parser that succeeds if the string passed in starts
/// with `str`.
pub fn string(comptime str: []const u8) Parser(void) {
    return struct {
        const Res = Result(void);
        fn func(s: []const u8) ?Res {
            if (!mem.startsWith(u8, s, str))
                return null;
            return Res.init({}, s[str.len..]);
        }
    }.func;
}

test "string" {
    expectResult(void, .{ .value = {}, .rest = "" }, string("aa")("aa"));
    expectResult(void, .{ .value = {}, .rest = "a" }, string("aa")("aaa"));
    expectResult(void, null, string("aa")("ba"));
    expectResult(void, null, string("aa")(""));
}

/// Construct a parser that repeatedly uses `parser` until `n` iterations is reached.
/// The parsers result will be an array of the results from the repeated parser.
pub fn manyN(
    comptime n: usize,
    comptime parser: anytype,
) Parser([n]ParserResult(@TypeOf(parser))) {
    return struct {
        const Array = [n]ParserResult(@TypeOf(parser));
        const Res = Result(Array);
        fn func(str: []const u8) ?Res {
            var rem = str;
            var res: Array = undefined;
            for (res) |*value| {
                const r = parser(rem) orelse return null;
                rem = r.rest;
                value.* = r.value;
            }

            return Res.init(res, rem);
        }
    }.func;
}

/// Construct a parser that repeatedly uses `parser` until it fails
/// or `m` iterations is reached. The parser constructed will only
/// succeed if `parser` succeeded at least `n` times. The parsers
/// result will be a string containing everything parsed.
pub fn manyRange(
    comptime n: usize,
    comptime m: usize,
    comptime parser: anytype,
) Parser([]const u8) {
    return struct {
        const Res = Result([]const u8);
        fn func(str: []const u8) ?Res {
            const first_n = manyN(n, parser)(str) orelse return null;
            var rem = first_n.rest;

            var i: usize = n;
            while (i < m) : (i += 1) {
                const r = parser(rem) orelse break;
                rem = r.rest;
            }
            return Res.init(str[0 .. str.len - rem.len], rem);
        }
    }.func;
}

/// Construct a parser that repeatedly uses `parser` until it fails.
/// The parsers result will be a string containing everything parsed.
pub fn many(comptime parser: anytype) Parser([]const u8) {
    return manyRange(0, math.maxInt(usize), parser);
}

test "many" {
    const parser1 = comptime many(string("ab"));
    expectResult([]const u8, .{ .value = "", .rest = "" }, parser1(""));
    expectResult([]const u8, .{ .value = "", .rest = "a" }, parser1("a"));
    expectResult([]const u8, .{ .value = "ab", .rest = "" }, parser1("ab"));
    expectResult([]const u8, .{ .value = "ab", .rest = "a" }, parser1("aba"));
    expectResult([]const u8, .{ .value = "abab", .rest = "" }, parser1("abab"));
    expectResult([]const u8, .{ .value = "abab", .rest = "a" }, parser1("ababa"));
    expectResult([]const u8, .{ .value = "ababab", .rest = "" }, parser1("ababab"));

    const parser2 = comptime manyRange(1, 2, string("ab"));
    expectResult([]const u8, null, parser2(""));
    expectResult([]const u8, null, parser2("a"));
    expectResult([]const u8, .{ .value = "ab", .rest = "" }, parser2("ab"));
    expectResult([]const u8, .{ .value = "ab", .rest = "a" }, parser2("aba"));
    expectResult([]const u8, .{ .value = "abab", .rest = "" }, parser2("abab"));
    expectResult([]const u8, .{ .value = "abab", .rest = "a" }, parser2("ababa"));
    expectResult([]const u8, .{ .value = "abab", .rest = "ab" }, parser2("ababab"));

    const parser3 = comptime many(char(0x100));
    expectResult([]const u8, .{ .value = "ĀĀĀ", .rest = "āāā" }, parser3("ĀĀĀāāā"));

    const parser4 = comptime manyN(3, range('a', 'b'));
    expectResult([3]u21, .{ .value = [_]u21{ 'a', 'b', 'a' }, .rest = "bab" }, parser4("ababab"));
}

/// Construct a parser that will call `parser` on the string
/// but never fails to parser. The parsers result will be the
/// result of `parser` on success and `null` on failure.
pub fn opt(comptime parser: anytype) Parser(?ParserResult(@TypeOf(parser))) {
    return struct {
        const Res = Result(?ParserResult(@TypeOf(parser)));
        fn func(str: []const u8) ?Res {
            if (parser(str)) |r|
                return Res.init(r.value, r.rest);
            return Res.init(null, str);
        }
    }.func;
}

test "opt" {
    const parser1 = comptime opt(range('a', 'z'));
    expectResult(?u21, .{ .value = 'a', .rest = "" }, parser1("a"));
    expectResult(?u21, .{ .value = 'a', .rest = "a" }, parser1("aa"));
    expectResult(?u21, .{ .value = null, .rest = "1" }, parser1("1"));
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
        fn func(str: []const u8) ?Res {
            var res: Res = undefined;
            res.rest = str;

            comptime var i = 0;
            comptime var j = 0;
            inline while (i < parsers.len) : (i += 1) {
                const r = parsers[i](res.rest) orelse return null;
                res.rest = r.rest;

                if (@TypeOf(r.value) != void) {
                    if (types.len == 1) {
                        res.value = r.value;
                    } else {
                        res.value[j] = r.value;
                        j += 1;
                    }
                }
            }
            return res;
        }
    }.func;
}

test "combine" {
    const parser1 = comptime combine(.{ opt(range('a', 'b')), opt(range('d', 'e')) });
    const Res = ParserResult(@TypeOf(parser1));
    expectResult(Res, .{ .value = .{ .@"0" = 'a', .@"1" = 'd' }, .rest = "" }, parser1("ad"));
    expectResult(Res, .{ .value = .{ .@"0" = 'a', .@"1" = null }, .rest = "a" }, parser1("aa"));
    expectResult(Res, .{ .value = .{ .@"0" = null, .@"1" = 'd' }, .rest = "a" }, parser1("da"));
    expectResult(Res, .{ .value = .{ .@"0" = null, .@"1" = null }, .rest = "qa" }, parser1("qa"));

    const parser2 = comptime combine(.{ opt(range('a', 'b')), char('d') });
    expectResult(?u21, .{ .value = 'a', .rest = "" }, parser2("ad"));
    expectResult(?u21, .{ .value = 'a', .rest = "a" }, parser2("ada"));
    expectResult(?u21, .{ .value = null, .rest = "a" }, parser2("da"));
    expectResult(?u21, null, parser2("qa"));
}

/// Takes a tuple of `Parser(T)` and constructs a parser that
/// only succeeds if one of the parsers succeed to parse. The
/// parsers will be called in order all with `str` as input.
/// The parser will return with the result of the first parser
/// that succeeded. The parsers result will be `Result(T)`
pub fn oneOf(comptime parsers: anytype) Parser(ParserResult(@TypeOf(parsers[0]))) {
    return struct {
        fn func(str: []const u8) ?Result(ParserResult(@TypeOf(parsers[0]))) {
            inline for (parsers) |p| {
                if (p(str)) |res|
                    return res;
            }
            return null;
        }
    }.func;
}

test "oneOf" {
    const parser1 = comptime oneOf(.{ range('a', 'b'), range('d', 'e') });
    expectResult(u21, .{ .value = 'a', .rest = "" }, parser1("a"));
    expectResult(u21, .{ .value = 'b', .rest = "" }, parser1("b"));
    expectResult(u21, .{ .value = 'd', .rest = "" }, parser1("d"));
    expectResult(u21, .{ .value = 'e', .rest = "" }, parser1("e"));
    expectResult(u21, .{ .value = 'a', .rest = "a" }, parser1("aa"));
    expectResult(u21, .{ .value = 'b', .rest = "a" }, parser1("ba"));
    expectResult(u21, .{ .value = 'd', .rest = "a" }, parser1("da"));
    expectResult(u21, .{ .value = 'e', .rest = "a" }, parser1("ea"));
    expectResult(u21, null, parser1("q"));
}

/// Takes any parser (preferable not of type `Parser([]const u8)`)
/// and converts it to a parser where the result is a string that
/// contains all characters parsed by `parser`.
pub fn asStr(comptime parser: anytype) Parser([]const u8) {
    return struct {
        const Res = Result([]const u8);
        fn func(str: []const u8) ?Res {
            const r = parser(str) orelse return null;
            return Res.init(str[0 .. str.len - r.rest.len], r.rest);
        }
    }.func;
}

test "asStr" {
    const parser1 = comptime asStr(char('a'));
    expectResult([]const u8, .{ .value = "a", .rest = "" }, parser1("a"));
    expectResult([]const u8, .{ .value = "a", .rest = "a" }, parser1("aa"));
    expectResult([]const u8, null, parser1("ba"));

    const parser2 = comptime asStr(combine(.{ opt(range('a', 'b')), opt(range('d', 'e')) }));
    expectResult([]const u8, .{ .value = "ad", .rest = "" }, parser2("ad"));
    expectResult([]const u8, .{ .value = "a", .rest = "a" }, parser2("aa"));
    expectResult([]const u8, .{ .value = "d", .rest = "a" }, parser2("da"));
    expectResult([]const u8, .{ .value = "", .rest = "qa" }, parser2("qa"));
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
        fn func(str: []const u8) ?Res {
            const r = parser(str) orelse return null;
            const v = conv(r.value) orelse return null;
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
    const parser1 = comptime convert(u8, toInt(u8, 10), asStr(string("123")));
    expectResult(u8, .{ .value = 123, .rest = "" }, parser1("123"));
    expectResult(u8, .{ .value = 123, .rest = "a" }, parser1("123a"));
    expectResult(u8, null, parser1("12"));

    const parser2 = comptime convert(u21, toChar, asStr(string("a")));
    expectResult(u21, .{ .value = 'a', .rest = "" }, parser2("a"));
    expectResult(u21, .{ .value = 'a', .rest = "a" }, parser2("aa"));
    expectResult(u21, null, parser2("b"));

    const parser3 = comptime convert(bool, toBool, any);
    expectResult(bool, .{ .value = true, .rest = "" }, parser3("true"));
    expectResult(bool, .{ .value = false, .rest = "" }, parser3("false"));
    expectResult(bool, null, parser3("b"));

    const parser4 = comptime convert(f32, toFloat(f32), asStr(string("1.23")));
    expectResult(f32, .{ .value = 1.23, .rest = "" }, parser4("1.23"));
    expectResult(f32, .{ .value = 1.23, .rest = "a" }, parser4("1.23a"));
    expectResult(f32, null, parser4("1.2"));

    const E = packed enum(u8) { a, b, _ };
    const parser5 = comptime convert(E, toEnum(E), any);
    expectResult(E, .{ .value = E.a, .rest = "" }, parser5("a"));
    expectResult(E, .{ .value = E.b, .rest = "" }, parser5("b"));
    expectResult(E, null, parser5("2"));

    const parser6 = comptime convert(u21, toChar, asStr(string("Āā")));
    expectResult(u21, .{ .value = 0x100, .rest = "" }, parser6("Āā"));
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
    return struct {
        const Res = Result(T);
        fn func(str: []const u8) ?Res {
            const r = parser(str) orelse return null;
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

/// Constructs a convert function for `as` that takes a tuple or an array and
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
                    "same number of fields. Convertion is not possible.");

            var res: T = undefined;
            inline for (struct_fields) |field, i|
                @field(res, field.name) = tuple[i];

            return res;
        }
    }.func;
}

test "map" {
    const Point = struct {
        x: usize,
        y: usize,
    };
    const parser1 = comptime map(Point, toStruct(Point), combine(.{ int(usize, 10), char(' '), int(usize, 10) }));
    expectResult(Point, .{ .value = .{ .x = 10, .y = 10 }, .rest = "" }, parser1("10 10"));
    expectResult(Point, .{ .value = .{ .x = 20, .y = 20 }, .rest = "aa" }, parser1("20 20aa"));
    expectResult(Point, null, parser1("12"));

    const parser2 = comptime map(Point, toStruct(Point), manyN(2, combine(.{ int(usize, 10), char(' ') })));
    expectResult(Point, .{ .value = .{ .x = 10, .y = 10 }, .rest = "" }, parser2("10 10 "));
    expectResult(Point, .{ .value = .{ .x = 20, .y = 20 }, .rest = "aa" }, parser2("20 20 aa"));
    expectResult(Point, null, parser1("12"));
}

/// Constructs a parser that discards the result returned from the parser
/// it warps.
pub fn discard(comptime parser: anytype) Parser(void) {
    return convert(void, struct {
        fn d(_: anytype) ?void {}
    }.d, parser);
}

test "discard" {
    const parser = comptime discard(many(char(' ')));
    expectResult(void, .{ .value = {}, .rest = "abc" }, parser(" abc"));
    expectResult(void, .{ .value = {}, .rest = "abc" }, parser("  abc"));
    expectResult(void, .{ .value = {}, .rest = "abc" }, parser("   abc"));
}

/// Construct a parser that succeeds if it parser an integer of
/// `base`. The result of this parser will be the string containing
/// the match.
pub fn intToken(comptime base: u8, comptime max_digits: usize) Parser([]const u8) {
    return comptime asStr(combine(.{
        opt(char('-')),
        manyRange(1, max_digits, digit(base)),
    }));
}

fn digits(val: anytype, base: u8) usize {
    var res: usize = 0;
    var tmp = val;
    while (tmp != 0) : (tmp /= @intCast(@TypeOf(val), base))
        res += 1;
    return math.max(1, res);
}

test "digits" {
    testing.expectEqual(@as(usize, 1), digits(@as(usize, 0b0), 2));
    testing.expectEqual(@as(usize, 1), digits(@as(usize, 000), 10));
    testing.expectEqual(@as(usize, 1), digits(@as(usize, 0x0), 16));
    testing.expectEqual(@as(usize, 1), digits(@as(usize, 0b1), 2));
    testing.expectEqual(@as(usize, 1), digits(@as(usize, 001), 10));
    testing.expectEqual(@as(usize, 1), digits(@as(usize, 0x1), 16));
    testing.expectEqual(@as(usize, 1), digits(@as(usize, 009), 10));
    testing.expectEqual(@as(usize, 1), digits(@as(usize, 0xF), 16));
    testing.expectEqual(@as(usize, 2), digits(@as(usize, 0b10), 2));
    testing.expectEqual(@as(usize, 2), digits(@as(usize, 0010), 10));
    testing.expectEqual(@as(usize, 2), digits(@as(usize, 0x10), 16));
    testing.expectEqual(@as(usize, 2), digits(@as(usize, 0b11), 2));
    testing.expectEqual(@as(usize, 2), digits(@as(usize, 0099), 10));
    testing.expectEqual(@as(usize, 2), digits(@as(usize, 0xFF), 16));
    testing.expectEqual(@as(usize, 3), digits(@as(usize, 0b100), 2));
    testing.expectEqual(@as(usize, 3), digits(@as(usize, 00100), 10));
    testing.expectEqual(@as(usize, 3), digits(@as(usize, 0x100), 16));
}

/// Same as `intToken` but also converts the parsed string
/// to an integer.
pub fn int(comptime Int: type, comptime base: u8) Parser(Int) {
    return comptime convert(
        Int,
        toInt(Int, base),
        intToken(base, digits(math.maxInt(Int), base)),
    );
}

test "int" {
    const parser1 = int(u8, 10);
    expectResult(u8, .{ .value = 0, .rest = "" }, parser1("0"));
    expectResult(u8, .{ .value = 1, .rest = "" }, parser1("1"));
    expectResult(u8, .{ .value = 1, .rest = "a" }, parser1("1a"));
    expectResult(u8, .{ .value = 255, .rest = "" }, parser1("255"));
    expectResult(u8, null, parser1("256"));

    const parser2 = int(u8, 16);
    expectResult(u8, .{ .value = 0x00, .rest = "" }, parser2("0"));
    expectResult(u8, .{ .value = 0x01, .rest = "" }, parser2("1"));
    expectResult(u8, .{ .value = 0x1a, .rest = "" }, parser2("1a"));
    expectResult(u8, .{ .value = 0x01, .rest = "g" }, parser2("1g"));
    expectResult(u8, .{ .value = 0xff, .rest = "" }, parser2("ff"));
    expectResult(u8, .{ .value = 0xff, .rest = "" }, parser2("FF"));
    expectResult(u8, .{ .value = 0x10, .rest = "0" }, parser2("100"));
}

/// Creates a parser that calls a function to optain its underlying parser.
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
        fn res(str: []const u8) ?Result(T) {
            return func()(str);
        }
    }.res;
}

test "ref" {
    const Scope = struct {
        const _digit = discard(digit(10));
        const _digits = oneOf(.{ combine(.{ _digit, _digits_ref }), _digit });
        const _digits_ref = ref(struct {
            fn f() Parser(void) {
                return _digits;
            }
        }.f);
    };
    const _digits = Scope._digits;
    expectResult(void, .{ .value = {}, .rest = "" }, _digits("0"));
}

pub fn expectResult(comptime T: type, m_expect: ?Result(T), m_actual: ?Result(T)) void {
    const expect = m_expect orelse {
        testing.expectEqual(@as(?Result(T), null), m_actual);
        return;
    };
    testing.expect(m_actual != null);
    const actual = m_actual.?;

    testing.expectEqualStrings(expect.rest, actual.rest);
    switch (T) {
        []const u8 => testing.expectEqualStrings(expect.value, actual.value),
        else => testing.expectEqual(expect.value, actual.value),
    }
}
