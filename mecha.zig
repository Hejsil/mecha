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

/// The reverse of `Parser`. Give it a `Parser` type
/// and this function will give you `T`.
pub fn ParserResult(comptime P: type) type {
    return @typeInfo(@typeInfo(P).Fn.return_type.?).Optional.child.Value;
}

/// A parser that only succeeds on the end of the string.
pub fn eos(str: []const u8) ?Result(void) {
    if (str.len != 0)
        return null;
    return Result(void).init({}, str);
}

test "eos" {
    testParser({}, "", eos(""));
    testParser(null, "", eos("a"));
}

/// A parser that always succeeds with the result being the
/// entire string. The same as the '.*$' regex.
pub fn any(str: []const u8) ?Result([]const u8) {
    return Result([]const u8).init(str, str[str.len..]);
}

test "any" {
    testParser("", "", any(""));
    testParser("a", "", any("a"));
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
    testParser({}, "", char('a')("a"));
    testParser({}, "a", char('a')("aa"));
    testParser(null, "", char('a')("ba"));
    testParser(null, "", char('a')(""));
    testParser({}, "ā", char(0x100)("Āā"));
    testParser(null, "", char(0x100)(""));
    testParser(null, "\xc0", char(0x100)("\xc0"));
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
    testParser('a', "", range('a', 'z')("a"));
    testParser('c', "", range('a', 'z')("c"));
    testParser('z', "", range('a', 'z')("z"));
    testParser('a', "a", range('a', 'z')("aa"));
    testParser('c', "a", range('a', 'z')("ca"));
    testParser('z', "a", range('a', 'z')("za"));
    testParser(null, "", range('a', 'z')("1"));
    testParser(null, "", range('a', 'z')(""));
    testParser(0x100, "ā", range(0x100, 0x100)("Āā"));
    testParser(null, "aa", range(0x100, 0x100)("aa"));
    testParser(null, "\xc0", range(0x100, 0x100)("\xc0"));
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
            => testParser(c, "", alpha(&[_]u8{c})),
            else => testParser(null, "", alpha(&[_]u8{c})),
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
            '0'...'1' => testParser(c, "", digit(2)(&[_]u8{c})),
            else => testParser(null, "", digit(2)(&[_]u8{c})),
        }
    }

    i = 0;
    while (i <= 255) : (i += 1) {
        const c = @intCast(u8, i);
        switch (c) {
            '0'...'9' => testParser(c, "", digit(10)(&[_]u8{c})),
            else => testParser(null, "", digit(10)(&[_]u8{c})),
        }
    }
    i = 0;
    while (i <= 255) : (i += 1) {
        const c = @intCast(u8, i);
        switch (c) {
            '0'...'9',
            'a'...'f',
            'A'...'F',
            => testParser(c, "", digit(16)(&[_]u8{c})),
            else => testParser(null, "", digit(16)(&[_]u8{c})),
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
    testParser({}, "", string("aa")("aa"));
    testParser({}, "a", string("aa")("aaa"));
    testParser(null, "", string("aa")("ba"));
    testParser(null, "", string("aa")(""));
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
    testParser("", "", parser1(""));
    testParser("", "a", parser1("a"));
    testParser("ab", "", parser1("ab"));
    testParser("ab", "a", parser1("aba"));
    testParser("abab", "", parser1("abab"));
    testParser("abab", "a", parser1("ababa"));
    testParser("ababab", "", parser1("ababab"));

    const parser2 = comptime manyRange(1, 2, string("ab"));
    testParser(null, "", parser2(""));
    testParser(null, "", parser2("a"));
    testParser("ab", "", parser2("ab"));
    testParser("ab", "a", parser2("aba"));
    testParser("abab", "", parser2("abab"));
    testParser("abab", "a", parser2("ababa"));
    testParser("abab", "ab", parser2("ababab"));

    const parser3 = comptime many(char(0x100));
    testParser("ĀĀĀ", "āāā", parser3("ĀĀĀāāā"));

    const parser4 = comptime manyN(3, range('a', 'b'));
    testParser([_]u21{ 'a', 'b', 'a' }, "bab", parser4("ababab"));
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
    testParser(@as(?u21, 'a'), "", parser1("a"));
    testParser(@as(?u21, 'a'), "a", parser1("aa"));
    testParser(@as(?u21, null), "1", parser1("1"));
}

fn ParsersTypes(comptime parsers: anytype) []const type {
    var types: []const type = &[_]type{};
    inline for (parsers) |parser| {
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
    testParser(Res{ .@"0" = 'a', .@"1" = 'd' }, "", parser1("ad"));
    testParser(Res{ .@"0" = 'a', .@"1" = null }, "a", parser1("aa"));
    testParser(Res{ .@"0" = null, .@"1" = 'd' }, "a", parser1("da"));
    testParser(Res{ .@"0" = null, .@"1" = null }, "qa", parser1("qa"));

    const parser2 = comptime combine(.{ opt(range('a', 'b')), char('d') });
    testParser('a', "", parser2("ad"));
    testParser('a', "a", parser2("ada"));
    testParser(@as(?u21, null), "a", parser2("da"));
    testParser(null, "", parser2("qa"));
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
    testParser('a', "", parser1("a"));
    testParser('b', "", parser1("b"));
    testParser('d', "", parser1("d"));
    testParser('e', "", parser1("e"));
    testParser('a', "a", parser1("aa"));
    testParser('b', "a", parser1("ba"));
    testParser('d', "a", parser1("da"));
    testParser('e', "a", parser1("ea"));
    testParser(null, "", parser1("q"));
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
    testParser("a", "", parser1("a"));
    testParser("a", "a", parser1("aa"));
    testParser(null, "", parser1("ba"));

    const parser2 = comptime asStr(combine(.{ opt(range('a', 'b')), opt(range('d', 'e')) }));
    testParser("ad", "", parser2("ad"));
    testParser("a", "a", parser2("aa"));
    testParser("d", "a", parser2("da"));
    testParser("", "qa", parser2("qa"));
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
    testParser(123, "", parser1("123"));
    testParser(123, "a", parser1("123a"));
    testParser(null, "", parser1("12"));

    const parser2 = comptime convert(u21, toChar, asStr(string("a")));
    testParser('a', "", parser2("a"));
    testParser('a', "a", parser2("aa"));
    testParser(null, "", parser2("b"));

    const parser3 = comptime convert(bool, toBool, any);
    testParser(true, "", parser3("true"));
    testParser(false, "", parser3("false"));
    testParser(null, "", parser3("b"));

    const parser4 = comptime convert(f32, toFloat(f32), asStr(string("1.23")));
    testParser(1.23, "", parser4("1.23"));
    testParser(1.23, "a", parser4("1.23a"));
    testParser(null, "", parser4("1.2"));

    const E = packed enum(u8) { a, b, _ };
    const parser5 = comptime convert(E, toEnum(E), any);
    testParser(E.a, "", parser5("a"));
    testParser(E.b, "", parser5("b"));
    testParser(null, "2", parser5("2"));

    const parser6 = comptime convert(u21, toChar, asStr(string("Āā")));
    testParser(0x100, "", parser6("Āā"));
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
    testParser({}, "abc", parser(" abc"));
    testParser({}, "abc", parser("  abc"));
    testParser({}, "abc", parser("   abc"));
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
    while (tmp != 0) : (tmp /= base)
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
    testParser(0, "", parser1("0"));
    testParser(1, "", parser1("1"));
    testParser(1, "a", parser1("1a"));
    testParser(255, "", parser1("255"));
    testParser(null, "", parser1("256"));

    const parser2 = int(u8, 16);
    testParser(0x00, "", parser2("0"));
    testParser(0x01, "", parser2("1"));
    testParser(0x1a, "", parser2("1a"));
    testParser(0x01, "g", parser2("1g"));
    testParser(0xff, "", parser2("ff"));
    testParser(0xff, "", parser2("FF"));
    testParser(0x10, "0", parser2("100"));
}

fn testParser(expected_value: anytype, rest: []const u8, m_res: anytype) void {
    switch (@typeInfo(@TypeOf(expected_value))) {
        .Null => testing.expect(m_res == null),
        else => {
            testing.expect(m_res != null);
            testing.expectEqualStrings(rest, m_res.?.rest);
            const T = @TypeOf(m_res.?.value);
            switch (T) {
                []u8,
                []const u8,
                => testing.expectEqualStrings(expected_value, m_res.?.value),
                else => testing.expectEqual(@as(T, expected_value), m_res.?.value),
            }
        },
    }
}
