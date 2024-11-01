const mecha = @import("mecha");
const std = @import("std");

const builtin = std.builtin;
const testing = std.testing;

const json = mecha.combine(.{ ws, element });

const value = mecha.oneOf(.{
    object,
    array,
    jstring,
    number,
    jtrue,
    jfalse,
    jnull,
});

const members = mecha.combine(.{
    member,
    mecha.combine(.{ comma, member })
        .many(.{ .collect = false })
        .discard(),
});

const elements = mecha.combine(.{
    element,
    mecha.combine(.{ comma, element })
        .many(.{ .collect = false })
        .discard(),
});

const array = mecha.combine(.{ lbracket, elements.opt().discard(), rbracket });
const element = mecha.ref(valueRef);
const member = mecha.combine(.{ jstring, colon, element });
const object = mecha.combine(.{ lcurly, members.opt().discard(), rcurly });

fn valueRef() mecha.Parser(void) {
    return value;
}

const colon = token(mecha.utf8.char(':'));
const comma = token(mecha.utf8.char(','));
const jfalse = token(mecha.string("false"));
const jnull = token(mecha.string("null"));
const jstring = token(mecha.combine(.{ mecha.utf8.char('"'), chars, mecha.utf8.char('"') }));
const jtrue = token(mecha.string("true"));
const lbracket = token(mecha.utf8.char('['));
const lcurly = token(mecha.utf8.char('{'));
const number = token(mecha.combine(.{ integer, fraction, exponent }));
const rbracket = token(mecha.utf8.char(']'));
const rcurly = token(mecha.utf8.char('}'));

fn token(comptime parser: anytype) mecha.Parser(void) {
    return mecha.combine(.{ parser.discard(), ws });
}

const chars = char.many(.{ .collect = false }).discard();

const char = mecha.oneOf(.{
    mecha.utf8.range(0x0020, '"' - 1).discard(),
    mecha.utf8.range('"' + 1, '\\' - 1).discard(),
    mecha.utf8.range('\\' + 1, 0x10FFFF).discard(),
    mecha.combine(.{
        mecha.utf8.char('\\').discard(),
        escape,
    }).discard(),
});

const escape = mecha.oneOf(.{
    mecha.utf8.char('"'),
    mecha.utf8.char('\\'),
    mecha.utf8.char('/'),
    mecha.utf8.char('b'),
    mecha.utf8.char('f'),
    mecha.utf8.char('n'),
    mecha.utf8.char('r'),
    mecha.utf8.char('t'),
    mecha.combine(.{ mecha.utf8.char('u'), hex, hex, hex, hex }),
});

const hex = mecha.oneOf(.{
    jdigit,
    mecha.utf8.range('a', 'f').discard(),
    mecha.utf8.range('A', 'F').discard(),
});

const integer = mecha.oneOf(.{
    mecha.combine(.{ onenine, digits }),
    jdigit,
    mecha.combine(.{ mecha.utf8.char('-').discard(), onenine, digits }),
    mecha.combine(.{ mecha.utf8.char('-').discard(), jdigit }),
});

const digits = jdigit.many(.{ .collect = false, .min = 1 }).discard();

const jdigit = mecha.oneOf(.{
    mecha.utf8.char('0').discard(),
    onenine,
});

const onenine = mecha.utf8.range('1', '9').discard();

const fraction = mecha.discard(mecha.opt(
    mecha.combine(.{ mecha.utf8.char('.').discard(), digits }),
));

const exponent = mecha.combine(.{
    mecha.oneOf(.{ mecha.utf8.char('E'), mecha.utf8.char('e') }).discard(),
    sign,
    digits,
}).opt().discard();

const sign = mecha.oneOf(.{
    mecha.utf8.char('+'),
    mecha.utf8.char('-'),
}).opt().discard();

const ws = mecha.oneOf(.{
    mecha.utf8.char(0x0020),
    mecha.utf8.char(0x000A),
    mecha.utf8.char(0x000D),
    mecha.utf8.char(0x0009),
}).many(.{ .collect = false }).discard();

fn ok(s: []const u8) !void {
    const res = json.parse(testing.allocator, s) catch @panic("test failure");
    try testing.expectEqualStrings("", s[res.index..]);
}

fn err(pos: usize, s: []const u8) !void {
    try mecha.expectErr(void, pos, try json.parse(testing.allocator, s));
}

fn errNotAllParsed(s: []const u8) !void {
    const res = json.parse(testing.allocator, s) catch @panic("test failure");
    try testing.expect(s[res.index..].len != 0);
}

fn any(s: []const u8) void {
    _ = json.parse(testing.allocator, s) catch {};
}

////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Additional tests not part of test JSONTestSuite.

test "y_trailing_comma_after_empty" {
    try ok(
        \\{"1":[],"2":{},"3":"4"}
    );
}

////////////////////////////////////////////////////////////////////////////////////////////////////

test "y_array_arraysWithSpaces" {
    try ok(
        \\[[]   ]
    );
}

test "y_array_empty" {
    try ok(
        \\[]
    );
}

test "y_array_empty-string" {
    try ok(
        \\[""]
    );
}

test "y_array_ending_with_newline" {
    try ok(
        \\["a"]
    );
}

test "y_array_false" {
    try ok(
        \\[false]
    );
}

test "y_array_heterogeneous" {
    try ok(
        \\[null, 1, "1", {}]
    );
}

test "y_array_null" {
    try ok(
        \\[null]
    );
}

test "y_array_with_1_and_newline" {
    try ok(
        \\[1
        \\]
    );
}

test "y_array_with_leading_space" {
    try ok(
        \\ [1]
    );
}

test "y_array_with_several_null" {
    try ok(
        \\[1,null,null,null,2]
    );
}

test "y_array_with_trailing_space" {
    try ok("[2] ");
}

test "y_number_0e+1" {
    try ok(
        \\[0e+1]
    );
}

test "y_number_0e1" {
    try ok(
        \\[0e1]
    );
}

test "y_number_after_space" {
    try ok(
        \\[ 4]
    );
}

test "y_number_double_close_to_zero" {
    try ok(
        \\[-0.000000000000000000000000000000000000000000000000000000000000000000000000000001]
    );
}

test "y_number_int_with_exp" {
    try ok(
        \\[20e1]
    );
}

test "y_number" {
    try ok(
        \\[123e65]
    );
}

test "y_number_minus_zero" {
    try ok(
        \\[-0]
    );
}

test "y_number_negative_int" {
    try ok(
        \\[-123]
    );
}

test "y_number_negative_one" {
    try ok(
        \\[-1]
    );
}

test "y_number_negative_zero" {
    try ok(
        \\[-0]
    );
}

test "y_number_real_capital_e" {
    try ok(
        \\[1E22]
    );
}

test "y_number_real_capital_e_neg_exp" {
    try ok(
        \\[1E-2]
    );
}

test "y_number_real_capital_e_pos_exp" {
    try ok(
        \\[1E+2]
    );
}

test "y_number_real_exponent" {
    try ok(
        \\[123e45]
    );
}

test "y_number_real_fraction_exponent" {
    try ok(
        \\[123.456e78]
    );
}

test "y_number_real_neg_exp" {
    try ok(
        \\[1e-2]
    );
}

test "y_number_real_pos_exponent" {
    try ok(
        \\[1e+2]
    );
}

test "y_number_simple_int" {
    try ok(
        \\[123]
    );
}

test "y_number_simple_real" {
    try ok(
        \\[123.456789]
    );
}

test "y_object_basic" {
    try ok(
        \\{"asd":"sdf"}
    );
}

test "y_object_duplicated_key_and_value" {
    try ok(
        \\{"a":"b","a":"b"}
    );
}

test "y_object_duplicated_key" {
    try ok(
        \\{"a":"b","a":"c"}
    );
}

test "y_object_empty" {
    try ok(
        \\{}
    );
}

test "y_object_empty_key" {
    try ok(
        \\{"":0}
    );
}

test "y_object_escaped_null_in_key" {
    try ok(
        \\{"foo\u0000bar": 42}
    );
}

test "y_object_extreme_numbers" {
    try ok(
        \\{ "min": -1.0e+28, "max": 1.0e+28 }
    );
}

test "y_object" {
    try ok(
        \\{"asd":"sdf", "dfg":"fgh"}
    );
}

test "y_object_long_strings" {
    try ok(
        \\{"x":[{"id": "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"}], "id": "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"}
    );
}

test "y_object_simple" {
    try ok(
        \\{"a":[]}
    );
}

test "y_object_string_unicode" {
    try ok(
        \\{"title":"\u041f\u043e\u043b\u0442\u043e\u0440\u0430 \u0417\u0435\u043c\u043b\u0435\u043a\u043e\u043f\u0430" }
    );
}

test "y_object_with_newlines" {
    try ok(
        \\{
        \\"a": "b"
        \\}
    );
}

test "y_string_1_2_3_bytes_UTF-8_sequences" {
    try ok(
        \\["\u0060\u012a\u12AB"]
    );
}

test "y_string_accepted_surrogate_pair" {
    try ok(
        \\["\uD801\udc37"]
    );
}

test "y_string_accepted_surrogate_pairs" {
    try ok(
        \\["\ud83d\ude39\ud83d\udc8d"]
    );
}

test "y_string_allowed_escapes" {
    try ok(
        \\["\"\\\/\b\f\n\r\t"]
    );
}

test "y_string_backslash_and_u_escaped_zero" {
    try ok(
        \\["\\u0000"]
    );
}

test "y_string_backslash_doublequotes" {
    try ok(
        \\["\""]
    );
}

test "y_string_comments" {
    try ok(
        \\["a/*b*/c/*d//e"]
    );
}

test "y_string_double_escape_a" {
    try ok(
        \\["\\a"]
    );
}

test "y_string_double_escape_n" {
    try ok(
        \\["\\n"]
    );
}

test "y_string_escaped_control_character" {
    try ok(
        \\["\u0012"]
    );
}

test "y_string_escaped_noncharacter" {
    try ok(
        \\["\uFFFF"]
    );
}

test "y_string_in_array" {
    try ok(
        \\["asd"]
    );
}

test "y_string_in_array_with_leading_space" {
    try ok(
        \\[ "asd"]
    );
}

test "y_string_last_surrogates_1_and_2" {
    try ok(
        \\["\uDBFF\uDFFF"]
    );
}

test "y_string_nbsp_uescaped" {
    try ok(
        \\["new\u00A0line"]
    );
}

test "y_string_nonCharacterInUTF-8_U+10FFFF" {
    try ok(
        \\["􏿿"]
    );
}

test "y_string_nonCharacterInUTF-8_U+FFFF" {
    try ok(
        \\["￿"]
    );
}

test "y_string_null_escape" {
    try ok(
        \\["\u0000"]
    );
}

test "y_string_one-byte-utf-8" {
    try ok(
        \\["\u002c"]
    );
}

test "y_string_pi" {
    try ok(
        \\["π"]
    );
}

test "y_string_reservedCharacterInUTF-8_U+1BFFF" {
    try ok(
        \\["𛿿"]
    );
}

test "y_string_simple_ascii" {
    try ok(
        \\["asd "]
    );
}

test "y_string_space" {
    try ok(
        \\" "
    );
}

test "y_string_surrogates_U+1D11E_MUSICAL_SYMBOL_G_CLEF" {
    try ok(
        \\["\uD834\uDd1e"]
    );
}

test "y_string_three-byte-utf-8" {
    try ok(
        \\["\u0821"]
    );
}

test "y_string_two-byte-utf-8" {
    try ok(
        \\["\u0123"]
    );
}

test "y_string_u+2028_line_sep" {
    try ok("[\"\xe2\x80\xa8\"]");
}

test "y_string_u+2029_par_sep" {
    try ok("[\"\xe2\x80\xa9\"]");
}

test "y_string_uescaped_newline" {
    try ok(
        \\["new\u000Aline"]
    );
}

test "y_string_uEscape" {
    try ok(
        \\["\u0061\u30af\u30EA\u30b9"]
    );
}

test "y_string_unescaped_char_delete" {
    try ok("[\"\x7f\"]");
}

test "y_string_unicode_2" {
    try ok(
        \\["⍂㈴⍂"]
    );
}

test "y_string_unicodeEscapedBackslash" {
    try ok(
        \\["\u005C"]
    );
}

test "y_string_unicode_escaped_double_quote" {
    try ok(
        \\["\u0022"]
    );
}

test "y_string_unicode" {
    try ok(
        \\["\uA66D"]
    );
}

test "y_string_unicode_U+10FFFE_nonchar" {
    try ok(
        \\["\uDBFF\uDFFE"]
    );
}

test "y_string_unicode_U+1FFFE_nonchar" {
    try ok(
        \\["\uD83F\uDFFE"]
    );
}

test "y_string_unicode_U+200B_ZERO_WIDTH_SPACE" {
    try ok(
        \\["\u200B"]
    );
}

test "y_string_unicode_U+2064_invisible_plus" {
    try ok(
        \\["\u2064"]
    );
}

test "y_string_unicode_U+FDD0_nonchar" {
    try ok(
        \\["\uFDD0"]
    );
}

test "y_string_unicode_U+FFFE_nonchar" {
    try ok(
        \\["\uFFFE"]
    );
}

test "y_string_utf8" {
    try ok(
        \\["€𝄞"]
    );
}

test "y_string_with_del_character" {
    try ok("[\"a\x7fa\"]");
}

test "y_structure_lonely_false" {
    try ok(
        \\false
    );
}

test "y_structure_lonely_int" {
    try ok(
        \\42
    );
}

test "y_structure_lonely_negative_real" {
    try ok(
        \\-0.1
    );
}

test "y_structure_lonely_null" {
    try ok(
        \\null
    );
}

test "y_structure_lonely_string" {
    try ok(
        \\"asd"
    );
}

test "y_structure_lonely_true" {
    try ok(
        \\true
    );
}

test "y_structure_string_empty" {
    try ok(
        \\""
    );
}

test "y_structure_trailing_newline" {
    try ok(
        \\["a"]
    );
}

test "y_structure_true_in_array" {
    try ok(
        \\[true]
    );
}

test "y_structure_whitespace_array" {
    try ok(" [] ");
}

////////////////////////////////////////////////////////////////////////////////////////////////////

test "n_array_1_true_without_comma" {
    try err(3,
        \\[1 true]
    );
}

test "n_array_a_invalid_utf8" {
    try err(1,
        \\[aå]
    );
}

test "n_array_colon_instead_of_comma" {
    try err(3,
        \\["": 1]
    );
}

test "n_array_comma_after_close" {
    try errNotAllParsed(
        \\[""],
    );
}

test "n_array_comma_and_number" {
    try err(1,
        \\[,1]
    );
}

test "n_array_double_comma" {
    try err(2,
        \\[1,,2]
    );
}

test "n_array_double_extra_comma" {
    try err(4,
        \\["x",,]
    );
}

test "n_array_extra_close" {
    try errNotAllParsed(
        \\["x"]]
    );
}

test "n_array_extra_comma" {
    try err(3,
        \\["",]
    );
}

test "n_array_incomplete_invalid_value" {
    try err(1,
        \\[x
    );
}

test "n_array_incomplete" {
    try err(4,
        \\["x"
    );
}

test "n_array_inner_array_no_comma" {
    try err(2,
        \\[3[4]]
    );
}

test "n_array_invalid_utf8" {
    try err(1,
        \\[ÿ]
    );
}

test "n_array_items_separated_by_semicolon" {
    try err(2,
        \\[1:2]
    );
}

test "n_array_just_comma" {
    try err(1,
        \\[,]
    );
}

test "n_array_just_minus" {
    try err(1,
        \\[-]
    );
}

test "n_array_missing_value" {
    try err(4,
        \\[   , ""]
    );
}

test "n_array_newlines_unclosed" {
    try err(10,
        \\["a",
        \\4
        \\,1,
    );
}

test "n_array_number_and_comma" {
    try err(2,
        \\[1,]
    );
}

test "n_array_number_and_several_commas" {
    try err(2,
        \\[1,,]
    );
}

test "n_array_spaces_vertical_tab_formfeed" {
    try err(1, "[\"\x0aa\"\\f]");
}

test "n_array_star_inside" {
    try err(1,
        \\[*]
    );
}

test "n_array_unclosed" {
    try err(3,
        \\[""
    );
}

test "n_array_unclosed_trailing_comma" {
    try err(2,
        \\[1,
    );
}

test "n_array_unclosed_with_new_lines" {
    try err(8,
        \\[1,
        \\1
        \\,1
    );
}

test "n_array_unclosed_with_object_inside" {
    try err(3,
        \\[{}
    );
}

test "n_incomplete_false" {
    try err(1,
        \\[fals]
    );
}

test "n_incomplete_null" {
    try err(1,
        \\[nul]
    );
}

test "n_incomplete_true" {
    try err(1,
        \\[tru]
    );
}

test "n_multidigit_number_then_00" {
    try errNotAllParsed("123\x00");
}

test "n_number_0.1.2" {
    try err(4,
        \\[0.1.2]
    );
}

test "n_number_-01" {
    try err(3,
        \\[-01]
    );
}

test "n_number_0.3e" {
    try err(4,
        \\[0.3e]
    );
}

test "n_number_0.3e+" {
    try err(4,
        \\[0.3e+]
    );
}

test "n_number_0_capital_E" {
    try err(2,
        \\[0E]
    );
}

test "n_number_0_capital_E+" {
    try err(2,
        \\[0E+]
    );
}

test "n_number_0.e1" {
    try err(2,
        \\[0.e1]
    );
}

test "n_number_0e" {
    try err(2,
        \\[0e]
    );
}

test "n_number_0e+" {
    try err(2,
        \\[0e+]
    );
}

test "n_number_1_000" {
    try err(3,
        \\[1 000.0]
    );
}

test "n_number_1.0e-" {
    try err(4,
        \\[1.0e-]
    );
}

test "n_number_1.0e" {
    try err(4,
        \\[1.0e]
    );
}

test "n_number_1.0e+" {
    try err(4,
        \\[1.0e+]
    );
}

test "n_number_-1.0." {
    try err(5,
        \\[-1.0.]
    );
}

test "n_number_1eE2" {
    try err(2,
        \\[1eE2]
    );
}

test "n_number_.-1" {
    try err(1,
        \\[.-1]
    );
}

test "n_number_+1" {
    try err(1,
        \\[+1]
    );
}

test "n_number_.2e-3" {
    try err(1,
        \\[.2e-3]
    );
}

test "n_number_2.e-3" {
    try err(2,
        \\[2.e-3]
    );
}

test "n_number_2.e+3" {
    try err(2,
        \\[2.e+3]
    );
}

test "n_number_2.e3" {
    try err(2,
        \\[2.e3]
    );
}

test "n_number_-2." {
    try err(3,
        \\[-2.]
    );
}

test "n_number_9.e+" {
    try err(2,
        \\[9.e+]
    );
}

test "n_number_expression" {
    try err(2,
        \\[1+2]
    );
}

test "n_number_hex_1_digit" {
    try err(2,
        \\[0x1]
    );
}

test "n_number_hex_2_digits" {
    try err(2,
        \\[0x42]
    );
}

test "n_number_infinity" {
    try err(1,
        \\[Infinity]
    );
}

test "n_number_+Inf" {
    try err(1,
        \\[+Inf]
    );
}

test "n_number_Inf" {
    try err(1,
        \\[Inf]
    );
}

test "n_number_invalid+-" {
    try err(2,
        \\[0e+-1]
    );
}

test "n_number_invalid-negative-real" {
    try err(9,
        \\[-123.123foo]
    );
}

test "n_number_invalid-utf-8-in-bigger-int" {
    try err(4,
        \\[123å]
    );
}

test "n_number_invalid-utf-8-in-exponent" {
    try err(4,
        \\[1e1å]
    );
}

test "n_number_invalid-utf-8-in-int" {
    try err(2,
        \\[0å]
    );
}

test "n_number_++" {
    try err(1,
        \\[++1234]
    );
}

test "n_number_minus_infinity" {
    try err(1,
        \\[-Infinity]
    );
}

test "n_number_minus_sign_with_trailing_garbage" {
    try err(1,
        \\[-foo]
    );
}

test "n_number_minus_space_1" {
    try err(1,
        \\[- 1]
    );
}

test "n_number_-NaN" {
    try err(1,
        \\[-NaN]
    );
}

test "n_number_NaN" {
    try err(1,
        \\[NaN]
    );
}

test "n_number_neg_int_starting_with_zero" {
    try err(3,
        \\[-012]
    );
}

test "n_number_neg_real_without_int_part" {
    try err(1,
        \\[-.123]
    );
}

test "n_number_neg_with_garbage_at_end" {
    try err(3,
        \\[-1x]
    );
}

test "n_number_real_garbage_after_e" {
    try err(2,
        \\[1ea]
    );
}

test "n_number_real_with_invalid_utf8_after_e" {
    try err(2,
        \\[1eå]
    );
}

test "n_number_real_without_fractional_part" {
    try err(2,
        \\[1.]
    );
}

test "n_number_starting_with_dot" {
    try err(1,
        \\[.123]
    );
}

test "n_number_U+FF11_fullwidth_digit_one" {
    try err(1,
        \\[ï¼]
    );
}

test "n_number_with_alpha_char" {
    try err(19,
        \\[1.8011670033376514H-308]
    );
}

test "n_number_with_alpha" {
    try err(4,
        \\[1.2a-3]
    );
}

test "n_number_with_leading_zero" {
    try err(2,
        \\[012]
    );
}

test "n_object_bad_value" {
    try err(4,
        \\["x", truth]
    );
}

test "n_object_bracket_key" {
    try err(1,
        \\{[: "x"}
    );
}

test "n_object_comma_instead_of_colon" {
    try err(1,
        \\{"x", null}
    );
}

test "n_object_double_colon" {
    try err(1,
        \\{"x"::"b"}
    );
}

test "n_object_emoji" {
    try err(1,
        \\{ð¨ð­}
    );
}

test "n_object_garbage_at_end" {
    try err(9,
        \\{"a":"a" 123}
    );
}

test "n_object_key_with_single_quotes" {
    try err(1,
        \\{key: 'value'}
    );
}

test "n_object_lone_continuation_byte_in_key_and_trailing_comma" {
    try err(9,
        \\{"¹":"0",}
    );
}

test "n_object_missing_colon" {
    try err(1,
        \\{"a" b}
    );
}

test "n_object_missing_key" {
    try err(1,
        \\{:"b"}
    );
}

test "n_object_missing_semicolon" {
    try err(1,
        \\{"a" "b"}
    );
}

test "n_object_missing_value" {
    try err(1,
        \\{"a":
    );
}

test "n_object_no-colon" {
    try err(1,
        \\{"a"
    );
}

test "n_object_non_string_key_but_huge_number_instead" {
    try err(1,
        \\{9999E9999:1}
    );
}

test "n_object_non_string_key" {
    try err(1,
        \\{1:1}
    );
}

test "n_object_repeated_null_null" {
    try err(1,
        \\{null:null,null:null}
    );
}

test "n_object_several_trailing_commas" {
    try err(7,
        \\{"id":0,,,,}
    );
}

test "n_object_single_quote" {
    try err(1,
        \\{'a':0}
    );
}

test "n_object_trailing_comma" {
    try err(7,
        \\{"id":0,}
    );
}

test "n_object_trailing_comment" {
    try errNotAllParsed(
        \\{"a":"b"}/**/
    );
}

test "n_object_trailing_comment_open" {
    try errNotAllParsed(
        \\{"a":"b"}/**//
    );
}

test "n_object_trailing_comment_slash_open_incomplete" {
    try errNotAllParsed(
        \\{"a":"b"}/
    );
}

test "n_object_trailing_comment_slash_open" {
    try errNotAllParsed(
        \\{"a":"b"}//
    );
}

test "n_object_two_commas_in_a_row" {
    try err(8,
        \\{"a":"b",,"c":"d"}
    );
}

test "n_object_unquoted_key" {
    try err(1,
        \\{a: "b"}
    );
}

test "n_object_unterminated-value" {
    try err(1,
        \\{"a":"a
    );
}

test "n_object_with_single_string" {
    try err(15,
        \\{ "foo" : "bar", "a" }
    );
}

test "n_object_with_trailing_garbage" {
    try errNotAllParsed(
        \\{"a":"b"}#
    );
}

test "n_single_space" {
    try err(1, " ");
}

test "n_string_1_surrogate_then_escape" {
    try err(1,
        \\["\uD800\"]
    );
}

test "n_string_1_surrogate_then_escape_u1" {
    try err(1,
        \\["\uD800\u1"]
    );
}

test "n_string_1_surrogate_then_escape_u1x" {
    try err(1,
        \\["\uD800\u1x"]
    );
}

test "n_string_1_surrogate_then_escape_u" {
    try err(1,
        \\["\uD800\u"]
    );
}

test "n_string_accentuated_char_no_quotes" {
    try err(1,
        \\[Ã©]
    );
}

test "n_string_backslash_00" {
    try err(1, "[\"\x00\"]");
}

test "n_string_escaped_backslash_bad" {
    try err(1,
        \\["\\\"]
    );
}

test "n_string_escaped_ctrl_char_tab" {
    try err(1, "\x5b\x22\x5c\x09\x22\x5d");
}

test "n_string_escaped_emoji" {
    try err(1, "[\"\x5c\xc3\xb0\xc2\x9f\xc2\x8c\xc2\x80\"]");
}

test "n_string_escape_x" {
    try err(1,
        \\["\x00"]
    );
}

test "n_string_incomplete_escaped_character" {
    try err(1,
        \\["\u00A"]
    );
}

test "n_string_incomplete_escape" {
    try err(1,
        \\["\"]
    );
}

test "n_string_incomplete_surrogate_escape_invalid" {
    try err(1,
        \\["\uD800\uD800\x"]
    );
}

test "n_string_incomplete_surrogate" {
    try err(1,
        \\["\uD834\uDd"]
    );
}

test "n_string_invalid_backslash_esc" {
    try err(1,
        \\["\a"]
    );
}

test "n_string_invalid_unicode_escape" {
    try err(1,
        \\["\uqqqq"]
    );
}

test "n_string_invalid_utf8_after_escape" {
    try err(1, "[\"\\\x75\xc3\xa5\"]");
}

test "n_string_invalid-utf-8-in-escape" {
    try err(1,
        \\["\uå"]
    );
}

test "n_string_leading_uescaped_thinspace" {
    try err(1,
        \\[\u0020"asd"]
    );
}

test "n_string_no_quotes_with_bad_escape" {
    try err(1,
        \\[\n]
    );
}

test "n_string_single_doublequote" {
    try err(1,
        \\"
    );
}

test "n_string_single_quote" {
    try err(1,
        \\['single quote']
    );
}

test "n_string_single_string_no_double_quotes" {
    try err(0,
        \\abc
    );
}

test "n_string_start_escape_unclosed" {
    try err(1,
        \\["\
    );
}

test "n_string_unescaped_crtl_char" {
    try err(1, "[\"a\x00a\"]");
}

test "n_string_unescaped_newline" {
    try err(1,
        \\["new
        \\line"]
    );
}

test "n_string_unescaped_tab" {
    try err(1, "[\"\t\"]");
}

test "n_string_unicode_CapitalU" {
    try err(1,
        \\"\UA66D"
    );
}

test "n_string_with_trailing_garbage" {
    try errNotAllParsed(
        \\""x
    );
}

test "n_structure_100000_opening_arrays" {
    return error.SkipZigTest;
    // try err(0, "[" ** 100000);
}

test "n_structure_angle_bracket_." {
    try err(0,
        \\<.>
    );
}

test "n_structure_angle_bracket_null" {
    try err(1,
        \\[<null>]
    );
}

test "n_structure_array_trailing_garbage" {
    try errNotAllParsed(
        \\[1]x
    );
}

test "n_structure_array_with_extra_array_close" {
    try errNotAllParsed(
        \\[1]]
    );
}

test "n_structure_array_with_unclosed_string" {
    try err(1,
        \\["asd]
    );
}

test "n_structure_ascii-unicode-identifier" {
    try err(0,
        \\aÃ¥
    );
}

test "n_structure_capitalized_True" {
    try err(1,
        \\[True]
    );
}

test "n_structure_close_unopened_array" {
    try errNotAllParsed(
        \\1]
    );
}

test "n_structure_comma_instead_of_closing_brace" {
    try err(10,
        \\{"x": true,
    );
}

test "n_structure_double_array" {
    try errNotAllParsed(
        \\[][]
    );
}

test "n_structure_end_array" {
    try err(0,
        \\]
    );
}

test "n_structure_incomplete_UTF8_BOM" {
    try err(0,
        \\ï»{}
    );
}

test "n_structure_lone-invalid-utf-8" {
    try err(0,
        \\å
    );
}

test "n_structure_lone-open-bracket" {
    try err(1,
        \\[
    );
}

test "n_structure_no_data" {
    try err(0,
        \\
    );
}

test "n_structure_null-byte-outside-string" {
    try err(1, "[\x00]");
}

test "n_structure_number_with_trailing_garbage" {
    try errNotAllParsed(
        \\2@
    );
}

test "n_structure_object_followed_by_closing_object" {
    try errNotAllParsed(
        \\{}}
    );
}

test "n_structure_object_unclosed_no_value" {
    try err(1,
        \\{"":
    );
}

test "n_structure_object_with_comment" {
    try err(1,
        \\{"a":/*comment*/"b"}
    );
}

test "n_structure_object_with_trailing_garbage" {
    try errNotAllParsed(
        \\{"a": true} "x"
    );
}

test "n_structure_open_array_apostrophe" {
    try err(1,
        \\['
    );
}

test "n_structure_open_array_comma" {
    try err(1,
        \\[,
    );
}

test "n_structure_open_array_object" {
    return error.SkipZigTest;
    // try err(0, "[{\"\":" ** 50000);
}

test "n_structure_open_array_open_object" {
    try err(1,
        \\[{
    );
}

test "n_structure_open_array_open_string" {
    try err(1,
        \\["a
    );
}

test "n_structure_open_array_string" {
    try err(4,
        \\["a"
    );
}

test "n_structure_open_object_close_array" {
    try err(1,
        \\{]
    );
}

test "n_structure_open_object_comma" {
    try err(1,
        \\{,
    );
}

test "n_structure_open_object" {
    try err(1,
        \\{
    );
}

test "n_structure_open_object_open_array" {
    try err(1,
        \\{[
    );
}

test "n_structure_open_object_open_string" {
    try err(1,
        \\{"a
    );
}

test "n_structure_open_object_string_with_apostrophes" {
    try err(1,
        \\{'a'
    );
}

test "n_structure_open_open" {
    try err(1,
        \\["\{["\{["\{["\{
    );
}

test "n_structure_single_eacute" {
    try err(0,
        \\é
    );
}

test "n_structure_single_star" {
    try err(0,
        \\*
    );
}

test "n_structure_trailing_#" {
    try errNotAllParsed(
        \\{"a":"b"}#{}
    );
}

test "n_structure_U+2060_word_joined" {
    try err(1,
        \\[â ]
    );
}

test "n_structure_uescaped_LF_before_string" {
    try err(1,
        \\[\u000A""]
    );
}

test "n_structure_unclosed_array" {
    try err(2,
        \\[1
    );
}

test "n_structure_unclosed_array_partial_null" {
    try err(7,
        \\[ false, nul
    );
}

test "n_structure_unclosed_array_unfinished_false" {
    try err(6,
        \\[ true, fals
    );
}

test "n_structure_unclosed_array_unfinished_true" {
    try err(7,
        \\[ false, tru
    );
}

test "n_structure_unclosed_object" {
    try err(12,
        \\{"asd":"asd"
    );
}

test "n_structure_unicode-identifier" {
    try err(0,
        \\Ã¥
    );
}

test "n_structure_UTF8_BOM_no_data" {
    try err(0,
        \\ï»¿
    );
}

test "n_structure_whitespace_formfeed" {
    try err(1, "[\x0c]");
}

test "n_structure_whitespace_U+2060_word_joiner" {
    try err(1,
        \\[â ]
    );
}

////////////////////////////////////////////////////////////////////////////////////////////////////

test "i_number_double_huge_neg_exp" {
    any(
        \\[123.456e-789]
    );
}

test "i_number_huge_exp" {
    any(
        \\[0.4e00669999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999969999999006]
    );
}

test "i_number_neg_int_huge_exp" {
    any(
        \\[-1e+9999]
    );
}

test "i_number_pos_double_huge_exp" {
    any(
        \\[1.5e+9999]
    );
}

test "i_number_real_neg_overflow" {
    any(
        \\[-123123e100000]
    );
}

test "i_number_real_pos_overflow" {
    any(
        \\[123123e100000]
    );
}

test "i_number_real_underflow" {
    any(
        \\[123e-10000000]
    );
}

test "i_number_too_big_neg_int" {
    any(
        \\[-123123123123123123123123123123]
    );
}

test "i_number_too_big_pos_int" {
    any(
        \\[100000000000000000000]
    );
}

test "i_number_very_big_negative_int" {
    any(
        \\[-237462374673276894279832749832423479823246327846]
    );
}

test "i_object_key_lone_2nd_surrogate" {
    any(
        \\{"\uDFAA":0}
    );
}

test "i_string_1st_surrogate_but_2nd_missing" {
    any(
        \\["\uDADA"]
    );
}

test "i_string_1st_valid_surrogate_2nd_invalid" {
    any(
        \\["\uD888\u1234"]
    );
}

test "i_string_incomplete_surrogate_and_escape_valid" {
    any(
        \\["\uD800\n"]
    );
}

test "i_string_incomplete_surrogate_pair" {
    any(
        \\["\uDd1ea"]
    );
}

test "i_string_incomplete_surrogates_escape_valid" {
    any(
        \\["\uD800\uD800\n"]
    );
}

test "i_string_invalid_lonely_surrogate" {
    any(
        \\["\ud800"]
    );
}

test "i_string_invalid_surrogate" {
    any(
        \\["\ud800abc"]
    );
}

test "i_string_invalid_utf-8" {
    any(
        \\["ÿ"]
    );
}

test "i_string_inverted_surrogates_U+1D11E" {
    any(
        \\["\uDd1e\uD834"]
    );
}

test "i_string_iso_latin_1" {
    any(
        \\["é"]
    );
}

test "i_string_lone_second_surrogate" {
    any(
        \\["\uDFAA"]
    );
}

test "i_string_lone_utf8_continuation_byte" {
    any(
        \\[""]
    );
}

test "i_string_not_in_unicode_range" {
    any(
        \\["ô¿¿¿"]
    );
}

test "i_string_overlong_sequence_2_bytes" {
    any(
        \\["À¯"]
    );
}

test "i_string_overlong_sequence_6_bytes" {
    any(
        \\["ü¿¿¿¿"]
    );
}

test "i_string_overlong_sequence_6_bytes_null" {
    any(
        \\["ü"]
    );
}

test "i_string_truncated-utf-8" {
    any(
        \\["àÿ"]
    );
}

test "i_string_utf16BE_no_BOM" {
    any("\x00\x5b\x00\x22\x00\xc3\xa9\x00\x22\x00\x5d");
}

test "i_string_utf16LE_no_BOM" {
    any("\x5b\x00\x22\x00\xc3\xa9\x00\x22\x00\x5d\x00");
}

test "i_string_UTF-16LE_with_BOM" {
    any("\xc3\xbf\xc3\xbe\x5b\x00\x22\x00\xc3\xa9\x00\x22\x00\x5d\x00");
}

test "i_string_UTF-8_invalid_sequence" {
    any(
        \\["æ¥Ñú"]
    );
}

test "i_string_UTF8_surrogate_U+D800" {
    any(
        \\["í "]
    );
}

test "i_structure_500_nested_arrays" {
    any(("[" ** 500) ++ ("]" ** 500));
}

test "i_structure_UTF-8_BOM_empty_object" {
    any(
        \\ï»¿{}
    );
}

test "truncated UTF-8 sequence" {
    try err(1, "\"\xc2\"");
    try err(1, "\"\xdf\"");
    try err(1, "\"\xed\xa0\"");
    try err(1, "\"\xf0\x80\"");
    try err(1, "\"\xf0\x80\x80\"");
}

test "invalid continuation byte" {
    try err(1, "\"\xc2\x00\"");
    try err(1, "\"\xc2\x7f\"");
    try err(1, "\"\xc2\xc0\"");
    try err(1, "\"\xc3\xc1\"");
    try err(1, "\"\xc4\xf5\"");
    try err(1, "\"\xc5\xff\"");
    try err(1, "\"\xe4\x80\x00\"");
    try err(1, "\"\xe5\x80\x10\"");
    try err(1, "\"\xe6\x80\xc0\"");
    try err(1, "\"\xe7\x80\xf5\"");
    try err(1, "\"\xe8\x00\x80\"");
    try err(1, "\"\xf2\x00\x80\x80\"");
    try err(1, "\"\xf0\x80\x00\x80\"");
    try err(1, "\"\xf1\x80\xc0\x80\"");
    try err(1, "\"\xf2\x80\x80\x00\"");
    try err(1, "\"\xf3\x80\x80\xc0\"");
    try err(1, "\"\xf4\x80\x80\xf5\"");
}

test "disallowed overlong form" {
    try err(1, "\"\xc0\x80\"");
    try err(1, "\"\xc0\x90\"");
    try err(1, "\"\xc1\x80\"");
    try err(1, "\"\xc1\x90\"");
    try err(1, "\"\xe0\x80\x80\"");
    try err(1, "\"\xf0\x80\x80\x80\"");
}

test "out of UTF-16 range" {
    try err(1, "\"\xf4\x90\x80\x80\"");
    try err(1, "\"\xf5\x80\x80\x80\"");
    try err(1, "\"\xf6\x80\x80\x80\"");
    try err(1, "\"\xf7\x80\x80\x80\"");
    try err(1, "\"\xf8\x80\x80\x80\"");
    try err(1, "\"\xf9\x80\x80\x80\"");
    try err(1, "\"\xfa\x80\x80\x80\"");
    try err(1, "\"\xfb\x80\x80\x80\"");
    try err(1, "\"\xfc\x80\x80\x80\"");
    try err(1, "\"\xfd\x80\x80\x80\"");
    try err(1, "\"\xfe\x80\x80\x80\"");
    try err(1, "\"\xff\x80\x80\x80\"");
}
