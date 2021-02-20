const std = @import("std");
usingnamespace @import("mecha");

const testing = std.testing;
const builtin = std.builtin;

const json = combine(.{ ws, element });

const value = oneOf(.{
    object,
    array,
    jstring,
    number,
    jtrue,
    jfalse,
    jnull,
});

const members = combine(.{
    member,
    discard(many(combine(.{ comma, member }))),
});

const elements = combine(.{
    element,
    discard(many(combine(.{ comma, element }))),
});

const member = combine(.{ jstring, colon, element });
const object = combine(.{ lcurly, discard(opt(members)), rcurly });
const array = combine(.{ lbracket, discard(opt(elements)), rbracket });
const element = ref(valueRef);

fn valueRef() Parser(void) {
    return value;
}

const number = token(combine(.{ integer, fraction, exponent }));
const jstring = token(combine(.{ utf8.char('"'), chars, utf8.char('"') }));
const jtrue = token(string("true"));
const jfalse = token(string("false"));
const jnull = token(string("null"));
const lcurly = token(utf8.char('{'));
const rcurly = token(utf8.char('}'));
const lbracket = token(utf8.char('['));
const rbracket = token(utf8.char(']'));
const colon = token(utf8.char(':'));
const comma = token(utf8.char(','));

fn token(comptime parser: anytype) Parser(void) {
    return combine(.{ discard(parser), ws });
}

const chars = discard(many(char));

const char = oneOf(.{
    discard(utf8.range(0x0020, '"' - 1)),
    discard(utf8.range('"' + 1, '\\' - 1)),
    discard(utf8.range('\\' + 1, 0x10FFFF)),
    combine(.{ utf8.char('\\'), escape }),
});

const escape = oneOf(.{
    utf8.char('"'),
    utf8.char('\\'),
    utf8.char('/'),
    utf8.char('b'),
    utf8.char('f'),
    utf8.char('n'),
    utf8.char('r'),
    utf8.char('t'),
    combine(.{ utf8.char('u'), hex, hex, hex, hex }),
});

const hex = oneOf(.{
    jdigit,
    discard(utf8.range('a', 'f')),
    discard(utf8.range('A', 'F')),
});

const integer = oneOf(.{
    combine(.{ onenine, digits }),
    jdigit,
    combine(.{ utf8.char('-'), onenine, digits }),
    combine(.{ utf8.char('-'), jdigit }),
});

const digits = discard(manyRange(1, std.math.maxInt(usize), jdigit));

const jdigit = oneOf(.{
    utf8.char('0'),
    onenine,
});

const onenine = discard(utf8.range('1', '9'));

const fraction = discard(opt(
    combine(.{ utf8.char('.'), digits }),
));

const exponent = discard(opt(
    combine(.{ oneOf(.{ utf8.char('E'), utf8.char('e') }), sign, digits }),
));

const sign = discard(opt(oneOf(.{
    utf8.char('+'),
    utf8.char('-'),
})));

const ws = discard(many(oneOf(.{
    utf8.char(0x0020),
    utf8.char(0x000A),
    utf8.char(0x000D),
    utf8.char(0x0009),
})));

fn ok(comptime s: []const u8) void {
    const res = json(testing.allocator, s) catch @panic("test failure");
    testing.expectEqualStrings("", res.rest);
}

fn err(comptime s: []const u8) void {
    testing.expectError(error.ParserFailed, json(testing.allocator, s));
}

fn errNotAllParsed(comptime s: []const u8) void {
    const res = json(testing.allocator, s) catch @panic("test failure");
    testing.expect(res.rest.len != 0);
}

fn any(comptime s: []const u8) void {
    _ = json(testing.allocator, s) catch {};
}

////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Additional tests not part of test JSONTestSuite.

test "y_trailing_comma_after_empty" {
    ok(
        \\{"1":[],"2":{},"3":"4"}
    );
}

////////////////////////////////////////////////////////////////////////////////////////////////////

test "y_array_arraysWithSpaces" {
    ok(
        \\[[]   ]
    );
}

test "y_array_empty" {
    ok(
        \\[]
    );
}

test "y_array_empty-string" {
    ok(
        \\[""]
    );
}

test "y_array_ending_with_newline" {
    ok(
        \\["a"]
    );
}

test "y_array_false" {
    ok(
        \\[false]
    );
}

test "y_array_heterogeneous" {
    ok(
        \\[null, 1, "1", {}]
    );
}

test "y_array_null" {
    ok(
        \\[null]
    );
}

test "y_array_with_1_and_newline" {
    ok(
        \\[1
        \\]
    );
}

test "y_array_with_leading_space" {
    ok(
        \\ [1]
    );
}

test "y_array_with_several_null" {
    ok(
        \\[1,null,null,null,2]
    );
}

test "y_array_with_trailing_space" {
    ok("[2] ");
}

test "y_number_0e+1" {
    ok(
        \\[0e+1]
    );
}

test "y_number_0e1" {
    ok(
        \\[0e1]
    );
}

test "y_number_after_space" {
    ok(
        \\[ 4]
    );
}

test "y_number_double_close_to_zero" {
    ok(
        \\[-0.000000000000000000000000000000000000000000000000000000000000000000000000000001]
    );
}

test "y_number_int_with_exp" {
    ok(
        \\[20e1]
    );
}

test "y_number" {
    ok(
        \\[123e65]
    );
}

test "y_number_minus_zero" {
    ok(
        \\[-0]
    );
}

test "y_number_negative_int" {
    ok(
        \\[-123]
    );
}

test "y_number_negative_one" {
    ok(
        \\[-1]
    );
}

test "y_number_negative_zero" {
    ok(
        \\[-0]
    );
}

test "y_number_real_capital_e" {
    ok(
        \\[1E22]
    );
}

test "y_number_real_capital_e_neg_exp" {
    ok(
        \\[1E-2]
    );
}

test "y_number_real_capital_e_pos_exp" {
    ok(
        \\[1E+2]
    );
}

test "y_number_real_exponent" {
    ok(
        \\[123e45]
    );
}

test "y_number_real_fraction_exponent" {
    ok(
        \\[123.456e78]
    );
}

test "y_number_real_neg_exp" {
    ok(
        \\[1e-2]
    );
}

test "y_number_real_pos_exponent" {
    ok(
        \\[1e+2]
    );
}

test "y_number_simple_int" {
    ok(
        \\[123]
    );
}

test "y_number_simple_real" {
    ok(
        \\[123.456789]
    );
}

test "y_object_basic" {
    ok(
        \\{"asd":"sdf"}
    );
}

test "y_object_duplicated_key_and_value" {
    ok(
        \\{"a":"b","a":"b"}
    );
}

test "y_object_duplicated_key" {
    ok(
        \\{"a":"b","a":"c"}
    );
}

test "y_object_empty" {
    ok(
        \\{}
    );
}

test "y_object_empty_key" {
    ok(
        \\{"":0}
    );
}

test "y_object_escaped_null_in_key" {
    ok(
        \\{"foo\u0000bar": 42}
    );
}

test "y_object_extreme_numbers" {
    ok(
        \\{ "min": -1.0e+28, "max": 1.0e+28 }
    );
}

test "y_object" {
    ok(
        \\{"asd":"sdf", "dfg":"fgh"}
    );
}

test "y_object_long_strings" {
    ok(
        \\{"x":[{"id": "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"}], "id": "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"}
    );
}

test "y_object_simple" {
    ok(
        \\{"a":[]}
    );
}

test "y_object_string_unicode" {
    ok(
        \\{"title":"\u041f\u043e\u043b\u0442\u043e\u0440\u0430 \u0417\u0435\u043c\u043b\u0435\u043a\u043e\u043f\u0430" }
    );
}

test "y_object_with_newlines" {
    ok(
        \\{
        \\"a": "b"
        \\}
    );
}

test "y_string_1_2_3_bytes_UTF-8_sequences" {
    ok(
        \\["\u0060\u012a\u12AB"]
    );
}

test "y_string_accepted_surrogate_pair" {
    ok(
        \\["\uD801\udc37"]
    );
}

test "y_string_accepted_surrogate_pairs" {
    ok(
        \\["\ud83d\ude39\ud83d\udc8d"]
    );
}

test "y_string_allowed_escapes" {
    ok(
        \\["\"\\\/\b\f\n\r\t"]
    );
}

test "y_string_backslash_and_u_escaped_zero" {
    ok(
        \\["\\u0000"]
    );
}

test "y_string_backslash_doublequotes" {
    ok(
        \\["\""]
    );
}

test "y_string_comments" {
    ok(
        \\["a/*b*/c/*d//e"]
    );
}

test "y_string_double_escape_a" {
    ok(
        \\["\\a"]
    );
}

test "y_string_double_escape_n" {
    ok(
        \\["\\n"]
    );
}

test "y_string_escaped_control_character" {
    ok(
        \\["\u0012"]
    );
}

test "y_string_escaped_noncharacter" {
    ok(
        \\["\uFFFF"]
    );
}

test "y_string_in_array" {
    ok(
        \\["asd"]
    );
}

test "y_string_in_array_with_leading_space" {
    ok(
        \\[ "asd"]
    );
}

test "y_string_last_surrogates_1_and_2" {
    ok(
        \\["\uDBFF\uDFFF"]
    );
}

test "y_string_nbsp_uescaped" {
    ok(
        \\["new\u00A0line"]
    );
}

test "y_string_nonCharacterInUTF-8_U+10FFFF" {
    ok(
        \\["􏿿"]
    );
}

test "y_string_nonCharacterInUTF-8_U+FFFF" {
    ok(
        \\["￿"]
    );
}

test "y_string_null_escape" {
    ok(
        \\["\u0000"]
    );
}

test "y_string_one-byte-utf-8" {
    ok(
        \\["\u002c"]
    );
}

test "y_string_pi" {
    ok(
        \\["π"]
    );
}

test "y_string_reservedCharacterInUTF-8_U+1BFFF" {
    ok(
        \\["𛿿"]
    );
}

test "y_string_simple_ascii" {
    ok(
        \\["asd "]
    );
}

test "y_string_space" {
    ok(
        \\" "
    );
}

test "y_string_surrogates_U+1D11E_MUSICAL_SYMBOL_G_CLEF" {
    ok(
        \\["\uD834\uDd1e"]
    );
}

test "y_string_three-byte-utf-8" {
    ok(
        \\["\u0821"]
    );
}

test "y_string_two-byte-utf-8" {
    ok(
        \\["\u0123"]
    );
}

test "y_string_u+2028_line_sep" {
    ok("[\"\xe2\x80\xa8\"]");
}

test "y_string_u+2029_par_sep" {
    ok("[\"\xe2\x80\xa9\"]");
}

test "y_string_uescaped_newline" {
    ok(
        \\["new\u000Aline"]
    );
}

test "y_string_uEscape" {
    ok(
        \\["\u0061\u30af\u30EA\u30b9"]
    );
}

test "y_string_unescaped_char_delete" {
    ok("[\"\x7f\"]");
}

test "y_string_unicode_2" {
    ok(
        \\["⍂㈴⍂"]
    );
}

test "y_string_unicodeEscapedBackslash" {
    ok(
        \\["\u005C"]
    );
}

test "y_string_unicode_escaped_double_quote" {
    ok(
        \\["\u0022"]
    );
}

test "y_string_unicode" {
    ok(
        \\["\uA66D"]
    );
}

test "y_string_unicode_U+10FFFE_nonchar" {
    ok(
        \\["\uDBFF\uDFFE"]
    );
}

test "y_string_unicode_U+1FFFE_nonchar" {
    ok(
        \\["\uD83F\uDFFE"]
    );
}

test "y_string_unicode_U+200B_ZERO_WIDTH_SPACE" {
    ok(
        \\["\u200B"]
    );
}

test "y_string_unicode_U+2064_invisible_plus" {
    ok(
        \\["\u2064"]
    );
}

test "y_string_unicode_U+FDD0_nonchar" {
    ok(
        \\["\uFDD0"]
    );
}

test "y_string_unicode_U+FFFE_nonchar" {
    ok(
        \\["\uFFFE"]
    );
}

test "y_string_utf8" {
    ok(
        \\["€𝄞"]
    );
}

test "y_string_with_del_character" {
    ok("[\"a\x7fa\"]");
}

test "y_structure_lonely_false" {
    ok(
        \\false
    );
}

test "y_structure_lonely_int" {
    ok(
        \\42
    );
}

test "y_structure_lonely_negative_real" {
    ok(
        \\-0.1
    );
}

test "y_structure_lonely_null" {
    ok(
        \\null
    );
}

test "y_structure_lonely_string" {
    ok(
        \\"asd"
    );
}

test "y_structure_lonely_true" {
    ok(
        \\true
    );
}

test "y_structure_string_empty" {
    ok(
        \\""
    );
}

test "y_structure_trailing_newline" {
    ok(
        \\["a"]
    );
}

test "y_structure_true_in_array" {
    ok(
        \\[true]
    );
}

test "y_structure_whitespace_array" {
    ok(" [] ");
}

////////////////////////////////////////////////////////////////////////////////////////////////////

test "n_array_1_true_without_comma" {
    err(
        \\[1 true]
    );
}

test "n_array_a_invalid_utf8" {
    err(
        \\[aå]
    );
}

test "n_array_colon_instead_of_comma" {
    err(
        \\["": 1]
    );
}

test "n_array_comma_after_close" {
    errNotAllParsed(
        \\[""],
    );
}

test "n_array_comma_and_number" {
    err(
        \\[,1]
    );
}

test "n_array_double_comma" {
    err(
        \\[1,,2]
    );
}

test "n_array_double_extra_comma" {
    err(
        \\["x",,]
    );
}

test "n_array_extra_close" {
    errNotAllParsed(
        \\["x"]]
    );
}

test "n_array_extra_comma" {
    err(
        \\["",]
    );
}

test "n_array_incomplete_invalid_value" {
    err(
        \\[x
    );
}

test "n_array_incomplete" {
    err(
        \\["x"
    );
}

test "n_array_inner_array_no_comma" {
    err(
        \\[3[4]]
    );
}

test "n_array_invalid_utf8" {
    err(
        \\[ÿ]
    );
}

test "n_array_items_separated_by_semicolon" {
    err(
        \\[1:2]
    );
}

test "n_array_just_comma" {
    err(
        \\[,]
    );
}

test "n_array_just_minus" {
    err(
        \\[-]
    );
}

test "n_array_missing_value" {
    err(
        \\[   , ""]
    );
}

test "n_array_newlines_unclosed" {
    err(
        \\["a",
        \\4
        \\,1,
    );
}

test "n_array_number_and_comma" {
    err(
        \\[1,]
    );
}

test "n_array_number_and_several_commas" {
    err(
        \\[1,,]
    );
}

test "n_array_spaces_vertical_tab_formfeed" {
    err("[\"\x0aa\"\\f]");
}

test "n_array_star_inside" {
    err(
        \\[*]
    );
}

test "n_array_unclosed" {
    err(
        \\[""
    );
}

test "n_array_unclosed_trailing_comma" {
    err(
        \\[1,
    );
}

test "n_array_unclosed_with_new_lines" {
    err(
        \\[1,
        \\1
        \\,1
    );
}

test "n_array_unclosed_with_object_inside" {
    err(
        \\[{}
    );
}

test "n_incomplete_false" {
    err(
        \\[fals]
    );
}

test "n_incomplete_null" {
    err(
        \\[nul]
    );
}

test "n_incomplete_true" {
    err(
        \\[tru]
    );
}

test "n_multidigit_number_then_00" {
    errNotAllParsed("123\x00");
}

test "n_number_0.1.2" {
    err(
        \\[0.1.2]
    );
}

test "n_number_-01" {
    err(
        \\[-01]
    );
}

test "n_number_0.3e" {
    err(
        \\[0.3e]
    );
}

test "n_number_0.3e+" {
    err(
        \\[0.3e+]
    );
}

test "n_number_0_capital_E" {
    err(
        \\[0E]
    );
}

test "n_number_0_capital_E+" {
    err(
        \\[0E+]
    );
}

test "n_number_0.e1" {
    err(
        \\[0.e1]
    );
}

test "n_number_0e" {
    err(
        \\[0e]
    );
}

test "n_number_0e+" {
    err(
        \\[0e+]
    );
}

test "n_number_1_000" {
    err(
        \\[1 000.0]
    );
}

test "n_number_1.0e-" {
    err(
        \\[1.0e-]
    );
}

test "n_number_1.0e" {
    err(
        \\[1.0e]
    );
}

test "n_number_1.0e+" {
    err(
        \\[1.0e+]
    );
}

test "n_number_-1.0." {
    err(
        \\[-1.0.]
    );
}

test "n_number_1eE2" {
    err(
        \\[1eE2]
    );
}

test "n_number_.-1" {
    err(
        \\[.-1]
    );
}

test "n_number_+1" {
    err(
        \\[+1]
    );
}

test "n_number_.2e-3" {
    err(
        \\[.2e-3]
    );
}

test "n_number_2.e-3" {
    err(
        \\[2.e-3]
    );
}

test "n_number_2.e+3" {
    err(
        \\[2.e+3]
    );
}

test "n_number_2.e3" {
    err(
        \\[2.e3]
    );
}

test "n_number_-2." {
    err(
        \\[-2.]
    );
}

test "n_number_9.e+" {
    err(
        \\[9.e+]
    );
}

test "n_number_expression" {
    err(
        \\[1+2]
    );
}

test "n_number_hex_1_digit" {
    err(
        \\[0x1]
    );
}

test "n_number_hex_2_digits" {
    err(
        \\[0x42]
    );
}

test "n_number_infinity" {
    err(
        \\[Infinity]
    );
}

test "n_number_+Inf" {
    err(
        \\[+Inf]
    );
}

test "n_number_Inf" {
    err(
        \\[Inf]
    );
}

test "n_number_invalid+-" {
    err(
        \\[0e+-1]
    );
}

test "n_number_invalid-negative-real" {
    err(
        \\[-123.123foo]
    );
}

test "n_number_invalid-utf-8-in-bigger-int" {
    err(
        \\[123å]
    );
}

test "n_number_invalid-utf-8-in-exponent" {
    err(
        \\[1e1å]
    );
}

test "n_number_invalid-utf-8-in-int" {
    err(
        \\[0å]
    );
}

test "n_number_++" {
    err(
        \\[++1234]
    );
}

test "n_number_minus_infinity" {
    err(
        \\[-Infinity]
    );
}

test "n_number_minus_sign_with_trailing_garbage" {
    err(
        \\[-foo]
    );
}

test "n_number_minus_space_1" {
    err(
        \\[- 1]
    );
}

test "n_number_-NaN" {
    err(
        \\[-NaN]
    );
}

test "n_number_NaN" {
    err(
        \\[NaN]
    );
}

test "n_number_neg_int_starting_with_zero" {
    err(
        \\[-012]
    );
}

test "n_number_neg_real_without_int_part" {
    err(
        \\[-.123]
    );
}

test "n_number_neg_with_garbage_at_end" {
    err(
        \\[-1x]
    );
}

test "n_number_real_garbage_after_e" {
    err(
        \\[1ea]
    );
}

test "n_number_real_with_invalid_utf8_after_e" {
    err(
        \\[1eå]
    );
}

test "n_number_real_without_fractional_part" {
    err(
        \\[1.]
    );
}

test "n_number_starting_with_dot" {
    err(
        \\[.123]
    );
}

test "n_number_U+FF11_fullwidth_digit_one" {
    err(
        \\[ï¼]
    );
}

test "n_number_with_alpha_char" {
    err(
        \\[1.8011670033376514H-308]
    );
}

test "n_number_with_alpha" {
    err(
        \\[1.2a-3]
    );
}

test "n_number_with_leading_zero" {
    err(
        \\[012]
    );
}

test "n_object_bad_value" {
    err(
        \\["x", truth]
    );
}

test "n_object_bracket_key" {
    err(
        \\{[: "x"}
    );
}

test "n_object_comma_instead_of_colon" {
    err(
        \\{"x", null}
    );
}

test "n_object_double_colon" {
    err(
        \\{"x"::"b"}
    );
}

test "n_object_emoji" {
    err(
        \\{ð¨ð­}
    );
}

test "n_object_garbage_at_end" {
    err(
        \\{"a":"a" 123}
    );
}

test "n_object_key_with_single_quotes" {
    err(
        \\{key: 'value'}
    );
}

test "n_object_lone_continuation_byte_in_key_and_trailing_comma" {
    err(
        \\{"¹":"0",}
    );
}

test "n_object_missing_colon" {
    err(
        \\{"a" b}
    );
}

test "n_object_missing_key" {
    err(
        \\{:"b"}
    );
}

test "n_object_missing_semicolon" {
    err(
        \\{"a" "b"}
    );
}

test "n_object_missing_value" {
    err(
        \\{"a":
    );
}

test "n_object_no-colon" {
    err(
        \\{"a"
    );
}

test "n_object_non_string_key_but_huge_number_instead" {
    err(
        \\{9999E9999:1}
    );
}

test "n_object_non_string_key" {
    err(
        \\{1:1}
    );
}

test "n_object_repeated_null_null" {
    err(
        \\{null:null,null:null}
    );
}

test "n_object_several_trailing_commas" {
    err(
        \\{"id":0,,,,,}
    );
}

test "n_object_single_quote" {
    err(
        \\{'a':0}
    );
}

test "n_object_trailing_comma" {
    err(
        \\{"id":0,}
    );
}

test "n_object_trailing_comment" {
    errNotAllParsed(
        \\{"a":"b"}/**/
    );
}

test "n_object_trailing_comment_open" {
    errNotAllParsed(
        \\{"a":"b"}/**//
    );
}

test "n_object_trailing_comment_slash_open_incomplete" {
    errNotAllParsed(
        \\{"a":"b"}/
    );
}

test "n_object_trailing_comment_slash_open" {
    errNotAllParsed(
        \\{"a":"b"}//
    );
}

test "n_object_two_commas_in_a_row" {
    err(
        \\{"a":"b",,"c":"d"}
    );
}

test "n_object_unquoted_key" {
    err(
        \\{a: "b"}
    );
}

test "n_object_unterminated-value" {
    err(
        \\{"a":"a
    );
}

test "n_object_with_single_string" {
    err(
        \\{ "foo" : "bar", "a" }
    );
}

test "n_object_with_trailing_garbage" {
    errNotAllParsed(
        \\{"a":"b"}#
    );
}

test "n_single_space" {
    err(" ");
}

test "n_string_1_surrogate_then_escape" {
    err(
        \\["\uD800\"]
    );
}

test "n_string_1_surrogate_then_escape_u1" {
    err(
        \\["\uD800\u1"]
    );
}

test "n_string_1_surrogate_then_escape_u1x" {
    err(
        \\["\uD800\u1x"]
    );
}

test "n_string_1_surrogate_then_escape_u" {
    err(
        \\["\uD800\u"]
    );
}

test "n_string_accentuated_char_no_quotes" {
    err(
        \\[Ã©]
    );
}

test "n_string_backslash_00" {
    err("[\"\x00\"]");
}

test "n_string_escaped_backslash_bad" {
    err(
        \\["\\\"]
    );
}

test "n_string_escaped_ctrl_char_tab" {
    err("\x5b\x22\x5c\x09\x22\x5d");
}

test "n_string_escaped_emoji" {
    err("[\"\x5c\xc3\xb0\xc2\x9f\xc2\x8c\xc2\x80\"]");
}

test "n_string_escape_x" {
    err(
        \\["\x00"]
    );
}

test "n_string_incomplete_escaped_character" {
    err(
        \\["\u00A"]
    );
}

test "n_string_incomplete_escape" {
    err(
        \\["\"]
    );
}

test "n_string_incomplete_surrogate_escape_invalid" {
    err(
        \\["\uD800\uD800\x"]
    );
}

test "n_string_incomplete_surrogate" {
    err(
        \\["\uD834\uDd"]
    );
}

test "n_string_invalid_backslash_esc" {
    err(
        \\["\a"]
    );
}

test "n_string_invalid_unicode_escape" {
    err(
        \\["\uqqqq"]
    );
}

test "n_string_invalid_utf8_after_escape" {
    err("[\"\\\x75\xc3\xa5\"]");
}

test "n_string_invalid-utf-8-in-escape" {
    err(
        \\["\uå"]
    );
}

test "n_string_leading_uescaped_thinspace" {
    err(
        \\[\u0020"asd"]
    );
}

test "n_string_no_quotes_with_bad_escape" {
    err(
        \\[\n]
    );
}

test "n_string_single_doublequote" {
    err(
        \\"
    );
}

test "n_string_single_quote" {
    err(
        \\['single quote']
    );
}

test "n_string_single_string_no_double_quotes" {
    err(
        \\abc
    );
}

test "n_string_start_escape_unclosed" {
    err(
        \\["\
    );
}

test "n_string_unescaped_crtl_char" {
    err("[\"a\x00a\"]");
}

test "n_string_unescaped_newline" {
    err(
        \\["new
        \\line"]
    );
}

test "n_string_unescaped_tab" {
    err("[\"\t\"]");
}

test "n_string_unicode_CapitalU" {
    err(
        \\"\UA66D"
    );
}

test "n_string_with_trailing_garbage" {
    errNotAllParsed(
        \\""x
    );
}

test "n_structure_100000_opening_arrays" {
    return error.SkipZigTest;
    // err("[" ** 100000);
}

test "n_structure_angle_bracket_." {
    err(
        \\<.>
    );
}

test "n_structure_angle_bracket_null" {
    err(
        \\[<null>]
    );
}

test "n_structure_array_trailing_garbage" {
    errNotAllParsed(
        \\[1]x
    );
}

test "n_structure_array_with_extra_array_close" {
    errNotAllParsed(
        \\[1]]
    );
}

test "n_structure_array_with_unclosed_string" {
    err(
        \\["asd]
    );
}

test "n_structure_ascii-unicode-identifier" {
    err(
        \\aÃ¥
    );
}

test "n_structure_capitalized_True" {
    err(
        \\[True]
    );
}

test "n_structure_close_unopened_array" {
    errNotAllParsed(
        \\1]
    );
}

test "n_structure_comma_instead_of_closing_brace" {
    err(
        \\{"x": true,
    );
}

test "n_structure_double_array" {
    errNotAllParsed(
        \\[][]
    );
}

test "n_structure_end_array" {
    err(
        \\]
    );
}

test "n_structure_incomplete_UTF8_BOM" {
    err(
        \\ï»{}
    );
}

test "n_structure_lone-invalid-utf-8" {
    err(
        \\å
    );
}

test "n_structure_lone-open-bracket" {
    err(
        \\[
    );
}

test "n_structure_no_data" {
    err(
        \\
    );
}

test "n_structure_null-byte-outside-string" {
    err("[\x00]");
}

test "n_structure_number_with_trailing_garbage" {
    errNotAllParsed(
        \\2@
    );
}

test "n_structure_object_followed_by_closing_object" {
    errNotAllParsed(
        \\{}}
    );
}

test "n_structure_object_unclosed_no_value" {
    err(
        \\{"":
    );
}

test "n_structure_object_with_comment" {
    err(
        \\{"a":/*comment*/"b"}
    );
}

test "n_structure_object_with_trailing_garbage" {
    errNotAllParsed(
        \\{"a": true} "x"
    );
}

test "n_structure_open_array_apostrophe" {
    err(
        \\['
    );
}

test "n_structure_open_array_comma" {
    err(
        \\[,
    );
}

test "n_structure_open_array_object" {
    return error.SkipZigTest;
    // err("[{\"\":" ** 50000);
}

test "n_structure_open_array_open_object" {
    err(
        \\[{
    );
}

test "n_structure_open_array_open_string" {
    err(
        \\["a
    );
}

test "n_structure_open_array_string" {
    err(
        \\["a"
    );
}

test "n_structure_open_object_close_array" {
    err(
        \\{]
    );
}

test "n_structure_open_object_comma" {
    err(
        \\{,
    );
}

test "n_structure_open_object" {
    err(
        \\{
    );
}

test "n_structure_open_object_open_array" {
    err(
        \\{[
    );
}

test "n_structure_open_object_open_string" {
    err(
        \\{"a
    );
}

test "n_structure_open_object_string_with_apostrophes" {
    err(
        \\{'a'
    );
}

test "n_structure_open_open" {
    err(
        \\["\{["\{["\{["\{
    );
}

test "n_structure_single_eacute" {
    err(
        \\é
    );
}

test "n_structure_single_star" {
    err(
        \\*
    );
}

test "n_structure_trailing_#" {
    errNotAllParsed(
        \\{"a":"b"}#{}
    );
}

test "n_structure_U+2060_word_joined" {
    err(
        \\[â ]
    );
}

test "n_structure_uescaped_LF_before_string" {
    err(
        \\[\u000A""]
    );
}

test "n_structure_unclosed_array" {
    err(
        \\[1
    );
}

test "n_structure_unclosed_array_partial_null" {
    err(
        \\[ false, nul
    );
}

test "n_structure_unclosed_array_unfinished_false" {
    err(
        \\[ true, fals
    );
}

test "n_structure_unclosed_array_unfinished_true" {
    err(
        \\[ false, tru
    );
}

test "n_structure_unclosed_object" {
    err(
        \\{"asd":"asd"
    );
}

test "n_structure_unicode-identifier" {
    err(
        \\Ã¥
    );
}

test "n_structure_UTF8_BOM_no_data" {
    err(
        \\ï»¿
    );
}

test "n_structure_whitespace_formfeed" {
    err("[\x0c]");
}

test "n_structure_whitespace_U+2060_word_joiner" {
    err(
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
    err("\"\xc2\"");
    err("\"\xdf\"");
    err("\"\xed\xa0\"");
    err("\"\xf0\x80\"");
    err("\"\xf0\x80\x80\"");
}

test "invalid continuation byte" {
    err("\"\xc2\x00\"");
    err("\"\xc2\x7f\"");
    err("\"\xc2\xc0\"");
    err("\"\xc3\xc1\"");
    err("\"\xc4\xf5\"");
    err("\"\xc5\xff\"");
    err("\"\xe4\x80\x00\"");
    err("\"\xe5\x80\x10\"");
    err("\"\xe6\x80\xc0\"");
    err("\"\xe7\x80\xf5\"");
    err("\"\xe8\x00\x80\"");
    err("\"\xf2\x00\x80\x80\"");
    err("\"\xf0\x80\x00\x80\"");
    err("\"\xf1\x80\xc0\x80\"");
    err("\"\xf2\x80\x80\x00\"");
    err("\"\xf3\x80\x80\xc0\"");
    err("\"\xf4\x80\x80\xf5\"");
}

test "disallowed overlong form" {
    err("\"\xc0\x80\"");
    err("\"\xc0\x90\"");
    err("\"\xc1\x80\"");
    err("\"\xc1\x90\"");
    err("\"\xe0\x80\x80\"");
    err("\"\xf0\x80\x80\x80\"");
}

test "out of UTF-16 range" {
    err("\"\xf4\x90\x80\x80\"");
    err("\"\xf5\x80\x80\x80\"");
    err("\"\xf6\x80\x80\x80\"");
    err("\"\xf7\x80\x80\x80\"");
    err("\"\xf8\x80\x80\x80\"");
    err("\"\xf9\x80\x80\x80\"");
    err("\"\xfa\x80\x80\x80\"");
    err("\"\xfb\x80\x80\x80\"");
    err("\"\xfc\x80\x80\x80\"");
    err("\"\xfd\x80\x80\x80\"");
    err("\"\xfe\x80\x80\x80\"");
    err("\"\xff\x80\x80\x80\"");
}
