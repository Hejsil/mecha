const std = @import("std");
usingnamespace @import("mecha");

const json = element;

fn valueRef() Parser(void) {
    return value;
}

const value = oneOf(.{
    object,
    array,
    string,
    number,
    string("true"),
    string("false"),
    string("null"),
});

const object = combine(.{
    char('{'),
    oneOf(.{ members, ws }),
    char('}'),
});

fn membersRef() Parser(void) {
    return members;
}

const members = oneOf(.{
    combine(.{ member, char(','), ref(membersRef) }),
    member,
});

const member = combine(.{ ws, jstring, ws, char(':'), element });

const array = combine(.{
    char('['),
    oneOf(.{ elements, ws }),
    char(']'),
});

fn elementsRef() Parser(void) {
    return members;
}

const elements = oneOf(.{
    combine(.{ element, char(','), ref(elementsRef) }),
    element,
});

fn elementRef() Parser(void) {
    return element;
}

const element = combine(.{ ws, ref(valueRef), ws });

const jstring = combine(.{ char('"'), characters, char('"') });

const characters = discard(many(character));

const character = oneOf(.{
    discard(range(0x0020, '"' - 1)),
    discard(range('"' + 1, '\\' - 1)),
    discard(range('\\' + 1, 0x10FFFF)),
    combine(.{ char('\\'), escape }),
});

const escape = oneOf(.{
    char('"'),
    char('\\'),
    char('/'),
    char('b'),
    char('f'),
    char('n'),
    char('r'),
    char('t'),
    combine(.{ char('u'), hex, hex, hex, hex }),
});

const hex = oneOf(.{
    jdigit,
    discard(range('a', 'f')),
    discard(range('A', 'F')),
});

const number = combine(.{ integer, fraction, exponent });

const integer = oneOf(.{
    combine(.{ onenine, digits }),
    jdigit,
    combine(.{ char('-'), jdigit }),
    combine(.{ char('-'), onenine, digits }),
});

const digits = discard(manyRange(1, std.math.maxInt(usize), jdigit));

const jdigit = oneOf(.{
    char('0'),
    onenine,
});

const onenine = discard(range('1', '9'));

const fraction = discard(opt(
    combine(.{ char('.'), digits }),
));

const exponent = opt(
    combine(.{ oneOf(.{ char('E'), char('e') }), sign, digits }),
);

const sign = discard(opt(oneOf(.{
    char('+'),
    char('-'),
})));

const ws = oneOf(.{
    char(0x0020),
    char(0x000A),
    char(0x000D),
    char(0x0009),
});

test "" {
    std.testing.expect(exponent(
        \\{
        \\    "a": null,
        \\}
    ) != null);
}
