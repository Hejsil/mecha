# Mecha

A parser combinator library for the [`Zig`](https://ziglang.org/)
programming language. Time to make your own parser mech!
![mech](https://thumbs.gfycat.com/GrippingElatedAzurevasesponge-size_restricted.gif)

```zig
const std = @import("std");
const testing = std.testing;

usingnamespace @import("mecha");

const Rgb = struct {
    r: u8,
    g: u8,
    b: u8,
};

fn toRgb(tuple: var) ?Rgb {
    return Rgb{
        .r = tuple.at(0).*,
        .g = tuple.at(1).*,
        .b = tuple.at(2).*,
    };
}

const hex = digit(16);
const hex2 = convert(u8, toInt(u8, 16), manyRange(2, 2, hex));
const rgb = convert(Rgb, toRgb, combine(.{ char('#'), hex2, hex2, hex2 }));

test "rgb" {
    const a = rgb("#aabbcc").?.value;
    testing.expectEqual(@as(u8, 0xaa), a.r);
    testing.expectEqual(@as(u8, 0xbb), a.g);
    testing.expectEqual(@as(u8, 0xcc), a.b);
}
```

