# Mecha

A parser combinator library for the [`Zig`](https://ziglang.org/)
programming language. Time to make your own parser mech!
![mech](https://thumbs.gfycat.com/GrippingElatedAzurevasesponge-size_restricted.gif)

```zig
const std = @import("std");

usingnamespace @import("mecha");

const Rgb = struct {
    r: u8,
    g: u8,
    b: u8,
};

fn toByte(v: u8) u8 {
    return v * 0x10 + v;
}

fn toByte2(v: [2]u8) u8 {
    return v[0] * 0x10 + v[1];
}

const hex = convert(u8, toInt(u8, 16), asStr(ascii.digit(16)));
const hex1 = map(u8, toByte, hex);
const hex2 = map(u8, toByte2, manyN(2, hex));
const rgb1 = map(Rgb, toStruct(Rgb), manyN(3, hex1));
const rgb2 = map(Rgb, toStruct(Rgb), manyN(3, hex2));
const rgb = combine(.{
    ascii.char('#'),
    oneOf(.{
        rgb2,
        rgb1,
    }),
});

test "rgb" {
    const a = rgb("#aabbcc").?.value;
    std.testing.expectEqual(@as(u8, 0xaa), a.r);
    std.testing.expectEqual(@as(u8, 0xbb), a.g);
    std.testing.expectEqual(@as(u8, 0xcc), a.b);

    const b = rgb("#abc").?.value;
    std.testing.expectEqual(@as(u8, 0xaa), b.r);
    std.testing.expectEqual(@as(u8, 0xbb), b.g);
    std.testing.expectEqual(@as(u8, 0xcc), b.b);
}

```

