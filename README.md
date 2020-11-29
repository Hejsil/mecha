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

fn toByte(v: u4) u8 {
    return (@as(u8, v) * 0x10) + v;
}

const hex1 = as(u8, toByte, int(u4, 16));
const hex2 = int(u8, 16);
const rgb1 = as(Rgb, toStruct(Rgb), manyN(3, hex1));
const rgb2 = as(Rgb, toStruct(Rgb), manyN(3, hex2));
const rgb = combine(.{
    char('#'),
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

