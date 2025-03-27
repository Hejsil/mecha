# Mecha

A parser combinator library for the [`Zig`](https://ziglang.org/)
programming language. Time to make your own parser mech!

```zig
const mecha = @import("mecha");
const std = @import("std");

const Rgb = struct {
    r: u8,
    g: u8,
    b: u8,
};

fn toByte(v: u4) u8 {
    return @as(u8, v) * 0x10 + v;
}

const hex1 = mecha.int(u4, .{
    .parse_sign = false,
    .base = 16,
    .max_digits = 1,
}).map(toByte);
const hex2 = mecha.int(u8, .{
    .parse_sign = false,
    .base = 16,
    .max_digits = 2,
});
const rgb1 = mecha.manyN(hex1, 3, .{}).map(mecha.toStruct(Rgb));
const rgb2 = mecha.manyN(hex2, 3, .{}).map(mecha.toStruct(Rgb));
const rgb = mecha.combine(.{
    mecha.ascii.char('#').discard(),
    mecha.oneOf(.{ rgb2, rgb1 }),
});

test "rgb" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const a = (try rgb.parse(allocator, "#aabbcc")).value.ok;
    try testing.expectEqual(@as(u8, 0xaa), a.r);
    try testing.expectEqual(@as(u8, 0xbb), a.g);
    try testing.expectEqual(@as(u8, 0xcc), a.b);

    const b = (try rgb.parse(allocator, "#abc")).value.ok;
    try testing.expectEqual(@as(u8, 0xaa), b.r);
    try testing.expectEqual(@as(u8, 0xbb), b.g);
    try testing.expectEqual(@as(u8, 0xcc), b.b);

    const c = (try rgb.parse(allocator, "#000000")).value.ok;
    try testing.expectEqual(@as(u8, 0), c.r);
    try testing.expectEqual(@as(u8, 0), c.g);
    try testing.expectEqual(@as(u8, 0), c.b);

    const d = (try rgb.parse(allocator, "#000")).value.ok;
    try testing.expectEqual(@as(u8, 0), d.r);
    try testing.expectEqual(@as(u8, 0), d.g);
    try testing.expectEqual(@as(u8, 0), d.b);
}
```


## Installation

Developers tend to either use
* The latest tagged release of Zig
* The latest build of Zigs master branch

Depending on which developer you are, you need to run different `zig fetch` commands:

```sh
# Version of mecha that works with a tagged release of Zig
# Replace `<REPLACE ME>` with the version of mecha that you want to use
# See: https://github.com/Hejsil/mecha/releases
zig fetch --save https://github.com/Hejsil/mecha/archive/refs/tags/<REPLACE ME>.tar.gz

# Version of mecha that works with latest build of Zigs master branch
zig fetch --save git+https://github.com/Hejsil/mecha
```

Then add the following to `build.zig`:

```zig
const mecha = b.dependency("mecha", .{});
exe.root_module.addImport("mecha", clap.module("mecha"));
```

