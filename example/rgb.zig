const std = @import("std");

usingnamespace @import("mecha");

const Rgb = struct {
    r: u8,
    g: u8,
    b: u8,
};

fn toByte(v: u4) u8 {
    return @as(u8, v) * 0x10 + v;
}

const hex1 = map(u8, toByte, int(u4, .{
    .parse_sign = false,
    .base = 16,
    .max_digits = 1,
}));
const hex2 = int(u8, .{
    .parse_sign = false,
    .base = 16,
    .max_digits = 2,
});
const rgb1 = map(Rgb, toStruct(Rgb), manyN(hex1, 3, .{}));
const rgb2 = map(Rgb, toStruct(Rgb), manyN(hex2, 3, .{}));
const rgb = combine(.{
    ascii.char('#'),
    oneOf(.{
        rgb2,
        rgb1,
    }),
});

test "rgb" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const a = (try rgb(allocator, "#aabbcc")).value;
    try testing.expectEqual(@as(u8, 0xaa), a.r);
    try testing.expectEqual(@as(u8, 0xbb), a.g);
    try testing.expectEqual(@as(u8, 0xcc), a.b);

    const b = (try rgb(allocator, "#abc")).value;
    try testing.expectEqual(@as(u8, 0xaa), b.r);
    try testing.expectEqual(@as(u8, 0xbb), b.g);
    try testing.expectEqual(@as(u8, 0xcc), b.b);

    const c = (try rgb(allocator, "#000000")).value;
    try testing.expectEqual(@as(u8, 0), c.r);
    try testing.expectEqual(@as(u8, 0), c.g);
    try testing.expectEqual(@as(u8, 0), c.b);

    const d = (try rgb(allocator, "#000")).value;
    try testing.expectEqual(@as(u8, 0), d.r);
    try testing.expectEqual(@as(u8, 0), d.g);
    try testing.expectEqual(@as(u8, 0), d.b);
}
