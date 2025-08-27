const mecha = @import("mecha");
const std = @import("std");

// expr := expr + expr
//      |  expr - expr
//      |  part;

// part := part * part
//      |  part / part
//      |  num

const Expr = struct {
    left: i32,
    op: u8,
    right: i32,
};

const num = mecha.int(i32, .{ .base = 10 });

const add_sub = mecha.oneOf(.{
    mecha.ascii.char('+'),
    mecha.ascii.char('-'),
});
const mul_div = mecha.oneOf(.{
    mecha.ascii.char('*'),
    mecha.ascii.char('/'),
});

const expr = mecha.recursiveRef(struct {
    fn f(comptime _expr: anytype) mecha.Parser(i32) {
        return mecha.oneOf(.{
            mecha.combine(.{ _expr, add_sub, part }).map(toResult),
            part,
        });
    }
}.f);

const part = mecha.recursiveRef(struct {
    fn f(comptime _part: anytype) mecha.Parser(i32) {
        return mecha.oneOf(.{
            mecha.combine(.{ _part, mul_div, atom }).map(toResult),
            atom,
        });
    }
}.f);

const atom = mecha.oneOf(.{
    mecha.combine(.{
        mecha.ascii.char('(').discard(),
        expr,
        mecha.ascii.char(')').discard(),
    }),
    num,
});

pub fn toResult(pexpr: anytype) i32 {
    const s = mecha.toStruct(Expr)(pexpr);
    return switch (s.op) {
        '+' => s.left + s.right,
        '-' => s.left - s.right,
        '*' => s.left * s.right,
        '/' => @divTrunc(s.left, s.right),
        else => unreachable,
    };
}

pub fn parseExpression(allocator: std.mem.Allocator, input: []const u8) !i32 {
    const result = try expr.parse(allocator, input);
    switch (result.value) {
        .ok => |value| {
            if (result.index == input.len) {
                return value;
            } else {
                return error.PartialParse;
            }
        },
        .err => return error.ParseError,
    }
}

test "basic numbers" {
    const gpa = std.testing.allocator;
    try std.testing.expectEqual(@as(i32, 42), try parseExpression(gpa, "42"));
    try std.testing.expectEqual(@as(i32, 0), try parseExpression(gpa, "0"));
    try std.testing.expectEqual(@as(i32, 123), try parseExpression(gpa, "123"));
}

test "simple calc" {
    const gpa = std.testing.allocator;
    try std.testing.expectEqual(@as(i32, 3), try parseExpression(gpa, "1+2"));
    try std.testing.expectEqual(@as(i32, 2), try parseExpression(gpa, "3-1"));
    try std.testing.expectEqual(@as(i32, 2), try parseExpression(gpa, "4/2"));
    try std.testing.expectEqual(@as(i32, 10), try parseExpression(gpa, "5*2"));
}

test "operator priority" {
    const gpa = std.testing.allocator;
    try std.testing.expectEqual(@as(i32, 7), try parseExpression(gpa, "1+3*2"));
    try std.testing.expectEqual(@as(i32, 8), try parseExpression(gpa, "(1+3)*2"));
    try std.testing.expectEqual(@as(i32, 7), try parseExpression(gpa, "3*2+1"));
    try std.testing.expectEqual(@as(i32, 4), try parseExpression(gpa, "4/2*2"));
    try std.testing.expectEqual(@as(i32, 1), try parseExpression(gpa, "4/(2*2)"));
}
