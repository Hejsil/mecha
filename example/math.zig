const mecha = @import("mecha");
const std = @import("std");
const testing = std.testing;

// expr := expr + part
//      |  expr - part
//      |  part;

// part := part * num
//      |  part / num
//      |  num

const Expr = struct {
    left: i32,
    op: u8,
    right: i32,
};

const num = mecha.int(i32, .{ .base = 10, .max_digits = 10 });

const add = mecha.ascii.char('+');
const sub = mecha.ascii.char('-');
const mul = mecha.ascii.char('*');
const div = mecha.ascii.char('/');

fn exprRef() mecha.Parser(i32) {
    return expr;
}
const expr_ref = mecha.ref(exprRef);

const expr = mecha.oneOf(.{
    mecha.combine(.{ expr_ref, add, part_ref })
        .map(mecha.toStruct(Expr))
        .map(toResult),
    mecha.combine(.{ expr_ref, sub, part_ref })
        .map(mecha.toStruct(Expr))
        .map(toResult),
    part_ref,
});

fn partRef() mecha.Parser(i32) {
    return part;
}

const part_ref = mecha.ref(partRef);

const part = mecha.oneOf(.{
    mecha.combine(.{ part_ref, mul, num })
        .map(mecha.toStruct(Expr))
        .map(toResult),
    mecha.combine(.{ part_ref, div, num })
        .map(mecha.toStruct(Expr))
        .map(toResult),
    num,
});

pub fn toResult(pexpr: Expr) i32 {
    return switch (pexpr.op) {
        '+' => pexpr.left + pexpr.right,
        '-' => pexpr.left - pexpr.right,
        '*' => pexpr.left * pexpr.right,
        '/' => @divTrunc(pexpr.left, pexpr.right),
        else => unreachable,
    };
}

const parser = expr_ref;

pub fn parseExpression(allocator: std.mem.Allocator, input: []const u8) !i32 {
    const result = try parser.parse(allocator, input);
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
    const allocator = testing.allocator;
    try testing.expectEqual(@as(i32, 42), try parseExpression(allocator, "42"));
    try testing.expectEqual(@as(i32, 0), try parseExpression(allocator, "0"));
    try testing.expectEqual(@as(i32, 123), try parseExpression(allocator, "123"));
}

test "simple calc" {
    const allocator = testing.allocator;
    try testing.expectEqual(@as(i32, 3), try parseExpression(allocator, "1+2"));
    try testing.expectEqual(@as(i32, 2), try parseExpression(allocator, "3-1"));
    try testing.expectEqual(@as(i32, 2), try parseExpression(allocator, "4/2"));
    try testing.expectEqual(@as(i32, 10), try parseExpression(allocator, "5*2"));
}

test "operator priority" {
    const allocator = testing.allocator;
    try testing.expectEqual(@as(i32, 7), try parseExpression(allocator, "1+3*2"));
    try testing.expectEqual(@as(i32, 7), try parseExpression(allocator, "3*2+1"));
}
