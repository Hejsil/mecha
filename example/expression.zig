const mecha = @import("mecha");
const std = @import("std");

const testing = std.testing;
const expression = mecha.expression;

fn parserResult(comptime P: type) type {
    return switch (@typeInfo(P)) {
        .pointer => |p| p.child.T,
        else => P.T,
    };
}

const Ops = struct {
    fn add(a: i32, b: i32) i32 {
        return a + b;
    }

    fn sub(a: i32, b: i32) i32 {
        return a - b;
    }

    fn mul(a: i32, b: i32) i32 {
        return a * b;
    }

    fn div(a: i32, b: i32) i32 {
        return @divTrunc(a, b);
    }

    fn pow(a: i32, b: i32) i32 {
        return std.math.powi(i32, a, @intCast(b)) catch unreachable;
    }

    fn neg(v: i32) i32 {
        return -v;
    }

    fn inc(v: i32) i32 {
        return v + 1;
    }
};

const ws = mecha.ascii.char(' ').discard().many(.{ .collect = false }).discard();

fn token(comptime p: anytype) mecha.Parser(parserResult(@TypeOf(p))) {
    return mecha.combine(.{ ws, p, ws });
}

const num = token(mecha.int(i32, .{}));
const atom = num;

const prefix_ops = .{
    expression.BinaryOp(i32).withPrefix(token(mecha.ascii.char('-')).mapConst(&Ops.neg)),
};

const postfix_ops = .{
    expression.BinaryOp(i32).withPostfix(token(mecha.ascii.char('!')).mapConst(&Ops.inc)),
};

const power_ops = .{
    expression.addBinaryOp(token(mecha.ascii.char('^')).mapConst(&Ops.pow), .right),
};

const mul_div_ops = .{
    expression.addBinaryOp(token(mecha.ascii.char('*')).mapConst(&Ops.mul), .left),
    expression.addBinaryOp(token(mecha.ascii.char('/')).mapConst(&Ops.div), .left),
};

const add_sub_ops = .{
    expression.addBinaryOp(token(mecha.ascii.char('+')).mapConst(&Ops.add), .left),
    expression.addBinaryOp(token(mecha.ascii.char('-')).mapConst(&Ops.sub), .left),
};

const parser = expression.binaryOp(
    .{ prefix_ops, postfix_ops, power_ops, mul_div_ops, add_sub_ops },
    atom,
);

fn parseExpression(allocator: std.mem.Allocator, input: []const u8) !i32 {
    const result = try parser.parse(allocator, input);
    return switch (result.value) {
        .ok => |value| if (result.index == input.len) value else error.PartialParse,
        .err => error.ParseError,
    };
}

test "binaryOp basic" {
    const allocator = testing.allocator;

    try testing.expectEqual(@as(i32, 42), try parseExpression(allocator, "42"));
    try testing.expectEqual(@as(i32, 7), try parseExpression(allocator, "1 + 2 * 3"));
    try testing.expectEqual(@as(i32, 9), try parseExpression(allocator, "1 + 2 * 4"));
}

test "binaryOp prefix postfix" {
    const allocator = testing.allocator;

    try testing.expectEqual(@as(i32, -2), try parseExpression(allocator, "-3!"));
    try testing.expectEqual(@as(i32, 9), try parseExpression(allocator, "2! * 3"));
}

test "binaryOp right associative" {
    const allocator = testing.allocator;

    try testing.expectEqual(@as(i32, 512), try parseExpression(allocator, "2 ^ 3 ^ 2"));
}
