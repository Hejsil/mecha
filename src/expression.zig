const mecha = @import("../mecha.zig");
const std = @import("std");

pub const Associativity = enum {
    left,
    right,
    none,
};

fn typecheckParser(comptime P: type) void {
    const err = "expected 'mecha.Parser(T)', found '" ++ @typeName(P) ++ "'";
    const PInner = switch (@typeInfo(P)) {
        .pointer => |info| info.child,
        else => P,
    };

    if (@typeInfo(PInner) != .@"struct") @compileError(err);
    if (!@hasDecl(PInner, "T")) @compileError(err);
    if (@TypeOf(PInner.T) != type) @compileError(err);
    if (PInner != mecha.Parser(PInner.T)) @compileError(err);
}

fn ParserResult(comptime P: type) type {
    return switch (@typeInfo(P)) {
        .pointer => |p| p.child.T,
        else => P.T,
    };
}

pub fn BinaryOp(comptime T: type) type {
    return union(enum) {
        prefix: mecha.Parser(*const fn (T) T),
        postfix: mecha.Parser(*const fn (T) T),
        infix: struct {
            parser: mecha.Parser(*const fn (T, T) T),
            associativity: Associativity,
        },

        pub fn withPrefix(parser: mecha.Parser(*const fn (T) T)) @This() {
            return .{ .prefix = parser };
        }

        pub fn withPostfix(parser: mecha.Parser(*const fn (T) T)) @This() {
            return .{ .postfix = parser };
        }

        pub fn withInfix(
            parser: mecha.Parser(*const fn (T, T) T),
            associativity: Associativity,
        ) @This() {
            return .{ .infix = .{ .parser = parser, .associativity = associativity } };
        }
    };
}

fn BinaryParserOperandType(comptime P: type) type {
    typecheckParser(P);
    const FnPtr = ParserResult(P);
    const Ptr = switch (@typeInfo(FnPtr)) {
        .pointer => |p| p,
        else => @compileError("binary operator parser must return '*const fn (T, T) T'"),
    };
    if (Ptr.size != .one or Ptr.is_const == false)
        @compileError("binary operator parser must return '*const fn (T, T) T'");

    const Fn = switch (@typeInfo(Ptr.child)) {
        .@"fn" => |f| f,
        else => @compileError("binary operator parser must return '*const fn (T, T) T'"),
    };
    if (Fn.params.len != 2)
        @compileError("binary operator parser must return '*const fn (T, T) T'");

    const lhs = Fn.params[0].type orelse @compileError("binary operator parser argument type cannot be inferred");
    const rhs = Fn.params[1].type orelse @compileError("binary operator parser argument type cannot be inferred");
    const ret = Fn.return_type orelse @compileError("binary operator parser return type cannot be inferred");

    if (lhs != rhs or lhs != ret)
        @compileError("binary operator parser must return '*const fn (T, T) T'");

    return lhs;
}

/// Creates an infix operator entry for use in `binaryOp` tables.
pub fn addBinaryOp(
    comptime parser: anytype,
    comptime associativity: Associativity,
) BinaryOp(BinaryParserOperandType(@TypeOf(parser))) {
    const T = BinaryParserOperandType(@TypeOf(parser));
    return BinaryOp(T).withInfix(parser, associativity);
}

/// Builds an expression parser from a Parsec-style operator table.
///
/// Operator table order is from highest precedence to lowest precedence.
pub fn binaryOp(comptime table: anytype, atom: anytype) mecha.Parser(ParserResult(@TypeOf(atom))) {
    typecheckParser(@TypeOf(atom));
    const T = ParserResult(@TypeOf(atom));
    const Res = mecha.Result(T);

    inline for (table) |level| {
        inline for (level) |op| {
            if (@TypeOf(op) != BinaryOp(T))
                @compileError("binaryOp table expects levels containing 'BinaryOp(" ++ @typeName(T) ++ ")'");
        }
    }

    return .{ .parse = struct {
        const InfixMatch = struct {
            index: usize,
            func: *const fn (T, T) T,
            associativity: Associativity,
        };

        const PrefixMatch = struct {
            index: usize,
            func: *const fn (T) T,
        };

        fn parse(allocator: std.mem.Allocator, str: []const u8) mecha.Error!Res {
            if (table.len == 0)
                return atom.parse(allocator, str);
            return parseLevel(table.len - 1, allocator, str);
        }

        fn parseLevel(comptime level_idx: usize, allocator: std.mem.Allocator, str: []const u8) mecha.Error!Res {
            const lhs = try parseTerm(level_idx, allocator, str);
            const left = switch (lhs.value) {
                .ok => |v| v,
                .err => return lhs,
            };
            const index = lhs.index;

            const infix = try parseInfix(level_idx, allocator, str[index..]);
            if (infix == null)
                return Res.ok(index, left);

            const first = infix.?;
            if (first.index == 0)
                return Res.err(index);

            return switch (first.associativity) {
                .left => parseLeftChain(level_idx, allocator, str, left, index, first),
                .right => parseRightChain(level_idx, allocator, str, left, index, first),
                .none => parseNoneChain(level_idx, allocator, str, left, index, first),
            };
        }

        fn parseTerm(comptime level_idx: usize, allocator: std.mem.Allocator, str: []const u8) mecha.Error!Res {
            const prefixed = try parsePrefixAndCore(level_idx, allocator, str);
            var value = switch (prefixed.value) {
                .ok => |v| v,
                .err => return prefixed,
            };

            var index = prefixed.index;
            while (true) {
                const post = try parsePostfix(level_idx, allocator, str[index..]);
                if (post == null)
                    break;

                const matched = post.?;
                if (matched.index == 0)
                    return Res.err(index);

                value = matched.func(value);
                index += matched.index;
            }

            return Res.ok(index, value);
        }

        fn parsePrefixAndCore(comptime level_idx: usize, allocator: std.mem.Allocator, str: []const u8) mecha.Error!Res {
            const pre = try parsePrefix(level_idx, allocator, str);
            if (pre) |matched| {
                if (matched.index == 0)
                    return Res.err(0);

                var next = try parsePrefixAndCore(level_idx, allocator, str[matched.index..]);
                switch (next.value) {
                    .err => {
                        next.index += matched.index;
                        return next;
                    },
                    .ok => |*v| {
                        v.* = matched.func(v.*);
                        next.index += matched.index;
                        return next;
                    },
                }
            }

            if (level_idx == 0)
                return atom.parse(allocator, str);
            return parseLevel(level_idx - 1, allocator, str);
        }

        fn parsePrefix(comptime level_idx: usize, allocator: std.mem.Allocator, str: []const u8) mecha.Error!?PrefixMatch {
            inline for (table[level_idx]) |op| {
                switch (op) {
                    .prefix => |p| {
                        const res = try p.parse(allocator, str);
                        switch (res.value) {
                            .ok => |f| return PrefixMatch{ .index = res.index, .func = f },
                            .err => {},
                        }
                    },
                    else => {},
                }
            }
            return null;
        }

        fn parsePostfix(comptime level_idx: usize, allocator: std.mem.Allocator, str: []const u8) mecha.Error!?PrefixMatch {
            inline for (table[level_idx]) |op| {
                switch (op) {
                    .postfix => |p| {
                        const res = try p.parse(allocator, str);
                        switch (res.value) {
                            .ok => |f| return PrefixMatch{ .index = res.index, .func = f },
                            .err => {},
                        }
                    },
                    else => {},
                }
            }
            return null;
        }

        fn parseInfix(comptime level_idx: usize, allocator: std.mem.Allocator, str: []const u8) mecha.Error!?InfixMatch {
            inline for (table[level_idx]) |op| {
                switch (op) {
                    .infix => |info| {
                        const res = try info.parser.parse(allocator, str);
                        switch (res.value) {
                            .ok => |f| {
                                return InfixMatch{
                                    .index = res.index,
                                    .func = f,
                                    .associativity = info.associativity,
                                };
                            },
                            .err => {},
                        }
                    },
                    else => {},
                }
            }
            return null;
        }

        fn parseLeftChain(
            comptime level_idx: usize,
            allocator: std.mem.Allocator,
            str: []const u8,
            first_lhs: T,
            first_index: usize,
            first_op: InfixMatch,
        ) mecha.Error!Res {
            var lhs = first_lhs;
            var index = first_index;
            var current_op = first_op;

            while (true) {
                index += current_op.index;
                const rhs_res = try parseTerm(level_idx, allocator, str[index..]);
                const rhs = switch (rhs_res.value) {
                    .ok => |v| v,
                    .err => return Res.err(index + rhs_res.index),
                };

                index += rhs_res.index;
                lhs = current_op.func(lhs, rhs);

                const next = try parseInfix(level_idx, allocator, str[index..]);
                if (next == null)
                    return Res.ok(index, lhs);

                current_op = next.?;
                if (current_op.index == 0)
                    return Res.err(index);
                if (current_op.associativity != .left)
                    return Res.err(index);
            }
        }

        fn parseRightChain(
            comptime level_idx: usize,
            allocator: std.mem.Allocator,
            str: []const u8,
            lhs: T,
            lhs_index: usize,
            op: InfixMatch,
        ) mecha.Error!Res {
            var index = lhs_index + op.index;
            const rhs_res = try parseTerm(level_idx, allocator, str[index..]);
            var rhs = switch (rhs_res.value) {
                .ok => |v| v,
                .err => return Res.err(index + rhs_res.index),
            };
            index += rhs_res.index;

            const next = try parseInfix(level_idx, allocator, str[index..]);
            if (next) |next_op| {
                if (next_op.index == 0)
                    return Res.err(index);
                if (next_op.associativity != .right)
                    return Res.err(index);

                const folded_rhs = try parseRightChain(level_idx, allocator, str, rhs, index, next_op);
                rhs = switch (folded_rhs.value) {
                    .ok => |v| v,
                    .err => return folded_rhs,
                };
                index = folded_rhs.index;
            }

            return Res.ok(index, op.func(lhs, rhs));
        }

        fn parseNoneChain(
            comptime level_idx: usize,
            allocator: std.mem.Allocator,
            str: []const u8,
            lhs: T,
            lhs_index: usize,
            op: InfixMatch,
        ) mecha.Error!Res {
            var index = lhs_index + op.index;
            const rhs_res = try parseTerm(level_idx, allocator, str[index..]);
            const rhs = switch (rhs_res.value) {
                .ok => |v| v,
                .err => return Res.err(index + rhs_res.index),
            };
            index += rhs_res.index;

            const next = try parseInfix(level_idx, allocator, str[index..]);
            if (next != null)
                return Res.err(index);

            return Res.ok(index, op.func(lhs, rhs));
        }
    }.parse };
}

test "binaryOp left right none" {
    const testing = std.testing;
    const fa = testing.failing_allocator;

    const Ops = struct {
        fn add(a: i32, b: i32) i32 {
            return a + b;
        }

        fn sub(a: i32, b: i32) i32 {
            return a - b;
        }

        fn pow(a: i32, b: i32) i32 {
            return std.math.powi(i32, a, @intCast(b)) catch unreachable;
        }

        fn eq(a: i32, b: i32) i32 {
            return if (a == b) 1 else 0;
        }
    };

    const atom = comptime mecha.int(i32, .{});
    const add_sub = comptime .{
        addBinaryOp(mecha.ascii.char('+').mapConst(&Ops.add), .left),
        addBinaryOp(mecha.ascii.char('-').mapConst(&Ops.sub), .left),
    };
    const power = comptime .{addBinaryOp(mecha.ascii.char('^').mapConst(&Ops.pow), .right)};
    const equal = comptime .{addBinaryOp(mecha.ascii.char('=').mapConst(&Ops.eq), .none)};

    const parser = comptime binaryOp(.{ power, add_sub }, atom);
    try mecha.expectOk(i32, 6, 5, try parser.parse(fa, "10-3-2"));
    try mecha.expectOk(i32, 5, 512, try parser.parse(fa, "2^3^2"));

    const eq_parser = comptime binaryOp(.{equal}, atom);
    try mecha.expectErr(i32, 3, try eq_parser.parse(fa, "1=1=1"));
}

test "binaryOp prefix and postfix" {
    const testing = std.testing;
    const fa = testing.failing_allocator;

    const Ops = struct {
        fn neg(v: i32) i32 {
            return -v;
        }

        fn inc(v: i32) i32 {
            return v + 1;
        }

        fn mul(a: i32, b: i32) i32 {
            return a * b;
        }
    };

    const atom = comptime mecha.int(i32, .{});
    const prefix_neg = comptime mecha.ascii.char('-').mapConst(&Ops.neg);
    const postfix_inc = comptime mecha.ascii.char('!').mapConst(&Ops.inc);
    const ops = comptime .{
        BinaryOp(i32).withPrefix(prefix_neg),
        BinaryOp(i32).withPostfix(postfix_inc),
        addBinaryOp(mecha.ascii.char('*').mapConst(&Ops.mul), .left),
    };

    const parser = comptime binaryOp(.{ops}, atom);
    try mecha.expectOk(i32, 3, -1, try parser.parse(fa, "-2!"));
    try mecha.expectOk(i32, 5, 12, try parser.parse(fa, "2!*3!"));
}
