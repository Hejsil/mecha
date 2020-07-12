const std = @import("std");

const debug = std.debug;
const testing = std.testing;

/// A tuple implementation structured as a tree of `first+second` pairs.
pub fn Tuple(comptime types: []const type) type {
    const Functions = struct {
        fn At(comptime T: type, comptime i: usize) type {
            var info = @typeInfo(T);
            if (info.Pointer.is_const)
                return *const types[i];
            return *types[i];
        }

        pub fn init(comptime Self: type) type {
            return struct {
                fn func(t: anytype) Self {
                    comptime debug.assert(t.len == types.len);

                    var res: Self = undefined;
                    comptime var i = 0;
                    inline while (i < t.len) : (i += 1) {
                        res.at(i).* = t[i];
                    }

                    return res;
                }
            };
        }

        pub fn at(t: anytype, comptime i: usize) At(@TypeOf(t), i) {
            comptime debug.assert(i < t.len);
            if (t.len <= 2 and i == 0)
                return &t.first;
            if (t.len <= 2 and i == 1)
                return &t.second;
            if (i < t.first.len)
                return t.first.at(i);
            return t.second.at(i - t.first.len);
        }
    };

    if (types.len <= 2) {
        return struct {
            comptime len: usize = types.len,
            first: if (types.len >= 1) types[0] else void,
            second: if (types.len == 2) types[1] else void,

            pub const init = Functions.init(@This()).func;
            pub const at = Functions.at;
        };
    } else {
        return struct {
            comptime len: usize = types.len,
            first: Tuple(types[0 .. types.len / 2]),
            second: Tuple(types[types.len / 2 ..]),

            pub const init = Functions.init(@This()).func;
            pub const at = Functions.at;
        };
    }
}

test "tuple" {
    const unit = Tuple(&[_]type{u8}).init(.{0});
    const pair = Tuple(&[_]type{ u8, u16 }).init(.{ 0, 1 });
    const trip = Tuple(&[_]type{ u8, u16, u32 }).init(.{ 0, 1, 2 });
    const quad = Tuple(&[_]type{ u8, u16, u32, u64 }).init(.{ 0, 1, 2, 3 });
    const all = Tuple(&[_]type{
        @TypeOf(unit),
        @TypeOf(pair),
        @TypeOf(trip),
        @TypeOf(quad),
    }).init(.{ unit, pair, trip, quad });

    comptime var i = 0;
    inline while (i < all.len) : (i += 1) {
        const t = all.at(i).*;

        comptime var j = 0;
        inline while (j < t.len) : (j += 1)
            testing.expectEqual(@as(u64, j), t.at(j).*);
    }
}
