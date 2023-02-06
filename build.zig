const builtin = @import("builtin");
const std = @import("std");

const Builder = std.build.Builder;

pub fn build(b: *Builder) void {
    const optimize = b.standardOptimizeOption(.{});
    const target = b.standardTargetOptions(.{});

    const test_step = b.step("test", "Run all tests in all modes.");

    inline for ([_][]const u8{
        "mecha.zig",
        "example/rgb.zig",
        "example/json.zig",
    }) |test_file| {
        const tests = b.addTest(.{
            .root_source_file = .{ .path = test_file },
            .optimize = optimize,
            .target = target,
        });
        tests.addAnonymousModule("mecha", .{ .source_file = .{ .path = "mecha.zig" } });
        test_step.dependOn(&tests.step);
    }

    const readme_step = b.step("readme", "Remake README.");
    const readme = readMeStep(b);
    readme_step.dependOn(readme);

    const all_step = b.step("all", "Build everything and runs all tests");
    all_step.dependOn(readme_step);
    all_step.dependOn(test_step);

    b.default_step.dependOn(all_step);
}

fn readMeStep(b: *Builder) *std.build.Step {
    const s = b.allocator.create(std.build.Step) catch unreachable;
    s.* = std.build.Step.init(.custom, "ReadMeStep", b.allocator, struct {
        fn make(_: *std.build.Step) anyerror!void {
            @setEvalBranchQuota(10000);
            const file = try std.fs.cwd().createFile("README.md", .{});
            const writer = file.writer();
            try writer.print(@embedFile("example/README.md.template"), .{
                @embedFile("example/rgb.zig"),
            });
        }
    }.make);
    return s;
}
