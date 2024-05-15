const builtin = @import("builtin");
const std = @import("std");

pub fn build(b: *std.Build) void {
    const optimize = b.standardOptimizeOption(.{});
    const target = b.standardTargetOptions(.{});

    const module = b.addModule("mecha", .{ .root_source_file = b.path("mecha.zig") });

    const test_step = b.step("test", "Run all tests in all modes.");
    for ([_][]const u8{
        "mecha.zig",
        "example/rgb.zig",
        "example/json.zig",
    }) |test_file| {
        const tests = b.addTest(.{
            .root_source_file = b.path(test_file),
            .optimize = optimize,
            .target = target,
        });
        const run_tests = b.addRunArtifact(tests);
        tests.root_module.addImport("mecha", module);
        test_step.dependOn(&run_tests.step);
    }

    const readme_step = b.step("readme", "Remake README.");
    const readme = readMeStep(b);
    readme_step.dependOn(readme);

    const all_step = b.step("all", "Build everything and runs all tests");
    all_step.dependOn(readme_step);
    all_step.dependOn(test_step);

    b.default_step.dependOn(all_step);
}

fn readMeStep(b: *std.Build) *std.Build.Step {
    const s = b.allocator.create(std.Build.Step) catch unreachable;
    s.* = std.Build.Step.init(.{
        .id = .custom,
        .name = "ReadMeStep",
        .owner = b,
        .makeFn = struct {
            fn make(_: *std.Build.Step, _: *std.Progress.Node) anyerror!void {
                @setEvalBranchQuota(10000);
                const file = try std.fs.cwd().createFile("README.md", .{});
                const writer = file.writer();
                try writer.print(@embedFile("example/README.md.template"), .{
                    @embedFile("example/rgb.zig"),
                });
            }
        }.make,
    });
    return s;
}
