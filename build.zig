const builtin = @import("builtin");
const std = @import("std");

pub fn build(b: *std.Build) void {
    const optimize = b.standardOptimizeOption(.{});
    const target = b.standardTargetOptions(.{});

    const module = b.addModule("mecha", .{
        .root_source_file = b.path("mecha.zig"),
    });

    const test_step = b.step("test", "Run all tests in all modes.");
    for ([_][]const u8{
        "mecha.zig",
        "example/rgb.zig",
        "example/json.zig",
    }) |test_file| {
        const tests = b.addTest(.{
            .root_module = b.createModule(.{
                .root_source_file = b.path(test_file),
                .optimize = optimize,
                .target = target,
            }),
        });
        const run_tests = b.addRunArtifact(tests);
        tests.root_module.addImport("mecha", module);
        test_step.dependOn(&run_tests.step);
    }

    b.default_step.dependOn(test_step);
}
