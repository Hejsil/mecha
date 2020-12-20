const builtin = @import("builtin");
const std = @import("std");

const Mode = builtin.Mode;
const Builder = std.build.Builder;

pub fn build(b: *Builder) void {
    const mode = b.standardReleaseOptions();
    const target = b.standardTargetOptions(.{});

    const test_all_step = b.step("test", "Run all tests in all modes.");
    inline for ([_]Mode{ Mode.Debug, Mode.ReleaseFast, Mode.ReleaseSafe, Mode.ReleaseSmall }) |test_mode| {
        const mode_str = comptime modeToString(test_mode);

        const test_step = b.step("test-" ++ mode_str, "Run all tests in " ++ mode_str ++ ".");
        test_all_step.dependOn(test_step);

        inline for ([_][]const u8{
            "mecha.zig",
            "example/rgb.zig",
            "example/json.zig",
        }) |test_file| {
            const tests = b.addTest(test_file);
            tests.addPackagePath("mecha", "mecha.zig");
            tests.setBuildMode(test_mode);
            tests.setTarget(target);
            tests.setNamePrefix(mode_str ++ " ");
            test_step.dependOn(&tests.step);
        }
    }

    const readme_step = b.step("readme", "Remake README.");
    const readme = readMeStep(b);
    readme_step.dependOn(readme);

    const all_step = b.step("all", "Build everything and runs all tests");
    all_step.dependOn(readme_step);
    all_step.dependOn(test_all_step);

    b.default_step.dependOn(all_step);
}

fn readMeStep(b: *Builder) *std.build.Step {
    const s = b.allocator.create(std.build.Step) catch unreachable;
    s.* = std.build.Step.init(.Custom, "ReadMeStep", b.allocator, struct {
        fn make(step: *std.build.Step) anyerror!void {
            @setEvalBranchQuota(10000);
            const file = try std.fs.cwd().createFile("README.md", .{});
            const stream = &file.outStream();
            try stream.print(@embedFile("example/README.md.template"), .{
                @embedFile("example/rgb.zig"),
            });
        }
    }.make);
    return s;
}

fn modeToString(mode: Mode) []const u8 {
    return switch (mode) {
        Mode.Debug => "debug",
        Mode.ReleaseFast => "release-fast",
        Mode.ReleaseSafe => "release-safe",
        Mode.ReleaseSmall => "release-small",
    };
}
