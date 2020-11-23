const mem = @import("mem_mock.zig");
const bitmap = @import("../../../src/kernel/bitmap.zig");
const vmm = @import("../../../src/kernel/vmm.zig");
const arch = @import("arch_mock.zig");
const std = @import("std");
const Allocator = std.mem.Allocator;

pub const VmmError = error{
    NotAllocated,
    AlreadyAllocated,
};

pub const Attributes = vmm.Attributes;

pub const BLOCK_SIZE: u32 = 1024;

pub const Mapper = vmm.Mapper;

pub const MapperError = error{
    InvalidVirtualAddress,
    InvalidPhysicalAddress,
    AddressMismatch,
    MisalignedVirtualAddress,
    MisalignedPhysicalAddress,
    NotMapped,
};

pub var kernel_vmm: VirtualMemoryManager(arch.VmmPayload) = undefined;

pub fn VirtualMemoryManager(comptime Payload: type) type {
    return struct {
        const Self = @This();

        pub fn init(start: usize, end: usize, allocator: *std.mem.Allocator, mapper: Mapper(Payload), payload: Payload) std.mem.Allocator.Error!Self {
            return Self{};
        }

        pub fn deinit(self: *Self) void {}

        pub fn isSet(self: *const Self, addr: usize) !bool {
            return true;
        }

        pub fn virtToPhys(self: *const Self, virt: usize) VmmError!usize {
            return 0;
        }

        pub fn alloc(self: *Self, num: u32, addr: ?usize, attrs: Attributes) std.mem.Allocator.Error!?usize {
            return 0;
        }

        pub fn free(self: *Self, vaddr: usize) (bitmap.Bitmap(u32).BitmapError || VmmError)!void {}

        pub fn copyData(self: *Self, other: *Self, comptime from: bool, data: if (from) []const u8 else []u8, dest: usize) (bitmap.Bitmap(usize).BitmapError || VmmError || Allocator.Error)!void {}
    };
}

pub fn init(mem_profile: *const mem.MemProfile, allocator: *Allocator) Allocator.Error!*VirtualMemoryManager(arch.VmmPayload) {
    kernel_vmm = try VirtualMemoryManager(arch.VmmPayload).init(0, 1024, allocator, arch.VMM_MAPPER, arch.KERNEL_VMM_PAYLOAD);
    return &kernel_vmm;
}
