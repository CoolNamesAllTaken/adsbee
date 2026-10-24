#include "ram_monitor.hh"

#include <malloc.h>
#include <unistd.h>

extern "C" {
extern char __StackLimit, __StackTop, __StackOneTop, __scratch_x_end__, __scratch_y_end__;
}

namespace {
constexpr uint32_t kPaint = 0xA5C3E1F0;
constexpr uint32_t kSPMarginBytes = 256;  // Left unpainted below the stack pointer of the painting function.

uint32_t core_1_stack_peak_bytes = 0;

inline uint32_t* Word(const void* p) { return reinterpret_cast<uint32_t*>((reinterpret_cast<uintptr_t>(p) + 3) & ~3u); }

void Paint(uint32_t* lo, uint32_t* hi) {
    for (uint32_t* p = lo; p < hi; p++) *p = kPaint;
}

// Lowest word in [lo, hi) that no longer holds the pattern, or hi.
uint32_t* LowestUsed(uint32_t* lo, uint32_t* hi) {
    while (lo < hi && *lo == kPaint) lo++;
    return lo;
}

uint32_t Core1StackPeakNow() {
    uint32_t* top = Word(&__StackOneTop);
    return (top - LowestUsed(Word(&__scratch_y_end__), top)) * sizeof(uint32_t);
}
}  // namespace

void RAMMonitor::PaintCore0Stack() {
    uint32_t sp;
    asm volatile("mov %0, sp" : "=r"(sp));
    Paint(Word(sbrk(0)), Word(&__StackLimit));
    Paint(Word(&__scratch_x_end__), reinterpret_cast<uint32_t*>((sp - kSPMarginBytes) & ~3u));
}

void RAMMonitor::PaintCore1Stack() {
    uint32_t peak = Core1StackPeakNow();
    if (peak > core_1_stack_peak_bytes) core_1_stack_peak_bytes = peak;
    Paint(Word(&__scratch_y_end__), Word(&__StackOneTop));
}

RAMMonitor::Usage RAMMonitor::GetUsage() {
    Usage usage;
    struct mallinfo info = mallinfo();
    usage.heap_in_use_bytes = info.uordblks;

    uint32_t* heap_top = Word(sbrk(0));
    uint32_t* ram_end = Word(&__StackLimit);
    uint32_t* stack_top = Word(&__StackTop);
    uint32_t* lowest = LowestUsed(heap_top, ram_end);
    usage.free_bytes = (lowest - heap_top) * sizeof(uint32_t);
    if (lowest < ram_end) {
        // Stack reached main RAM: all of scratch X above its contents, plus the part of main RAM it used.
        usage.core_0_stack_peak_bytes = ((stack_top - Word(&__scratch_x_end__)) + (ram_end - lowest)) * sizeof(uint32_t);
    } else {
        usage.core_0_stack_peak_bytes = (stack_top - LowestUsed(Word(&__scratch_x_end__), stack_top)) * sizeof(uint32_t);
    }

    uint32_t core_1_now = Core1StackPeakNow();
    usage.core_1_stack_peak_bytes = core_1_now > core_1_stack_peak_bytes ? core_1_now : core_1_stack_peak_bytes;
    return usage;
}
