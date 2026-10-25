#!/usr/bin/env python3
"""Put boot-progress probes into a COPY of the source XNU kernel (never the original).

There is no serial console on the device and the kernel cannot draw before its
own video console exists, so the early boot stages are reported by side
channels. The stage code lives in the zero padding after the kernel entry
(_start is one `b`) and displaced instructions are re-executed there:

  stage 1 (kernel entry, MMU off)       blue bar, then continues
  stage 2 (just before the MMU is on)   magenta bar, then continues
  stage 3 (right after the MMU is on)   waits --reset-delay seconds, then PSCI
                                        SYSTEM_RESET. A reboot by itself after
                                        that time shows the CPU got through the
                                        MMU enable; the frame buffer is not
                                        mapped by then, so time is the signal.
  panic screen (--panic-screen)         panic() and its common panic funnel draw
                                        their format string on the
                                        kernel's own frame buffer mapping and
                                        stops (scripts/xnu-panic-screen.c).
                                        --no-reset leaves out stages 3 and 4.
  stage 4 (--reset-after SYMBOL)        the same wait and reset, but placed after
                                        the call to SYMBOL in --in FUNCTION (the
                                        Nth call, --occurrence). It replaces
                                        stage 3, so one run asks one question:
                                        did the kernel get past that call?

The bars are the 1/16th bands of the frame buffer below the green one that
DarwinBoot paints (band index = stage). Each patch site is checked against its
expected original instruction first, and the tool refuses a kernel that does
not match. Offsets are specific to the kernel built by build-xnu-4k-baseline.sh.
"""
import argparse
import os
import shutil
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

ENTRY_VA = 0xFFFFFFF00B9D0488        # LC_UNIXTHREAD pc, `b start_first_cpu`
START_FIRST_CPU = 0xFFFFFFF00B9D205C
MMU_ENABLE_VA = 0xFFFFFFF00B9D2330   # msr SCTLR_EL1, x0
AFTER_MMU_VA = 0xFFFFFFF00B9D2350    # mov x0, #0x300000
PANIC_VA = 0xFFFFFFF00BF69B04      # _panic
VINFO_VA = 0xFFFFFFF00C0A2970      # _vinfo
PANIC_CAVE_END = 0xFFFFFFF00B9D0FF0
CAVE_SIZE = 0x60
CAVES = {1: 0xFFFFFFF00B9D0500, 2: 0xFFFFFFF00B9D0560, 3: 0xFFFFFFF00B9D05C0, 4: 0xFFFFFFF00B9D0620}
# Stage 4 makes its call and then waits, which takes more than the shared 0x60 (it also carries the
# branch back to the call site). It is the last cave, so it may use everything up to PANIC_CAVE_END
# minus the 0x60 the panic screen would need; the panic screen itself is refused when the two would
# overlap, in main(). The per-cave emptiness check uses the same size, so nothing is overwritten
# unseen. This used to be 0x300 when stage 4 also painted; it no longer paints, so it is smaller.
# Stages 5 and up exist only for the --ladder form, which needs one call-plus-wait cave per site.
CAVE_SIZE_BY_STAGE = {4: 0x140, 5: 0x140, 6: 0x140, 7: 0x140, 8: 0x140, 9: 0x140}
TIMEBASE = 19200000

PAINT = """
  ldr x1, [{args}, #0x28]
  ldr x2, [{args}, #0x38]
  ldr x3, [{args}, #0x48]
  mul x2, x2, x3
  lsr x2, x2, #4
  bic x2, x2, #7
  mov x4, #{band}
  mul x5, x2, x4
  add x1, x1, x5
  movz w6, #{lo}
  movk w6, #{hi}, lsl #16
1:
  stp w6, w6, [x1], #8
  subs x2, x2, #8
  b.hi 1b
  dsb sy
"""

# After the MMU is on the frame buffer is reachable only through the physical map, and this site
# cannot reach it: the board's frame buffer is *below* gPhysBase (DarwinBoot's window starts at the
# top of DRAM; the panel sits in the low reserved range), so it falls outside the physical map that
# physmap_base covers, and phystokv() panics with "illegal PA" instead of translating it. ml_io_map()
# would work, but it needs kernel_map, which kmem_init() creates in kernel_bootstrap - long after
# _arm_vm_init returns. Until a site past kernel_bootstrap is hooked, report here by timing alone:
# the cave waits and resets, so a reset proves the call returned.
#
# KEEL: do not resurrect a store through physmap_base at this point. It faults on this board.
# DarwinBoot's video base is 0x9C000000 while gPhysBase is about 0xC2E04000, so the panel is 0x24A
# MiB below the aperture; phystokv() panics "illegal PA" and hangs the machine at this site.
PAINT_PHYS = ""

SOURCES = {
    1: ".text\n.global _start\n_start:\n" + PAINT.format(args='x0', band=1, lo='0x00FF', hi='0xFF00') + "  b target\n",
    2: ".text\n.global _start\n_start:\n" + PAINT.format(args='x20', band=2, lo='0x00FF', hi='0xFFFF')
       + "  msr SCTLR_EL1, x0\n  b target\n",
    3: """.text
.global _start
_start:
  mov x0, #0x300000
  mrs x1, cntpct_el0
  ldr x2, ={ticks}
  add x2, x1, x2
1:
  isb
  mrs x1, cntpct_el0
  cmp x1, x2
  b.lo 1b
  movz w0, #0x0009
  movk w0, #0x8400, lsl #16
  mov x1, xzr
  mov x2, xzr
  mov x3, xzr
  smc #0
2:
  wfe
  b 2b
""" + ".ltorg\n",
    4: """.text
.global _start
_start:
  bl callee
  ldr x2, ={ticks}
  cbz x2, 2f
  mrs x1, cntpct_el0
  add x2, x1, x2
1:
  isb
  mrs x1, cntpct_el0
  cmp x1, x2
  b.lo 1b
  movz w0, #0x0009
  movk w0, #0x8400, lsl #16
  mov x1, xzr
  mov x2, xzr
  mov x3, xzr
  smc #0
  wfe
  b .
2:
  b target
""" + ".ltorg\n",
}

# Reset at the call site without making the call. The wait is what makes --ladder work: without it
# every level resets at once and the only detectable outcome is "reached the first site". With it,
# level n resets n seconds after the kernel arrives there, so the delay names the deepest site the
# kernel reached. A zero delay keeps the old immediate-reset behavior for a single probe.
RESET_BEFORE = """.text
.global _start
_start:
  ldr x2, ={ticks}
  cbz x2, 2f
  mrs x1, cntpct_el0
  add x2, x1, x2
1:
  isb
  mrs x1, cntpct_el0
  cmp x1, x2
  b.lo 1b
2:
  movz w0, #0x0009
  movk w0, #0x8400, lsl #16
  mov x1, xzr
  mov x2, xzr
  mov x3, xzr
  smc #0
3:
  wfe
  b 3b
""" + ".ltorg\n"


def kernel_symbols(kernel):
    """Address -> name for the kernel's symbols, from llvm-nm."""
    nm = shutil.which('llvm-nm') or '/opt/homebrew/opt/llvm/bin/llvm-nm'
    table = {}
    for line in subprocess.run([nm, '-n', kernel], capture_output=True, text=True, check=True).stdout.splitlines():
        parts = line.split()
        if len(parts) == 3:
            table.setdefault(int(parts[0], 16), parts[2])
    return table


def function_range(symbols, name):
    """Start and end (next symbol) of a function by its symbol name."""
    starts = sorted(symbols)
    for start, symbol in symbols.items():
        if symbol == name:
            return start, next(address for address in starts if address > start)
    raise SystemExit(f'No symbol {name} in the kernel')


def find_entry(data, symbols, function):
    """The first instruction of FUNCTION, for a probe that fires on entry.

    _arm_init is reached by a tail jump: _start_first_cpu loads its address into LR and returns,
    so there is no `bl _arm_init` anywhere to find. Hook the entry instead.
    """
    low, _ = function_range(symbols, function)
    return low


def find_call(data, symbols, function, name, occurrence):
    """The VA and target of the Nth `bl name` inside FUNCTION."""
    hits = []
    low, high = function_range(symbols, function)
    for va in range(low, high, 4):
        word = struct.unpack_from('<I', data, file_offset(va))[0]
        if word >> 26 == 0b100101:
            delta = word & 0x3FFFFFF
            delta -= (1 << 26) if delta & (1 << 25) else 0
            target = va + delta * 4
            if symbols.get(target) == name:
                hits.append((va, target))
    if len(hits) < occurrence:
        raise SystemExit(f'{function} has {len(hits)} call(s) to {name}, not {occurrence}')
    return hits[occurrence - 1]


def assemble_c(source, va, workdir, symbols):
    """Build a freestanding C file for VA; returns (bytes, load address of the first byte, address of panic_screen).

    The linker may start .text a little after VA (it keeps the ELF headers in front), so the
    load address is read back from the ELF and is what the caller must write the bytes to."""
    clang = shutil.which('clang') or '/opt/homebrew/opt/llvm/bin/clang'
    lld = shutil.which('ld.lld') or '/opt/homebrew/opt/llvm/bin/ld.lld'
    objcopy = shutil.which('llvm-objcopy') or '/opt/homebrew/opt/llvm/bin/llvm-objcopy'
    nm = shutil.which('llvm-nm') or '/opt/homebrew/opt/llvm/bin/llvm-nm'
    # UNIXNU_UEFI is the Mu-Silicium checkout when the unixnu driver runs this script.
    font_dir = Path(os.environ.get('UNIXNU_UEFI') or ROOT / 'uefi-sheng') / 'Silicon/Silicium/SiliciumPkg/Library/FrameBufferSerialPortLib'
    if not (font_dir / 'Font.h').is_file():
        raise SystemExit('Panic screen requires Mu-Silicium FrameBufferSerialPortLib/Font.h; '
                         'set --uefi PATH or [build] uefi in unixnu.local.toml '
                         '(UNIXNU_UEFI for direct script calls)')
    obj, elf, binary = (workdir / name for name in ('panic.o', 'panic.elf', 'panic.bin'))
    definitions = []
    for macro, name, width in (('MAX_MEM', '_max_mem', 8),
                               ('PAGE_TOTAL', '_vm_page_pages', 4),
                               ('PAGE_FREE', '_vm_page_free_count', 4)):
        address = symbols.get(name)
        if address is None or address % width or not any(
                base <= address and address + width <= base + size
                for base, size, _, _ in SEGMENTS):
            raise SystemExit(f'Missing or invalid diagnostic symbol {name}')
        definitions.append(f'-D{macro}={address:#x}UL')
    # Optional: the board's banner buffer for the panic message (kits/sheng/BootProgress.c); kernels without it get 0 (no copy).
    text = symbols.get('_boot_progress_panic_text')
    if text is not None:
        if not any(base <= text and text + 256 <= base + size for base, size, _, _ in SEGMENTS):
            raise SystemExit('Invalid _boot_progress_panic_text')
        definitions.append(f'-DPANIC_TEXT={text:#x}UL')
    # -fomit-frame-pointer: this code runs on the panic path with no debugger unwind, and some
    # clang builds keep a frame pointer even in a noreturn loop (park()), which overran the
    # cave by a few bytes on Linux clang 21.1.8 but not on Apple clang 21.0.0. Dropping it keeps
    # the size the same on every host.
    subprocess.run([clang, '--target=aarch64-none-elf', '-ffreestanding', '-fno-builtin', '-fno-stack-protector',
                    '-mgeneral-regs-only', '-fno-pic', '-mcmodel=tiny', '-Oz', '-fomit-frame-pointer',
                    f'-DVINFO={VINFO_VA:#x}UL',
                    *definitions, f'-I{font_dir}', '-c', source, '-o', obj], check=True)
    script = workdir / 'panic.ld'
    script.write_text('SECTIONS { . = %#x; .text : { *(.text.a_entry) *(.text.a_common) *(.text*) *(.rodata*) } /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) *(.ARM.*) } }\n' % va)
    size = shutil.which('llvm-size') or '/opt/homebrew/opt/llvm/bin/llvm-size'
    sizes = subprocess.run([size, '--format=berkeley', obj], capture_output=True, text=True, check=True).stdout.splitlines()[-1].split()
    if int(sizes[1]) or int(sizes[2]):
        # The code runs from the kernel's read-only text: a global would fault on its first store.
        raise SystemExit(f'{source.name} has writable data (data {sizes[1]}, bss {sizes[2]}); use the stack')
    subprocess.run([lld, '-T', script, '-e', 'panic_screen', obj, '-o', elf], check=True)
    # Only .text: a plain binary dump would start at the ELF headers kept in front of it.
    subprocess.run([objcopy, '-O', 'binary', '-j', '.text', elf, binary], check=True)
    readelf = shutil.which('llvm-readelf') or '/opt/homebrew/opt/llvm/bin/llvm-readelf'
    load = None
    for line in subprocess.run([readelf, '-S', elf], capture_output=True, text=True, check=True).stdout.splitlines():
        parts = line.replace('[', ' ').replace(']', ' ').split()
        if len(parts) >= 4 and parts[1] == '.text':
            load = int(parts[3], 16)
    if load is None or load < va:
        raise SystemExit('Cannot find where the linker put .text')
    entry = None
    for line in subprocess.run([nm, elf], capture_output=True, text=True, check=True).stdout.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[2] == 'panic_screen':
            entry = int(parts[0], 16)
    if entry != load:
        raise SystemExit(f'panic_screen at {entry:#x} is not the first byte {load:#x}')
    return binary.read_bytes(), load, entry


def panic_common_entry(workdir, code, load):
    """Resolve the real alternate entry and verify its distinct argument ABI."""
    nm = shutil.which('llvm-nm') or '/opt/homebrew/opt/llvm/bin/llvm-nm'
    names = {parts[2]: int(parts[0], 16)
             for line in subprocess.check_output([nm, workdir / 'panic.elf'], text=True).splitlines()
             if len(parts := line.split()) == 3}
    entry = names.get('panic_screen_common')
    main = names.get('panic_screen_main')
    if entry is None or main is None or not load <= entry <= load + len(code) - 8:
        raise SystemExit('Common panic renderer entry is missing or out of bounds')
    at = entry - load
    if code[at:at + 8] != struct.pack('<II', 0xf9400021, branch(entry + 4, main)):
        raise SystemExit('Common panic entry does not dereference the Darwin va_list pointer and branch to the renderer')
    return entry


ROOT = Path(__file__).resolve().parents[1]


SEGMENTS = []   # (vmaddr, vmsize, fileoff, filesize) of the kernel being patched


def load_segments(data):
    """Read the Mach-O segment table; the file layout differs between kernel builds."""
    magic, _, _, _, ncmds = struct.unpack_from('<IiiII', data, 0)
    if magic != 0xFEEDFACF:
        raise SystemExit('Not a 64-bit Mach-O')
    offset = 32
    SEGMENTS.clear()
    for _ in range(ncmds):
        cmd, size = struct.unpack_from('<II', data, offset)
        if cmd == 0x19:
            _, vmaddr, vmsize, fileoff, filesize = struct.unpack_from('<16sQQQQ', data, offset + 8)
            if filesize:
                SEGMENTS.append((vmaddr, vmsize, fileoff, filesize))
        offset += size


def unixthread_pc(data):
    """LC_UNIXTHREAD entry pc (arm64 thread state: flavor, count, x0..x28, fp, lr, sp, pc)."""
    offset = 32
    for _ in range(struct.unpack_from('<I', data, 16)[0]):
        cmd, size = struct.unpack_from('<II', data, offset)
        if cmd == 0x5:
            return struct.unpack_from('<Q', data, offset + 16 + 32 * 8)[0]
        offset += size
    raise SystemExit('No LC_UNIXTHREAD in kernel')


def rebase(kernel, data):
    """The probe sites are fixed offsets from the entry; shift them for another kernel build.

    _panic and _vinfo come from the symbol table when the kernel has one (the plain source
    kernel does); the retained candidate layout is the unshifted case.
    """
    global ENTRY_VA, START_FIRST_CPU, MMU_ENABLE_VA, AFTER_MMU_VA, PANIC_VA, VINFO_VA, PANIC_CAVE_END, CAVES
    delta = unixthread_pc(data) - ENTRY_VA
    if delta:
        ENTRY_VA += delta
        START_FIRST_CPU += delta
        MMU_ENABLE_VA += delta
        AFTER_MMU_VA += delta
        PANIC_CAVE_END += delta
        CAVES = {stage: va + delta for stage, va in CAVES.items()}
        PANIC_VA += delta
        VINFO_VA += delta
    names = {name: va for va, name in kernel_symbols(kernel).items()}
    if '_start_first_cpu' in names:
        START_FIRST_CPU = names['_start_first_cpu']
        # Native bootstrap table-capacity checks can grow before SCTLR setup.
        # Locate the unique instruction sequence in this bounded entry body;
        # do not assume a constant offset from the Mach-O entry point.
        matches = []
        for va in range(START_FIRST_CPU, START_FIRST_CPU + 0x1000, 4):
            def instruction(at):
                return struct.unpack_from('<I', data, file_offset(at))[0]
            if (instruction(va) == 0xD5181000 and
                    instruction(va + 4) == 0xD5033FDF and
                    instruction(va + 0x20) == 0xD2A00600 and
                    instruction(va + 0x24) == 0xD5181040):
                matches.append(va)
        if len(matches) != 1:
            raise SystemExit('Require one verified SCTLR/ISB/CPACR entry sequence')
        MMU_ENABLE_VA = matches[0]
        AFTER_MMU_VA = MMU_ENABLE_VA + 0x20
    if '_panic' in names and '_vinfo' in names:
        PANIC_VA = names['_panic']
        # Board diagnostics seed this ABI-compatible prefix from valid console
        # mappings, then pin it to their retained GOP mapping. Ordinary source
        # kernels without the observer retain the original vinfo path.
        VINFO_VA = names.get('_boot_progress_panic_vinfo', names['_vinfo'])
    return names


def file_offset(va):
    for vmaddr, vmsize, fileoff, filesize in SEGMENTS:
        if vmaddr <= va < vmaddr + min(vmsize, filesize):
            return fileoff + (va - vmaddr)
    raise SystemExit(f'{va:#x} is not in a file-backed segment of this kernel')


def branch(from_va, to_va):
    delta = (to_va - from_va) // 4
    if (to_va - from_va) % 4 or not -(1 << 25) <= delta < (1 << 25):
        raise SystemExit('Branch out of range')
    return 0x14000000 | (delta & 0x3FFFFFF)


def assemble(source, va, symbols, workdir):
    asm, obj, elf, binary = (workdir / name for name in ('cave.S', 'cave.o', 'cave.elf', 'cave.bin'))
    asm.write_text(source)
    clang = shutil.which('clang') or '/opt/homebrew/opt/llvm/bin/clang'
    lld = shutil.which('ld.lld') or '/opt/homebrew/opt/llvm/bin/ld.lld'
    objcopy = shutil.which('llvm-objcopy') or '/opt/homebrew/opt/llvm/bin/llvm-objcopy'
    subprocess.run([clang, '--target=aarch64-none-elf', '-c', asm, '-o', obj], check=True)
    subprocess.run([lld, f'-Ttext={va:#x}', *[f'--defsym={name}={value:#x}' for name, value in symbols.items()], '-e', '_start', obj, '-o', elf], check=True)
    subprocess.run([objcopy, '-O', 'binary', elf, binary], check=True)
    return binary.read_bytes()


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('kernel', type=Path, help='the COPY of the kernel to patch in place')
    parser.add_argument('--reset-delay', type=int, default=6, help='seconds before the reset')
    parser.add_argument('--reset-after', metavar='SYMBOL', help='place the reset after this call in arm_init instead of stage 3')
    parser.add_argument('--reset-before', action='store_true', help='reset at the call site before invoking SYMBOL (requires --reset-after)')
    parser.add_argument('--panic-screen', action='store_true', help='draw panic() messages on the screen')
    parser.add_argument('--no-reset', action='store_true', help='no reset probe at all')
    parser.add_argument('--occurrence', type=int, default=1, help='which call to SYMBOL (1 = first)')
    parser.add_argument('--in', dest='function', default='_arm_init', help='function that makes the call (default _arm_init)')
    parser.add_argument('--ladder', metavar='SYMBOL[,SYMBOL...]',
                        help='one reset probe per SYMBOL, in order, with --reset-delay N giving the '
                             'Nth probe a delay of N seconds: the earliest site reached resets first, '
                             'so a single boot reports how far the function got')
    args = parser.parse_args()
    if args.reset_before and not args.reset_after and not args.ladder:
        raise SystemExit('--reset-before requires --reset-after')
    data = bytearray(args.kernel.read_bytes())
    load_segments(data)
    kernel_names = rebase(args.kernel, data)

    def word(va):
        return struct.unpack_from('<I', data, file_offset(va))[0]

    expected = {ENTRY_VA: branch(ENTRY_VA, START_FIRST_CPU), MMU_ENABLE_VA: 0xD5181000, AFTER_MMU_VA: 0xD2A00600}
    for va, value in expected.items():
        if word(va) != value:
            raise SystemExit(f'{va:#x} holds {word(va):#010x}, expected {value:#010x}: not the kernel these probes are for')
    for stage, va in CAVES.items():
        size = CAVE_SIZE_BY_STAGE.get(stage, CAVE_SIZE)
        if any(data[file_offset(va):file_offset(va) + size]):
            raise SystemExit(f'Padding at {va:#x} is not empty')

    # (site, cave stage, symbols the cave is linked with)
    sites = [(ENTRY_VA, 1, {'target': START_FIRST_CPU}),
             (MMU_ENABLE_VA, 2, {'target': MMU_ENABLE_VA + 4})]
    ladder = None
    if args.no_reset:
        description = 'no reset probe'
    elif args.ladder:
        # Sites from shallow to deep. Probe n gets a delay of n seconds, so the shallowest site the
        # kernel actually reaches fires first and its delay says which site that was.
        symbols = kernel_symbols(args.kernel)
        names = [name.strip() for name in args.ladder.split(',') if name.strip()]
        if not names:
            raise SystemExit('--ladder needs at least one symbol')
        ladder = []
        for index, name in enumerate(names, 1):
            stage = 4 + index - 1
            if stage not in CAVES:
                # Lay out the extra caves right after the last one in use, each as large as the
                # cave before it. CAVE_SIZE_BY_STAGE holds a size per stage, not a cumulative
                # offset, so the previous cave's own size is what advances the address.
                previous = max(CAVES)
                CAVES[stage] = CAVES[previous] + CAVE_SIZE_BY_STAGE.get(previous, CAVE_SIZE)
                size = CAVE_SIZE_BY_STAGE.get(stage, CAVE_SIZE)
                if CAVES[stage] + size > PANIC_CAVE_END:
                    raise SystemExit(f'{len(names)} ladder probes need room up to '
                                     f'{CAVES[stage] + size:#x}, past the padding end {PANIC_CAVE_END:#x}')
                if any(data[file_offset(CAVES[stage]):file_offset(CAVES[stage]) + size]):
                    raise SystemExit(f'Padding at {CAVES[stage]:#x} is not empty')
            call_va, callee = find_call(data, symbols, args.function, name, 1)
            ladder.append((call_va, stage, {'callee': callee, 'target': call_va + 4}, name))
        sites.extend((site, stage, syms) for site, stage, syms, _ in ladder)
        description = (f'stage 4 ladder of {len(names)} reset probes in {args.function}: '
                       + ', '.join(f'{i}={n}@{s:#x}' for i, (s, _, _, n) in enumerate(ladder, 1)))
    elif args.reset_after:
        symbols = kernel_symbols(args.kernel)
        if args.reset_after == '@entry':
            # Fire on entry to args.function itself. _arm_init is reached by a tail jump (its address
            # goes into LR at _start_first_cpu), so there is no call to hook. This form must be used
            # with --reset-before: the site's original first instruction is displaced and never
            # re-executed, so falling through into the function would corrupt it.
            if not args.reset_before:
                raise SystemExit('--reset-after @entry needs --reset-before')
            call_va = find_entry(data, symbols, args.function)
            sites.append((call_va, 4, {}))
            description = f'stage 4 reset on entry to {args.function} (at {call_va:#x})'
        else:
            call_va, callee = find_call(data, symbols, args.function, args.reset_after, args.occurrence)
            # No frame buffer store here: the panel is outside the physical aperture at this site (see
            # PAINT_PHYS). The cave makes the call, waits, then resets, so the timing is the answer.
            sites.append((call_va, 4, {'callee': callee, 'target': call_va + 4}))
            description = f'stage 4 {"reset" if args.reset_before or args.reset_delay else "bar"} after call #{args.occurrence} to {args.reset_after} in {args.function} (at {call_va:#x})'
    else:
        sites.append((AFTER_MMU_VA, 3, {'target': AFTER_MMU_VA + 4}))
        description = f'stage 3 reset {args.reset_delay} s after the MMU is on'

    with tempfile.TemporaryDirectory() as tmp:
        for site, stage, symbols in sites:
            if ladder and stage >= 4:
                # Level n waits n * --reset-delay. A one-second step is too close to the reset
                # itself to time by hand, so the step is the configured delay.
                seconds = (stage - 3) * args.reset_delay
            else:
                seconds = args.reset_delay
            # Stages past 4 exist only for the ladder and have the same shape as stage 4.
            template = 4 if stage > 4 else stage
            shape = RESET_BEFORE if (stage >= 4 and args.reset_before) else SOURCES[template]
            source = shape.format(ticks=TIMEBASE * seconds)
            code = assemble(source, CAVES[stage], symbols, Path(tmp))
            limit = CAVE_SIZE_BY_STAGE.get(stage, CAVE_SIZE)
            if len(code) > limit:
                raise SystemExit(f'Stage {stage} code is {len(code):#x} bytes, its cave holds {limit:#x}')
            data[file_offset(CAVES[stage]):file_offset(CAVES[stage]) + len(code)] = code
    for site, stage, _ in sites:
        struct.pack_into('<I', data, file_offset(site), branch(site, CAVES[stage]))
    if args.panic_screen:
        # Right after the last probe cave in use, so the padding is shared as tightly as possible.
        last = max(sites, key=lambda entry: CAVES[entry[1]])[1]
        PANIC_CAVE = CAVES[last] + CAVE_SIZE_BY_STAGE.get(last, CAVE_SIZE)
        if word(PANIC_VA) in (0, 0xFFFFFFFF) or any(data[file_offset(PANIC_CAVE):file_offset(PANIC_CAVE_END)]):
            raise SystemExit('panic() or the panic screen padding is not as expected')
        with tempfile.TemporaryDirectory() as tmp:
            code, load, entry = assemble_c(ROOT / 'scripts/xnu-panic-screen.c', PANIC_CAVE, Path(tmp), kernel_names)
            common_entry = panic_common_entry(Path(tmp), code, load)
        if load + len(code) > PANIC_CAVE_END:
            raise SystemExit(f'panic screen is {len(code):#x} bytes at {load:#x}, the padding ends at {PANIC_CAVE_END:#x}')
        if any(data[file_offset(load):file_offset(load) + len(code)]):
            raise SystemExit(f'Padding at {load:#x} is not empty')
        data[file_offset(load):file_offset(load) + len(code)] = code
        struct.pack_into('<I', data, file_offset(PANIC_VA), branch(PANIC_VA, entry))
        common = kernel_names.get('_panic_trap_to_debugger')
        if common is None or word(common) in (0, 0xFFFFFFFF):
            raise SystemExit('Common panic funnel is missing; refuse a partially covered panic screen')
        struct.pack_into('<I', data, file_offset(common), branch(common, common_entry))
        description += f', panic screen ({len(code):#x} bytes at {entry:#x}; common funnel at {common:#x})'
    args.kernel.write_bytes(data)
    print(f'patched {args.kernel.name}: stage 1 blue bar, stage 2 magenta bar, {description}')

if __name__ == '__main__':
    main()
