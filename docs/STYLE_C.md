# C style guide

C is used here only at the edges, where Bend is too slow or cannot reach:
serializing HTML and SSE, HTTP framing, and the glue around SQLite and
crypto. Every line of C is **trusted, unproven code**. The goal of this guide
is to keep that code small, boring, bounded and checked.

It adapts TigerBeetle's TigerStyle (safety, then performance, then developer
experience) and Casey Muratori's performance-aware programming (know what the
machine does, and don't pessimize).

## 0. Priorities

1. **Safety.** No undefined behaviour, no unbounded anything, no silent failure.
2. **Performance.** Decided at design time, not patched in later.
3. **Developer experience.** Clear, obvious code. Cleverness only where it
   pays for itself in 1 or 2.

When in doubt, write less C. If something can live in Bend with a law, it goes
in Bend.

## 1. Where C is allowed

- Bend effect files (`*.c` next to a `def X() -> IO(..): import "./x.c"`).
- Serializers: HTML, SSE and HTTP framing. They turn Bend's structured values
  into bytes.
- Vendored, audited, single-file libraries: the SQLite amalgamation and
  Monocypher (crypto, including Argon2 password hashing).
- Nothing else. No business rules and no authorization decisions in C. C
  never decides whether something is *allowed*; it only moves bytes that Bend
  already decided on.

## 2. Limits on everything

Every resource has a fixed upper bound, named, and checked:

```c
#define request_size_max      (64 * 1024)
#define header_count_max      64
#define post_body_size_max    (256 * 1024)
#define sse_clients_max       4096
#define fragment_size_max     (128 * 1024)
```

- Allocate everything at startup: client tables, arenas, buffers. Nothing is
  `malloc`ed in steady state. Each request gets an arena that is reset, not
  freed.
- Every loop has a known maximum iteration count, stated or asserted.
- Hitting a limit is a handled error with a clear message, never a crash and
  never a truncation.
- No recursion. The call graph must be a tree you can read.

## 3. Assertions

- On average, at least two assertions per function: preconditions,
  postconditions and invariants.
- **Assertions stay on in production.** A crash is better than corrupt state
  or a leak.
- Assert the positive and the negative space: what must hold, and what must
  never happen.
- Pair assertions: when data crosses a boundary, check it where it is written
  *and* where it is read.
- Assert compile-time facts with `_Static_assert` (sizes, alignments, limit
  relationships).

```c
static u32 escape_html(u8 *out, u32 out_cap, const u8 *in, u32 in_len) {
    assert(out != NULL && in != NULL);
    assert(out_cap >= in_len * 6);          /* worst case: every byte is &quot; */
    ...
    assert(written <= out_cap);
    return written;
}
```

## 4. Types and arithmetic

- Explicit widths only: `u8 u16 u32 u64 i32 i64` (typedef'd once). Never plain
  `int` or `long`.
- Sizes and indexes are `u32` unless they genuinely need 64 bits. Lengths
  travel with their pointers.
- Check every arithmetic operation that could overflow with
  `__builtin_add_overflow` / `__builtin_mul_overflow`.
- Name units: `timeout_ms`, `size_bytes`, `price_cents`. Put qualifiers last so
  related names line up: `latency_ms_max`, `latency_ms_min`.

## 5. Strings and bytes

- **No NUL-terminated strings inside the program.** Use a slice:
  `struct { const u8 *ptr; u32 len; }`. NUL only appears at the boundary with
  APIs that demand it (SQLite, a filename) and is added right there.
- Banned: `strcpy strcat sprintf gets strtok atoi` and any function without a
  length. Use a bounded writer with an explicit capacity, as in the escaper
  example above.
- User data is never a format string.
- Text from users is **bytes to escape**, never markup. The C escaper must
  match Bend's proven `H.text` byte for byte (see §9).

## 6. Control flow and functions

- Functions stay under about 70 lines. If one doesn't fit on a screen, split it
  by *what it does*, not by arbitrary size.
- Simple, explicit control flow: early returns for errors and one clear main
  path. No `goto`, except a single cleanup label when unavoidable.
- Every error is handled or returned upward. Never ignore a return value; mark
  functions `__attribute__((warn_unused_result))`.
- No function pointers in hot paths unless a table of them is the fastest
  thing (measure it).

## 7. Performance (the Casey part)

- **Don't pessimize.** Write the code that does the work, directly. No layers
  of abstraction that the CPU has to step through: no virtual dispatch, no
  generic containers, no per-item allocation, no "clean code" indirection.
- **Know the data.** Before writing a loop, know how many items there are, how
  big they are, and where they live in memory. Iterate over contiguous arrays.
  Pointer chasing is the enemy.
- **Batch.** One `write` of a whole SSE frame instead of many small writes. One
  SQLite transaction per batch of writes. Render a shared fragment once for all
  clients.
- **Precompute.** The page shell and fixed template parts are byte arrays
  built at startup, copied with `memcpy`.
- **Measure, then change.** Every performance claim comes with a number
  (`perf stat`, a benchmark in `bench/`) from before and after. Keep a
  performance budget per operation and fail CI when it's exceeded.
- Think in cycles and bytes. "Escaping 20 KB should take about 20 µs." If it
  takes 10× that, find out why.

## 8. Build flags

```
-std=c11 -O2 -Wall -Wextra -Werror -Wconversion -Wshadow -Wvla
-fstack-protector-strong -D_FORTIFY_SOURCE=3 -fno-strict-aliasing
-fPIE -pie -Wl,-z,relro,-z,now
```

Test and fuzz builds add `-fsanitize=address,undefined` (and `-fsanitize=fuzzer`
for fuzz targets).

## 9. Testing: C is checked against Bend

Unproven code earns trust in three ways:

1. **Differential testing against the proven Bend reference.** Every C
   serializer has a Bend twin with laws (`H.text`, `V.seat_cell`, ...). A test
   generates inputs, runs both, and requires byte-identical output.
2. **Fuzzing.** Every parser and serializer has a libFuzzer target that asserts
   the law directly: no unescaped `<` or quote in escaped output; parsing a
   rendered SSE frame gives back the original.
3. **Sanitizers in CI** on the full test suite.

## 10. Bend effects

- Bend's C runtime names (`Term`, `io_str`, `CID_*`, ...) have **no ABI
  promise**. Pin the Bend commit, and rebuild and retest effects on every
  upgrade.
- Blocking calls (SQLite, file IO, hashing) go through `io_work` on a helper
  thread, never directly on the event loop.
- Free what `io_cstr` hands you. Better: copy it into the request arena
  immediately.
- User-defined handle types aren't supported yet, so global resources (the
  SQLite connection) live in one explicit `static` struct, initialized once and
  asserted on every use.
- When vendoring SQLite into a Bend effect, add
  `#define SQLITE_INT64_TYPE long` first; SQLite's `u64` otherwise clashes with
  the runtime's.

## 11. Review checklist

- [ ] Is this C, or should it be Bend with a law?
- [ ] Every loop and buffer bounded, with a named limit?
- [ ] At least two assertions per function, positive and negative space?
- [ ] No unbounded string functions, no format strings from data?
- [ ] Every overflow checked, every return value used?
- [ ] Differential test against Bend, and a fuzz target?
- [ ] A benchmark number for anything claimed to be fast?
