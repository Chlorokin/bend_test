# CLAUDE.md (draft: rename to `CLAUDE.md` at the repo root)

## What this project is

An experiment to find out **how far a web app can get on performance, security
and correctness at the same time** by combining:

- **Bend 2** for every decision the app makes, with machine-checked laws
  (`LAWS.bend`) and proofs (`PROOF.bend`).
- **C** at the edges only: serialization, HTTP framing, SQLite and crypto glue.
  C is written TigerStyle and kept small, bounded, fuzzed and differentially
  tested against Bend.
- **SQLite** (the single-file amalgamation, compiled into the binary) for
  storage.
- **Datastar** for the UI: server-rendered HTML fragments over SSE, with as
  little client JS as possible.

The goal isn't to finish a blog. It's to **measure and write down** where
proofs reach, where they stop, what they cost, and how fast the result is.
Findings go in `FINDINGS.md`. An honest negative result is a success.

Read first: `docs/STYLE_BEND.md`, `docs/STYLE_C.md`, and the Proof Tickets
code in `core/` and `server/` (a working example of Bend + Datastar with a
model-vs-database cross-check).

## Priorities

1. **Correctness and security:** proven where possible, checked everywhere else.
2. **Performance:** designed in, measured, with budgets.
3. **Developer experience.**

Never trade 1 for 2. When a proof is too expensive, say so in `FINDINGS.md` and
fall back to differential tests and fuzzing. Never quietly drop a guarantee.

## Architecture

```
browser ── Datastar (SSE + @post) ──▶ HTTP/SSE framing (C)
                                         │ requests as Bend values
                                         ▼
                                 Bend core (native binary)
                                 · parse & validate requests      ◀── laws
                                 · authorize, decide, plan writes ◀── laws
                                 · build views as structured data ◀── laws
                                         │ effects
                         ┌───────────────┼────────────────┐
                         ▼               ▼                ▼
                 SQLite (C effect)  HTML/SSE serializer  crypto (Monocypher, C)
                                    (C, checked against Bend's reference renderer)
```

- The server **is** the Bend native binary (`bend main.bend -o app`). C effects
  are pasted into it by the Bend compiler, so the deployable is one binary
  depending only on libc.
- Develop against the JavaScript target (fast rebuilds, bun's built-in SQLite
  for the JS side of effects). Benchmark only native builds.
- **Trust boundary:** everything in `.bend` with a law is proven; `.c` and
  the vendored libraries are trusted. Keep a table of every trusted component
  in `FINDINGS.md`, with how it's checked.
- Where Bend models the database, cross-check the model against SQLite at
  runtime and in tests, as Proof Tickets does with TigerBeetle.

### Why C and not Zig

Bend's effects are `.c` files that the compiler pastes into its own generated
C. The edge code therefore has to be C. Zig is fine for standalone tools and
benchmarks, but not in the product path.

## Choosing where things run: server, vanilla JS, or local-first

Pick the **first** tier that works. Justify anything below tier 1 in a code
comment.

**1. Server-rendered (Datastar SSE): the default.**
- Anything shared, contended, authoritative or covered by a law: posts,
  comments, permissions, publishing, moderation, anything security-relevant.
- The server owns the state and patches fragments by element id.
- Render shared fragments **once** and send them to every client. Send
  per-viewer fragments per client, and only the ones that changed.

**2. Vanilla JS (Datastar signals, or small scripts).**
- Presentation state nobody else cares about, or that must respond within a
  frame (under 16 ms): toggles, tabs, sorting or filtering data already on the
  page, form hints, the caret and selection in the editor, animations.
- Never the source of truth. Anything that matters is re-validated by the
  server's laws.

**3. Local-first (browser SQLite + sync).**
- Single-owner data that must work offline or instantly, and whose conflicts
  merge cleanly: **drafts in the editor**, personal notes, reading lists.
- The merge function is written in Bend with merge laws (commutative,
  associative, idempotent, nothing lost) and runs in the browser via Bend's JS
  target and on the server natively: the same proven code on both sides.
- **Never** for contended or authoritative data (publishing, permissions,
  anything two users can race on).

## Fast JS (Casey-style: know what the engine does)

The client JS is small, so write it to be fast by construction:

- **Monomorphic shapes.** Create objects with all their fields in the same
  order, in one place (a constructor function or literal). Never add or
  `delete` properties later. Keep each call site seeing one shape: V8 inline
  caches go polymorphic after 2–4 shapes and megamorphic after that.
- **Small integers stay small.** Keep hot numbers as 31-bit integers (`x | 0`)
  or put them in typed arrays. Don't mix ints, floats and `undefined` in one
  array.
- **Typed arrays for data.** The editor's text buffer is a gap buffer or piece
  table over a `Uint8Array` or `Uint16Array`, not a string rebuilt on every
  keystroke. Line starts go in an `Int32Array`.
- **No allocation in hot paths.** No closures, spread, `map`/`filter` chains or
  template-string churn per keystroke or per frame. Reuse objects and buffers.
  Garbage collection pauses are dropped frames.
- **The DOM is the expensive part.** Batch reads, then writes (never interleave
  layout reads like `offsetHeight` with writes). One `requestAnimationFrame`
  per frame. Change `textContent` rather than `innerHTML` where possible. Use
  event delegation on a parent, not a listener per element.
- **Plain loops beat clever ones.** `for (let i = 0; i < n; i++)` over arrays;
  avoid `arguments`, `try/catch` in the innermost loop, `with`, `eval`.
- **Ship less.** No framework and no bundle beyond Datastar plus a few KB of
  our own. Budget: under 30 KB of JS total, compressed.
- **Measure** with `performance.now()` and the Chrome profiler. Each claim
  comes with a number.

## The test app: a blog with an editor

Small feature set, deep guarantees:

- Authors sign up, write posts in a Markdown editor (live preview), save
  drafts (local-first, works offline), and publish.
- Readers view published posts and comment. Authors moderate comments on their
  own posts.
- An admin can suspend accounts.

### Laws to prove (in `LAWS.bend`)

**Output safety (XSS and injection)**
- `text_is_clean`: escaped user text contains no `< > " '`.
- `markdown_allowlist`: rendered Markdown contains only allowlisted tags and
  attributes, for any input.
- `markdown_well_formed`: every tag the renderer opens it also closes, in
  order.
- `links_are_safe`: every `href`/`src` the renderer emits is relative,
  `https:`, `http:` or `mailto:`. Never `javascript:`, `data:` or `vbscript:`,
  whatever the case, spacing or encoding.
- `names_cannot_inject`: user text can't change the tag structure of any view
  (as in Proof Tickets).
- `no_header_splitting`: response header values never contain CR or LF.
- `sse_round_trip`: parsing a framed SSE event gives back the original
  fragment, so user text can't break out of an event.
- `sql_params_only`: queries are built from a typed query value; user strings
  only ever appear as bound parameters, never in SQL text.

**Authorization and confidentiality**
- `only_author_edits`: editing or deleting a post by anyone but its author (or
  an admin) changes nothing.
- `drafts_are_private` (non-interference): the page served to any user who
  isn't the author is byte-identical for any two states that differ only in
  that author's drafts.
- `suspended_cannot_write`: no command from a suspended account changes
  anything.
- `deleted_stays_deleted`: a deleted comment is never rendered again, on any
  page.
- `csrf_required`: every state-changing request without a valid token for its
  session changes nothing.

**Integrity**
- `history_append_only`: the revision history of a post only grows; published
  revisions are never rewritten.
- `draft_merge_converges`: merging draft edits is commutative, associative and
  idempotent, and never loses an edit.
- `slug_unique_and_safe`: slugs are unique and contain only `[a-z0-9-]`, so no
  path traversal, whatever the title.
- `redirects_are_local`: every redirect target is a same-site relative path
  (no open redirect).
- `rate_limit_holds`: for any request sequence, a client never exceeds the
  allowed actions per window.

**Text hygiene**
- `no_bidi_controls`: titles, slugs and names never contain Unicode
  bidirectional override characters (Trojan-source style spoofing).
- `limits_enforced`: every stored field is within its size limit, checked
  before storage.

**Trusted, not proven (tested instead)**
- Password hashing (Argon2id via Monocypher) and constant-time token
  comparison: timing is outside Bend's reach. Test with known-answer vectors,
  and mark them trusted in `FINDINGS.md`.
- The C serializers: differential tests against Bend's reference renderer,
  plus fuzzing.
- SQLite itself, the C compiler, the Bend runtime and the browser.

### Response headers (asserted in a law: every response has them)

`Content-Security-Policy: default-src 'self'; script-src 'self'; object-src 'none'; base-uri 'none'; frame-ancestors 'none'`,
`X-Content-Type-Options: nosniff`, `Referrer-Policy: same-origin`, cookies
`HttpOnly; Secure; SameSite=Strict`.

## Performance budgets (measure on every change that could affect them)

- Server p50 < 1 ms and p99 < 5 ms for a post page (excluding network), at 1k
  requests per second.
- SSE fan-out: one change reaches 1,000 connected clients in < 50 ms.
- SQLite: > 20k small writes per second, batched in transactions.
- Editor: keystroke to preview update < 16 ms for a 50 KB post.
- Page weight: HTML < 30 KB and JS < 30 KB compressed for a typical post.
- Keep benchmark scripts in `bench/` and results in `FINDINGS.md`, with the
  machine they ran on.

## Rules for Claude working in this repo

- Run `bend core/PROOF.bend` before every commit. It must print
  `All terms check.`
- `LAWS.bend` belongs to the human. Propose new laws freely, but never weaken,
  remove or rename one without asking.
- Put new decision logic in Bend with a law. Put it in C only if it moves bytes
  and has no policy. Say which, and why, in the commit message.
- Every C function gets a differential test against its Bend twin and, if it
  parses or serializes, a fuzz target.
- No new dependencies without asking. Allowed today: SQLite amalgamation,
  Monocypher, Datastar (vendored), bun (build and dev only), clang.
- Every performance claim comes with a measurement. Every "proven" claim names
  the law.
- When something can't be proven, write it in `FINDINGS.md` under "limits"
  with what was done instead.
- Known Bend limits: runtime `Nat` stops at 2⁴⁸; the checker overflows on large
  concrete numbers; `String` is a slow linked list; the JavaScript target is
  about 50× slower than native; C effects have no ABI promise, so pin Bend.
