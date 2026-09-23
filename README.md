# Proof Tickets

A small box office for testing how far proofs go in a real app. It uses:

- **[Bend 2](https://github.com/bendlang/bend)** for the business logic, a model of TigerBeetle, the HTML views, and **10 machine-checked laws** about all of them.
- **[TigerBeetle](https://tigerbeetle.com)** as the real ledger. Seats and money are accounts, and a hold is a linked pair of pending transfers.
- **[Datastar](https://data-star.dev)** for the UI. The server pushes HTML fragments over SSE, so every visitor sees the same seat map live.

Visitors get a $200 wallet. They can hold a seat (which reserves the seat and the money together), then pay or release it before the timer runs out. They can also try the "break it" buttons, each of which attacks one law.

## Run it

You need [bun](https://bun.sh), git, curl and unzip. The app is tested on Linux; the setup script also knows the macOS download.

```sh
./scripts/setup.sh   # pinned Bend compiler, TigerBeetle 0.17.9, npm deps; checks the proofs
./scripts/dev.sh     # fresh TigerBeetle on :3001, app on http://localhost:3000
```

Open two browsers (or one normal window and one private window) to be two visitors.

To check the proofs yourself:

```sh
bun run prove        # bend core/PROOF.bend  ->  "All terms check."
```

## The laws

`core/LAWS.bend` states them and `core/PROOF.bend` proves them. The server re-runs the checker when it boots and shows the result on the page.

| Law | Says |
|---|---|
| `no_overdraft` | No transfer of any kind (create, post, void) can take a seat or wallet below zero. This is TigerBeetle's `debits_must_not_exceed_credits`, stated over the model. |
| `chain_no_overdraft` | The same holds for linked chains. |
| `all_or_nothing` | A chain either fully succeeds or leaves the ledger exactly as it was. |
| `retry_is_harmless` | Applying the same transfer twice is the same as applying it once. |
| `wallet_never_overdrawn` | No sequence of visitor commands, of any length, with any ids, overdraws a wallet. |
| `seat_never_oversold` | No sequence of visitor commands puts more than one hold or sale on a seat. |
| `only_holder_pays` / `only_holder_releases` | A hold that isn't yours produces no transfers at all. |
| `text_is_clean` | Escaped visitor text never contains `<`, `>`, `"` or `'`. |
| `names_cannot_inject` | A seat's HTML has the same tag structure whatever the holder's name is. |

## How it fits together

```
browser ──Datastar/SSE──▶ server/server.ts ──▶ core/*.bend   (decides, renders, is proven)
                               │
                               └──▶ server/bridge.ts ──▶ TigerBeetle   (the real ledger)
                                         ▲
                                         └── runs every command on BOTH, compares
                                             statuses and every account's 4 balances
```

- `core/ledger.bend` models the part of TigerBeetle the app uses. It stores a log of transfers and derives balances from it, and it runs the checks in TigerBeetle's order so the status codes can be compared one for one.
- `core/boxoffice.bend` turns each command (join, hold, pay, release) into a linked chain of transfers and derives the seat map.
- `core/html.bend` and `core/view.bend` produce the HTML.
- `server/` is plain TypeScript: sessions, SSE, hold timers, and the translation to TigerBeetle's wire format. It imports the `.bend` files directly and calls them in-process.

## What the proofs don't cover

The page lists these too. **Break the model** demonstrates the first one live.

1. **The model is not the database.** Every law is about `ledger.bend`. That TigerBeetle behaves the same way is only *checked*, one command at a time, by the cross-check. When the model is wrong (it has no clock, so it doesn't know TigerBeetle expired a hold), the cross-check turns red and names the accounts that differ. From that point on, the proofs describe a ledger that isn't the real one.
2. **Time and liveness.** The model has no clock. "Holds expire" is a `setInterval` in the shell, with TigerBeetle's own timeout as a backstop. The proofs can say what happens *if* a hold is released, but not that it *will* be.
3. **The shell.** The id encoding (typed ids to u128), flag translation, status-code mapping, sessions and the TypeScript-rendered panels are all unproven. The panels call the proven escaper, but nothing forces them to.
4. **Numbers.** Bend's runtime `Nat` stops at 2⁴⁸, while TigerBeetle uses u128. That is why ids are small counters and prices are in cents.
5. **The laws.** A proof shows the code meets the law as written. A law nobody wrote down, such as refunds or a per-visitor seat limit, is simply not there.
6. **The idempotency law only helps callers who reuse ids.** The server assigns fresh ids to each click, so a double-clicked "Pay" is stopped by `AlreadyPosted`, not by `retry_is_harmless`.
7. **The retry law is about state, not status codes.** TigerBeetle 0.17 answers a retried *failed* transfer with `id_already_failed`, but the model re-evaluates it and returns the original error. Both leave the ledger unchanged, so the law holds on both sides, but the cross-check would flag the different codes.

## What the proofs cost

Non-comment lines:

| | code | proof |
|---|---|---|
| Bend core (ledger model, box office, HTML) | ~710 | ~950 (`PROOF.bend`, 111 lemmas) + 77 (`LAWS.bend`) |
| TypeScript shell (unproven) | ~550 | — |

Notes from writing them:

- **Designing for proof mattered more than proving.** Storing a transfer *log* and deriving balances meant no subtraction ever appears, so every balance lemma is "this sum went up" or "this sum went down". Typing account ids (`Seat{k}` rather than a u128) made "a hold never credits a seat" a fact the checker computes instead of arithmetic about ranges.
- **Bend has no tactics.** Each branch in the program needs a matching lemma. `ledger.apply` has 7 checks in TigerBeetle's order, so three different laws each walk those 7 helpers (`safe_*`, `shape_*`, `seen_*`). The generic `shape` lemma ("a transfer either changes nothing or commits exactly one entry") was the reusable piece.
- **Some facts are proved by computation.** `genesis_bound` splits the seat number 12 ways, and in each branch the checker simply evaluates opening day.
- **Checking is fast:** about 1.3 s for everything, so re-proving on every server boot is cheap.
