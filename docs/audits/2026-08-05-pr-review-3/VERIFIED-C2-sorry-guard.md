# VERIFIED — the `sorry` blind spot, and a dead guard underneath it

**Independently verified by the lead, 2026-08-05.** Reviewer R1 reported *"No live `sorry` or
`axiom` in the blind spot — but nothing would tell us if there were."* **The second clause is
right and the first is FALSE.** Verifying it surfaced a second, worse defect the reviewer did not
find. Nothing below is taken from a reviewer report; every line states its instrument.

> ⚠️ **Method note.** The first pass at this used `grep`, which returned **11 false positives** —
> docstrings reading *"Zero sorry. Zero axioms."* — and would have missed the real one had it been
> phrased differently. Lean questions go through the lean4 tooling. Every finding below was
> re-established with `lean4-skills-sorry-analyzer` (a real parser) and then with **Lean itself**.

---

## F1 — there is exactly one live `sorry` in the repository, and it is in the blind spot

**Instrument 1 — `lean4-skills-sorry-analyzer` over the whole tree:**

```
Sorry Summary: 1 total across 1 file(s) with sorries; 2039 file(s) scanned
  lean/SKEFTHawking/SingularConnSquareCrossReal.lean: 1 sorries
```

It correctly ignored `:105`, a *comment* containing the text `all_goals sorry`, and reported only
`:112`, the live tactic. This is the discrimination `grep` cannot make.

**Instrument 2 — Lean itself** (`lake build SKEFTHawking.SingularConnSquareCrossReal`):

```
⚠ [8779/8779] Built SKEFTHawking.SingularConnSquareCrossReal (9.2s)
warning: SKEFTHawking/SingularConnSquareCrossReal.lean:39:8: declaration uses `sorry`
Build completed successfully (8779 jobs).
```

Authoritative. The declaration at `:39` uses `sorry`; the module otherwise compiles clean (0
errors). Committed under *"feat: DR Harness wip"*.

**Why nothing saw it:** the module is **unreachable from `lean/SKEFTHawking.lean`**. Verified by
computing the transitive import closure of the root aggregate — **2 039 files on disk, 2 011
reachable, 28 unreachable**. `lakefile.toml` declares `[[lean_lib]] name = "SKEFTHawking"` with
**no `globs`**, so Lake builds the root plus its transitive imports only. A file on disk that
nothing imports is built by nothing, indexed by nothing, and counted by nothing.

**Scope, stated precisely.** Those 28 modules are outside the dependency closure of everything the
library exports, so **no shipped theorem can depend on this `sorry`.** Kernel purity of published
results is intact. This is not silent unsoundness in the papers. What it *is*: the project's
headline invariant is documented as **"zero sorry"** and enforced as **"zero sorry in the
transitive closure of `SKEFTHawking.lean`"**, and the two diverge by 28 modules / ~239
declarations with the qualifier stated nowhere.

**Aggravating detail:** eleven of the never-built modules assert **"Zero sorry. Zero axioms."** in
their own docstrings. Those are claims about code no compiler has ever seen. (Of the 28, ~4 are
legitimate exe/metaprogram roots — `ExtractDeps`, `AxiomAudit`, `AtlasAttr`, `AxiomClosure` —
correctly outside the library. The other ~24 are research content.)

---

## F2 — CRITICAL, and not found by any reviewer: the pre-commit `sorry` guard cannot fire, for any module

`scripts/pre-commit-sync.sh:68` and `:70`:

```sh
if [ -f /tmp/skeft-lean.$$ ] && grep -qF "declaration uses 'sorry'" /tmp/skeft-lean.$$; then
```

**`grep -F` with STRAIGHT single quotes (0x27).** Lean v4.32.0 emits **backticks (0x60)** —
confirmed by `od -c` on the real build log:

```
l a r a t i o n   u s e s   ` s o r r y `
```

**Decisive test — the guard's own expression against a log that genuinely contains the warning:**

| pattern | result |
|---|---|
| `grep -qF "declaration uses 'sorry'"` (the guard) | **NO MATCH — guard does not fire** |
| ``grep -qF 'declaration uses `sorry`'`` | matches |

So the project's **first line of defence against a `sorry`, the one that hard-blocks commits to
`main`, is inert — not only for the 28 unbuilt modules but for every module in the project.** The
guard's own comment at `:65` asserts *"Lean prints `declaration uses 'sorry'`"*, so the author
believed it; the comment also records that this build-based guard deliberately **replaced** a
grep-based source scan. The replacement was the right call — the 11 docstring false positives above
prove the old one was unusable — but the new one has never been tested against real Lean output.

**When it diverged is NOT established.** Lean's message format changed at some version; the repo is
on `v4.32.0` (bumped 2026-07-29). I did not locate the Lean source that emits it and make no claim
about which bump broke it.

**This is not a regression from ADR-009.** `main` carries the identical guard, same straight
quotes. Verified with `git show main:scripts/pre-commit-sync.sh`.

---

## F3 — the backstop, and what it does and does not cover

`axiom_closure_allowlist` / `atlas_integrity` test for `sorryAx` in the transitive axiom closure.
**The predicate logic is correct** — verified directly:

```python
core = {'propext','sorryAx'}
core.issubset(KERNEL) and not any('sorryAx' in a for a in core|set(proj))   # -> False (flagged)
```

But it reads `lean_deps.json`, which is derived from `ExtractDeps` over the **root closure** — the
same population. Verified: `SKEFTHawking.SingularConnSquareCrossReal` **is not in
`lean_deps.json`**, and there are **0 `sorryAx` records** anywhere in it.

### The layered result

| where the `sorry` is | pre-commit guard (F2) | `axiom_closure_allowlist` | caught? |
|---|---|---|---|
| in a **built** module | **dead** (quote mismatch) | alive, correct logic | **yes**, by validate.py only |
| in an **unbuilt** module | dead | blind (population) | **NO** — the live case |

I did **not** run a production-seeded mutation of a `sorry` into a built module end-to-end; that
requires a full `ExtractDeps` re-run (~30 min). The backstop's *logic* is verified; its *pipeline*
is not. Stated rather than assumed.

---

## Fixes

1. **F2 — match what Lean actually emits**, and both historical forms, so a future format change
   degrades to a false positive rather than silence. Applied.
2. **F1 — detection**: a check that every `.lean` under `lean/SKEFTHawking/` is reachable from the
   root aggregate. Derived, cannot drift, would have caught this on day one. **Not applied** — it
   goes red at 28 immediately, and closing it is an operator decision: allowlist the ~4 genuine
   exe/metaprogram roots and ratchet the rest, or import the ~24 research modules and fix what
   surfaces (starting with this `sorry`, and with 12 `FaultTolerance/*` modules that have never
   been compiled at all).
