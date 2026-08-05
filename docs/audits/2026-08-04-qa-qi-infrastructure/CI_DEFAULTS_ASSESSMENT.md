# CI defaults — assessment (R5-C1)

**Question put:** what are sensible CI defaults? The stated intent was to avoid bogging down
development with `--strict`-style filtering, given that surface area is already called at
other stages of the harness.

**Finding: that intent is correct and the measurements support it — but it is not why CI is
absent.** There is a second, harder reason nobody had written down, and it would have broken
the obvious CI workflow on its first run.

Every number below is measured on this branch, 2026-08-05.

---

## 1. The blocker nobody recorded: mtime freshness is meaningless on a fresh checkout

`counts_fresh`, `tables_fresh` and `claim_clusters_fresh` decide staleness by comparing
mtimes. Git sets every file's mtime to checkout time, in index order — so on a fresh clone
`docs/` is written before `lean/`, `src/` and `papers/`.

Measured on a real `git clone` of this branch:

```
docs/counts.json               mtime = 1785915261.937
  src/core/constants.py                1785915262.606   STALE -> regenerate
  src/core/visualizations.py           1785915262.608   STALE -> regenerate
  lean/lean_deps.json                  1785915262.338   STALE -> regenerate
  newest of 2039 *.lean                1785915262.269   STALE -> regenerate
```

**All four criteria read stale, on an untouched clone.** `counts_fresh` would then shell out
to `update_counts.py` — which invokes `ExtractDeps` through `lake`, under a **1800-second
timeout** — on a runner that has no Lean toolchain. `tables_fresh` (300 s) and
`claim_clusters_fresh` follow.

So the naive workflow (`uv run python scripts/validate.py`) does not fail fast on CI; it
either hangs for half an hour or dies inside a regenerator, on every push, forever. That is a
design problem, not an oversight, and it is the first thing any CI work has to solve.

**Corollary worth keeping:** the three regenerators are *self-healing developer conveniences*
that happen to be registered as checks. They are the right thing at a workstation and the
wrong thing on a runner.

## 2. What the suite actually costs

| | measured |
|---|---|
| 55 checks (excluding the 3 regenerators + `notebook_exec`) | **332.6 s** |
| …of which **43 checks run in under 1 second** | ~15 s total |
| `axiom_closure_allowlist` | **145.4 s** — needs `lake` |
| `lean_docstring_refs_resolve` | **52.8 s** — greps `.lake/packages/mathlib` |
| `readiness_verdicts_agree` / `graph_integrity` / `prose_theorem_reference_coverage` | 26.7 / 25.8 / 23.7 s |
| `pytest tests/` (fast) | **270 s** — 5,447 passed |
| `pytest tests/ -m ''` (with slow) | +~10 min (`test_build_graph.py` alone is 573 s) |
| `notebook_exec` on a cold cache | 91 notebooks — the cache is **gitignored**, so CI always pays full price |
| `validate.py --strict --force-latex` | 480 s |

**The cost is not spread — it is four checks.** Nearly the whole suite is free.

## 3. The trap in the cheap answer

Drop the Lean toolchain from CI and the suite gets ~200 s faster. It also **stops running 7
checks that read `lean_deps.json` and 3 that shell to `lake`** — and reports green.

That is *"absence of measurement rendered as success"*, the exact finding this whole audit
exists to close, reintroduced at the CI layer. A CI job that silently covers 48 of 59 while
printing a green tick is worse than no CI, because it manufactures confidence.

**Any CI here must assert its own coverage.** That is the load-bearing requirement, and it is
what distinguishes this design from the one-file GitHub Actions workflow R5 proposed.

## 4. Recommended defaults

The harness is already tiered. CI should fill the **unattended** tier — the one a developer
can skip — not duplicate the others.

| tier | trigger | runs | cost | exists? |
|---|---|---|---|---|
| 0 | pre-commit hook | 3 checks, fail-open, `main`-only | <1 s | ✅ |
| **1** | **CI: every push / PR** | `pytest tests/` + `validate.py --ci` | **~10 min** | ❌ **the gap** |
| **2** | **CI: nightly / pre-merge** | `pytest -m ''`, `notebook_exec`, `--force-latex` | ~45 min | ❌ |
| 3 | wave close | `gate_precheck.py s9` / `s10` / `s13` | varies | ✅ |
| 4 | submission | `gate_precheck.py submission` (`--strict`) | 8 min | ✅ |

### `--strict` stays out of tier 1 — confirmed, with the reason

The recollection is right, and there is a concrete demonstration. `bundle_source_freshness`
WARNs whenever a source paper moved after its last bundle lift — **the normal state of an
in-progress bundle**. Under `--strict` that is a hard fail, so a strict CI would go red on
correct work in the middle of every wave. A gate that fires on correct work gets switched off,
and then it protects nothing.

`WAVE_EXECUTION_PIPELINE.md` Invariant #12 already scopes `--strict` to the Paper Submission
Gate. Tier 4 is its home; it acquired a caller on 2026-08-05 and it is not needed anywhere
earlier.

### What `--ci` should mean

A mode, not a check list — so it cannot drift from the registry:

1. **Skip the three regenerators.** Their premise (mtime) is invalid on a runner. Their
   *content* obligation is covered elsewhere: `paper_table` now parses the shipped table
   (QI-31) and `inventory_index_autogen_fresh` compares content.
2. **Skip `notebook_exec`.** No cache exists on a runner; it belongs to tier 2.
3. **Assert a coverage floor.** Fail if the number of checks that actually executed drops
   below a frozen count — the house ratchet idiom, applied to CI itself. A missing toolchain
   then shows up as a red build with "48 of 56 ran", not a green tick.
4. **Never archive**, never write to the tree — a CI run that dirties the working tree cannot
   be re-run idempotently.

**Measured end-to-end after implementing it:** `validate.py --ci` runs **53 of 55 in 397 s**
(the two reds are the known publication-workstream pair), and the coverage floor is satisfied
at exactly 55 — zero headroom. With `pytest tests/` at 270 s, **tier 1 is ~11 minutes**.

That is more than the 8 min this section first estimated from summing per-check times; the
difference is interpreter start-up and the one-per-run `lean_deps` snapshot. Recorded as
measured rather than as projected — the estimate was mine and it was 30 % light.

## 5. What this does *not* solve

CI is R5-C1. It does **not** address C2–C5 (figure content, number-recomputation,
theorem-statement correspondence, citation content) — those are absent *checks*, and CI can
only run checks that exist. Running an empty gate more often changes nothing.

Per the operator's routing, C2–C5 are **submission blockers and non-infrastructural → ADR-010.**

## 6. Recommendation

Ship tier 1 and tier 2. The enabling work is the `--ci` mode with the coverage floor — without
it the workflow file is actively harmful, because it will be green for the wrong reason.
