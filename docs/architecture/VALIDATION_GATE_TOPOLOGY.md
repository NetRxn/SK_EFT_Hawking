# Validation gate topology — what runs when, and what it blocks

**Production document.** Written 2026-08-05. The gate layering was previously described only in
comments inside `gate_precheck.py` and `pre-commit-sync.sh`, so *"will this red block my Lean
wave?"* had no answerable home.

**Companions:** [`VALIDATION_ARCHITECTURE.md`](VALIDATION_ARCHITECTURE.md) ·
[`CHECK_AUTHORING_GUIDE.md`](CHECK_AUTHORING_GUIDE.md) · `docs/WAVE_EXECUTION_PIPELINE.md`

---

## 1. The tiers

| tier | trigger | what runs | blocks? | cost |
|---|---|---|---|---|
| **0 — commit** | every `git commit` | leak/IP guard (staged diff) · `pre-commit-notebooks.sh` (**only staged `.ipynb`**) · `pre-commit-sync.sh`: incremental `lake build` if `.lean` staged, then **3 named checks** | **fail-open**; hard-blocks on `main` only | <1 s + build |
| **1 — reviewer prechecks** | before dispatching an LLM reviewer | `gate_precheck.py s9` (2 checks) · `s10` (4 checks) | yes — do not spend reviewer budget on a stale tree | seconds |
| **2 — wave close** | `/skeft-qa:wave-close` | `sync.py --full`, then `gate_precheck.py s13` = **full suite + `--force-latex`** | yes — no Stage-13 dispatch on a red tree | ~2–3 min |
| **3 — submission** | before arXiv/journal | `gate_precheck.py submission` = full suite **+ the six `--strict` legs** | yes | ~8 min |
| **— CI** | *none* | deliberately no scheduled runner | n/a | n/a |

The three checks at tier 0 are `formula_grounding`, `placeholder_not_cited`,
`native_decide_regression`. They are named individually — **tier 0 never runs the full suite.**

## 2. The question this document exists to answer

> *Will a red caused by paper content block routine Lean development?*

**At tier 0: no.** Commits run three named checks, all Lean/substrate-side. A red in
`paper_latex_compiles` or `readiness_submission_gate` cannot block a commit.

**At tier 2: yes, and this is a known sharp edge.** `gate_precheck s13` runs the *whole* suite, so
closing a **pure-Lean wave** can be blocked by paper-corpus state that the wave never touched.

⚠️ **This is deliberate but under-scoped.** The rationale is sound — Stage 13 dispatches an
expensive fresh-context reviewer, and doing so on a tree with known-bad artifacts wastes it. But
"the tree is clean" is currently interpreted as *every check green*, including checks about
bundles unrelated to the wave. A Lean wave should not be gated on D3's LaTeX.

**Current state of the paper-side reds** (2026-08-05), so the sharp edge is at least legible:

| check | state | owner |
|---|---|---|
| `paper_latex_compiles` | ✅ **green** (D3's undefined `\Imm` fixed) | — |
| `bundle_metadata_matches_graph` | ❌ **14 of 21** bundles assert `stage13_status='green'` with open blockers | Stage-13 review cycle, not `bundle_readiness.py` — see §4 |
| `readiness_submission_gate` | ❌ 0 green / 3 yellow / 61 red across 64 papers | genuine corpus state → ADR-010 |

## 3. Flags and what they mean

| flag | effect | who passes it |
|---|---|---|
| `--strict` | promotes 6 submission advisories to hard failures; **implies `--no-memo`** | `gate_precheck submission` only |
| `--force-latex` | recompiles every bundle draft, bypassing the per-draft cache | `gate_precheck s13` / `submission` |
| `--no-memo` | re-measures the memoized Lean checks | manual, or implied by `--strict` |
| `--ci` | skips the 3 mtime regenerators + `notebook_exec`; enforces the coverage floor; never archives | nothing today |
| `--force-notebooks` | bypasses the notebook skip-cache | manual, after a kernel/dependency change |

`--strict` is scoped to submission by Pipeline Invariant #12, and the reason is concrete:
`bundle_source_freshness` WARNs whenever a source paper moved after its last bundle lift — the
**normal** state of an in-progress bundle. A strict wave-close gate would go red on correct work
mid-wave, and a gate that fires on correct work gets switched off.

## 4. Field ownership — who writes what

A recurring failure mode is a check telling you to run a script that cannot fix the field.

| field | written by | NOT written by |
|---|---|---|
| `blockers_open`, `advisories_open`, `open_findings`, `blocked_p1_gates`, `readiness` | `bundle_readiness.write_metadata_counts` | — |
| `stage13_status`, `stage9_status`, `stage10_status` | the **Stage-13/9/10 review cycle** (`BUNDLE_LIFT_PROCEDURE` §§8–10) | `bundle_readiness.py` |
| `freshness_stale` | `check_bundle_source_freshness.py` | `bundle_readiness.py` (deliberately — two writers made `validate.py` non-idempotent) |
| `docs/counts.json` / `counts.tex` | `update_counts.py` | — |
| `lean/lean_deps.json` + `.hash` | `extract_lean_deps.py` | — |

So a `stage13_status='green'` contradicted by open blockers means **a past review has been
invalidated by newly-minted findings** — the fix is to re-run Stage 13, not the counts writer.

## 5. Costs (measured 2026-08-05)

| | |
|---|---|
| full suite, steady state | **134.2 s** (was 317.8 s) |
| `pytest tests/` (fast) | ~285 s, 5,554 tests |
| `axiom_closure_allowlist` | 171.6 s cold / **0.1 s** memo-warm |
| `paper_latex_compiles` | 16.6 s for 21 drafts / ~0 s cached |

---

*See `docs/audits/2026-08-04-qa-qi-infrastructure/CI_DEFAULTS_ASSESSMENT.md` for why there is no
scheduled CI, and what a runner would have to fix first (mtime freshness is meaningless on a
fresh clone).*
