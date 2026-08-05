# CI defaults — assessment (R5-C1)

**Question put:** what are sensible CI defaults? The stated intent was to avoid bogging down
development with `--strict`-style filtering, given that surface area is already called at
other stages of the harness.

**Answer, revised 2026-08-05 (v2):** the `--strict` half of that intent is right and is
demonstrated below. But the framing of the question — *when should a runner run the suite* —
was the wrong one, and v1 of this document answered it. The right question is *why does the
suite cost 332 s when the diff touched three files*, and answering it removes most of the
reason to want a runner at all.

Timings below are measured on this branch. **Change-frequency figures are measured on `main`**,
not here — see §2 for why that distinction cost this document a wrong headline.

---

## 0. What v1 got wrong, and why

v1 proposed a five-tier plan whose live tiers were a **~11-minute job on every push** and a
**~45-minute nightly**. Both were artifacts of an unexamined choice: *put the work on a fresh
GitHub Actions clone*. Three consequences followed from that choice alone, and none of them
are properties of the work itself.

1. **The nightly existed because of a cache that a fresh clone does not have.** `notebook_exec`
   already carries a per-notebook content-hash skip-cache (`NOTEBOOK_EXEC_CACHE`), and
   `scripts/pre-commit-notebooks.sh` already executes **exactly the staged `.ipynb` files** on
   every commit. Change-scoped notebook execution is not a thing to build — it has been in the
   harness the whole time. It only looks expensive from a runner, where the cache is gitignored
   and every one of the 91 notebooks is "changed".
2. **The 11-minute push job duplicated three gates that already fire.** `pre-commit-sync.sh`
   runs an incremental `lake build` on staged `.lean` plus three fast soundness checks;
   `gate_precheck.py s9/s10/s13` gates each reviewer dispatch; `wave-close` runs the full sync
   and gate. A push-triggered re-run of the same suite is not defence in depth, it is the same
   depth twice.
3. **Neither tier addressed the actual cost.** Both simply relocated a 332-second suite.

The measurements in v1 were sound; the instrument was wrong. What follows re-derives from the
harness that exists.

**v2 then made its own version of the same error** — measuring change frequency on *this*
branch, which is core QA/QI infrastructure and therefore nothing like normal operation (normal
work here is Lean, or paper/notebook). §2's frequency table is re-measured on `main` and the
correction is marked; one revert decision (§3) had to be re-justified because its stated reason
was a branch artifact. Recorded rather than quietly fixed, because the failure is
representative: *a measurement is only as good as the population it was taken over*, and this
document has now got that wrong in two different directions.

---

## 1. The harness, as it actually is

| stage | trigger | what runs | change-scoped? |
|---|---|---|---|
| leak / IP guard | every commit | staged diff only | ✅ |
| `pre-commit-notebooks.sh` | every commit | **only staged `.ipynb`** | ✅ |
| `pre-commit-sync.sh` (b) | staged `.lean` | incremental `lake build` | ✅ |
| `pre-commit-sync.sh` (c) | every commit | 3 fast checks, fail-open, block on `main` only | n/a (<1 s) |
| **`validate.py` (full)** | **wave close · `/sync` · the `/goal` acceptance gate** | **all 59 checks, every time** | ❌ |
| `gate_precheck s9/s10` | before a reviewer dispatch | 1 and 4 checks | ✅ |
| `gate_precheck s13` | before adversarial review | full suite + LaTeX | ❌ |
| `gate_precheck submission` | before arXiv/journal | full + the six `--strict` legs | correct as-is |

**Every stage in this harness is change-scoped except the expensive one.** The commit gate
scopes notebooks to what you staged and Lean to whether you touched Lean; the full suite scopes
nothing. So the harness offered two settings — 3 checks in under a second, or 59 checks in
332 s — with nothing in between, and the `/goal` loop pays the second one at every wave close.

## 2. Where the cost is, and where the changes are

**Cost concentration** (55 checks, excluding the three regenerators and `notebook_exec`):

| | measured |
|---|---|
| whole suite | **332.6 s** |
| **43 checks finishing in under one second** | ~15 s total |
| `axiom_closure_allowlist` | **145.4 s** (`lake env lean --run AxiomAudit`) |
| `lean_docstring_refs_resolve` | **52.8 s** (greps the pinned Mathlib tree) |
| `paper_latex_compiles` | **16.6 s** (pdflatex × 21 bundle drafts) |
| `readiness_verdicts_agree` / `graph_integrity` / `prose_theorem_reference_coverage` | 26.7 / 25.8 / 23.7 s |

**Change frequency.** ⚠️ v2 of this document measured the last 400 commits *on this branch* and
built its argument on that. **That window is unrepresentative** — this branch is core QA/QI
infrastructure, where normal work is Lean or paper/notebook. Corrected, over **all 5,814 commits
on `main` since 2026-03-01**:

| tree | commits | share |
|---|---|---|
| `lean/` | 4,526 | **78 %** |
| `docs/` | 1,424 | 24 % |
| `src/` | 340 | 5.8 % |
| `papers/` | 338 | 5.8 % |
| `scripts/` | 281 | 4.8 % |
| `tests/` | 193 | 3.3 % |
| `notebooks/` | 49 | **0.84 %** |

This **weakens** the headline claim v2 made from the branch window ("`lean/` does not move in
53 % of commits, so half of every run is wasted"). On real history Lean moves in **78 %** of
commits, so on a Lean wave the memo correctly re-measures and saves nothing. Its value is
narrower and worth stating exactly:

- **Repeat runs inside one gate cycle** — the common case. A `/goal` loop runs `validate.py`,
  fixes a doc/paper/count issue, and runs it again; every re-run after a non-Lean fix now costs
  0.1 s instead of 198 s for those two checks.
- **Paper / notebook / doc-side waves**, where Lean genuinely did not move.

The `notebooks/` figure survives the correction — **0.84 %** on `main`, against 0.75 % on the
branch. Read it carefully though: it is a *per-commit* rate, and notebook work arrives in bursts
(a wave touches several at once, then nothing for weeks), so it does **not** say notebook work
is unimportant. What it supports is only the narrow claim it is used for here: a *nightly*
re-execution of all 91 buys nothing, because notebook execution is already scoped twice over —
by content hash in the skip-cache, and to the staged files at commit time.

The `papers/` figure cuts the other way and makes the silently-skipping LaTeX gate *more*
serious, not less.

`paper_latex_compiles` shows what the project had been doing about this instead. It responded to
its own cost by *skipping by default*: without `--force-latex` it returned `passed=True` with
detail `SKIPPED (slow)`. A plain `validate.py` therefore reported that check green while **D3
carried two fatal compile errors**. The "slow" premise was never re-measured either — 21 drafts
is 16.6 s, not the "minutes" its docstring claimed. That is this audit's central defect wearing a
performance justification, and it is the predictable end state of a gate that is expensive and
cannot be scoped: it gets turned off.

## 3. What was built

Not a runner. Two change-scoping caches, in the idiom the repo already uses twice
(`extract_lean_deps.py`'s source-hash skip; `NOTEBOOK_EXEC_CACHE`):

- **`scripts/validation/_memo.py`** — a shared input-fingerprint memo. A check's verdict is
  reused only while a fingerprint of *every* input it reads is unchanged since its last PASS.
  Applied to `axiom_closure_allowlist` (key: Lean sources + toolchain/Mathlib pin set +
  `AXIOM_METADATA` + `is_native_decide_axiom`) and `lean_docstring_refs_resolve` (Lean sources +
  pin set).
- **`paper_latex_compiles` per-draft cache** — a draft is recompiled only when its full input
  closure moves (the `.tex`, everything it `\input`s transitively, its figures, its `.bib`).
  With the cost gone, **the slow gate is gone too: the compile is now always on.**

**Measured:** `axiom_closure_allowlist` **171.6 s → 0.1 s** when the Lean substrate has not
moved. LaTeX compiles every run at ~0 s for an unchanged corpus instead of not compiling at all.

**The load-bearing direction, proven in the production tree** — a cache that hits is worthless
if it also hits across a change it should have caught. Four consecutive real runs of
`validate.py --check lean_docstring_refs_resolve`, appending one comment line to
`lean/SKEFTHawking/A1Ext.lean` between the second and third:

| # | tree state | result |
|---|---|---|
| 1 | unchanged | `SKIPPED (cached)` — **0.1 s** |
| 2 | unchanged | `SKIPPED (cached)` — **0.1 s** |
| 3 | **one `.lean` file edited** | **re-ran — 51.4 s** ✅ |
| 4 | same edited state | `SKIPPED (cached)` — 0.1 s |

Row 3 is the assertion that matters, and it is measured against the real tree rather than a
fixture. Note also what row 4 does *not* claim: the cache stores **one entry per check**, keyed
on the last passing state, so reverting a file to a previously-vetted state MISSES and re-runs.
That is the safe direction; a keyed history would trade it for unbounded growth
(`lean_docstring_refs_resolve` alone replays 844 detail lines).

**Full-suite effect, end to end:**

| `validate.py --no-archive`, all 59 checks | |
|---|---|
| before (recorded at ADR-009 close, 2026-08-04) | **317.8 s** — *with `paper_latex_compiles` skipping* |
| after, steady state | **134.2 s** — *with the LaTeX compile actually running* |

⚠️ Measured properly on the second of two consecutive runs, and the reason is worth keeping.
The *first* attempt at this number came back **360.6 s — slower than baseline** — because the
seeded-invalidation probe above had just left the cache keyed to the edited tree, so both Lean
checks correctly re-measured. A single post-change run would have been a wrong number in either
direction depending on what ran before it.

### Built, measured, and reverted: per-notebook `src/` scoping

`notebook_exec` scopes per notebook by *content*, but its cache is gated on one
fingerprint of **all** of `src/`, so any `src/` edit discards all 91 entries at once. That
looks like exactly the over-broad invalidation this section is about, so it was built:
module-level `src.*` dependency graph, AST-parsed, transitively closed per notebook.

It buys almost nothing, and getting to that answer took **two** measurements, because the
first one was made on the wrong window:

- ❌ **First (branch, wrong):** *"of the last 400 commits, 42 touch `src/` and all 42 touch
  `src/core/`; zero touch `src/` without it."* True of this infra branch, and false in
  general. On `main` since 2026-03-01, **62 of 340** `src/` commits touch `src/` *without*
  touching `src/core/` — so this argument does not hold.
- ✅ **Second (structural, holds):** blast radius under exact module-level dependency
  closure, measured by really editing each file:

  | edited file | notebooks that re-execute |
  |---|---|
  | `src/core/formulas.py` | **91 / 91** |
  | `src/vestigial/hs_rhmc_mlx.py` | 82 / 91 |
  | `src/wkb/spectrum.py` | 82 / 91 |
  | `src/second_order/coefficients.py` | 82 / 91 |
  | `src/resurgence/bdg_self_energy.py` | 0 / 91 |

  Even a *non-core* edit invalidates **82 of 91**, because every notebook imports `src.core`
  and `src.core`'s re-exports pull the domain packages back in — which Pipeline Invariants
  #1–#3 make structural, not incidental.

So the exact answer is 82 where the coarse answer is 91: a ~10 % saving, on the 1 % of
commits that touch `src/` without `src/core/`. Not worth a dependency-graph walker. And a
notebook whose physics inputs moved genuinely must re-run (correctness over expediency).
Reverted, with the finding recorded in the check's docstring as a settled fork.

Worth stating because the scoped version **passed its own tests and produced 8 distinct
fingerprints** — machinery that does nothing, looking like it works. It also turned up a real
bug on the way: a regex import-scanner matched `src/core/aristotle_interface.py:9`, where a
*docstring example* imports a module path that does not exist, and that one phantom edge
poisoned 85 of 91 closures.

### The hazard this creates, and the four guards on it

A memoized check reports PASS **without measuring anything** — which is precisely the defect
this audit exists to close, one layer up. It is sound only if the key covers every input, and a
key that misses one is *worse* than no cache: it manufactures a green tick that survives the
very change it should have caught. So:

1. **The body's own source is folded into every key automatically** (by `memoized`, not by each
   caller — a guard you can forget to apply is the parallel-list failure this codebase keeps
   re-finding). Editing a check invalidates its cache.
2. **`tests/test_validation_memo.py` seeds a real change into each declared input, in the
   production tree, and asserts the key moves** — per QI-30, a mutation caught against a patched
   fixture establishes nothing about production.
3. **Only PASS is cached, and a FAIL evicts.** A broken check re-runs every time; D3 cannot be
   recorded once and skipped forever.
4. **The skip is visible** in the report, and says what it is conditional on.

Plus two escapes: `--no-memo`, and **`--strict` implies it** — the Paper Submission Gate is the
one irreversible consumer, so it always re-measures. `tests/conftest.py` disables the memo
suite-wide, so no test can write a cache entry keyed on the real tree from a verdict reached
under a monkeypatch.

### What this does NOT speed up — stated because it is the dominant mode

On a **Lean wave** — 78 % of commits — `axiom_closure_allowlist` must re-run, and 145 s is
what it costs. The memo is correct to save nothing there. Anyone reading this document as
"the suite is fast now" has read it wrong: what got cheaper is the *repeat* run and the
paper/doc-side wave.

The remaining lever, unbuilt and not proposed here, is making that check **incremental** —
re-deriving the axiom closure only for declarations whose transitive dependencies moved,
rather than the whole environment. `AxiomAudit.lean` already memoizes `AxiomClosure`
internally, so the work is in giving it a persistent cross-run cache, which is Lean-side and
a different piece of work from anything in this branch. Filed as an observation, not a plan.

## 4. The recommendation

**No scheduled CI. No nightly. No per-push suite.** With §3 in place the harness's own stages
carry the load at a cost proportional to the diff, and each of the three jobs v1 proposed is
either already done by a cheaper gate or was an artifact of the runner.

`--strict` stays out of routine gates, as originally intended, and there is a concrete
demonstration rather than an agreement: `bundle_source_freshness` WARNs whenever a source paper
moved after its last bundle lift — **the normal state of an in-progress bundle**. Under
`--strict` that is a hard fail, so a strict routine gate goes red on correct work in the middle
of every wave, and a gate that fires on correct work gets switched off. Invariant #12 scopes
`--strict` to the Paper Submission Gate; `gate_precheck submission` is its caller.

### What a runner could still add — and why it is not proposed today

Exactly one thing the local harness cannot do by construction: prove the repo validates on a
machine that is **not this workstation** — no warm `.lake`, no gitignored caches, no locally
installed hooks. That is a release-integrity question, not a per-push one.

It is also **currently impossible**, and this is the finding from v1 worth keeping. On a real
`git clone` of this branch:

```
docs/counts.json               mtime = 1785915261.937
  src/core/constants.py                1785915262.606   STALE -> regenerate
  src/core/visualizations.py           1785915262.608   STALE -> regenerate
  lean/lean_deps.json                  1785915262.338   STALE -> regenerate
  newest of 2039 *.lean                1785915262.269   STALE -> regenerate
```

Git writes every file's mtime at checkout time in index order, so `docs/` lands before `src/`,
`lean/` and `papers/`. **All four of `counts_fresh`'s staleness criteria read STALE on an
untouched clone**, and it then shells to `update_counts.py` — 1800-second timeout, needs `lake`.
`tables_fresh` (300 s) and `claim_clusters_fresh` follow. The three regenerators are workstation
conveniences registered as checks; mtime freshness is meaningless on a fresh checkout.

`validate.py --ci` (built 2026-08-05) is the mode that survives that: it skips the three
regenerators and `notebook_exec`, never archives, and **fails below a coverage floor** — because
a runner that loses the Lean toolchain gets ~200 s faster *and* greener, which is this audit's
own finding reintroduced at the CI layer. Measured **53/55 in 397 s**, floor met at exactly 55.
It is retained and tested (`tests/test_ci_mode.py`), and it is the right mode for an on-demand
or release-time fresh-clone check **if the operator ever wants one**. No workflow file is
proposed, and none is added: on a public repo that is an outward-facing change and the
operator's call.

## 5. What this does *not* solve

CI is R5-C1 alone. It does **not** address C2–C5 (figure content, number recomputation,
theorem-statement correspondence, citation content) — those are *absent checks*, and no schedule
can run a check that does not exist. Per the operator's routing, C2–C5 are submission blockers
and non-infrastructural → **ADR-010**.

⚠️ **One consequence to state plainly.** Turning off the LaTeX slow gate makes a default
`validate.py` **red on D3's two fatal compile errors**. That is not a regression — it is the
suite reporting a failure it has always had and never showed. `gate_precheck s13` has been red
on it since `--force-latex` was added there earlier on 2026-08-05, so wave close was already
blocked; the default run now agrees with the gate. Fixing D3 is ADR-010's.
