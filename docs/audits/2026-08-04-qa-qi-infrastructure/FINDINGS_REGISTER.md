# PR-review findings register — all 53 actionable non-Critical

**Source of truth:** [`reviewer-reports/`](reviewer-reports/) — the six reviewers' own
words. This file is the tracker; when the two disagree, the report wins.

**Status legend:** ✅ fixed · 🔧 in progress · ⬜ open · 🔁 superseded/duplicate ·
❌ **not reproduced** (the filed claim was measured and is wrong as stated)

> ⚠️ **Every entry below was RE-MEASURED before being actioned**, per the standing rule
> that a filed finding's count, consumer and effort are *claims*. Several did not survive
> that: the counts in R6-M1 and my own re-count of it were both wrong in different
> directions, and R4-I1's stated mechanism is not what the code does. Those are marked ❌
> with the measurement, not silently dropped.

---

## ⛔ CRITICALS — status (asked and answered 2026-08-05: **five are OPEN**)

Nine Criticals were filed across the six reviewers. Four (R4's) became QI-31…QI-34 and are
fixed; R1's, R2's and R3-C1 are fixed. **R5 filed five under the heading "Critical gaps (a
wrong artifact can ship)" and all five are open.**

⚠️ **I under-recorded them.** They went onto disk in `PR_REVIEW_2026-08-05.md` §3 as *"What
has NO enforcement at all"* — a list of gaps — and the resume point routed them to ADR-010 as
*"the unshipped correspondence checks"*. R5's own framing was **Critical**, each with a stated
likelihood and blast radius. Severity was dropped in transcription. That is the same defect as
the "~17", one level up: a summary that loses the property the reader needs.

| id | Critical | verified 2026-08-05 | status |
|---|---|---|---|
| R1-C1 | published paper table shipped EMPTY | — | ✅ `6c89beaa` |
| R2-C1 | `test_an_illegible_figure_fails` vacuous; `if pt < FLOOR_PT:` had zero coverage | — | ✅ fixed |
| R2-C2 | `test_the_legibility_floor_is_8pt` textbook change-detector | — | ✅ deleted |
| R3-C1 | "all 59 mutation-verified" false; seam guard defeatable by prose | — | ✅ fixed + retracted |
| R3-C2 | QI-30's criterion applied to one check, never swept | 4 of 59 swept | 🔧 **PARTIAL** — ratcheted (`FIXTURE_ONLY_CEILING=55`), not swept |
| R4-C1…C4 | the four checks that cannot fail | — | ✅ QI-31…QI-34 |
| **R5-C1** | **no CI — nothing runs the 59 checks automatically** | no `.github/workflows`; hook = 3 of 59, fail-open, `main`-only | 🔁 **RE-DIAGNOSED** — see below |
| **R5-C2** | **figure *content* unverified; Stage 9 has no gate** | **137 specs, 118 with `physics_checks=[]`, 0 runners**; only the dashboard reads the report; `bundle_figure_integrity` still filtered to `d11_/d12_` | ⬜ **OPEN** |
| **R5-C3** | **nothing recomputes a paper-quoted number from its formula** | `threshold_arithmetic`: **0 files, not registered** | ⬜ **OPEN** |
| **R5-C4** | **nothing checks a cited theorem's STATEMENT supports the prose** | `theorem_quoted_bound_matches_lean_literal`: **0 files, not registered** | ⬜ **OPEN** |
| **R5-C5** | **citation *content* verification inert; both replacements never shipped** | `bibitem_registry_character_match`, `citation_bibkey_form_matches_metadata`: **0 files each, not registered** | ⬜ **OPEN** |

### R5-C1 re-diagnosed (2026-08-05, v2 — after operator pushback)

The finding is real; **"add CI" was the wrong remedy, and my first answer took it at face
value.** v1 of `CI_DEFAULTS_ASSESSMENT.md` proposed an ~11-minute per-push job and a
~45-minute nightly. Re-measured against the harness that exists:

- `scripts/pre-commit-notebooks.sh` already executes **only the staged `.ipynb`**, and
  `notebook_exec` already carries a per-notebook content-hash skip-cache. The nightly's whole
  cost was an artifact of running on a fresh clone where that cache is gitignored — and
  `notebooks/` moved in **49 of the 5,814 commits on `main` since 2026-03-01 (0.84 %)**.
- The per-push job re-ran what `pre-commit-sync.sh`, `gate_precheck s9/s10/s13` and
  `wave-close` already run. Same depth twice, not defence in depth.

The genuine defect underneath: **every stage of this harness is change-scoped except the
expensive one.** `validate.py` full runs all 59 checks regardless of the diff, including 198 s
of Lean-substrate checks that re-derive the same answer on every re-run within a gate cycle.
(⚠️ An earlier draft justified this with *"the Lean tree does not move in 53 % of commits"* —
measured on THIS infra branch. On `main` it moves in **78 %**, so the memo's value is the
repeat run and the paper/doc-side wave, not "half of all runs".) The gate that
could not be scoped had already started opting out — `paper_latex_compiles` was slow-gated into
returning PASS-without-compiling, which is why D3's two fatal errors were invisible.

Remedied by change-scoping rather than scheduling: `scripts/validation/_memo.py` (input-
fingerprint memo, applied to the two Lean checks — **171.6 s → 0.1 s** measured) and a per-draft
LaTeX compile cache that let the slow gate be **deleted**. Full suite, `validate.py
--no-archive`: **317.8 s → 134.2 s**, and the LaTeX compile now actually runs (it was skipping). Guards on the "PASS without
measuring" hazard: production-seeded key tests, PASS-only caching with eviction on FAIL, the
body's own source in every key, a visible skip line, and `--strict` bypassing the memo outright.

`validate.py --ci` + the coverage floor are retained and tested — the right mode for an
on-demand fresh-clone check, which is the one thing a runner could add that the local harness
cannot. **No workflow file, no schedule**; that remains the operator's call, and the fresh-clone
mtime blocker (below, §1 of the assessment) must be fixed before any runner is useful.

R5's own words on why C2–C5 are Critical rather than Important — worth quoting, because the
severity is the part that got lost:

- **C3** — *"a paper claiming `G > 0.01` where the correct value was `0.5` (factor 50), with a
  companion photon count wrong by 25×; the drift propagated across 4 sites and survived a full
  per-paper Stage-13 review."*
- **C4** — *"prose said 'formally bounded at ≤1.8%'; the Lean theorem is a generic algebraic
  envelope and the 1.8% lives in a **docstring**. Blast radius: severe — it converts a
  formal-verification claim into an unsupported one, which is the project's headline
  differentiator."*
- **C5** — *"fabricated/mis-targeted citations are the single most-documented LLM authoring
  defect, and the project already had the paper40 incident (a hallucinated arXiv ID pointing at
  a graph-NN paper). Blast radius: severe; **this is a one-strike arXiv trigger**."*
- **C2** — *"a figure that plots the wrong quantity under a confident caption is exactly the
  arXiv-moderation failure mode, and the project already documented this end-to-end."*

**None of the five is a merge blocker for this branch** — every one is a pre-existing absence,
not a regression, and none makes the suite red. They are submission blockers. The distinction
matters and was not being drawn: the branch is safe to merge; the *corpus* is not safe to
submit.

Two have a cheap first cut R5 costed itself: C2's `d11_/d12_` filter deletion (~3 lines) and
C5's `citation_bibkey_form_matches_metadata` (1–2 h, and it catches two named real cases,
`KaulMajumdar1998` and `SextyWetterich2009`).

---

## R4 — enforcement efficacy (11 Important) — the reviewer who returned "No"

| id | finding | status |
|---|---|---|
| R4-I1 | `cross_path_consistency`'s two legs "are one assertion" | ❌ **not reproduced as stated** — see below |
| R4-I2 | `paper_latex_compiles` unreachable from every automated caller | ✅ `2577fdbc` — `s13` now passes `--force-latex` |
| R4-I3 | the 14 unresolved `ARISTOTLE_THEOREMS` keys still launder into `all_lean_names` | ✅ `b4a2d367` |
| R4-I4 | `tracked_hypotheses_fresh` bare-`except` fail-open | ✅ `0077714a` |
| R4-I5 | `nogo_substrate_integrity`: empty-backing free pass, dead `sorryAx` conjunct, `native_decide` stripped | ✅ `0077714a` |
| R4-I6 | two advertised `formula_grounding` legs are dead | ⬜ open |
| R4-I7 | the three freshness regenerators cannot fail on staleness | ✅ `1a7f016d` |
| R4-I8 | `readiness_verdicts_agree`'s reverse leg is unreachable | ⬜ open |
| R4-I9 | `atlas_integrity` `SystemExit` aborts the suite | ✅ `4ca3ff4b` |
| R4-I10 | `notebook_exec` skip-cache fingerprint too narrow | ✅ `dd195033` |
| R4-I11 | six `--strict` legs have no automated caller | ✅ `2577fdbc` — new `gate_precheck submission` stage |

### ❌ R4-I1 — measured, and the mechanism is not the one filed

The claim: leg 2 compares `decoherence_parameter(Γ,κ)` against `summ['delta_k_at_T_H']`,
which is itself `decoherence_parameter(Γ,κ)` — *"the same function"*, so the legs
*"cannot fail independently."*

Measured on the live platform:

```
leg1  direct   = 6.021424108396742e-07   spectrum = 6.021448963045517e-07
leg2  formulas = 1.2042848216793483e-06  spectrum = 1.2042897926091034e-06
identical right-hand sides: False        identical left-hand sides: False
```

`decoherence_parameter` returns `2Γ/κ`, so leg 2 is leg 1 scaled by 2 **on both sides** —
and the two sides differ in the 6th significant digit, i.e. the spectrum path computes its
own `Γ_H` rather than reusing the caller's. Leg 2 therefore *does* constrain
`decoherence_parameter`'s factor of 2, which leg 1 does not.

**The real defect is different and still worth fixing:** leg 1's reference side is an
INLINE re-implementation (`gamma_eff * (T_H/c_s)**2 / kappa`) rather than a call to the
canonical `formulas.py` entry point, so it cannot detect drift in the canonical formula —
in a check registered as *"catches duplicate implementations that drift apart"*, which
thereby introduces a third one. Re-filed on that basis; **⬜ open**.

---

## R1 — architecture and correctness (6 Important)

| id | finding | status |
|---|---|---|
| R1-I2 | `bundle_registry_consistency` Leg C lost a third of its scope (`glob`→`rglob`) | ✅ `6c89beaa` |
| R1-I3 | a behaviour change shipped inside the phase ADR-009 D4 requires to be behaviour-preserving | ✅ ADR corrected in the QI sweep |
| R1-I4 | `_iter_test_functions` double-yields on nested classes | ⬜ open — **and the on-disk note contradicts the reviewer** (see §Contradictions) |
| R1-I5 | `build_graph`'s comment asserts `readiness_gates` imports only stdlib; it now imports `validation._tex` | ⬜ open |
| R1-I6 | `test_regenerators_precede_their_consumers` never widened; `_REGENERATORS` names two members it never asserts | ⬜ open |
| R1-I7 | merge to `main` turns the wave-close gate red | ✅ decided by operator: merge readiness first |

## R2 — test quality (5 Important)

| id | finding | status |
|---|---|---|
| R2-I3 | `test_validate_flag_propagation` asserts an exact source substring | ⬜ open |
| R2-I4 | `test_d5_lean_toolchain` pins message *text* and asserts two strings merely differ | ⬜ open |
| R2-I5 | the D5 seam guard is satisfiable by a docstring | ✅ fixed in the QI sweep |
| R2-I6 | `AWAITING_*` — two constants in the same file asserted to agree | ⬜ open (judged defensible; see the reviewer's own hedge) |
| R2-I7 | `EXPECTED_CHECKS` ordering freeze duplicates `_CANONICAL_ORDER` | ⬜ open |

## R3 — deferred scope (9 Important)

| id | finding | status |
|---|---|---|
| R3-I1 | QI-16 marked FIXED; 4 wrong §Deferred ordinals remain outside `scripts/validation/` | ⬜ open |
| R3-I2 | `RESUME_STATE.md` still carries three claims the audit says it corrected | ⬜ open |
| R3-I3 | §Deferred item 6's "no defect to fix here" overstates its own measurement | ✅ superseded — `--strict` now has a caller |
| R3-I4 | QI-15 removed 8 `TODO(semantic-review)` markers without recording a per-site decision | ⬜ open |
| R3-I5 | the BinOp path-alias gap; `_PHYSLIB_DIR` is the one unpinned site | ⬜ open |
| R3-I6 | QI-01's fix is Lean-only; `extract_python_test_nodes` was the same class | ✅ `6c89beaa` |
| R3-I7 | the map's five documented silent-drop points are neither findings nor residuals | ⬜ open |
| R3-I8 | `provenance_dashboard`'s exclusion from the QI-01 guard is asserted, not measured | ⬜ open |
| R3-I9 | the "eight always-pass checks" population is a syntactic lower bound | ⬜ open |

## R5 — coverage adequacy (6 Important)

| id | finding | status |
|---|---|---|
| R5-I1 | Invariant #10 has no enforcement and **22 live violations** | 🔧 measured: 22 confirmed, in 4 files, all `theorem` |
| R5-I2 | notebook stored-output correctness covers 2 of 91 | ⬜ ADR-010 (operator decision (b)) |
| R5-I3 | LaTeX gate opt-in **and** no BibTeX, so undefined citations are undetected | ✅ half (`2577fdbc`); ⬜ **BibTeX half open** |
| R5-I4 | no scan for LLM artifacts / placeholder strings in TeX | ⬜ open |
| R5-I5 | headline certainty-calibration has no mechanism | ⬜ open |
| R5-I6 | Invariants #1/#2/#3 enforced for notebooks only; **177 `src/` modules unscanned** | ⬜ open |

## R6 — test appropriateness (16, unlabelled)

| id | finding | status |
|---|---|---|
| R6-M1 | atlas negative frontier mis-derived; CLI and web export unfiltered; the digest's filter untested | 🔧 measured — **29 on the frontier**, from 3 modules |
| R6-M2 | `NarrativeGrounding` is a change-detector for five historical overclaims | ⬜ open |
| R6-M3 | numeric-claim protection is anchored regressions; captions stripped before scanning | ⬜ open |
| R6-M4 | eleven tests assert data the test itself declared | ⬜ open |
| R6-M5 | a decoy fixture in `test_d5_prose_lean_refs` | ⬜ open |
| R6-M6 | a test whose docstring denies what it is (**R2 called the same file a strength**) | ⬜ open — needs adjudication |
| R6-M8 | the 11 readiness-gate evaluators have zero direct tests | ⬜ open |
| R6-M9 | the graph extractor suite is unit-shaped, empty-tolerant, deselected | ✅ RED-test half `4a16826e`; ⬜ structural half open |
| R6-S1 | Stage-13 finding → gate: no end-to-end test | ⬜ open |
| R6-S3 | no headings-minted reconciliation (partial loss is invisible) | ⬜ open |
| R6-S4 | `find_stage13_review_evidence` decides whether Stage 13 happened, untested, and writes back | ⬜ open |
| R6-S5 | `gate_precheck` had zero tests | ✅ `2577fdbc`; ⬜ `review_runner` half open |
| R6-S6 | display↔gate agreement untested in both directions | ⬜ open |
| R6-S7 | real-data baselines absent for ~9 of 13 d5 files | ⬜ open |
| — | the human-verification write path is a stub | ⬜ open — **highest value remaining** |
| — | severity typos silently downgrade | ✅ `4a16826e` |

---

## Contradictions between the on-disk summary and the reviewer

These need a decision, not just recovery. In each case the summary records the version
the reviewer **rejected**:

1. **`_iter_test_functions`** — the summary says the current behaviour "is the correct
   behaviour, so this is a latent-but-guarded shape rather than a defect." R1-I4 *and*
   R3-M4 both say it double-**mints**, and that `TestGraphTestNodeCoverage` would fail
   with a *negative* count and misdiagnose it as a drop.
2. **BinOp path-alias gap** — summary: "a known, deliberate limit, not an oversight."
   R3-I5: "**NO — should be a defect.** Same shape as QI-11," and `_PHYSLIB_DIR` is
   unpinned.
3. **README §4c** — "All four workstreams complete — 29 of 29 findings closed" / "5398
   passed". R3-M1 measured five workstreams, 31 findings, 5401 passed. **Still stale.**
4. **The hedge-regex guard** (`test_d5_lean_substrate.py:302-330`) — R2 lists it as a
   *strength*; R6-M6 says it is a hardcoded fixture list whose docstring denies what it
   is. Direct reviewer-vs-reviewer disagreement, unresolved.

## Also not in this register

**48 Minor findings** (R1 #8–15, R2 #8–12, R3 M1–M6, R4 M1–M10, R5 M0–M4) live only in
[`reviewer-reports/`](reviewer-reports/). Several are substantive measurements, e.g.
R4's: `parameter_provenance` leg 4 is **82 % blind** (169 of 206 silent `None`) while
printing *"All provenance values match code"*; `citation_primary_sources_present` covers
**69 of 652** entries; `disclosure_consistency` has never had a non-zero candidate
population.
