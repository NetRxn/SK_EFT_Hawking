# Substrate-lane re-file — ARCHITECTURE_TODOs D45–D49, 2026-08-12

**What this is.** ADR-012 D4 and P8. The I1 drafting wave (2026-08-11) found nine substrate
defects and filed them into `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` as D45–D49,
because it was the nearest open drawer. That was drift: the file's charter is one
architecture-accuracy pass under a standing operator build-freeze, and **nothing in `scripts/`,
`src/`, `tests/` or `.claude/` parses it** — every reference is inside a comment. Work items went
into a file with no reader. This document gives them a queue that has teeth.

**Every claim below was RE-MEASURED at HEAD before filing**, per ADR-012 D4 (*"each is
re-measured at filing and assigned its own lane — the ADR does not pre-assign them"*). That
re-measurement changed the answer for four of the nine.

| item | re-measured verdict | filed |
|---|---|---|
| D45-a `tetrad_gap_solution` bracket | **LIVE** — `formulas.py:2411` still reads `lo, hi = 1e-10 * Lambda, Lambda` | finding 1 |
| D45-b KLRS mis-attribution | **LIVE** — `EWBaryogenesisChiralityWall.lean:52` still attributes `m_H = 72 ± 2 GeV` to KLRS | finding 2 |
| D45-c figure defects | ✅ **FIXED 2026-08-11** — the generator carries the repair and the tree now derives from the module's dependency edges | not filed |
| D45-d bare-name registry key | **LIVE** — both declarations exist; the bare key resolves to `SecondOrderSK` | finding 3 |
| D46-a `IsLocallyWellPosed := True` | **LIVE** in Lean; the I1 apex claim that cited it was corrected | finding 4 |
| D46-b `IsNullGeodesicallyIncomplete := 0 < lam_max` | **LIVE** — definitionally positivity of a real | finding 5 |
| D46-c `check_bundle_consistency` docstring | **LIVE** — the body performs no bibkey, ±2σ or Lean-reference comparison | finding 6 |
| D46-d `\aristotleruns` counts `manual` | **LIVE** — measured 322 entries / 44 distinct / **3 manual** → 319 prover-closed across 43 genuine runs | finding 7 |
| D47 fabricated seed anecdote | ✅ **FIXED** — no occurrence survives in `papers/I1/paper_draft.tex` | not filed |
| D48 `leviCivita_unique_of_isLeviCivita` | **LIVE** — `h_smooth` still quantifies over every section triple | finding 8 |
| D49 chirality-wall Aristotle claim | ✅ **FIXED** — retired in four places; the figure derives from the module | not filed |

**D50 and D51 stay in the working doc**, per ADR-012 C1: both are architecture-accuracy defects
and belong to that file's charter. This document does not touch them.

⚠️ **These are PRE-EXISTING recorded debt, not new growth.** Every item was written down on
2026-08-11, before ADR-012 P5 froze its ratchet baselines on 2026-08-12. The ratchets did not
count them because they were filed where nothing reads. Filing them makes a known population
visible; it does not enlarge it. That distinction matters because the opposite move — laundering
newly-created debt through a "re-derivation" — is the abuse the ratchet rule exists to prevent,
and the discriminator is the date on the record.

---

## Findings

### 1 — 🔴 `tetrad_gap_solution` returns a value that is not a fixed point, silently

- **Severity:** critical
- **Lane:** substrate
- **Gate:** `ComputationCorrectness`
- **Location:** `src/core/formulas.py:2411`
- **Observed:** the bisection brackets at `lo, hi = 1e-10 * Lambda, Lambda`. The gap equation's
  fixed point exceeds Λ for G above a saturation coupling `G* = G_c/(1−log 2)`, so above `G*` the
  function returns exactly Λ and **that value is not a fixed point**. Measured at Λ = N_f = 1, the
  fixed-point residual is −7e−13 at G/G\* = 0.99 and **+49.0** at G/G\* = 50.
- **Evidence:** no exception and no warning is raised, while the docstring promises *"For G > G_c:
  returns the nontrivial solution Δ\* > 0"*. The Python layer encodes exactly the bound Lean
  **refuted** — the disproof of `gap_solution_bounded` sits in `TetradGapEquation.lean:311–325` as
  a commented block, and the numerics never got the message.
- **Expected:** either the true Δ > Λ, or a raise. Never a non-solution returned as a solution.
- **Fix:** bracket above Λ, or solve `G·N_f·I(Δ) = 1` directly. Add a residual assertion so the
  function cannot return a point it has not verified.
- **Verify:** `uv run python -m pytest tests/test_formulas.py -k tetrad_gap -q`

⚠️ **This is the canonical `substrate` case and the reason the lane exists** — the theorem and the
implementation disagree, so the repair needs a Lean-side statement, a Python-side fix, and a
regression test asserting the two agree. It is neither a proof obligation the atlas covers nor a
paper finding.

### 2 — 🔴 A Lean docstring attributes a number to a paper that does not contain it

- **Severity:** major
- **Lane:** prose
- **Gate:** `CitationIntegrity`
- **Location:** `lean/SKEFTHawking/EWBaryogenesisChiralityWall.lean:52`
- **Observed:** the reference block credits Kajantie–Laine–Rummukainen–Shaposhnikov 1996 with
  *"lattice crossover threshold m_H = 72 ± 2 GeV"*. Both PDFs were read in full: **KLRS gives
  70 GeV < m_H,c < 95 GeV, most likely ≈ 80 GeV.** The 72.4 ± 1.7 GeV figure is
  Csikor–Fodor–Heitger 1999's full-SM transform of their own 66.5 ± 1.4 GeV endpoint — and the
  next line of the same block already cites CFH correctly for it.
- **Evidence:** `HYPOTHESIS_REGISTRY`'s `source` string gets this right, so the docstring is the
  sole wrong copy. Re-measured at HEAD: line 52 is unchanged.
- **Expected:** KLRS credited with its own range; the 72.4 GeV figure credited to CFH 1999 only.
- **Fix:** correct line 52 to KLRS's published range. ⚠️ Check the module's other five `72`
  occurrences (lines 25, 278, 293) — those already say CFH, so only the reference block is wrong,
  but confirm rather than assume.
- **Verify:** `uv run python scripts/validate.py --check prose_theorem_reference_coverage`

⚠️ **Prior-art fidelity is the failure class that survives every automated layer**, because each
one verifies that a source exists and resolves, never that the prose represents it faithfully.
Only reading the cited paper catches this, which is why the lane is `prose` and not `lean` — the
file is Lean, the worker profile is not.

### 3 — 🔵 A bare-name Aristotle registry key resolves to a different module's theorem

- **Severity:** minor
- **Lane:** infra
- **Gate:** `LeanProofSubstance`
- **Location:** `src/core/constants.py:1019`
- **Observed:** `'altFDR_uniqueness_test': '3eedcabb'` is keyed by a bare declaration name. Both
  `SKEFTHawking.SecondOrderSK.altFDR_uniqueness_test` (`SecondOrderSK.lean:788`) and
  `SKEFTHawking.SKDoubling.firstOrder_altSign_uniqueness_test` (`SKDoubling.lean:636`) exist, and
  `SKDoubling`'s source comments claim that run. A drafter asked to cite the run ID for the
  first-order result would attach the second-order run.
- **Evidence:** re-measured at HEAD — both declarations present, the key unqualified.
- **Expected:** registry keys distinguish same-named declarations across modules.
- **Fix:** ⚠️ **Not a one-line rename.** `ARISTOTLE_THEOREMS` keys are consumed by
  `update_counts.py`, the graph extractor and the paper-side macros; establish the consumer set
  before requalifying, or the repair moves the defect. Filed rather than fixed for that reason.
- **Verify:** `uv run python scripts/validate.py --check aristotle_registry_resolves`

### 4 — 🔵 `IsLocallyWellPosed` is `True`, and cannot gate anything

- **Severity:** minor
- **Lane:** lean
- **Gate:** `LeanProofSubstance`
- **Location:** `lean/SKEFTHawking/CauchyProblem.lean:146`
- **Observed:** `def IsLocallyWellPosed (_S : Spacetime) : Prop := True`. It appears in three
  theorem **conclusions** (`CauchyProblem.lean:198`, `WaveEquation1D.lean:325,344`) and in **zero**
  hypotheses, so nothing consumes it and `trivial` discharges it.
- **Evidence:** re-measured at HEAD — the definition is unchanged. ⚠️ **The claim that rested on
  it was already corrected:** I1's apex registration no longer says the missing PDE infrastructure
  is *"scoped as the gating Prop"*. Severity is `minor` because the false claim is retracted and
  the substrate weakness is disclosed — not because the Prop got stronger.
- **Expected:** either a substantive well-posedness predicate, or a name that does not promise one.
- **Fix:** the honest interim is the name. A Prop called `IsLocallyWellPosed` that is `True`
  invites the next author to cite it as a gate; renaming it to record that the infrastructure is
  *named rather than reinvented* costs nothing and removes the trap.
- **Verify:** `cd lean && lake build SKEFTHawking.CauchyProblem`

### 5 — 🔴 `IsNullGeodesicallyIncomplete` is definitionally `0 < lam_max`

- **Severity:** major
- **Lane:** lean
- **Gate:** `LeanProofSubstance`
- **Location:** `lean/SKEFTHawking/PenroseSingularity.lean:220`
- **Observed:** the conclusion of the curve-level focusing chain is *defined* as positivity of a
  real parameter. The mathematical weight sits entirely in the comparison bound and the strict
  negativity of the expansion — not in the word "incompleteness". This is CLAUDE.md's own
  defining-the-conclusion anti-pattern.
- **Evidence:** re-measured at HEAD, lines 220–221 unchanged.
- **Expected:** wherever that chain is presented as a singularity theorem, the definitional
  content is disclosed.
- **Fix:** ⚠️ **This lands on D3's headline singularity-theorem chain, not on I1.** Two steps, and
  the first is a measurement this finding deliberately does not pre-judge: establish whether D3's
  manuscript already carries the disclosure. If it does, this is a Lean-side strengthening only.
  If it does not, the prose is overclaiming and that is the urgent half.
- **Verify:** `uv run python scripts/validate.py --check placeholder_theorem_disclosure`
- **Needs-operator:** queue

### 6 — 🔵 `check_bundle_consistency`'s docstring describes a check its body never runs

- **Severity:** minor
- **Lane:** infra
- **Gate:** `CrossPaperConsistency`
- **Location:** `scripts/validation/checks/bundles_readiness.py:2188`
- **Observed:** the docstring promises comparison on bibkey, on numerical value *"within ±2σ of the
  citation's reported uncertainty, or within 1% relative tolerance"*, and on Lean theorem
  reference. The body branches on `match_kind`, passes exact clusters on the construction
  argument, emits an advisory for normalized clusters, and fails only on an unrecognized kind.
- **Evidence:** re-measured at HEAD — a scan of the body for `sigma`, `tolerance`, `abs(`,
  `bibkey` and `theorem` returns **nothing**. No numerical comparison anywhere.
- **Expected:** the docstring and the body agree.
- **Fix:** rewrite the docstring to the body. Implementing the docstring instead is a much larger
  change and needs ADR-010 §6a approval; the documentation defect should not wait on it, because a
  reader trusting the docstring takes a green as a consistency guarantee it does not provide.
- **Verify:** `uv run python -m pytest tests/test_d5_bundles_readiness.py -k consistency -q`

### 7 — 🔴 `\aristotleruns` counts the string `manual` as a prover run

- **Severity:** major
- **Lane:** infra
- **Gate:** `NumericalFreshness`
- **Location:** `scripts/update_counts.py:353`
- **Observed:** `count_aristotle` computes `len(set(ARISTOTLE_THEOREMS.values()))` and
  `len(ARISTOTLE_THEOREMS)`. Three entries carry the marker `manual` for theorems closed by hand.
- **Evidence:** re-measured at HEAD — **322 entries, 44 distinct values, 3 `manual`**
  (`firstOrder_normalization`, `complex_pseudofermion_pfaffian`, `heatbath_a_trick_covariance`), so
  the truth is **319 prover-closed theorems across 43 genuine runs** against a published 322/44.
  Both macros are one high wherever they appear, including two sites in I1's introduction.
- **Expected:** the marker is discarded from the run count, and both figures are emitted so a
  manuscript can state either honestly.
- **Fix:** filter the marker in `count_aristotle` and emit `aristotle_manual` alongside. ⚠️ **This
  is a cascade, not a one-liner**, and that is why it is filed rather than fixed here:
  `counts.tex` sits in every bundle's `\input` closure, so the repair requires
  `scripts/update_counts.py`, then a prose sweep for manuscripts stating 322 or 44, then
  `scripts/compile_bundle_pdf.py --all --force` — the four-step order in
  `VALIDATION_ARCHITECTURE.md` §5.1. Skipping step three is what took the CI floor red on
  2026-08-12.
- **Verify:** `uv run python scripts/validate.py --check counts_fresh`

### 8 — 🔴 `leviCivita_unique_of_isLeviCivita` is plausibly vacuous

- **Severity:** major
- **Lane:** lean
- **Gate:** `LeanProofSubstance`
- **Location:** `lean/SKEFTHawking/LeviCivita.lean:366`
- **Observed:** `h_smooth` is quantified over **every** section triple
  `∀ (X Y Z : Π x : M, TangentSpace I x)`, with six differentiability conjuncts. Sections here are
  arbitrary dependent functions with no smoothness constraint, so on any manifold admitting a
  single section non-differentiable at `x` the hypothesis is FALSE and the theorem holds
  vacuously. Its docstring calls it *"the substantive Wald §3.1 / Kobayashi–Nomizu IV.2.2
  uniqueness theorem at bundle level"*.
- **Evidence:** re-measured at HEAD — the binder is unchanged. The substantive content is one
  level down: `koszul_identity_of_isLeviCivita` (`:267`) takes `X Y Z` as explicit parameters with
  per-triple hypotheses, and `leviCivita_pointwise_unique_of_koszul` does the real work. **Only
  the composition over-quantifies.**
- **Expected:** `h_smooth` restricted to the triples the proof actually forms, so the composed
  statement is non-vacuous.
- **Fix:** restrict the binder. Until then any manuscript presenting this should cite the
  per-triple Koszul identity and the kernel, not the composition — which is what I1 §12 already
  does, and is the honest interim treatment.
- **Verify:** `cd lean && lake build SKEFTHawking.LeviCivita`

⚠️ **This arrives from a direction the preemptive-strengthening checklist did not anticipate:**
not a tautological conclusion, but a hypothesis strong enough to be unsatisfiable. Question 4 of
the checklist asks whether a statement self-discharges; it does not ask whether the statement can
be *reached*. Worth adding.
