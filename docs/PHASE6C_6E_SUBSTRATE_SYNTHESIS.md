# Phases 6C\* and 6E\* — Substrate Synthesis

**Written 2026-07-30 at the D11/D12 first content-lift.**

**Why this file exists.** The per-wave lab notebooks for these arcs live under
`docs/dev-loops/Phase6E*/` and `docs/dev-loops/Phase6C*/`, which are
**gitignored**. Everything load-bearing in them — guardrails, retracted claims,
kernel no-gos, honesty caveats — was therefore one `git clean -x` from being
lost. This is the tracked lift of that content, satisfying the Stage A.alt
working-docs gate of `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`.

> **⚠️ Note on location.** The absorption protocol names
> `temporary/working-docs/` as the home for this synthesis. **That directory is
> itself gitignored**, so a synthesis written there would reproduce exactly the
> durability failure it exists to fix. This file therefore lives in tracked
> `docs/`. Anyone following the protocol literally should do the same, and the
> protocol's wording is worth amending.

It is a **synthesis**, not a transcript. Where a roadmap and the tree
disagreed, the tree wins and the disagreement is recorded.

---

## 1. The two arcs at a glance

| Arc | Phases | Modules | Bundle | Axioms / sorry / tracked Props |
|---|---|---|---|---|
| 6C\* + 6ED | 6CA, 6CB, 6CD, 6CE, 6ED | 22 | D11 | 0 / 0 / **0** |
| 6E\* | 6EA, 6EB, 6EC, 6EE | 13 | D12 | 0 / 0 / 11 (all disclosed) |

Kernel purity for the 6E\* arc was verified from **extracted axiom closures for
every declaration in all thirteen modules**, not by spot check:
`axiom_deps_project` empty and `axiom_deps_core` exactly
`{propext, Classical.choice, Quot.sound}` throughout.

---

## 2. Guardrails that were respected (and why they matter)

These are the constraints the arcs deliberately did **not** violate. Recording
them matters because a later wave that quietly crosses one would look like
progress.

### 6CE — algebraic path only

> **⚠️ GUARDRAIL — algebraic path ONLY.** Do not attempt full two-scale /
> periodic-homogenization convergence (the documented substrate-stall). Use
> only the algebraic derivation.

Basis for the stall: Mathlib has Sobolev *inequalities*, not two-scale
convergence; PhysLib's `Optics/Basic.lean` docstring reads *"This directory is
currently a place holder."* The guardrail was respected, not merely noted —
`MaxwellGarnett.lean`'s own header repeats it.

**Important framing correction (2026-07-30).** Two-scale convergence is
formalized in **no** proof assistant. So this must be described as a choice
between two equally *unformalized* routes in which the algebraic one was
tractable — **not** as avoiding an existing formalization. The earlier framing
would have been an overclaim.

### 6EA — state the exact bound, never a folklore form

> **⚠️ GUARDRAIL.** The folklore "miss error ≥ e^(−N_diff)" is FALSE in general
> … The correct universal statement is the Le Cam/Bhattacharyya average-error
> floor `P_e ≥ (1/4)·exp(−(√N_a−√N_b)²)`; the exponential form `e^(−N_a)` is
> exact only as the zero-false-alarm miss optimum at a dark baseline. Wave 1
> proves BOTH the correct floor AND the two-sided refutation … the refutation
> is a first-class deliverable.

### 6EC — the linearized model *is* the object

> **GUARDRAIL 1.** No theorem is a claim about a physical device. A physical
> detector realizes this model only inside a validity neighbourhood of its bias
> point, and *that identification is the consumer's declared hypothesis*, never
> smuggled in here.

### Two-layer honesty (both arcs, every module header)

> The *mathematics* … is Lean-verified. The identification of a physical
> instrument's impulse response with an admissible `h`, and of a physical noise
> source with the whiteness hypothesis, is the **consumer's declared
> hypothesis** — never smuggled into these statements.

---

## 3. Retracted claims — the durable record

Each of these was believed, shipped or written down, then found wrong. They are
the highest-value content in the gitignored notebooks.

### 6ED — the Haldane classification (deleted 2026-07-29)

`haldane_chern_iff_mass_inversion` was **deleted**. Both halves were wrong:

1. **False.** The 4×4 invariant flips at `|m| ≈ 3.3177`, strictly inside the
   analytic window `|m| < 3√3 ≈ 5.1962` — so on roughly 36% of the window the
   masses invert while the invariant reads `0`.
2. **Contentless.** The theorem carried no content beyond its hypotheses anyway.

Replaced by `haldane_massInversion_not_sufficient_at_N4`.
**Standing rule:** no statement may be phrased as holding "exactly where the
masses invert" at fixed `N`.

### 6EA — three separate retractions

- **Neyman–Pearson overclaim, struck twice.** No Neyman–Pearson or
  likelihood-ratio theorem ships in this phase; the floors are symmetric
  Bayes/Le Cam bounds. (The *opposite* over-correction — claiming their total
  absence — was also retracted.)
- **"Most-consumed floor" claim verified FALSE — but the correction was itself
  over-stated, and is corrected here (2026-07-30).** The accurate position:
  6EB and 6EC reference **zero** Wave-1 declarations (true). But
  `poisson_avgError_floor` **is** consumed by 6EE —
  `Control.photon_budget_ceiling` (`CompositeReadoutCeilings.lean:252`) and
  `Control.photon_budget_floor_attributed` (`:310`) call it directly — so
  "Wave 1 is standalone" is **wrong**. Only
  `poisson_darkBaseline_miss_floor` genuinely has zero external references.
  What is a finding is any text calling the Poisson layer the *series'
  most-consumed* floor. Caught by the Stage-10 D12 reviewer, which checked the
  live dependency graph rather than inheriting the roadmap's wording.
- **`expNeg_enclosure` call retracted** — 6EA makes no direct call to it. The
  standing lesson recorded at the time: *"never let a brick-consumption
  bookkeeping goal set a certified constant."* The factor-6 constant in the
  old `folklore_missFloor_beaten_sixfold` was exactly that artefact — 25×
  below truth — and the shipped name is now `folklore_missFloor_beaten_148fold`.

> **6EA's characteristic failure mode, recorded verbatim:** *narrative inflation
> around correct mathematics.* The mathematics was never wrong; the prose around
> it repeatedly was.

### 6EC — a physics BLOCKER, found by adversarial review

> Wave 3's Johnson channel modelled Johnson noise as pure *output* noise. …
> **A first-order ETF effect was missing from the wave whose subject is
> electrothermal feedback.** The headline factor is corrected from `|1+ℒ|` to
> `|1−ℒ|` — the two ETF effects partially cancel — so an ETF-unaware budget at
> the published `ℒ = 3` point is **2×** low, not 4×.

Also retracted in the same pass: `phonon_psd_eq_johnsonNyquist_scaled` was
relabelled from "citation" to **"resemblance"** (it constrains nothing, holding
for any expression of the same monomial shape, and is unit-incoherent as
provenance); `drivenBalance_eq_effectiveConductance_form` was **removed** as a
congruence wrapper whose statement never mentioned the predicate its docstring
claimed; and `thermalResponseAmplitude` was negative for negative drive, so both
its name and its docstring were false.

### 6EC — the deferral that was reversed by operator directive

> **⛔ NO LONGER DEFERRED.** … a tracked deferral reads as *handled* while
> leaving CLOSED work carrying known defects — and I5 in particular showed this
> phase's own headline thesis was **not derivable** from its shipped
> declarations.

### 6EE — close-out qualification (quote if D12 calls the series clean)

Six fresh-context adversarial rounds returned, in order,
`1/7/6 → 1/3/5 → 0/3/5 → 0/2/5 → 0/2/4 → 0/3/5` (BLOCKER/MAJOR/IMPORTANT). The
stricter operator bar — zero of all three — was **not** reached; a seventh
review was terminated by the operator.

- **What is solid:** the Lean substrate. 191/191 kernel-pure, zero project
  axioms.
- **What is not:** the roadmap's remediation tables are a **review log, not
  verified claims** — three rows were found to misdescribe their own fixes.
  Git history is the reliable record.

Also disclosed there: the 6EB and 6EC BITES witnesses fire at
`matchedBudget = 0`, a signal-free readout. Honest, but **degenerate** — no
non-degenerate biting point is bracketed for those two ceilings.

### 6CA — the QWZ spike, and a stale roadmap header

The Q4-Lane-C QWZ `C = ±1` spike returned **KILL/DEFER** on its own stop-rule
(2 of 5 gate criteria failed). It is a **defer, not a dead fork** — no kernel
no-go warranted. It was subsequently superseded in effect: 6ED W3 proved the
transcendental obstruction does not bind, and the Haldane frame became the
repo's first nontrivial concrete Chern frame.

⚠️ **`Phase6CA_Roadmap.md`'s header is stale** (dated 2026-06-30, says route
decision pending). The live ledger is `Phase6CA_prime_Roadmap.md` (2026-07-20).

---

## 4. Kernel no-gos registered from these arcs

Machine-enforced in `KERNEL_NOGO_REGISTRY` (`src/core/constants.py`), each
backed by a refutation theorem rather than prose
(`validate.py --check nogo_substrate_integrity`).

| Key | Verdict | Backing |
|---|---|---|
| `honeycomb_phase_chart_gl2z_invariant` | refutation | `structureFactor_zero_set_not_shear_invariant`, `isHoneycombChart_of_neighbours` |
| `spectrum_determines_multiband_model` | refutation | `bernal_spectrum_not_determine_model`, `bernal_chirality_two`, `bernalSwapped_chirality_zero` |
| `unsigned_matched_saturation_characterization` | refutation | `unsigned_saturation_characterization_false`, `filteredSNR_neg_matched_eq_neg_budget`, `power_unsigned_characterization_false` |

Plus three prose-only settled forks (not kernel-encodable) in
`SETTLED_FORKS.md`: `6ea-interval-restricted-gaussian-lower-tail` (banned on
*uselessness*, not falsity — its RHS goes negative across the entire operating
range), `6ea-optimalhypothesisrate-quantum-seam` (dead; type-level impossible
two independent ways), and `6eb-enbw-convention-falsifier-shape` (banned; the
product `S₀·ENBW` is convention-INVARIANT, so only *mixing* conventions is
detectable).

### The most transferable result in either arc

From `spectrum_determines_multiband_model`:

> The first pass shipped the **conjugated (wrong) matrix and passed every
> gate** — determinant, gap, enclosure, kernel purity, sorry-count,
> `validate.py`.

**Standing consequence:** for any multi-band Hamiltonian in this project, ship
at least one **eigenvector-level** invariant (winding, Berry phase, chirality)
verified against the primary source. *A determinant-level gate cannot certify a
model's identification.*

---

## 5. Discretization and modelling constraints worth not rediscovering

- **`3 ∣ N` grids are inadmissible** (6ED). Such grids sample `K`/`K'` where the
  `d`-vector is purely longitudinal, the south-pole vertex gives
  `‖d‖ + d₃ = 0`, and `lbVec` degenerates. Kills `N = 3, 6, 12, 24, …`. Two
  recorded corrections: the earlier "branch-cut" explanation was a *symptom*,
  not the cause, and a companion table wrongly offered `6×6` as clean.
- **A spectral gap does NOT imply nonvanishing nearest-neighbour overlaps.**
  `AdmissibleBandFrame.overlap_ne` is an explicit structure field for exactly
  this reason.
- **The north-pole condition is a real coordinate singularity**, not a
  cosmetic hypothesis: `lbVec ![0,0,-1] = ![0,0]`.
- **Isotropy is chart-specific**, not universal (`quadForm_of_chart`).
- **`ENBW·T ≥ 1/2` is one-sided-convention-specific.** The one- and two-sided
  normalizations provably disagree on the boxcar at every `T > 0`, so a
  convention-ambiguous statement is *wrong*, not differently phrased.
- **Where the modelling actually lives.** In `IsWhiteFilteredVariance`'s
  *definition* (Parseval + spectral flatness) and `IsShotFilteredMoments`'s
  *definition* (Campbell's theorem) — not in the theorems that consume them.
  A withdrawn claim worth remembering: *"an abbreviation cannot make a
  hypothesis stronger"* — `IsThermalFluctuationLimited` does not let a consumer
  state physics rather than spectral algebra.

---

## 6. Names that resolve to nothing (citation traps)

Any occurrence in a draft is a finding. From the 6E\* arc:
`folklore_missFloor_beaten_sixfold`,
`johnsonNEP_naive_understates_by_one_sub_loopGain`,
`johnsonNEP_bare_understates_by_one_plus_loopGain`, `shot_variance_eq_mean`
(a *claim* defect — its asserted content is refuted by its own file's
theorems), `matched_filter_snr_optimal`, `avg_error_ge_of_z_le`, `nep_def`,
`enbw_def`, `snr_composition`, `drivenBalance_eq_effectiveConductance_form`,
`phonon_nep_floor`, `johnson_nep_via_responsivity`,
`avgError_ge_half_gaussianQ`. From 6ED: `haldane_chern_iff_mass_inversion`,
`honeycombBloch_isHermitian`.

Two names deliberately retain a dead identifier in their *name* while their
*statements* are fully migrated, because frozen review artifacts cite them:
`hasSum_poissonPMFReal_mul_id`, `hasSum_poissonPMFReal_mul_descFactorial`.

Also: **`thrErr1_mono_in_sigma` must not be counted as a separate result** —
its own docstring forbids it, since `thrErr1 μ₁ σ t` is *definitionally*
`thrErr0 t σ μ₁`.

---

## 7. Counting conventions — do not mix

Two conventions circulate and they disagree materially:

- **Source-authored declarations** — what the papers use.
- **`lean_deps.json` extraction** — larger; additionally counts Lean-generated
  equation lemmas (e.g. `ETFModel` 50 vs 68).

⚠️ **Roadmap-quoted counts are stale** against the live extract. Regenerate
before typesetting any count, and state which convention is in use.

---

## 8. Novelty posture — both arcs

Every novelty claim is scoped to pinned versions (Mathlib `81a5d257`, PhysLib
`c4843367`) and to the checks actually performed.

- **D12's original novelty claim was REFUTED** by a live sweep (2026-07-28),
  inside our own dependency tree: Mathlib already kernel-checks a sub-Gaussian
  Chernoff bound (ours is a factor-2 *sharpening*, not a first), and PhysLib
  already kernel-checks quantum hypothesis testing. Only the narrowed,
  knowledge-hedged form survives.
- **Two blocking pre-submission checks remain open for D12:**
  `RemyDegenne/testing-lower-bounds` (highest prior-art risk — a
  Bayes-binary-risk ↔ divergence bound there would be substantially our Le Cam
  floor), and Isabelle/AFP + Coq `infotheo` (wholly unassessed).
- **D11's claims survived** a comparable sweep, but carry four mandatory
  carve-outs (PhysLib `TightBindingChain`; Cubical Agda Gysin + ℂP^∞; Isabelle
  winding numbers; Coq Lax–Milgram) and two coverage gaps (the Isabelle AFP was
  not searchable; HOL4/PVS coverage is weak).
- **Sibling precedent, live:** Phase 6BD's novelty was **refuted** by QBlue
  (Rocq, arXiv:2509.18583). That failure mode is not hypothetical.

Full detail: `papers/D11/prior_art_novelty.md`, `papers/D12/prior_art_novelty.md`.

---

*Companion to `docs/ARCHITECTURE_SCOPE.md` (which gained its 6C\*/6E\* section
on the same date) and to the two bundle drafts. Supersedes nothing; the
gitignored lab notebooks remain the per-wave detail if they survive.*
