# Wave 6w.4 — Chebyshev-TN + aperiodic-lattice substrate

**Phase:** 6w
**Wave:** 6w.4 (Aalto-style Chebyshev TN methods + Penrose-tiling-style aperiodic lattices)
**Status:** ✅ SHIPPED 2026-05-26 PM. 16 substantive theorems across `lean/SKEFTHawking/{ChebyshevTN,AperiodicLattice}.lean`. Build clean 8711 jobs; zero new axioms; zero sorries; key theorems verified kernel-only `[propext, Classical.choice, Quot.sound]`.
**Bundle target:** I1 substrate; later D7 candidate.
**LoE:** ~3-4 sessions per Phase6w_Roadmap.md

---

## Goal

Build the Mathlib-PR-quality substrate for (i) Chebyshev tensor-network
contraction methods (Antão-Sun-Fumega-Lado 2026, PRL 136, 156601,
DOI 10.1103/hhdf-xpwg; arXiv:2506.05230) and (ii) aperiodic /
quasicrystal lattices (Penrose-tiling cut-and-project method,
crystallographic-restriction-theorem-style arguments).

Consumed by Wave 6w.5 (categorical-Chern ↔ real-space-Chern bridge
on quasicrystals) and Wave 6w.6 (combined classical-simulability
demarcation).

## Substantive deliverables

### Module 1 — `lean/SKEFTHawking/ChebyshevTN.lean`

* `chebyshevT : ℕ → ℝ → ℝ` — first-kind Chebyshev polynomials defined
  via the recurrence relation `T_0(x) = 1`, `T_1(x) = x`,
  `T_{n+1}(x) = 2x · T_n(x) - T_{n-1}(x)`.
* `ChebyshevExpansion` — structure carrying a finite list of
  coefficients `(c_0, c_1, ..., c_N) ∈ ℝ` representing the truncated
  expansion `∑_{n=0}^N c_n · T_n(x)`.
* `evalChebyshev : ChebyshevExpansion → ℝ → ℝ` — evaluate the
  expansion at point `x`.
* **Substantive theorems (≥5):**
  - `chebyshevT_zero` (T_0(x) = 1).
  - `chebyshevT_one` (T_1(x) = x).
  - `chebyshevT_recurrence` (T_{n+2}(x) = 2x · T_{n+1}(x) - T_n(x)).
  - `chebyshevT_eval_one` (T_n(1) = 1 by induction).
  - `chebyshevT_eval_neg_one` (T_n(-1) = (-1)^n by induction).

### Module 2 — `lean/SKEFTHawking/AperiodicLattice.lean`

* `Lattice2D` = a subset of `ℝ × ℝ`, treated as the set of
  lattice points.
* `IsPeriodic2D L v` — predicate `v ≠ 0 ∧ ∀ p ∈ L, p + v ∈ L`.
* `IsAperiodic2D L` — predicate `∀ v, v ≠ 0 → ¬ (∀ p ∈ L, p + v ∈ L)`.
* `IsTranslationInvariant L v` — `∀ p ∈ L, p + v ∈ L` (no non-zero
  constraint).
* `singletonLattice p` — singleton lattice `{p}`.
* `emptyLattice` — empty lattice `∅`.
* **Substantive theorems (≥5):**
  - `emptyLattice_translation_invariant_under_all_v`: vacuous truth
    on the empty lattice.
  - `singletonLattice_aperiodic`: every singleton lattice is aperiodic.
  - `singletonLattice_translation_invariant_iff_zero`: a singleton
    lattice is translation-invariant under `v` iff `v = 0`.
  - `IsAperiodic2D_iff_no_nonzero_translation`: substantive
    biconditional characterizing aperiodicity.
  - `union_of_translation_invariants_translation_invariant`: closure
    under union for given `v`.

### Pipeline integration

- Add `ChebyshevTN` and `AperiodicLattice` to root `SKEFTHawking.lean`
  imports.
- `lake build` clean.

## Acceptance criteria (Wave 6w.4)

- ✅ ≥10 substantive theorems shipped across both modules.
- ✅ Modules build clean; zero new project-local axioms; zero sorries.
- ✅ Key theorems verified kernel-only `[propext, Classical.choice, Quot.sound]`.
- ✅ Primary source cached per Invariant #11.
- ✅ Preemptive-strengthening 5Q checklist applied.

## Cross-references

- Phase 6w roadmap: `docs/roadmaps/Phase6w_Roadmap.md`
- Aalto PRL: arXiv:2506.05230 / PRL 136, 156601 (2026).
- Wave 6w.2 BP-on-TN substrate (sibling): `lean/SKEFTHawking/BeliefPropagation.lean`.
- Wave 6w.5 Chern bridge (downstream consumer): TBD.
