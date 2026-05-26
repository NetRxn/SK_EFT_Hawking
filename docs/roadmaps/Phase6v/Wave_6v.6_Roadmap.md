# Wave 6v.6 — W-state QFT decomposition in Q(ζ_N) (D6 §6)

**Bundle target:** D6 §6.

**Status:** ✅ SHIPPED 2026-05-26.

**Sources:**
- W. Dür, G. Vidal, J. I. Cirac, "Three qubits can be entangled in two inequivalent ways," Phys. Rev. A 62, 062314 (2000); arXiv:quant-ph/0005115; DOI 10.1103/PhysRevA.62.062314. Foundational W-state paper.
- Kyoto-Hiroshima W-state projective-measurement work (Kyoto Univ. press 2025-09-16, ScienceDaily feature May 2026) per strategy synthesis F9; specific arXiv ID not yet well-indexed. Cited indirectly via the well-known cyclic-shift-eigenstate decomposition.

**Wave goal.** Substrate-level kernel-verified encoding of two complementary claims:

1. **Cyclic-shift eigenvalue structure:** the n-qubit W-state has Z_n cyclic-shift symmetry, so single-shot projective measurement in the cyclic-shift eigenbasis yields one of n outcomes indexed by k ∈ {0, 1, …, n−1}, with eigenvalues ζ_n^k (n-th roots of unity). The natural number field for the QFT_n measurement basis is Q(ζ_n).
2. **Cyclotomic substrate connection:** for the n = 5 case (which the project's existing `QCyc5` module supports), the QFT_5 measurement basis lives natively in Q(ζ_5); for n = 8 (QCyc16) and n = 40 (QCyc40), the corresponding QFT_n measurement bases are natively in the project's existing cyclotomic substrate.

Substantive content: the W-state cyclic-shift eigenvalue spectrum has exactly n distinct values (all n-th roots of unity), and the natural-number-field requirement on the QFT measurement basis is exactly that the field contains the n-th cyclotomic polynomial roots.

## Deliverables

| Stage | Action | Status |
|---:|---|:---:|
| 1 | Per-wave roadmap + bibkey. | ✅ SHIPPED |
| 2 | (skip) — no new Python formulas. | SKIP |
| 3a | Ship Lean `lean/SKEFTHawking/FaultTolerance/WStateQFT.lean` (~110 LoC, kernel-only): `WStateCyclicShiftDecomposition n` structure, `nQubitWStateBasisSize` function, `wState_basis_size_eq_n`, `IsCyclotomicQFTBasis` predicate, substrate-level connection to `QCyc5` / `QCyc16` / `QCyc40` cyclotomic-field-of-record, substantive contrast `n_qubit_w_state_basis_strictly_smaller_than_full_hilbert` (the W-state QFT basis size `n` is strictly smaller than the full Hilbert-space dimension `2^n` for `n ≥ 2`, the exponential-vs-polynomial separation). | ✅ SHIPPED |
| 4 | (Aristotle — not needed.) | SKIP |
| 5 | `lake env lean` clean. | ✅ SHIPPED (file-gate) |
| 6 | `tests/test_w_state_qft.py` regression. | ✅ SHIPPED |
| 7 | `validate.py` checks: citation_primary_sources_present. | ✅ SHIPPED |
| 8 | (skip) — no new figures. | SKIP |
| 9 | (skip) — no figures. | SKIP |
| 10 | D6 §6 populated with Wave-6v.6 substantive content. | ✅ SHIPPED |
| 11 | (skip) — no new notebooks. | SKIP |
| 12 | Phase6v_Roadmap.md status; per-wave roadmap finalized; Inventory_Index + stakeholder docs DEFERRED to Phase 6v close. | ✅ SHIPPED |
| 13 | DEFERRED. | DEFERRED |
| 14 | QI — none. | ✅ NO-FINDINGS |

## No-axiom discipline

Zero new project-local axioms. The exponential-vs-polynomial separation (`n < 2^n` for n ≥ 2) is discharged by `Nat.lt_two_pow_self`.

## Wave 6v.6b follow-up (queued 2026-05-26, post-Phase-6v-close scout)

**Scout finding:** my shipping of `IsCyclotomicQFTBasis (_n : ℕ) : Prop := True` was **premature scoping**. Mathlib v4.29.1 contains `CyclotomicField n ℚ` (in `Mathlib/NumberTheory/Cyclotomic/Basic.lean`) with the `IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ)` instance + `IsPrimitiveRoot` (in `Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean`) + the canonical `primitiveRoot_spec`. Substantive Tier-1 lift is ~4 LoC.

**Wave 6v.6b action set** (executed in the next session, per `temporary/working-docs/phase6v_deferred_followup_plan.md`):

1. Add imports `Mathlib.NumberTheory.Cyclotomic.Basic` + `Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots` to `WStateQFT.lean`.
2. Replace `def IsCyclotomicQFTBasis (_n : ℕ) : Prop := True` with `def IsCyclotomicQFTBasis (n : ℕ) : Prop := ∃ ζ : CyclotomicField n ℚ, IsPrimitiveRoot ζ n`.
3. Discharge `wState_basis_isCyclotomic (n : ℕ) (hn : 1 ≤ n) : IsCyclotomicQFTBasis n` via Mathlib's `IsCyclotomicExtension.exists_prim_root` (or equivalent — exact API name to confirm via MCP).
4. Update `wave_6v_6_substantive_closure` to use the new non-vacuous witness (add `(by decide : 1 ≤ 40)`).
5. Add `wState_basis_isCyclotomic_at_QCyc_sizes` (substantive non-vacuity at n = 5, 40, 80 — the project's QCyc_n cyclotomic-substrate sizes).
6. Update D6 §6 paragraph to cite the substantive `wState_basis_isCyclotomic` instead of the placeholder.

**Tier 2 (Mathlib-PR-quality, NOT in 6v.6b scope):** bridge the project's existing QCyc_n custom-struct cyclotomic-substrate modules to Mathlib's `CyclotomicField n ℚ` via algebra isomorphisms. ~100 LoC. Deferred to a separate future wave; remains a genuine "future Mathlib substrate" deliverable.

Estimated effort for Tier 1 (6v.6b): ~30 LoC + 1 commit. Scope: cheap follow-up, not a separate wave.

**Scout report:** `temporary/working-docs/phase6v_scout_report_2026-05-26.md`.
**Action plan:** `temporary/working-docs/phase6v_deferred_followup_plan.md`.
