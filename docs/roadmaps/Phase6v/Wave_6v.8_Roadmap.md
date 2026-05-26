# Wave 6v.8 — NbRe triplet superconductor SOTA BdG + SPT classification

**Bundle targets:** D2 §"SPT classification — material exhibits" (primary) + D4 §"topological-qubit substrate candidates" (cross-bridge).

**Status:** ✅ SHIPPED 2026-05-26 (focused substrate-level encoding; full SOTA BdG sub-wave 8.C deferred to future infrastructure wave per honest LoE).

**Source paper:**
F. Colangelo et al., "Unveiling Intrinsic Triplet Superconductivity in Noncentrosymmetric NbRe through Inverse Spin-Valve Effects," Phys. Rev. Lett. 135, 226002 (2025); arXiv:2510.08110; DOI 10.1103/q1nb-cvh6. Bibkey: `Colangelo2025NbReTripletSpinValve`. Primary-source cache: `Lit-Search/Phase-1-and-Background/primary-sources/Colangelo2025NbReTripletSpinValve.pdf`.

**Wave goal.** Substrate-level kernel-verified encoding of the NbRe material's distinguishing properties:

1. **Noncentrosymmetric crystal structure.** NbRe lacks spatial-inversion symmetry, enabling antisymmetric spin-orbit coupling (ASOC). The Lean substrate ships an `IsNoncentrosymmetric` predicate witnessing this on the NbRe parameter capsule.
2. **Triplet-pairing channel.** Colangelo et al. 2025 demonstrate inverse-spin-valve effects on Py/NbRe/Py heterostructures, evidencing intrinsic equal-spin triplet pairing. The Lean substrate ships an `IsTripletSuperconductor` predicate with NbRe as a substantive witness, contrasted with the canonical s-wave singlet baseline (e.g., elemental Nb).
3. **Cross-bridge to SPT classification.** A noncentrosymmetric triplet superconductor with preserved time-reversal symmetry falls in the DIII topological class — the same class that hosts Kitaev DIII period-16 (and the project's existing Z₁₆ anomaly classification connects via Rokhlin). The substrate ships a cross-bridge predicate `IsDIIITopologicalSuperconductor` linking NbRe to the project's existing `Z16Classification` substrate.

**Sub-wave scoping (honest LoE):**
- **8.A (parameters + provenance):** Tc ≈ 8.7 K, crystal symmetry, ASOC scale, d-vector pairing notation. SHIPPED.
- **8.B (toy substrate-level BdG):** lifts the project's existing `BdGHamiltonian.lean` toy 4×4 BdG to a 2-site NbRe-flavored toe-hold. SHIPPED at substrate level.
- **8.C (full 3D SOTA BdG):** the full 3D non-centrosymmetric lattice + SOC + d-vector triplet pairing + singlet-triplet mixing model — DEFERRED per the strategy synthesis's "no new project-local axioms" discipline. The 3D winding-number identity Mathlib lacks ships as the `H_NbReWindingNumberIdentity` tracked Prop with discharge plan in this roadmap.
- **8.D (D2 + D4 paper lifts):** D2 §"SPT material exhibits" + D4 §"topological-qubit substrate candidates" populated with Wave 6v.8 substantive content. SHIPPED.

## Key parameters

| Symbol | Value | Source | Use |
|---|---:|---|---|
| `Tc_NbRe` | 8.7 | K (Colangelo et al. 2025) | superconducting transition temperature |
| `ASOC scale` | ~10 meV | order-of-magnitude estimate | antisymmetric spin-orbit coupling |
| `d-vector` | parallel to [001] (representative) | Colangelo Sec. III | pairing axis |
| `pairing channel` | triplet (equal-spin) | Colangelo headline | type tag |

## Deliverables

| Stage | Action | Status |
|---:|---|:---:|
| 1 | Per-wave roadmap + PDF cache + bibkey. | ✅ SHIPPED |
| 2 | (skip) — no new Python formulas. | SKIP |
| 3a | Ship Lean `lean/SKEFTHawking/NbReTripletSPT.lean` (~150 LoC, kernel-only): `NbReParameters` capsule, `PairingChannel` inductive, `IsNoncentrosymmetric`, `IsTripletSuperconductor`, NbRe witness theorems, contrast with `elementalNbParameters` (canonical s-wave singlet), `IsDIIITopologicalSuperconductor` cross-bridge predicate to SPT-classification, `H_NbReWindingNumberIdentity` tracked Prop (for sub-wave 8.C discharge). | ✅ SHIPPED |
| 4 | (Aristotle — not needed.) | SKIP |
| 5 | `lake env lean` clean. | ✅ SHIPPED (file-gate) |
| 6 | `tests/test_nbre_triplet_spt.py` regression. | ✅ SHIPPED |
| 7 | `validate.py` citation_primary_sources_present PASS. | ✅ SHIPPED |
| 8 | (skip) — no new figures. | SKIP |
| 9 | (skip) — no figures. | SKIP |
| 10 | D2 + D4 paragraphs added cross-referencing the Lean substrate. | ✅ SHIPPED |
| 11 | (skip) — no new notebooks. | SKIP |
| 12 | Phase6v_Roadmap.md updated; per-wave roadmap finalized; stakeholder docs DEFERRED. | ✅ SHIPPED |
| 13 | DEFERRED. | DEFERRED |
| 14 | QI — none. | ✅ NO-FINDINGS |

## Tracked Prop introduced (`H_NbReWindingNumberIdentity`)

The full 3D non-centrosymmetric BdG sub-wave 8.C requires a 3D winding-number identity that Mathlib doesn't yet have (the project's existing winding-number substrate is 1D + 2D only). Per Pipeline Invariant #15: ships as a TRACKED PROP, not a new project-local axiom. Discharge plan: a future Mathlib-3D-winding-number-substrate wave (LoE ~300-500 LoC infrastructure; outside Phase 6v scope).

## No-axiom discipline

Zero new project-local `axiom` declarations. One new tracked Prop (`H_NbReWindingNumberIdentity`) with explicit discharge plan above.
