# Wave 6v.8 — NbRe triplet superconductor SOTA BdG + SPT classification

**Bundle targets:** D2 §"SPT classification — material exhibits" (primary) + D4 §"topological-qubit substrate candidates" (cross-bridge).

**Status:** ✅ FULLY SHIPPED 2026-05-26 (post-DR-return + Sub-wave 8.C substantive discharge via Fu–Kane / Sato–Fujimoto Pfaffian Pathway A).

## Sub-wave 8.C close (post-DR-return 2026-05-26)

**✅ SUB-WAVE 8.C SUBSTANTIVELY DISCHARGED** via Pathway A from the decomposition-pathways DR dossier `Lit-Search/Phase-6v/wave6v8C_nbRe_DIII_decomposition_pathways.md` (returned 2026-05-26).

**Substantive content of the discharge:**
- The tracked Prop `H_NbReWindingNumberIdentity` is **substantively strengthened** from the original `True` placeholder to `∀ sc : SCParameters, IsDIIITopologicalSuperconductor sc → fuKaneInvariant sc = -1`.
- The strengthened body is proved kernel-only via the canonical Fu–Kane / Sato–Fujimoto TRIM-product Pfaffian Z₂ invariant:
  ```
    δ(sc) := ∏_{k ∈ TRIMs} Int.sign (Pf (w(sc, k)))
  ```
  evaluating to −1 for NbRe (DIII-topological) and +1 for elemental Nb (DIII-trivial).
- Headline theorem `fuKaneInvariant_eq_neg_one_of_DIII_topological` quantifies universally over any DIII-topological parameter capsule (not just NbRe). NbRe instance discharged via `nbRe_fuKaneInvariant_neg_one`.
- 4×4 closed-form Pfaffian `pf4 a b c d e f := a*f - b*e + c*d` vendored inline in `NbReTripletSPT.lean` §7.A; general `Matrix.pfaffian` upstream-Mathlib-PR-quality contribution documented as a follow-up but not load-bearing.
- Project-local axiom count **UNCHANGED at 0**.
- Kernel-only axiom closure `[propext, Classical.choice, Quot.sound]` on all new headline theorems.
- 21 Python regression tests in `tests/test_nbre_fu_kane_pfaffian.py` mirror the Lean substrate and validate the substantive invariant per material class.

**Decomposition-pathway selection.** The DR evaluated 5 candidate pathways for the 3D DIII Z₂ invariant Mathlib v4.29.1 lacks (A = Fu–Kane TRIM Pfaffian; B = ℤ₁₆ mod-2 projection; C = Fu–Kane–Mele weak+strong; D = Berry-phase Wilson loop; E = Karoubi K-theory). Pathway A was selected at ~220 LoC project-local (vs. the original ~2000 LoC MapDegree estimate). Substrate leverage was GREEN (existing `PauliMatrices.lean` + `BdGHamiltonian.lean` + `MajoranaKramers.lean` + `SCParameters` capsule). Pathways B, C, D, E rejected with reasons documented in the DR.

**Source paper:**
F. Colangelo et al., "Unveiling Intrinsic Triplet Superconductivity in Noncentrosymmetric NbRe through Inverse Spin-Valve Effects," Phys. Rev. Lett. 135, 226002 (2025); arXiv:2510.08110; DOI 10.1103/q1nb-cvh6. Bibkey: `Colangelo2025NbReTripletSpinValve`. Primary-source cache: `Lit-Search/Phase-1-and-Background/primary-sources/Colangelo2025NbReTripletSpinValve.pdf`.

**Wave goal.** Substrate-level kernel-verified encoding of the NbRe material's distinguishing properties:

1. **Noncentrosymmetric crystal structure.** NbRe lacks spatial-inversion symmetry, enabling antisymmetric spin-orbit coupling (ASOC). The Lean substrate ships an `IsNoncentrosymmetric` predicate witnessing this on the NbRe parameter capsule.
2. **Triplet-pairing channel.** Colangelo et al. 2025 demonstrate inverse-spin-valve effects on Py/NbRe/Py heterostructures, evidencing intrinsic equal-spin triplet pairing. The Lean substrate ships an `IsTripletSuperconductor` predicate with NbRe as a substantive witness, contrasted with the canonical s-wave singlet baseline (e.g., elemental Nb).
3. **Cross-bridge to SPT classification.** A noncentrosymmetric triplet superconductor with preserved time-reversal symmetry falls in the DIII topological class — the same class that hosts Kitaev DIII period-16 (and the project's existing Z₁₆ anomaly classification connects via Rokhlin). The substrate ships a cross-bridge predicate `IsDIIITopologicalSuperconductor` linking NbRe to the project's existing `Z16Classification` substrate.

**Sub-wave scoping (honest LoE):**
- **8.A (parameters + provenance):** Tc ≈ 8.7 K, crystal symmetry, ASOC scale, d-vector pairing notation. ✅ SHIPPED.
- **8.B (toy substrate-level BdG):** lifts the project's existing `BdGHamiltonian.lean` toy 4×4 BdG to a 2-site NbRe-flavored toe-hold. ✅ SHIPPED at substrate level.
- **8.C (Fu–Kane / Sato–Fujimoto Pfaffian Z₂ — Pathway A):** the canonical noncentrosymmetric-BCS Z₂ invariant via TRIM-product Pfaffian. ✅ **SHIPPED 2026-05-26 post-DR-return.** The original deferral plan called for a ~2000 LoC `MapDegree` upstream Mathlib contribution; the DR selected Pathway A at ~220 LoC project-local instead, using the 4×4 closed-form Pfaffian directly. `H_NbReWindingNumberIdentity` is **substantively discharged** kernel-only (NOT shipped as a tracked Prop). The general `Matrix.pfaffian` upstream Mathlib contribution remains a documented follow-up.
- **8.D (D2 + D4 paper lifts):** D2 §"SPT material exhibits" + D4 §"topological-qubit substrate candidates" populated with Wave 6v.8 substantive content. ✅ SHIPPED.

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
| 3a | Ship Lean `lean/SKEFTHawking/NbReTripletSPT.lean` (~500 LoC, kernel-only): `NbReParameters` capsule, `PairingChannel` inductive, `IsNoncentrosymmetric`, `IsTripletSuperconductor`, NbRe witness theorems, contrast with `elementalNbParameters` (canonical s-wave singlet), `IsDIIITopologicalSuperconductor` cross-bridge predicate to SPT-classification, **and §7 Sub-wave 8.C substantive discharge**: 4×4 closed-form Pfaffian + TRIM enumeration + sewing-matrix coefficient profile + `fuKaneInvariant` + `fuKaneInvariant_eq_neg_one_of_DIII_topological` + `H_NbReWindingNumberIdentity_holds` discharge. | ✅ SHIPPED |
| 4 | (Aristotle — not needed.) | SKIP |
| 5 | `lake env lean` clean. | ✅ SHIPPED (file-gate) |
| 6 | `tests/test_nbre_triplet_spt.py` + `tests/test_nbre_fu_kane_pfaffian.py` (Sub-wave 8.C, 21 cases) regression. | ✅ SHIPPED |
| 7 | `validate.py` citation_primary_sources_present PASS. | ✅ SHIPPED |
| 8 | (skip) — no new figures. | SKIP |
| 9 | (skip) — no figures. | SKIP |
| 10 | D2 + D4 paragraphs added cross-referencing the Lean substrate. | ✅ SHIPPED |
| 11 | (skip) — no new notebooks. | SKIP |
| 12 | Phase6v_Roadmap.md updated; per-wave roadmap finalized; stakeholder docs DEFERRED. | ✅ SHIPPED |
| 13 | DEFERRED. | DEFERRED |
| 14 | QI — none. | ✅ NO-FINDINGS |

## Tracked Prop discharge — substantively shipped 2026-05-26 (post-DR-return, same day)

The DR dispatched on the morning of 2026-05-26 returned the same day with a dossier (`Lit-Search/Phase-6v/wave6v8C_nbRe_DIII_decomposition_pathways.md`) recommending **Pathway A — Fu–Kane / Sato–Fujimoto TRIM-product Pfaffian** at ~220 LoC project-local, vs. the original ~2000 LoC `MapDegree` upstream estimate.

**Why Pathway A:** Mathlib v4.29.1 has the commutative-algebra substrate (det, `Equiv.Perm.sign`, `Fintype`, `Int.sign`) required for the TRIM-product invariant; only the 4×4 closed-form Pfaffian `pf4 a b c d e f := a*f - b*e + c*d` needs to be vendored (~10 LoC). The Pfaffian-Z₂ formulation is the canonical condensed-matter-physicist route since Sato–Fujimoto PRB 79, 094504 (2009) and Qi–Hughes–Raghu–Zhang PRB 81, 134508 (2010), and is the explicit form Ono–Po–Shiozaki PRR 3, 023086 (2021) tabulate for the noncentrosymmetric space groups.

**Substantive discharge:**

The tracked Prop body was strengthened from
```
  ∀ sc, IsDIIITopologicalSuperconductor sc → True
```
to
```
  ∀ sc, IsDIIITopologicalSuperconductor sc → fuKaneInvariant sc = -1
```

and the strengthened form is proved kernel-only via
`fuKaneInvariant_eq_neg_one_of_DIII_topological` (universally
quantified over any DIII-topological capsule, not just NbRe).

Pathways B, C, D, E were rejected with reasons recorded in the DR
dossier (B: BdG → Pin⁺ bordism map itself absent in Mathlib; C: S²
vs T² manifold mismatch in `FermiPointTopology.lean`; D: ~1200 LoC
Berry-phase Wilson-loop substrate gap; E: ~2000 LoC K-theory).

## No-axiom discipline

Zero new project-local `axiom` declarations. **Zero tracked Props remain at Wave 6v.8 close** — `H_NbReWindingNumberIdentity` is substantively discharged. Project-local axiom count UNCHANGED at 0.
