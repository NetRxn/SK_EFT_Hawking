import Mathlib
import SKEFTHawking.SingularFunctoriality

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-homhomeo) — a homeomorphism induces a homology isomorphism

`Homology.map` of a homeomorphism `e : ↑X ≃ₜ ↑Y` is a **linear equivalence**, with inverse
`Homology.map e.symm` (homology functoriality `Homology.map_comp` / `Homology.map_id`).

This is the bridge used by the homology-colimit **bottom endpoint** of the Poincaré-duality ladder: for a
compact manifold the colimit collapses onto `H_n(sub univ)`, which the universal-set homeomorphism
`↥univ ≃ₜ M` identifies with `H_n(M)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.SingularHomologyHomeo

/-- **A homeomorphism induces a homology isomorphism**: `Homology.map e` is a `ℤ/2`-linear equivalence
with inverse `Homology.map e.symm`. -/
noncomputable def homologyHomeoEquiv {X Y : TopCat} (e : ↑X ≃ₜ ↑Y) (n : ℕ) :
    Homology X n ≃ₗ[ZMod 2] Homology Y n :=
  LinearEquiv.ofLinear (Homology.map (toContinuousMap e) n)
    (Homology.map (toContinuousMap e.symm) n)
    (by
      have hcm : (toContinuousMap e).comp (toContinuousMap e.symm) = ContinuousMap.id ↑Y := by
        ext y; exact e.apply_symm_apply y
      rw [← Homology.map_comp (X := Y) (Y := X) (Z := Y), hcm, Homology.map_id])
    (by
      have hcm : (toContinuousMap e.symm).comp (toContinuousMap e) = ContinuousMap.id ↑X := by
        ext x; exact e.symm_apply_apply x
      rw [← Homology.map_comp (X := X) (Y := Y) (Z := X), hcm, Homology.map_id])

end SKEFTHawking.SingularHomologyHomeo
