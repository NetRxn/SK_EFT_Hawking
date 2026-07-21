/-
# Reducing `H₃(K3;ℤ)` 2-torsion-freeness to a 2-saturation of the degree-3 seam image

`KummerK3E1Package.KummerK3H3TwoTorsionFree` is the orientation input of the K3 → row bridge
(`IntOrientationMod2Lift.intOrientation_of_h3_twoTorsionFree` consumes it). This module reduces
it, through the **unconditional** K7 Mayer–Vietoris, to a precise linear-algebra statement about
the concrete degree-3 seam map — removing the carrier-level `H₃(K3)` from the obligation.

The MV degree-3 window (cover `K3 = qThick ∪ eImage`, `k7_hcov`) is

    H₃(qThick ∩ eImage) --Δ₃--> H₃(qThick) ⊕ H₃(eImage) --Σ₃--> H₃(K3) --> 0

with `Σ₃` surjective (`k7Sum3_surjective`, from `H₂(collar) = 0`) and `ker Σ₃ = im Δ₃`
(`k7_exact_middle`). Hence `H₃(K3;ℤ) ≅ coker Δ₃`, and a cokernel `M / im f` is 2-torsion-free
**iff** `im f` is 2-saturated in `M` (a `2•y ∈ im f` forces `y ∈ im f`). So

    (im Δ₃ is 2-saturated in H₃(qThick) ⊕ H₃(eImage))  ⟹  KummerK3H3TwoTorsionFree.

This isolates the remaining content in the seam map's image. Banked already: `H₃(eImage) = 0`
(`eImageH3_eq_zero`) and `H₃(qThick ∩ eImage) ≅ ℤ¹⁶` (`interHnEquivInt 3`). The still-open
dependency is `H₃(qThick) ≅ H₃(Q)` together with the concrete map `Δ₃` into it — Q-side degree-3
homology, not yet computed in tree (cf. the degree-2 `H₂(Q;ℤ) ≅ ℤ⁶` that the b₂ = 22 arc did).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerK3E1Package
import SKEFTHawking.KummerK7MVAssembly

namespace SKEFTHawking.KummerK3H3Reduction

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerWeld (eImage)
open SKEFTHawking.KummerK7MVAssembly
open SKEFTHawking.SingularMayerVietorisLESInt

noncomputable section

/-- The degree-3 MV seam map `Δ₃ : H₃(qThick ∩ eImage) → H₃(qThick) ⊕ H₃(eImage)`. -/
abbrev delta3 := mvHomDiagInt (X := KummerK3top) qThick eImage 3

/-- **THE REDUCTION** — `H₃(K3;ℤ)` is 2-torsion-free as soon as the degree-3 seam image `im Δ₃` is
2-saturated in `H₃(qThick) ⊕ H₃(eImage)`. Via `Σ₃` surjective + `ker Σ₃ = im Δ₃`, `H₃(K3) ≅ coker Δ₃`,
and a cokernel is 2-torsion-free iff the subgroup is 2-saturated. Removes the carrier-level `H₃(K3)`
from the residual, leaving only a statement about the concrete seam map. -/
theorem kummerK3H3TwoTorsionFree_of_delta3_two_saturated
    (hsat : ∀ y, (2 : ℤ) • y ∈ Set.range delta3 → y ∈ Set.range delta3) :
    KummerK3E1Package.KummerK3H3TwoTorsionFree := by
  intro x hx
  obtain ⟨y, hy⟩ := k7Sum3_surjective x
  have h2y : mvHomSumInt (X := KummerK3top) qThick eImage 3 ((2 : ℤ) • y) = 0 := by
    rw [map_smul, hy]; exact hx
  have hmem : (2 : ℤ) • y ∈ Set.range delta3 := (k7_exact_middle 2 _).mp h2y
  have hSumZero : mvHomSumInt (X := KummerK3top) qThick eImage 3 y = 0 :=
    (k7_exact_middle 2 y).mpr (hsat y hmem)
  rw [← hy]; exact hSumZero

/-- **THE REDUCTION IS LOSSLESS** — the 2-saturation of `im Δ₃` is not merely sufficient for but
*exactly equivalent* to `H₃(K3;ℤ)` 2-torsion-freeness. The converse is the same machinery run
backwards: `2•y ∈ im Δ₃ = ker Σ₃ ⟹ 2•(Σ₃ y) = 0 ⟹ Σ₃ y = 0` (by 2-torsion-freeness) `⟹ y ∈ ker Σ₃ =
im Δ₃`. So the reduction narrows the residual to a genuinely equivalent target, not a stronger one. -/
theorem kummerK3H3TwoTorsionFree_iff_delta3_two_saturated :
    KummerK3E1Package.KummerK3H3TwoTorsionFree ↔
      ∀ y, (2 : ℤ) • y ∈ Set.range delta3 → y ∈ Set.range delta3 := by
  refine ⟨fun h3 y hy2 => ?_, kummerK3H3TwoTorsionFree_of_delta3_two_saturated⟩
  have hz : mvHomSumInt (X := KummerK3top) qThick eImage 3 ((2 : ℤ) • y) = 0 :=
    (k7_exact_middle 2 _).mpr hy2
  rw [map_smul] at hz
  exact (k7_exact_middle 2 y).mp (h3 _ hz)

end

end SKEFTHawking.KummerK3H3Reduction
