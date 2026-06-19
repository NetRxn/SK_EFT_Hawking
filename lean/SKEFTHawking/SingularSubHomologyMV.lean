import Mathlib
import SKEFTHawking.SingularMayerVietorisLES
import SKEFTHawking.SingularOpenDualityMVSquare

/-!
# Phase 5q.F (w₂-foundation) — the bottom-row homology MV LES of the Poincaré-duality `5`-lemma

The **bottom row** of the PD `5`-lemma ladder is the Mayer–Vietoris long exact sequence of the
*space* `sub (U ∪ V)` under its open cover `{val⁻¹'U, val⁻¹'V}`. The diagonal/sum
`SingularOpenDualityMVSquare.subHomDiag`/`subHomSum` (the subspace-inclusion maps `homOfSubset`)
were already built; this file supplies the **connecting map** `subHomConnecting` matching them, and
proves the **three exactness** statements
`subHom_exact_sum`/`subHom_exact_connecting`/`subHom_exact_middle` closing the sequence
`⋯ → Hₙ₊₁(sub(U∪V)) →[δ] Hₙ(sub(U∩V)) →[Δ] Hₙ(sub U)⊕Hₙ(sub V) →[Σ] Hₙ(sub(U∪V)) → ⋯`.

## Construction (no new homology theory)
Instantiate `SingularMayerVietorisLES` at the **ambient space** `sub (U ∪ V)`, with the two open
sets `A = Subtype.val⁻¹'U`, `B = Subtype.val⁻¹'V` in `↥(U∪V)`. The cover condition holds since every
`p : ↥(U∪V)` has `p.val ∈ U ∪ V` (so `A ∪ B = univ`) and `A`, `B` are open (`cover_preimage`); and
`A ∩ B = Subtype.val⁻¹'(U∩V)`. The reassociation **seam** isos `seamU`/`seamV`/`seamI`
(`H(sub A) ≅ H(sub U)`, etc., the underlying map identity on `X`) transport the LES maps
`mvHomDiag`/`mvHomSum`/`mvDelta` onto `subHomDiag`/`subHomSum`/`subHomConnecting` via the
cap-naturality squares `diagSquare`/`sumSquare`; the three `mv_exact_*` exactness statements then
transfer through the seam `LinearEquiv`s with `Function.Exact.of_ladder_linearEquiv_of_exact`.

`subHom_exact_middle` is indexed at `n + 1` to match `SingularMayerVietorisLES.mv_exact_middle` (and
its compactly-supported-cohomology twin `SingularCSCMayerVietorisMiddle.cscMv_exact_middle`), whose
Barratt–Whitehead chase needs the positive-degree connecting map.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularSubsetHomology
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularMayerVietorisLES

namespace SKEFTHawking.SingularSubHomologyMV

variable {X : TopCat}

/-- The reassociation homeomorphism `sub R ≃ₜ sub T` for a subset `R : Set ↑(sub S)` whose
membership matches `Subtype.val ⁻¹' T` (`hmem`) and a target `T ⊆ S` (`hTS`): the nested subtype
`{p : ↥S // p ∈ R}` matches `{x // x ∈ T}` (underlying map is the identity on `X`). Same shape as
`SingularMayerVietorisLES.seamHomeo`, but lands directly in `sub T` (avoids a trailing `T ∩ S`). -/
def subSeamHomeo {S : Set ↑X} {R : Set ↑(sub S)} {T : Set ↑X} (hTS : T ⊆ S)
    (hmem : ∀ p : ↥(sub S), p ∈ R ↔ (p : ↑X) ∈ T) :
    ↥(sub R) ≃ₜ ↥(sub T) where
  toFun p := ⟨p.1.1, (hmem p.1).mp p.2⟩
  invFun q := ⟨⟨q.1, hTS q.2⟩, (hmem _).mpr q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The seam **homology isomorphism** `H(sub R) ≅ H(sub T)` induced by `subSeamHomeo` (a
homeomorphism, so functoriality gives the iso in every degree). -/
noncomputable def subSeamEquiv {S : Set ↑X} {R : Set ↑(sub S)} {T : Set ↑X} (hTS : T ⊆ S)
    (hmem : ∀ p : ↥(sub S), p ∈ R ↔ (p : ↑X) ∈ T) (n : ℕ) :
    Homology (sub R) n ≃ₗ[ZMod 2] Homology (sub T) n :=
  LinearEquiv.ofBijective
    (Homology.map ⟨subSeamHomeo hTS hmem, (subSeamHomeo hTS hmem).continuous⟩ n)
    (Homology.map_bijective_of_comp_id_all
      ⟨subSeamHomeo hTS hmem, (subSeamHomeo hTS hmem).continuous⟩
      ⟨(subSeamHomeo hTS hmem).symm, (subSeamHomeo hTS hmem).symm.continuous⟩
      (ContinuousMap.ext fun _ => rfl) (ContinuousMap.ext fun _ => rfl) n)

@[simp] theorem subSeamEquiv_apply {S : Set ↑X} {R : Set ↑(sub S)} {T : Set ↑X} (hTS : T ⊆ S)
    (hmem : ∀ p : ↥(sub S), p ∈ R ↔ (p : ↑X) ∈ T) (n : ℕ) (w : Homology (sub R) n) :
    subSeamEquiv hTS hmem n w
      = Homology.map ⟨subSeamHomeo hTS hmem, (subSeamHomeo hTS hmem).continuous⟩ n w := rfl

variable [T2Space ↑X]

omit [T2Space ↑X] in
/-- The open cover `{val⁻¹'U, val⁻¹'V}` of `sub (U ∪ V)`: every point lies in `U` or `V`, and both
preimages are open (so equal their interiors). -/
theorem cover_preimage (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) :
    (⋃ s ∈ ({Subtype.val ⁻¹' U, Subtype.val ⁻¹' V} : Set (Set ↑(sub (U ∪ V)))), interior s)
      = Set.univ := by
  rw [Set.biUnion_insert, Set.biUnion_singleton]
  rw [(hU.preimage continuous_subtype_val).interior_eq,
    (hV.preimage continuous_subtype_val).interior_eq]
  ext p
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true]
  exact p.2

/-- The seam equiv `H(sub (val⁻¹'U)) ≅ H(sub U)` (for the `U`-leg of the cover of `sub (U ∪ V)`). -/
noncomputable def seamU (U V : Set ↑X) (n : ℕ) :
    Homology (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) n ≃ₗ[ZMod 2] Homology (sub U) n :=
  subSeamEquiv (S := U ∪ V) (T := U) Set.subset_union_left (fun _ => Iff.rfl) n

/-- The seam equiv `H(sub (val⁻¹'V)) ≅ H(sub V)` (for the `V`-leg of the cover of `sub (U ∪ V)`). -/
noncomputable def seamV (U V : Set ↑X) (n : ℕ) :
    Homology (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) n ≃ₗ[ZMod 2] Homology (sub V) n :=
  subSeamEquiv (S := U ∪ V) (T := V) Set.subset_union_right (fun _ => Iff.rfl) n

/-- The seam equiv `H(sub (val⁻¹'U ∩ val⁻¹'V)) ≅ H(sub (U ∩ V))` (for the overlap of the cover). -/
noncomputable def seamI (U V : Set ↑X) (n : ℕ) :
    Homology (sub ((Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) ∩ Subtype.val ⁻¹' V)) n
      ≃ₗ[ZMod 2] Homology (sub (U ∩ V)) n :=
  subSeamEquiv (S := U ∪ V) (T := U ∩ V)
    (Set.inter_subset_left.trans Set.subset_union_left) (fun _ => Iff.rfl) n

/-- **The bottom-row MV connecting map** `δ : Hₙ₊₁(sub(U∪V)) → Hₙ(sub(U∩V))` of the PD `5`-lemma —
the Mayer–Vietoris connecting homomorphism of the space `sub(U ∪ V)` under its open cover
`{val⁻¹'U, val⁻¹'V}` (instantiating `SingularMayerVietorisLES.mvDelta` at ambient `sub(U∪V)`),
post-composed with the seam iso `seamI` so its codomain is `Hₙ(sub(U∩V))` (matching `subHomDiag`'s
domain). Closes the bottom-row LES
`⋯ →[δ] Hₙ(sub(U∩V)) →[subHomDiag] Hₙ(sub U)⊕Hₙ(sub V) →[subHomSum] Hₙ(sub(U∪V)) → ⋯`. -/
noncomputable def subHomConnecting (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    Homology (sub (U ∪ V)) (n + 1) →ₗ[ZMod 2] Homology (sub (U ∩ V)) n :=
  (seamI U V n).toLinearMap.comp
    (mvDelta (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
      (cover_preimage U V hU hV))

/-- Naturality: two `Homology.map`s of continuous maps that compose to equal maps agree. -/
theorem map_comp_eq_of_comp_eq {Y Z W : TopCat} (f : C(↑Y, ↑Z)) (g : C(↑Z, ↑W))
    (h : C(↑Y, ↑W)) (hgf : g.comp f = h) (n : ℕ) (w : Homology Y n) :
    Homology.map g n (Homology.map f n w) = Homology.map h n w := by
  rw [← LinearMap.comp_apply, ← Homology.map_comp, hgf]

omit [T2Space ↑X] in
/-- **The Δ seam-matching square** (applied form):
`subHomDiag ∘ seamI = (seamU × seamV) ∘ mvHomDiag`. Both routes from `Hₙ(sub(A∩B))` to
`Hₙ(sub U) ⊕ Hₙ(sub V)` are the pair of subspace-inclusion pushforwards (`val`-comps agree). -/
theorem diagSquare (U V : Set ↑X) (n : ℕ)
    (w : Homology (sub ((Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) ∩ Subtype.val ⁻¹' V)) n) :
    SingularOpenDualityMVSquare.subHomDiag U V n (seamI U V n w)
      = (seamU U V n).prodCongr (seamV U V n)
          (mvHomDiag (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n w) := by
  rw [SingularOpenDualityMVSquare.subHomDiag, LinearMap.prod_apply, Pi.prod, mvHomDiag_apply,
    LinearEquiv.prodCongr_apply]
  refine Prod.ext ?_ ?_
  · show Homology.map (subInclCM Set.inter_subset_left) n
          (Homology.map ⟨subSeamHomeo
            (Set.inter_subset_left.trans Set.subset_union_left) (fun _ => Iff.rfl), _⟩ n w)
        = Homology.map ⟨subSeamHomeo Set.subset_union_left (fun _ => Iff.rfl), _⟩ n
            (Homology.map (subIncl Set.inter_subset_left) n w)
    rw [map_comp_eq_of_comp_eq _ _ _ (rfl : _ = _) n,
      map_comp_eq_of_comp_eq _ _ _ (rfl : _ = _) n]
    congr 1
  · show Homology.map (subInclCM Set.inter_subset_right) n
          (Homology.map ⟨subSeamHomeo
            (Set.inter_subset_left.trans Set.subset_union_left) (fun _ => Iff.rfl), _⟩ n w)
        = Homology.map ⟨subSeamHomeo Set.subset_union_right (fun _ => Iff.rfl), _⟩ n
            (Homology.map (subIncl Set.inter_subset_right) n w)
    rw [map_comp_eq_of_comp_eq _ _ _ (rfl : _ = _) n,
      map_comp_eq_of_comp_eq _ _ _ (rfl : _ = _) n]
    congr 1

omit [T2Space ↑X] in
/-- **The Σ seam-matching square** (applied form): `subHomSum ∘ (seamU × seamV) = mvHomSum` (the
target ambient `Hₙ(sub(U∪V))` is shared, no seam there). Both routes from `Hₙ(sub U) ⊕ Hₙ(sub V)`
are the difference (= sum over `ℤ/2`) of the two ambient-inclusion pushforwards. -/
theorem sumSquare (U V : Set ↑X) (n : ℕ)
    (p : Homology (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) n
      × Homology (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) n) :
    SingularOpenDualityMVSquare.subHomSum U V n ((seamU U V n p.1, seamV U V n p.2))
      = mvHomSum (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n p := by
  have hU' : homOfSubset (Set.subset_union_left (s := U) (t := V)) n (seamU U V n p.1)
      = Homology.map (ambIncl (X := sub (U ∪ V)) (Subtype.val ⁻¹' U)) n p.1 := by
    show Homology.map (subInclCM Set.subset_union_left) n
          (Homology.map ⟨subSeamHomeo Set.subset_union_left (fun _ => Iff.rfl), _⟩ n p.1)
        = Homology.map (ambIncl (X := sub (U ∪ V)) (Subtype.val ⁻¹' U)) n p.1
    rw [map_comp_eq_of_comp_eq _ _ _ (rfl : _ = _) n]
    rfl
  have hV' : homOfSubset (Set.subset_union_right (s := U) (t := V)) n (seamV U V n p.2)
      = Homology.map (ambIncl (X := sub (U ∪ V)) (Subtype.val ⁻¹' V)) n p.2 := by
    show Homology.map (subInclCM Set.subset_union_right) n
          (Homology.map ⟨subSeamHomeo Set.subset_union_right (fun _ => Iff.rfl), _⟩ n p.2)
        = Homology.map (ambIncl (X := sub (U ∪ V)) (Subtype.val ⁻¹' V)) n p.2
    rw [map_comp_eq_of_comp_eq _ _ _ (rfl : _ = _) n]
    rfl
  rw [SingularOpenDualityMVSquare.subHomSum, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, mvHomSum,
    LinearMap.coprod_apply, hU', hV', sub_eq_add_neg,
    neg_eq_of_add_eq_zero_left (ZModModule.add_self _)]

/-! ## The bottom-row Mayer–Vietoris exactness (three terms) -/

omit [T2Space ↑X] in
/-- **MV exactness at `Hₙ₊₁(sub(U∪V))`**: `Function.Exact subHomSum subHomConnecting`. Transported
from `SingularMayerVietorisLES.mv_exact_ambient` (the LES of `sub(U∪V)` under `{val⁻¹'U, val⁻¹'V}`)
through the seam isos via `sumSquare` and the definition of `subHomConnecting`. -/
theorem subHom_exact_sum (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) {n : ℕ} :
    Function.Exact (SingularOpenDualityMVSquare.subHomSum U V (n + 1))
      (subHomConnecting U V hU hV n) := by
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := (seamU U V (n + 1)).prodCongr (seamV U V (n + 1)))
    (e₂ := LinearEquiv.refl (ZMod 2) (Homology (sub (U ∪ V)) (n + 1)))
    (e₃ := seamI U V n) ?_ ?_
    (mv_exact_ambient (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
      (cover_preimage U V hU hV))
  · refine LinearMap.ext fun p => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.refl_apply, LinearEquiv.prodCongr_apply]
    exact sumSquare U V (n + 1) p
  · rfl

omit [T2Space ↑X] in
/-- **MV exactness at `Hₙ(sub(U∩V))`**: `Function.Exact subHomConnecting subHomDiag`. Transported
from `SingularMayerVietorisLES.mv_exact_inter` through the seam isos via `diagSquare` and the
definition of `subHomConnecting`. -/
theorem subHom_exact_connecting (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) {n : ℕ} :
    Function.Exact (subHomConnecting U V hU hV n)
      (SingularOpenDualityMVSquare.subHomDiag U V n) := by
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := LinearEquiv.refl (ZMod 2) (Homology (sub (U ∪ V)) (n + 1)))
    (e₂ := seamI U V n)
    (e₃ := (seamU U V n).prodCongr (seamV U V n)) ?_ ?_
    (mv_exact_inter (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
      (cover_preimage U V hU hV))
  · rfl
  · refine LinearMap.ext fun w => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.prodCongr_apply]
    exact diagSquare U V n w

omit [T2Space ↑X] in
/-- **MV middle exactness at `Hₙ₊₁(sub U) ⊕ Hₙ₊₁(sub V)`**: `Function.Exact subHomDiag subHomSum`.
Transported from `SingularMayerVietorisLES.mv_exact_middle` through the seam isos via `diagSquare`
and `sumSquare`. Indexed at `n + 1` to match `mv_exact_middle` (and its
compactly-supported-cohomology twin `SingularCSCMayerVietorisMiddle.cscMv_exact_middle`), whose
Barratt–Whitehead chase needs the positive-degree connecting map. -/
theorem subHom_exact_middle (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) {n : ℕ} :
    Function.Exact (SingularOpenDualityMVSquare.subHomDiag U V (n + 1))
      (SingularOpenDualityMVSquare.subHomSum U V (n + 1)) := by
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := seamI U V (n + 1))
    (e₂ := (seamU U V (n + 1)).prodCongr (seamV U V (n + 1)))
    (e₃ := LinearEquiv.refl (ZMod 2) (Homology (sub (U ∪ V)) (n + 1))) ?_ ?_
    (mv_exact_middle (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
      (cover_preimage U V hU hV))
  · refine LinearMap.ext fun w => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.prodCongr_apply]
    exact diagSquare U V (n + 1) w
  · refine LinearMap.ext fun p => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.refl_apply, LinearEquiv.prodCongr_apply]
    exact sumSquare U V (n + 1) p

end SKEFTHawking.SingularSubHomologyMV
