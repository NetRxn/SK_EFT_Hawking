/-
# Phase 5q.H (E1 integral topology) — the bottom-row homology MV LES of the integral PD 5-lemma

Integral (`ZMod 2 → ℤ`) mirror of `SingularSubHomologyMV`. The **bottom row** of the integral PD `5`-lemma
ladder is the Mayer–Vietoris long exact sequence of the *space* `sub (U ∪ V)` under its open cover
`{val⁻¹'U, val⁻¹'V}`. The diagonal/sum `subHomDiagInt`/`subHomSumInt` (subspace-inclusion maps
`homOfSubsetInt`) were built in `SingularOpenDualityMVSquareInt`; this file supplies the matching
**connecting map** `subHomConnectingInt` and proves the three exactness statements
`subHom_exact_sumInt`/`subHom_exact_connectingInt`/`subHom_exact_middleInt`.

## Construction (no new homology theory)
Instantiate the completed integral absolute homology MV LES (`SingularMayerVietorisLESInt`) at the ambient
space `sub (U ∪ V)` with the two opens `A = Subtype.val⁻¹'U`, `B = Subtype.val⁻¹'V` in `↥(U∪V)`. The
reassociation **seam** isos `seamU`/`seamV`/`seamI` (`H(sub A;ℤ) ≅ H(sub U;ℤ)`, etc.; underlying map the
identity on `X`) transport `mvHomDiagInt`/`mvHomSumInt`/`mvDeltaInt` onto `subHomDiagInt`/`subHomSumInt`/
`subHomConnectingInt` via the cap-naturality squares `diagSquareInt`/`sumSquareInt`; the three `mv_exact_*Int`
statements transfer through the seam `LinearEquiv`s with `Function.Exact.of_ladder_linearEquiv_of_exact`.

The (coefficient-agnostic) seam homeomorphism `subSeamHomeo` and the cover lemma `cover_preimage` are reused
from the mod-2 module; only the *homology* transport is redone over ℤ. The mod-2 `sumSquare`'s char-2 trick
(`ZModModule.add_self`) is unnecessary here — `subHomSumInt`/`mvHomSumInt` are both honest ℤ-differences.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularMayerVietorisLESInt
import SKEFTHawking.SingularOpenDualityMVSquareInt
import SKEFTHawking.SingularSubHomologyMV

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularSubsetHomologyInt
open SKEFTHawking.SingularSphereHomologyInt (Homology.mapInt_bijective_of_comp_id_all)
open SKEFTHawking.SingularMayerVietorisLESInt
open SKEFTHawking.SingularOpenDualityMVSquareInt
open SKEFTHawking.SingularMayerVietorisLES (ambIncl subIncl)
open SKEFTHawking.SingularSubHomologyMV (subSeamHomeo cover_preimage)

namespace SKEFTHawking.SingularSubHomologyMVInt

variable {X : TopCat}

/-- The integral seam **homology isomorphism** `Hₙ(sub R;ℤ) ≅ Hₙ(sub T;ℤ)` induced by the
coefficient-agnostic `subSeamHomeo` (a homeomorphism, so integral functoriality +
`mapInt_bijective_of_comp_id_all` give the iso in every degree). -/
noncomputable def subSeamEquivInt {S : Set ↑X} {R : Set ↑(sub S)} {T : Set ↑X} (hTS : T ⊆ S)
    (hmem : ∀ p : ↥(sub S), p ∈ R ↔ (p : ↑X) ∈ T) (n : ℕ) :
    Homology (sub R) n ≃ₗ[ℤ] Homology (sub T) n :=
  LinearEquiv.ofBijective
    (Homology.mapInt ⟨subSeamHomeo hTS hmem, (subSeamHomeo hTS hmem).continuous⟩ n)
    (Homology.mapInt_bijective_of_comp_id_all ⟨subSeamHomeo hTS hmem, (subSeamHomeo hTS hmem).continuous⟩
      ⟨(subSeamHomeo hTS hmem).symm, (subSeamHomeo hTS hmem).symm.continuous⟩
      (ContinuousMap.ext fun _ => rfl) (ContinuousMap.ext fun _ => rfl) n)

@[simp] theorem subSeamEquivInt_apply {S : Set ↑X} {R : Set ↑(sub S)} {T : Set ↑X} (hTS : T ⊆ S)
    (hmem : ∀ p : ↥(sub S), p ∈ R ↔ (p : ↑X) ∈ T) (n : ℕ) (w : Homology (sub R) n) :
    subSeamEquivInt hTS hmem n w
      = Homology.mapInt ⟨subSeamHomeo hTS hmem, (subSeamHomeo hTS hmem).continuous⟩ n w := rfl

variable [T2Space ↑X]

/-- The seam equiv `Hₙ(sub (val⁻¹'U);ℤ) ≅ Hₙ(sub U;ℤ)` (the `U`-leg of the cover of `sub (U ∪ V)`). -/
noncomputable def seamU (U V : Set ↑X) (n : ℕ) :
    Homology (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) n ≃ₗ[ℤ] Homology (sub U) n :=
  subSeamEquivInt (S := U ∪ V) (T := U) Set.subset_union_left (fun _ => Iff.rfl) n

/-- The seam equiv `Hₙ(sub (val⁻¹'V);ℤ) ≅ Hₙ(sub V;ℤ)` (the `V`-leg of the cover of `sub (U ∪ V)`). -/
noncomputable def seamV (U V : Set ↑X) (n : ℕ) :
    Homology (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) n ≃ₗ[ℤ] Homology (sub V) n :=
  subSeamEquivInt (S := U ∪ V) (T := V) Set.subset_union_right (fun _ => Iff.rfl) n

/-- The seam equiv `Hₙ(sub (val⁻¹'U ∩ val⁻¹'V);ℤ) ≅ Hₙ(sub (U ∩ V);ℤ)` (the cover overlap). -/
noncomputable def seamI (U V : Set ↑X) (n : ℕ) :
    Homology (sub ((Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) ∩ Subtype.val ⁻¹' V)) n
      ≃ₗ[ℤ] Homology (sub (U ∩ V)) n :=
  subSeamEquivInt (S := U ∪ V) (T := U ∩ V)
    (Set.inter_subset_left.trans Set.subset_union_left) (fun _ => Iff.rfl) n

/-- **The bottom-row integral MV connecting map** `δ : Hₙ₊₁(sub(U∪V);ℤ) → Hₙ(sub(U∩V);ℤ)` — the integral MV
connecting homomorphism of `sub(U ∪ V)` under `{val⁻¹'U, val⁻¹'V}` (`mvDeltaInt` at ambient `sub(U∪V)`),
post-composed with the seam iso `seamI` so its codomain matches `subHomDiagInt`'s domain. -/
noncomputable def subHomConnectingInt (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    Homology (sub (U ∪ V)) (n + 1) →ₗ[ℤ] Homology (sub (U ∩ V)) n :=
  (seamI U V n).toLinearMap.comp
    (mvDeltaInt (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
      (cover_preimage U V hU hV))

/-- Naturality: two `Homology.mapInt`s of continuous maps that compose to equal maps agree. -/
theorem map_comp_eq_of_comp_eqInt {Y Z W : TopCat} (f : C(↑Y, ↑Z)) (g : C(↑Z, ↑W))
    (h : C(↑Y, ↑W)) (hgf : g.comp f = h) (n : ℕ) (w : Homology Y n) :
    Homology.mapInt g n (Homology.mapInt f n w) = Homology.mapInt h n w := by
  rw [← LinearMap.comp_apply, ← Homology.mapInt_comp, hgf]

omit [T2Space ↑X] in
/-- **The Δ seam-matching square** (integral, applied form): `subHomDiagInt ∘ seamI =
(seamU × seamV) ∘ mvHomDiagInt`. -/
theorem diagSquareInt (U V : Set ↑X) (n : ℕ)
    (w : Homology (sub ((Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) ∩ Subtype.val ⁻¹' V)) n) :
    subHomDiagInt U V n (seamI U V n w)
      = (seamU U V n).prodCongr (seamV U V n)
          (mvHomDiagInt (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n w) := by
  rw [subHomDiagInt, LinearMap.prod_apply]
  simp only [Function.prod_def]
  rw [ mvHomDiagInt_apply, LinearEquiv.prodCongr_apply]
  refine Prod.ext ?_ ?_
  · show Homology.mapInt (subInclCM Set.inter_subset_left) n
          (Homology.mapInt ⟨subSeamHomeo
            (Set.inter_subset_left.trans Set.subset_union_left) (fun _ => Iff.rfl), _⟩ n w)
        = Homology.mapInt ⟨subSeamHomeo Set.subset_union_left (fun _ => Iff.rfl), _⟩ n
            (Homology.mapInt (subIncl Set.inter_subset_left) n w)
    rw [map_comp_eq_of_comp_eqInt _ _ _ (rfl : _ = _) n,
      map_comp_eq_of_comp_eqInt _ _ _ (rfl : _ = _) n]
    congr 1
  · show Homology.mapInt (subInclCM Set.inter_subset_right) n
          (Homology.mapInt ⟨subSeamHomeo
            (Set.inter_subset_left.trans Set.subset_union_left) (fun _ => Iff.rfl), _⟩ n w)
        = Homology.mapInt ⟨subSeamHomeo Set.subset_union_right (fun _ => Iff.rfl), _⟩ n
            (Homology.mapInt (subIncl Set.inter_subset_right) n w)
    rw [map_comp_eq_of_comp_eqInt _ _ _ (rfl : _ = _) n,
      map_comp_eq_of_comp_eqInt _ _ _ (rfl : _ = _) n]
    congr 1

omit [T2Space ↑X] in
/-- **The Σ seam-matching square** (integral, applied form): `subHomSumInt ∘ (seamU × seamV) = mvHomSumInt`.
Both are the honest ℤ-difference of the two ambient-inclusion pushforwards, so it matches directly (no
char-2 trick). -/
theorem sumSquareInt (U V : Set ↑X) (n : ℕ)
    (p : Homology (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) n
      × Homology (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) n) :
    subHomSumInt U V n ((seamU U V n p.1, seamV U V n p.2))
      = mvHomSumInt (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n p := by
  have hU' : homOfSubsetInt (Set.subset_union_left (s := U) (t := V)) n (seamU U V n p.1)
      = Homology.mapInt (ambIncl (X := sub (U ∪ V)) (Subtype.val ⁻¹' U)) n p.1 := by
    show Homology.mapInt (subInclCM Set.subset_union_left) n
          (Homology.mapInt ⟨subSeamHomeo Set.subset_union_left (fun _ => Iff.rfl), _⟩ n p.1)
        = Homology.mapInt (ambIncl (X := sub (U ∪ V)) (Subtype.val ⁻¹' U)) n p.1
    rw [map_comp_eq_of_comp_eqInt _ _ _ (rfl : _ = _) n]
    rfl
  have hV' : homOfSubsetInt (Set.subset_union_right (s := U) (t := V)) n (seamV U V n p.2)
      = Homology.mapInt (ambIncl (X := sub (U ∪ V)) (Subtype.val ⁻¹' V)) n p.2 := by
    show Homology.mapInt (subInclCM Set.subset_union_right) n
          (Homology.mapInt ⟨subSeamHomeo Set.subset_union_right (fun _ => Iff.rfl), _⟩ n p.2)
        = Homology.mapInt (ambIncl (X := sub (U ∪ V)) (Subtype.val ⁻¹' V)) n p.2
    rw [map_comp_eq_of_comp_eqInt _ _ _ (rfl : _ = _) n]
    rfl
  rw [subHomSumInt, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, hU', hV', mvHomSumInt_apply]

/-! ## The bottom-row integral Mayer–Vietoris exactness (three terms) -/

omit [T2Space ↑X] in
/-- **Integral MV exactness at `Hₙ₊₁(sub(U∪V))`**: `Function.Exact subHomSumInt subHomConnectingInt`. -/
theorem subHom_exact_sumInt (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) {n : ℕ} :
    Function.Exact (subHomSumInt U V (n + 1)) (subHomConnectingInt U V hU hV n) := by
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := (seamU U V (n + 1)).prodCongr (seamV U V (n + 1)))
    (e₂ := LinearEquiv.refl ℤ (Homology (sub (U ∪ V)) (n + 1)))
    (e₃ := seamI U V n) ?_ ?_
    (mv_exact_ambientInt (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
      (cover_preimage U V hU hV))
  · refine LinearMap.ext fun p => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.refl_apply, LinearEquiv.prodCongr_apply]
    exact sumSquareInt U V (n + 1) p
  · rfl

omit [T2Space ↑X] in
/-- **Integral MV exactness at `Hₙ(sub(U∩V))`**: `Function.Exact subHomConnectingInt subHomDiagInt`. -/
theorem subHom_exact_connectingInt (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) {n : ℕ} :
    Function.Exact (subHomConnectingInt U V hU hV n) (subHomDiagInt U V n) := by
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := LinearEquiv.refl ℤ (Homology (sub (U ∪ V)) (n + 1)))
    (e₂ := seamI U V n)
    (e₃ := (seamU U V n).prodCongr (seamV U V n)) ?_ ?_
    (mv_exact_interInt (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
      (cover_preimage U V hU hV))
  · rfl
  · refine LinearMap.ext fun w => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.prodCongr_apply]
    exact diagSquareInt U V n w

omit [T2Space ↑X] in
/-- **Integral MV middle exactness at `Hₙ₊₁(sub U) ⊕ Hₙ₊₁(sub V)`**: `Function.Exact subHomDiagInt
subHomSumInt`. Indexed at `n + 1` to match `mv_exact_middleInt` (whose Barratt–Whitehead chase needs the
positive-degree connecting map). -/
theorem subHom_exact_middleInt (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) {n : ℕ} :
    Function.Exact (subHomDiagInt U V (n + 1)) (subHomSumInt U V (n + 1)) := by
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := seamI U V (n + 1))
    (e₂ := (seamU U V (n + 1)).prodCongr (seamV U V (n + 1)))
    (e₃ := LinearEquiv.refl ℤ (Homology (sub (U ∪ V)) (n + 1))) ?_ ?_
    (mv_exact_middleInt (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
      (cover_preimage U V hU hV))
  · refine LinearMap.ext fun w => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.prodCongr_apply]
    exact diagSquareInt U V (n + 1) w
  · refine LinearMap.ext fun p => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.refl_apply, LinearEquiv.prodCongr_apply]
    exact sumSquareInt U V (n + 1) p

end SKEFTHawking.SingularSubHomologyMVInt
