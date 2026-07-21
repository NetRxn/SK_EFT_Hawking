/-
# Phase 5q.H — the BASIS-ID slice: `{α, β}` is a unimodular change of basis of `H²(S²×S²;ℤ)`

The third open piece flagged by `SphereProdCrossInt`'s recon gate (the one independent of the
cross-product value): showing the cross family `![alphaOf xS, betaOf xS]` really is a basis of
`H²(S²×S²;ℤ)`, i.e. is related to the COMPUTED basis `sphereProdBasis2Computed` by a unimodular
matrix — the `hcong` hypothesis of `SphereProdCrossValueFeed.sphereProd_s2s2_hyp_of_congr_pm`.

The recon gate flagged this as blocked because `deltaGen` is an `Exists.choose` section, "pinned
only up to adding any multiple of `sumInto`, so its factor-projections are NOT forced by
`deltaGen_spec`". **That obstruction does not apply to the projection that is actually needed.**
The `sumInto`-ambiguity DIES under the second-factor projection (`sumInto_prodSnd : snd_* ∘ sumInto
= 0`), so `snd_* deltaGen` is canonical regardless of the split choice — and it is pinned NOT by
`deltaGen_spec` but by a counting argument:

* `snd_*` on `H₂` is SURJECTIVE (the slice `y ↦ (basePoint, y)` is a section of `sndCM`);
* `{sumInto 1, deltaGen}` SPAN `H₂(S²×S²;ℤ)` (`sphereProdHTwoEquivInt_symm_apply`), and `sumInto`
  dies under `snd_*`, so `im (snd_*) = ℤ · snd_*(deltaGen)`;
* hence `ℤ · snd_*(deltaGen) = H₂(S²;ℤ) ≅ ℤ`, i.e. `snd_*(deltaGen)` is a GENERATOR
  (`deltaSnd_isUnit`).

That is the only nontrivial coordinate: the change-of-basis matrix is lower-triangular,
`P = !![1, 0; a, b]` with `b = ⟨xS, snd_* deltaGen⟩` a unit, because `α = fst* xS` reads `1` on
generator 1 (`sumInto_prodFst`) and `β = snd* xS` reads `0` on it (`sumInto_prodSnd`).

Deliverables: `deltaSnd_isUnit`, the general Gram change-of-basis congruence
`intCongr_gram_of_basis_change`, the basis-ID `crossFamily_basis_intCongr`, and — combining with
`SphereProdHemiUnitInt.hcross_pm` — the **fully unconditional** `sphereProd_s2s2_hyp`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SphereProdHemiUnitInt

namespace SKEFTHawking.SphereProdBasisIdInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularCohomologyFunctorialityInt (kroneckerHInt_cohomologyPullbackInt)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularSphereBottom (basePoint)
open SKEFTHawking.SingularProdContractibleInt (prodFst)
open SKEFTHawking.SingularLineMinusPointInt (topSphereIsoInt)
open SKEFTHawking.SphereProdHTwoInt (SphSph sndCM deltaGen sumInto sphereProdHTwoEquivInt
  sphereProdHTwoEquivInt_symm_apply sumInto_prodFst sumInto_prodSnd)
open SKEFTHawking.SphereWitnessTowerInt (SphereProdT sphereProdCohomTwoEquivInt
  sphereProdBasis2Computed sphereProdIntH2Basis sphereProdCohomTwoEquivInt_fst
  sphereProdCohomTwoEquivInt_snd)
open SKEFTHawking.SphereProdHFourInt (sphereProdIntFundClassHonest)
open SKEFTHawking.SphereProdCrossInt (alphaOf betaOf crossFamily)
open SKEFTHawking.SphereProdCrossWitnessInt (xS kroneckerHInt_xS)

/-! ## §1. The second-factor projection is split -/

/-- The polar slice `S² → S²×S²`, `y ↦ (basePoint, y)` — a section of the second-factor
projection. -/
noncomputable def sndSection : C(↑(Sph 2), ↑SphSph) :=
  ⟨fun y => (basePoint 2, y), by fun_prop⟩

theorem sndCM_comp_sndSection : sndCM.comp sndSection = ContinuousMap.id ↑(Sph 2) := rfl

/-- **`snd_*` is surjective on integral homology in every degree** (it is split by the polar
slice). -/
theorem mapInt_sndCM_surjective (n : ℕ) : Function.Surjective (Homology.mapInt sndCM n) :=
  fun y => ⟨Homology.mapInt sndSection n y, by
    rw [← LinearMap.comp_apply, ← Homology.mapInt_comp, sndCM_comp_sndSection,
      Homology.mapInt_id, LinearMap.id_apply]⟩

/-! ## §2. `snd_* deltaGen` is a generator of `H₂(S²;ℤ)` -/

/-- **The canonical second-projection of the split generator.** `deltaGen` is only pinned modulo
`sumInto`, but `sumInto` dies under `snd_*` (`sumInto_prodSnd`), so THIS class is independent of
the split choice. -/
noncomputable def deltaSnd : Homology (Sph 2) 2 :=
  Homology.mapInt sndCM 2 (deltaGen (basePoint 2))

/-- **`snd_* deltaGen` GENERATES `H₂(S²;ℤ)`** — the counting argument that replaces the
normalization the recon gate expected from `deltaGen_spec`: `snd_*` is onto and `sumInto` is in its
kernel, so the whole of `H₂(S²;ℤ)` is the `ℤ`-span of `deltaSnd`. -/
theorem deltaSnd_isUnit : IsUnit (topSphereIsoInt 1 deltaSnd) := by
  obtain ⟨x, hx⟩ := mapInt_sndCM_surjective 2 ((topSphereIsoInt 1).symm 1)
  have hxd : x = sumInto (basePoint 2) (sphereProdHTwoEquivInt x).1
      + (sphereProdHTwoEquivInt x).2 • deltaGen (basePoint 2) := by
    conv_lhs => rw [← sphereProdHTwoEquivInt.symm_apply_apply x]
    exact sphereProdHTwoEquivInt_symm_apply _ _
  rw [hxd, map_add, sumInto_prodSnd, zero_add, map_smul] at hx
  have h1 : (sphereProdHTwoEquivInt x).2 * topSphereIsoInt 1 deltaSnd = 1 := by
    have h2 := congrArg (topSphereIsoInt 1) hx
    rwa [map_smul, smul_eq_mul, LinearEquiv.apply_symm_apply] at h2
  exact IsUnit.of_mul_eq_one (b := (sphereProdHTwoEquivInt x).2) (by rw [← h1]; ring)

/-! ## §3. The two computed generators, named -/

/-- Generator 1 of `H₂(S²×S²;ℤ)`: the `[S²×pt]` factor class. -/
theorem genOne_eq : sphereProdHTwoEquivInt.symm ((1 : ℤ), (0 : ℤ)) = sumInto (basePoint 2) 1 := by
  rw [sphereProdHTwoEquivInt_symm_apply, zero_smul, add_zero]

/-- Generator 2 of `H₂(S²×S²;ℤ)`: the split section `deltaGen`. -/
theorem genTwo_eq : sphereProdHTwoEquivInt.symm ((0 : ℤ), (1 : ℤ)) = deltaGen (basePoint 2) := by
  rw [sphereProdHTwoEquivInt_symm_apply, one_smul, map_zero, zero_add]

/-! ## §4. The coordinates of `α` and `β` in the computed basis -/

/-- `α = fst* xS` reads `1` on generator 1 (`sumInto_prodFst` + the defining pairing of `xS`). -/
theorem alphaOf_xS_fst : (sphereProdCohomTwoEquivInt (alphaOf xS)).1 = 1 := by
  rw [sphereProdCohomTwoEquivInt_fst, alphaOf, kroneckerHInt_cohomologyPullbackInt, genOne_eq,
    sumInto_prodFst, kroneckerHInt_xS, LinearEquiv.apply_symm_apply]

/-- `β = snd* xS` reads `0` on generator 1 (the leg's second factor is contractible). -/
theorem betaOf_xS_fst : (sphereProdCohomTwoEquivInt (betaOf xS)).1 = 0 := by
  rw [sphereProdCohomTwoEquivInt_fst, betaOf, kroneckerHInt_cohomologyPullbackInt, genOne_eq,
    sumInto_prodSnd, map_zero]

/-- `β` reads the `deltaSnd` coordinate on generator 2 — a UNIT by `deltaSnd_isUnit`. -/
theorem betaOf_xS_snd :
    (sphereProdCohomTwoEquivInt (betaOf xS)).2 = topSphereIsoInt 1 deltaSnd := by
  rw [sphereProdCohomTwoEquivInt_snd, betaOf, kroneckerHInt_cohomologyPullbackInt, genTwo_eq,
    kroneckerHInt_xS]
  rfl

/-- The computed basis in coordinates: `bₖ` is the `k`-th standard vector. -/
theorem cohomTwoEquiv_basis2 (k : Fin 2) :
    sphereProdCohomTwoEquivInt (sphereProdBasis2Computed k)
      = if k = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ)) := by
  rw [sphereProdBasis2Computed, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    Module.Basis.map_apply]
  fin_cases k <;> simp [Pi.basisFun_apply]

/-- Every degree-2 class expands in the computed basis by its `sphereProdCohomTwoEquivInt`
coordinates. -/
theorem basis2_expand (ω : Cohomology SphereProdT 2) :
    ω = (sphereProdCohomTwoEquivInt ω).1 • sphereProdBasis2Computed 0
      + (sphereProdCohomTwoEquivInt ω).2 • sphereProdBasis2Computed 1 := by
  apply sphereProdCohomTwoEquivInt.injective
  rw [map_add, map_smul, map_smul, cohomTwoEquiv_basis2 0, cohomTwoEquiv_basis2 1]
  refine Prod.ext ?_ ?_ <;> simp

/-! ## §5. The Gram matrix under a unimodular change of basis -/

/-- **A unimodular change of family carries a Gram matrix to a congruent one.** Pure bilinear
algebra: if `Cⱼ = Σᵢ Pᵢⱼ Bᵢ` with `P` unimodular then `Gram C = Pᵀ (Gram B) P`. -/
theorem gram_congr_of_basis_change {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (f : M →ₗ[R] M →ₗ[R] R) (B C : Fin n → M) (P : Matrix (Fin n) (Fin n) R)
    (hC : ∀ j, C j = ∑ i, P i j • B i) :
    P.transpose * (Matrix.of fun i j => f (B i) (B j)) * P
      = Matrix.of fun i j => f (C i) (C j) := by
  ext j k
  have hR : (Matrix.of fun i j => f (C i) (C j)) j k
      = ∑ a, ∑ b, P a j * P b k * f (B a) (B b) := by
    show f (C j) (C k) = _
    rw [hC j, hC k, show f (∑ a, P a j • B a) = ∑ a, f (P a j • B a) from map_sum f _ _,
      LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show f (P a j • B a) = P a j • f (B a) from f.map_smul _ _,
      LinearMap.smul_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show (f (B a)) (P b k • B b) = P b k • (f (B a)) (B b) from (f (B a)).map_smul _ _,
      smul_eq_mul, smul_eq_mul]
    ring
  have hL : (P.transpose * (Matrix.of fun i j => f (B i) (B j)) * P) j k
      = ∑ b, ∑ a, P a j * P b k * f (B a) (B b) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    ring
  rw [hL, hR, Finset.sum_comm]

/-! ## §6. The basis-ID and the unconditional `s2s2_hyp` -/

/-- The lower-triangular change-of-basis matrix from the computed basis to `![α, β]`. -/
noncomputable def crossP : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; (sphereProdCohomTwoEquivInt (alphaOf xS)).2, topSphereIsoInt 1 deltaSnd]

/-- The change of basis is UNIMODULAR: lower-triangular with `1` and the `deltaSnd` unit on the
diagonal. -/
theorem crossP_isUnit_det : IsUnit crossP.det := by
  rw [crossP, Matrix.det_fin_two_of]
  simpa using deltaSnd_isUnit

/-- **THE BASIS-ID**: the cross family `![α, β]` at the witness generator `xS` is a unimodular
change of basis of the computed `H²(S²×S²;ℤ)` basis, so the two Gram matrices are integrally
congruent. This is exactly the `hcong` hypothesis of the fed reducer. -/
theorem crossFamily_basis_intCongr :
    IntCongr (interMatrix sphereProdIntFundClassHonest sphereProdIntH2Basis)
      (Matrix.of fun i j => interFormInt sphereProdIntFundClassHonest
        (crossFamily xS i) (crossFamily xS j)) := by
  refine ⟨crossP, crossP_isUnit_det,
    gram_congr_of_basis_change (interFormInt sphereProdIntFundClassHonest)
      sphereProdBasis2Computed (crossFamily xS) crossP (fun j => ?_)⟩
  fin_cases j
  · show alphaOf xS = ∑ i, crossP i 0 • sphereProdBasis2Computed i
    rw [Fin.sum_univ_two]
    conv_lhs => rw [basis2_expand (alphaOf xS)]
    rw [alphaOf_xS_fst]
    rfl
  · show betaOf xS = ∑ i, crossP i 1 • sphereProdBasis2Computed i
    rw [Fin.sum_univ_two]
    conv_lhs => rw [basis2_expand (betaOf xS)]
    rw [betaOf_xS_fst, betaOf_xS_snd]
    rfl

/-- **THE SHARP UNCONDITIONAL FORM**: the `S²×S²` intersection matrix on the computed `H²` basis is
integrally congruent to the HYPERBOLIC PLANE ITSELF — `II(S²×S²) ≅ H`, not merely "to some
hyperbolic form". Both inputs are now discharged: the cross value by the MV cup–Stokes peel
(`SphereProdHemiUnitInt.hcross_pm`) and the change of basis by `crossFamily_basis_intCongr`. -/
theorem sphereProd_interMatrix_intCongr_hyp :
    IntCongr (interMatrix sphereProdIntFundClassHonest sphereProdIntH2Basis) Hyp :=
  crossFamily_basis_intCongr.trans
    (SphereProdCrossValueFeed.crossFamily_gram_intCongr_of_isUnit xS
      SphereProdHemiUnitInt.hcross_pm)

/-- **THE UNCONDITIONAL `s2s2_hyp`**: the `S²×S²` intersection form IS hyperbolic — no hypotheses.
The cross value is discharged by the MV cup–Stokes peel (`SphereProdHemiUnitInt.hcross_pm`) and
the basis-ID by `crossFamily_basis_intCongr`. -/
theorem sphereProd_s2s2_hyp :
    ∃ N, IsHyperbolicForm N ∧
      IntCongr (interMatrix sphereProdIntFundClassHonest sphereProdIntH2Basis) N :=
  SphereProdHemiUnitInt.sphereProd_s2s2_hyp_of_congr crossFamily_basis_intCongr

end SKEFTHawking.SphereProdBasisIdInt
