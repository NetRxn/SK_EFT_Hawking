/-
# Phase 5q.H — K7 finale: the pair residual is EXACTLY "the exceptional class is 2-divisible"

`KummerPairTubeSeparation` relocated the whole `Torsion(H₂(K3;ℤ)) = ⊥` residual onto the local
model as `PairH2TwoTorsionFree` — `H₂(eImage, collar;ℤ)` has no 2-torsion — and proved it
*equivalent* to `H₂(ResE, ∂ResE;ℤ) ≅ ℤ` (16 copies). Both forms are statements about **all** of a
group. This module replaces them by a **finite existence statement about 16 relative classes**:

> **`Halvable v`** — `∃ q : H₂(eImage, collar;ℤ), 2 • q = pairProj v`.
>
> `pairH2TwoTorsionFree_iff_halvable` : the residual `↔ ∀ v, Halvable v`.
> `pairH2TwoTorsionFree_iff_exceptional_halvable` : `↔ ∀ i : EIndex, Halvable (exceptional i)`.

`exceptional i = eImageH2EquivInt.symm (Pi.single i 1)` is the zero-section class of the `i`-th
resolution piece. So the ENTIRE remaining geometric content of the unconditional ℤ²² headline is:

> **the exceptional sphere class `[Sᵢ] ∈ H₂(E)` is divisible by two in `H₂(E, ∂E;ℤ)`** —

which is precisely the Euler number `−2` of the `𝒪(−2)` piece in its cleanest homological form
(the fiber disk `q` has `2q = ±[S²]` rel boundary). A future geometric worker no longer has to
*compute a group*; it has to *construct one relative class per copy* and identify its double.

## The mechanism — a counting bijection, not a weakening

Write `Q := H₂(eImage,collar;ℤ) ⧸ im pairProj`, which the landed SES pins to `(ℤ/2)¹⁶`
(`pairCokerEquiv`, `pairCoker_card`). The banked halving map `pairHalve` (`m ↦ pairProj⁻¹(2m)` in
`ℤ¹⁶` coordinates) descends mod 2 to `pairCokerCoord : Q → (ℤ/2)¹⁶`, and

* `pairCokerCoord` is **injective** ⟺ `pairHalve` is injective ⟺ the residual
  (`pairCokerCoord_injective_iff`, `pairHalve_injective_iff`);
* `pairCokerCoord` is **surjective** ⟺ every class is halvable
  (`pairCokerCoord_surjective_iff`).

Source and target are finite of the *same* cardinality `2¹⁶` — the Euler-number pin — so injective
⟺ surjective (`Finite.injective_iff_surjective_of_equiv pairCokerEquiv`). That single equivalence
is the whole proof, and it is why nothing is lost: the two forms are equivalent, not merely
sufficient. (The counting genuinely uses `pairCoker_card = 2¹⁶`: for an `𝒪(−1)` piece the cokernel
is trivial and halvability of a generator is FALSE while 2-torsion-freeness still holds.)

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerPairTubeSeparation

namespace SKEFTHawking.KummerPairHalving

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.KummerWeld (EIndex)
open SKEFTHawking.KummerK7MVAssembly (eImageH2EquivInt)
open SKEFTHawking.KummerK3TorsionFree (redMod2)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerPairTubeSeparation
open scoped SKEFTHawking.KummerK7Delta1Image

noncomputable section

/-! ## §1. The halving map, characterised -/

/-- **The defining property of `pairHalve`**: `pairProj` of the `pairHalve` coordinate vector is the
double. (`pairHalve m` is by construction `pairProj⁻¹(2m)` read in `ℤ¹⁶` coordinates.) -/
theorem pairProj_pairHalve (m : PairH2) :
    pairProj (eImageH2EquivInt.symm (pairHalve m)) = (2 : ℤ) • m := by
  have h1 : eImageH2EquivInt.symm (pairHalve m)
      = (LinearEquiv.ofInjective pairProj pairProj_injective).symm (doubleIntoPairRange m) := by
    simp only [pairHalve, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply]
  rw [h1, ← LinearEquiv.ofInjective_apply pairProj
      (h := pairProj_injective) ((LinearEquiv.ofInjective pairProj pairProj_injective).symm
      (doubleIntoPairRange m)),
    LinearEquiv.apply_symm_apply]
  rfl

/-- `pairHalve` reads off the doubled coordinate vector on the free sublattice. -/
theorem pairHalve_pairProj (u : Homology ESub 2) :
    pairHalve (pairProj u) = (2 : ℤ) • eImageH2EquivInt u := by
  have h1 : pairProj (eImageH2EquivInt.symm (pairHalve (pairProj u)))
      = pairProj ((2 : ℤ) • u) := by
    rw [pairProj_pairHalve, map_smul]
  have h2 : eImageH2EquivInt.symm (pairHalve (pairProj u)) = (2 : ℤ) • u := pairProj_injective h1
  have h3 : pairHalve (pairProj u) = eImageH2EquivInt ((2 : ℤ) • u) := by
    rw [← h2, LinearEquiv.apply_symm_apply]
  rw [h3, map_smul]

/-- **The residual is exactly the injectivity of `pairHalve`.** The `←` direction is the banked
`pairHalve_injective`; the `→` direction is immediate from `pairProj_pairHalve`. -/
theorem pairHalve_injective_iff : Function.Injective pairHalve ↔ PairH2TwoTorsionFree := by
  constructor
  · intro h m hm
    have h1 : pairProj (eImageH2EquivInt.symm (pairHalve m)) = 0 := by
      rw [pairProj_pairHalve, hm]
    have h2 : eImageH2EquivInt.symm (pairHalve m) = 0 :=
      pairProj_injective (by rw [h1, map_zero])
    have h3 : pairHalve m = 0 := by
      rw [← LinearEquiv.apply_symm_apply eImageH2EquivInt (pairHalve m), h2, map_zero]
    exact h (by rw [h3, map_zero])
  · exact pairHalve_injective

/-! ## §2. `Halvable` — the finite geometric form of the residual -/

/-- **`Halvable v`** — the class `pairProj v ∈ H₂(eImage, collar;ℤ)` is divisible by two. For `v`
the zero-section class of the `i`-th resolution piece this is exactly the Euler number `−2`: the
fiber disk `q` of the `𝒪(−2)` piece satisfies `2q = ±[S²]` in `H₂(E, ∂E;ℤ)`. -/
def Halvable (v : Homology ESub 2) : Prop := ∃ q : PairH2, (2 : ℤ) • q = pairProj v

/-- The halvable classes form a submodule — so halvability need only be checked on generators. -/
def halvableSubmodule : Submodule ℤ (Homology ESub 2) where
  carrier := {v | Halvable v}
  zero_mem' := ⟨0, by rw [smul_zero, map_zero]⟩
  add_mem' := by
    rintro a b ⟨qa, hqa⟩ ⟨qb, hqb⟩
    exact ⟨qa + qb, by rw [smul_add, hqa, hqb, map_add]⟩
  smul_mem' := by
    rintro c a ⟨qa, hqa⟩
    exact ⟨c • qa, by rw [smul_comm, hqa, map_smul]⟩

theorem mem_halvableSubmodule {v : Homology ESub 2} : v ∈ halvableSubmodule ↔ Halvable v := Iff.rfl

/-- `redMod2` kills doubles. -/
theorem redMod2_two_smul (w : EIndex → ℤ) : redMod2 ((2 : ℤ) • w) = 0 := by
  funext i
  show (((((2 : ℤ) • w) i : ℤ)) : ZMod 2) = 0
  show (((2 : ℤ) * w i : ℤ) : ZMod 2) = 0
  push_cast
  rw [show ((2 : ZMod 2)) = 0 from rfl, zero_mul]

/-- A coordinate vector killed by `redMod2` is a double. -/
theorem two_dvd_of_redMod2_eq_zero {w : EIndex → ℤ} (h : redMod2 w = 0) :
    ∃ u : EIndex → ℤ, w = (2 : ℤ) • u := by
  refine ⟨fun i => w i / 2, ?_⟩
  funext i
  obtain ⟨c, hc⟩ : (2 : ℤ) ∣ w i := by
    have h5 := (ZMod.intCast_zmod_eq_zero_iff_dvd (w i) 2).mp (congrFun h i)
    exact_mod_cast h5
  show w i = (2 : ℤ) * (w i / 2)
  rw [hc]
  omega

/-! ## §3. The cokernel coordinate and the counting bijection -/

/-- **The cokernel coordinate** `Q = H₂(eImage,collar;ℤ)/im pairProj → (ℤ/2)¹⁶`: the halving map
read mod 2. Well defined because `pairHalve (pairProj u) = 2 • u` is a double. -/
def pairCokerCoord : (PairH2 ⧸ LinearMap.range pairProj) →ₗ[ℤ] (EIndex → ZMod 2) :=
  Submodule.liftQ _ (redMod2.comp pairHalve) (by
    rintro _ ⟨u, rfl⟩
    show redMod2 (pairHalve (pairProj u)) = 0
    rw [pairHalve_pairProj, redMod2_two_smul])

@[simp] theorem pairCokerCoord_mk (m : PairH2) :
    pairCokerCoord (Submodule.Quotient.mk m) = redMod2 (pairHalve m) := rfl

/-- **Injectivity of the cokernel coordinate is injectivity of `pairHalve`.** -/
theorem pairCokerCoord_injective_iff :
    Function.Injective pairCokerCoord ↔ Function.Injective pairHalve := by
  constructor
  · intro h
    rw [injective_iff_map_eq_zero]
    intro m hm
    have h1 : pairCokerCoord (Submodule.Quotient.mk m) = 0 := by
      rw [pairCokerCoord_mk, hm, map_zero]
    have h2 : (Submodule.Quotient.mk m : PairH2 ⧸ LinearMap.range pairProj) = 0 := by
      rw [injective_iff_map_eq_zero] at h
      exact h _ h1
    obtain ⟨u, rfl⟩ := (Submodule.Quotient.mk_eq_zero _).mp h2
    have h3 : (2 : ℤ) • eImageH2EquivInt u = 0 := by rw [← pairHalve_pairProj, hm]
    have h4 : eImageH2EquivInt u = 0 := by
      funext i
      show eImageH2EquivInt u i = (0 : ℤ)
      have h5 : (2 : ℤ) * eImageH2EquivInt u i = 0 := congrFun h3 i
      omega
    rw [show u = 0 from eImageH2EquivInt.map_eq_zero_iff.mp h4, map_zero]
  · intro h
    rw [injective_iff_map_eq_zero]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H m =>
      rw [pairCokerCoord_mk] at hy
      obtain ⟨w, hw⟩ := two_dvd_of_redMod2_eq_zero hy
      have h1 : pairHalve (m - pairProj (eImageH2EquivInt.symm w)) = 0 := by
        rw [map_sub, pairHalve_pairProj, LinearEquiv.apply_symm_apply, hw, sub_self]
      rw [injective_iff_map_eq_zero] at h
      have h2 : m - pairProj (eImageH2EquivInt.symm w) = 0 := h _ h1
      have h3 : m = pairProj (eImageH2EquivInt.symm w) := by
        rwa [sub_eq_zero] at h2
      rw [h3]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩

/-- **Surjectivity of the cokernel coordinate is halvability of every class.** -/
theorem pairCokerCoord_surjective_iff :
    Function.Surjective pairCokerCoord ↔ ∀ v : Homology ESub 2, Halvable v := by
  constructor
  · intro h v
    obtain ⟨y, hy⟩ := h (redMod2 (eImageH2EquivInt v))
    induction y using Submodule.Quotient.induction_on with
    | H m =>
      rw [pairCokerCoord_mk] at hy
      have h1 : redMod2 (pairHalve m - eImageH2EquivInt v) = 0 := by
        rw [map_sub, hy, sub_self]
      obtain ⟨w, hw⟩ := two_dvd_of_redMod2_eq_zero h1
      refine ⟨m - pairProj (eImageH2EquivInt.symm w), ?_⟩
      have h2 : pairHalve (m - pairProj (eImageH2EquivInt.symm w)) = eImageH2EquivInt v := by
        rw [map_sub, pairHalve_pairProj, LinearEquiv.apply_symm_apply, ← hw]
        abel
      have h3 := pairProj_pairHalve (m - pairProj (eImageH2EquivInt.symm w))
      simp only [h2, LinearEquiv.symm_apply_apply] at h3
      exact h3.symm
  · intro h t
    obtain ⟨v, hv⟩ : ∃ v : EIndex → ℤ, redMod2 v = t := by
      refine ⟨fun i => ((t i).val : ℤ), ?_⟩
      funext i
      show ((((t i).val : ℤ)) : ZMod 2) = t i
      push_cast
      exact ZMod.natCast_zmod_val (t i)
    obtain ⟨q, hq⟩ := h (eImageH2EquivInt.symm v)
    refine ⟨Submodule.Quotient.mk q, ?_⟩
    rw [pairCokerCoord_mk]
    have h1 : pairProj (eImageH2EquivInt.symm (pairHalve q))
        = pairProj (eImageH2EquivInt.symm v) := by rw [pairProj_pairHalve, hq]
    have h2 : eImageH2EquivInt.symm (pairHalve q) = eImageH2EquivInt.symm v :=
      pairProj_injective h1
    have h3 : pairHalve q = v := eImageH2EquivInt.symm.injective h2
    rw [h3, hv]

/-! ## §4. The headline equivalence -/

/-- **The residual is EXACTLY halvability.** `H₂(eImage, collar;ℤ)` has no 2-torsion iff every
class of the free sublattice `H₂(eImage;ℤ) ≅ ℤ¹⁶` is divisible by two in the pair group. Proof: the
cokernel coordinate `Q → (ℤ/2)¹⁶` has injectivity ⟺ the residual and surjectivity ⟺ halvability,
and source and target are finite of the same cardinality `2¹⁶` (`pairCokerEquiv`). -/
theorem pairH2TwoTorsionFree_iff_halvable :
    PairH2TwoTorsionFree ↔ ∀ v : Homology ESub 2, Halvable v := by
  rw [← pairHalve_injective_iff, ← pairCokerCoord_injective_iff,
    Finite.injective_iff_surjective_of_equiv (f := pairCokerCoord) pairCokerEquiv.toEquiv,
    pairCokerCoord_surjective_iff]

/-- **The residual as an EQUATION of sublattices**: `H₂(eImage;ℤ) ≅ ℤ¹⁶` sits inside
`H₂(eImage, collar;ℤ)` as *exactly* the subgroup of doubles. The `≥` inclusion is unconditional
(`two_smul_mem_range_pairProj`, the exponent-2 cokernel); the residual is the `≤` inclusion. -/
theorem pairH2TwoTorsionFree_iff_range_eq_doubles :
    PairH2TwoTorsionFree ↔
      LinearMap.range pairProj
        = LinearMap.range ((2 : ℤ) • LinearMap.id : PairH2 →ₗ[ℤ] PairH2) := by
  rw [pairH2TwoTorsionFree_iff_halvable]
  constructor
  · intro h
    refine le_antisymm ?_ ?_
    · rintro _ ⟨v, rfl⟩
      obtain ⟨q, hq⟩ := h v
      exact ⟨q, by simpa using hq⟩
    · rintro _ ⟨m, rfl⟩
      have hm : (2 : ℤ) • m ∈ LinearMap.range pairProj := two_smul_mem_range_pairProj m
      simpa using hm
  · intro h v
    have hmem : pairProj v ∈ LinearMap.range ((2 : ℤ) • LinearMap.id : PairH2 →ₗ[ℤ] PairH2) := by
      rw [← h]; exact ⟨v, rfl⟩
    obtain ⟨q, hq⟩ := hmem
    exact ⟨q, by simpa using hq⟩

/-- **The exceptional class of the `i`-th resolution piece** — the zero-section generator of the
`i`-th `ℤ` summand of `H₂(eImage;ℤ) ≅ ℤ¹⁶`. -/
def exceptional (i : EIndex) : Homology ESub 2 := eImageH2EquivInt.symm (Pi.single i 1)

theorem eImageH2EquivInt_exceptional (i : EIndex) :
    eImageH2EquivInt (exceptional i) = Pi.single i 1 := by
  simp only [exceptional, LinearEquiv.apply_symm_apply]

/-- The exceptional classes span `H₂(eImage;ℤ)`. -/
theorem span_exceptional : Submodule.span ℤ (Set.range exceptional) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  have hsum : v = ∑ i : EIndex, (eImageH2EquivInt v i) • exceptional i := by
    apply eImageH2EquivInt.injective
    rw [map_sum]
    funext j
    have hcomp : ∀ i : EIndex,
        eImageH2EquivInt ((eImageH2EquivInt v i) • exceptional i)
          = (eImageH2EquivInt v i) • (Pi.single i 1 : EIndex → ℤ) := by
      intro i
      rw [map_smul, eImageH2EquivInt_exceptional]
    simp only [hcomp]
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [hsum]
  refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨i, rfl⟩

/-- **The residual reduced to 16 geometric witnesses.** `H₂(eImage, collar;ℤ)` has no 2-torsion iff
each of the 16 exceptional sphere classes is divisible by two in the relative group. This is the
Euler number `−2` of the `𝒪(−2)` resolution piece stated as an existence: `2 • (fiber disk) =
[S²]`. -/
theorem pairH2TwoTorsionFree_iff_exceptional_halvable :
    PairH2TwoTorsionFree ↔ ∀ i : EIndex, Halvable (exceptional i) := by
  rw [pairH2TwoTorsionFree_iff_halvable]
  refine ⟨fun h i => h _, fun h v => ?_⟩
  have hsub : (⊤ : Submodule ℤ (Homology ESub 2)) ≤ halvableSubmodule := by
    rw [← span_exceptional]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact h i
  exact hsub (Submodule.mem_top)

/-- **The anti-shuffling certificate.** The 16-witness form is EQUIVALENT to the mission-form
target `H₂(ResE, ∂ResE;ℤ) ≅ ℤ` (16 copies) — not merely sufficient for it. Chains this module's
equivalence with the landed `pairH2TwoTorsionFree_iff_equiv`. -/
theorem exceptional_halvable_iff_pairH2_equiv :
    (∀ i : EIndex, Halvable (exceptional i)) ↔ Nonempty (PairH2 ≃ₗ[ℤ] (EIndex → ℤ)) := by
  rw [← pairH2TwoTorsionFree_iff_exceptional_halvable, pairH2TwoTorsionFree_iff_equiv]

/-! ## §5. The finale, on 16 witnesses -/

/-- **`Torsion(H₂(K3;ℤ)) = ⊥` from 16 halvings.** -/
theorem kummerK3_torsion_free_of_exceptional_halvable
    (h : ∀ i : EIndex, Halvable (exceptional i)) :
    Submodule.torsion ℤ (Homology KummerK3top 2) = ⊥ :=
  kummerK3_torsion_free_of_pairH2TwoTorsionFree
    (pairH2TwoTorsionFree_iff_exceptional_halvable.mpr h)

/-- **`kummerK3_b2_target` from 16 halvings** — the ℤ²² headline with its residual reduced to the
construction of one relative fiber-disk class per resolution piece. -/
theorem kummerK3_b2_target_of_exceptional_halvable
    (h : ∀ i : EIndex, Halvable (exceptional i)) :
    SKEFTHawking.KummerK7Opener.kummerK3_b2_target :=
  kummerK3_b2_target_of_pairH2TwoTorsionFree
    (pairH2TwoTorsionFree_iff_exceptional_halvable.mpr h)

end

end SKEFTHawking.KummerPairHalving
