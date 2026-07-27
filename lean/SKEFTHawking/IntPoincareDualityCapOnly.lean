/-
# Phase 5q.H · E1 — integral Poincaré duality from the CAP ALONE (the Kronecker half discharged)

Sharpens brick 9 (`IntCapProductInt.IntCapIso`) and brick 9′ (`IntPoincareDualityCapIso.IntCapIsoData`).
Both carried **two** disclosed geometric inputs:

* (i) the integral cap `· ⌢ [M] : H²(M;ℤ) → H₂(M;ℤ)` is an isomorphism — the genuine PD core;
* (ii) the integral Kronecker `H₂(M;ℤ) → Dual ℤ (H²(M;ℤ))` is a perfect pairing.

**Input (ii) is not independent.** This module proves it is a CONSEQUENCE of (i) plus the finiteness
that the `IntH2Basis` datum already presupposes (`H₂(M;ℤ)` finite free), with **no `H₁` freeness /
`Ext`-vanishing input at all**:

* the absolute UCT map `κ = kroneckerHInt 2 : H²(M;ℤ) → Dual ℤ (H₂(M;ℤ))` is SURJECTIVE
  unconditionally (`SingularAbsoluteUCInt.kroneckerHInt_surjective_of_projective`; the boundaries are
  projective over the PID ℤ, universally — `SphereWitnessTowerInt.boundariesProjective`);
* the cap iso (i) transports `H₂` finite-free to `H²` finite-free, so `κ` is a surjection from a
  Noetherian ℤ-module onto a module isomorphic to it; conjugating by that isomorphism makes `κ` a
  surjective ENDOmorphism of `H₂(M;ℤ)`, hence injective (`IsNoetherian.injective_of_surjective_endomorphism`
  — Orzech/Vasconcelos). So `κ` is bijective and `Ext(H₁(M;ℤ), ℤ) = 0` is *forced*, not assumed;
* dualizing `κ` through the reflexivity of the finite free `H₂` gives the flip
  `H₂ ≃ₗ Dual ℤ H²` with the exact computation rule `⟨b, h⟩` that `IntCapIso.kronEquiv_apply` demands.

## Headlines (all kernel-pure, no `sorry`/`native_decide`/`maxHeartbeats`/axiom)

* `kroneckerHInt2_bijective_of_capBijective` — the UCT map at degree 2 is bijective, from the cap iso;
* `kronFlipOfCapBijective` (+ `_apply`) — the Kronecker flip, built, not disclosed;
* `intCapIsoOfCapBijective` — `IntCapIso zM` from `Function.Bijective (capMapLin zM)` ALONE;
* `intPoincareDualityOfCapBijective` — **`IntPoincareDuality` from the single geometric datum
  "the integral cap `· ⌢ [M]` is bijective"**;
* `interMatrix_isUnimodular_of_capBijective` — the σ÷16 leg's UNIMODULAR conjunct from that datum;
* `capBijective_of_capDualBasis` — the *usable* sufficient condition: if some basis of `H²(M;ℤ)` caps
  onto a basis of `H₂(M;ℤ)`, the cap is bijective. This is the same cap-dual data
  (`IntersectionMatrixBasisChange.interMatrix_capDual`) that the Gram span must produce anyway, so on
  any carrier where the Gram computation is executed in cap-dual coordinates, integral PD comes free.

Net effect on the disclosed-input ledger: `IntPoincareDuality` ⟸ ONE geometric Prop
(`Function.Bijective (capMapLin [M])`), where before it was two isos, or two integer determinants.
-/
import Mathlib
import SKEFTHawking.IntPoincareDualityCapIso
import SKEFTHawking.SingularAbsoluteUCInt

namespace SKEFTHawking.IntPDCapOnly

open SKEFTHawking SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularAbsoluteUCInt

variable {X : TopCat}

/-! ## §1. The cap iso transports finiteness/freeness to `H²` -/

section CapBij

variable {zM : Homology X 4}

/-- **The cap equivalence** `H²(M;ℤ) ≃ₗ[ℤ] H₂(M;ℤ)` packaged from bijectivity of the BUILT cap map
`capMapLin zM = (capHInt 2 1).flip [M]`. Its underlying map is `capMapLin zM` definitionally
(`LinearEquiv.ofBijective`), which is what pins the whole construction below to the geometric cap
rather than to an abstract choice. -/
noncomputable def capEquivOfBijective (hcap : Function.Bijective (capMapLin zM)) :
    Cohomology X 2 ≃ₗ[ℤ] Homology X 2 :=
  LinearEquiv.ofBijective _ hcap

@[simp] theorem capEquivOfBijective_apply (hcap : Function.Bijective (capMapLin zM))
    (a : Cohomology X 2) : capEquivOfBijective hcap a = capHInt 2 1 a zM := rfl

/-- **`H²(M;ℤ)` is free** once `H₂(M;ℤ)` is and the cap is an iso. -/
theorem cohomology_two_free_of_capBijective [Module.Free ℤ (Homology X 2)]
    (hcap : Function.Bijective (capMapLin zM)) : Module.Free ℤ (Cohomology X 2) :=
  Module.Free.of_equiv (capEquivOfBijective hcap).symm

/-- **`H²(M;ℤ)` is finitely generated** once `H₂(M;ℤ)` is and the cap is an iso. -/
theorem cohomology_two_finite_of_capBijective [Module.Finite ℤ (Homology X 2)]
    (hcap : Function.Bijective (capMapLin zM)) : Module.Finite ℤ (Cohomology X 2) :=
  Module.Finite.equiv (capEquivOfBijective hcap).symm

/-! ## §2. The UCT map at degree 2 is BIJECTIVE — with no `Ext`-vanishing input -/

/-- **A finite free ℤ-module is isomorphic to its dual** (via a chosen basis and its dual basis).
The bookkeeping step that turns the UCT surjection `H² ↠ Dual H₂` into a surjective ENDOmorphism of
`H₂`, so Orzech/Vasconcelos applies. Not canonical (basis-dependent) — and it need not be: only the
EXISTENCE of some iso is used, and injectivity of `κ` is a basis-free conclusion. -/
noncomputable def dualSelfEquivOfFiniteFree (M : Type*) [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M] : Module.Dual ℤ M ≃ₗ[ℤ] M := by
  classical
  exact (Module.Free.chooseBasis ℤ M).dualBasis.equiv (Module.Free.chooseBasis ℤ M) (Equiv.refl _)

/-- **The absolute UCT map `κ = kroneckerHInt 2` is INJECTIVE, given the cap iso** — with no `H₁`
freeness / `Ext`-vanishing hypothesis.

`κ : H²(M;ℤ) → Dual ℤ (H₂(M;ℤ))` is surjective unconditionally (projective boundaries). The cap iso
makes `H²` finite free like `H₂`; picking a basis identifies `Dual ℤ H₂ ≃ H₂`, so
`d ∘ κ ∘ cap⁻¹ : H₂ → H₂` is a surjective endomorphism of a Noetherian ℤ-module, hence injective
(`IsNoetherian.injective_of_surjective_endomorphism`). Injectivity of `κ` follows since the two outer
maps are equivalences. So over a carrier whose `H₂` is finite free, integral PD FORCES
`Ext(H₁(M;ℤ), ℤ) = 0` rather than needing it as a separate input. -/
theorem kroneckerHInt2_injective_of_capBijective [Module.Free ℤ (Homology X 2)]
    [Module.Finite ℤ (Homology X 2)] [Module.Projective ℤ (boundaries X 1)]
    (hcap : Function.Bijective (capMapLin zM)) :
    Function.Injective (kroneckerHInt (X := X) 2) := by
  classical
  -- (`isNoetherian_of_fg_of_noetherian'` no longer exists in this Mathlib pin; the instance
  -- is found directly from `Module.Finite ℤ _` over the Noetherian ring `ℤ`.)
  haveI : IsNoetherian ℤ (Homology X 2) := inferInstance
  set e : Cohomology X 2 ≃ₗ[ℤ] Homology X 2 := capEquivOfBijective hcap with he
  set d : Module.Dual ℤ (Homology X 2) ≃ₗ[ℤ] Homology X 2 :=
    dualSelfEquivOfFiniteFree (Homology X 2) with hd
  have hks : Function.Surjective (kroneckerHInt (X := X) 2) :=
    kroneckerHInt_surjective_of_projective (X := X) (N := 1)
  set f : Homology X 2 →ₗ[ℤ] Homology X 2 :=
    (d.toLinearMap.comp (kroneckerHInt (X := X) 2)).comp e.symm.toLinearMap with hf
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨w, hw⟩ := d.surjective y
    obtain ⟨a, ha⟩ := hks w
    exact ⟨e a, by simp [hf, ha, hw]⟩
  have hfi : Function.Injective f := IsNoetherian.injective_of_surjective_endomorphism f hfs
  intro a b hab
  have : f (e a) = f (e b) := by simp only [hf, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, hab]
  exact e.injective (hfi this)

/-- **The absolute UCT map `κ = kroneckerHInt 2` is BIJECTIVE, given the cap iso.** Surjectivity is
unconditional (projective boundaries); injectivity is §2's forced `Ext`-vanishing. -/
theorem kroneckerHInt2_bijective_of_capBijective [Module.Free ℤ (Homology X 2)]
    [Module.Finite ℤ (Homology X 2)] [Module.Projective ℤ (boundaries X 1)]
    (hcap : Function.Bijective (capMapLin zM)) :
    Function.Bijective (kroneckerHInt (X := X) 2) :=
  ⟨kroneckerHInt2_injective_of_capBijective hcap,
    kroneckerHInt_surjective_of_projective (X := X) (N := 1)⟩

/-- **The degree-2 UCT iso `H²(M;ℤ) ≃ₗ Dual ℤ (H₂(M;ℤ))`, from the cap iso.** The
hypothesis-free-in-`H₁` replacement for `SingularAbsoluteUCInt.ucIntEquivOfFree` on a carrier carrying
integral PD. -/
noncomputable def ucEquivOfCapBijective [Module.Free ℤ (Homology X 2)]
    [Module.Finite ℤ (Homology X 2)] [Module.Projective ℤ (boundaries X 1)]
    (hcap : Function.Bijective (capMapLin zM)) :
    Cohomology X 2 ≃ₗ[ℤ] Module.Dual ℤ (Homology X 2) :=
  LinearEquiv.ofBijective _ (kroneckerHInt2_bijective_of_capBijective hcap)

/-! ## §3. The Kronecker FLIP `H₂ ≃ₗ Dual ℤ H²` — built, not disclosed -/

/-- **The integral Kronecker flip `H₂(M;ℤ) ≃ₗ[ℤ] Dual ℤ (H²(M;ℤ))`, BUILT from the cap iso.** The
double-dual reflexivity of the finite free `H₂` composed with the dual of §2's UCT iso — the same
shape as `SingularAbsoluteUCInt.kronFlipOfFree`, but with the `H₁`-freeness input replaced by the cap
iso. This is exactly field (ii) of `IntCapIso`, so that field is no longer an independent disclosure. -/
noncomputable def kronFlipOfCapBijective [Module.Free ℤ (Homology X 2)]
    [Module.Finite ℤ (Homology X 2)] [Module.Projective ℤ (boundaries X 1)]
    (hcap : Function.Bijective (capMapLin zM)) :
    Homology X 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology X 2) :=
  haveI : Module.IsReflexive ℤ (Homology X 2) :=
    Module.IsReflexive.of_finite_of_free ℤ (Homology X 2)
  (Module.evalEquiv ℤ (Homology X 2)).trans (ucEquivOfCapBijective hcap).dualMap

/-- **The flip computes as the Kronecker pairing**: `kronFlipOfCapBijective hcap h b = ⟨b, h⟩`. The
`kronEquiv_apply` obligation of `IntCapIso`. -/
theorem kronFlipOfCapBijective_apply [Module.Free ℤ (Homology X 2)]
    [Module.Finite ℤ (Homology X 2)] [Module.Projective ℤ (boundaries X 1)]
    (hcap : Function.Bijective (capMapLin zM)) (h : Homology X 2) (b : Cohomology X 2) :
    kronFlipOfCapBijective hcap h b = kroneckerHInt 2 b h := rfl

/-! ## §4. `IntCapIso` and `IntPoincareDuality` from the cap datum ALONE -/

/-- **`IntCapIso [M]` from bijectivity of the cap map alone.** Field (i) is the packaged hypothesis;
field (ii) is §3's built flip. So the two-disclosure `IntCapIso` collapses to ONE geometric Prop on
any carrier with `H₂(M;ℤ)` finite free. -/
noncomputable def intCapIsoOfCapBijective [Module.Free ℤ (Homology X 2)]
    [Module.Finite ℤ (Homology X 2)] [Module.Projective ℤ (boundaries X 1)]
    (hcap : Function.Bijective (capMapLin zM)) : IntCapIso zM where
  capEquiv := capEquivOfBijective hcap
  capEquiv_apply _ := rfl
  kronEquiv := kronFlipOfCapBijective hcap
  kronEquiv_apply _ _ := rfl

/-- **INTEGRAL POINCARÉ DUALITY FROM THE CAP DATUM ALONE.** Given only that the built integral cap
`· ⌢ [M] : H²(M;ℤ) → H₂(M;ℤ)` is bijective (and `H₂(M;ℤ)` finite free — the finiteness the
`IntH2Basis` datum already presupposes), the disclosed `IntPoincareDuality` perfect-pairing datum is
INHABITED, with `toDualEquiv` the composite `cap` then `Kronecker-flip` — hence equal to
`interFormInt` by the descended cap–cup adjunction, per `toDualEquiv_apply`. No `Ext`-vanishing,
no `H₁`-freeness, no second disclosed iso, no determinant hypothesis. -/
noncomputable def intPoincareDualityOfCapBijective [Module.Free ℤ (Homology X 2)]
    [Module.Finite ℤ (Homology X 2)] [Module.Projective ℤ (boundaries X 1)]
    (hcap : Function.Bijective (capMapLin zM)) :
    IntPoincareDuality (intFundamentalClassOfHomology zM) :=
  intPoincareDualityOfCapIso (intCapIsoOfCapBijective hcap)

/-- **The σ÷16 leg's UNIMODULAR conjunct from the cap datum alone** — for any finite free basis `B` of
`H²(M;ℤ)`, the integer intersection matrix is unimodular (`det = ±1`). The end-to-end statement: the
whole `IsEvenUnimodular` → `σ ÷ 16` pipeline's unimodularity input is ONE geometric Prop. -/
theorem interMatrix_isUnimodular_of_capBijective [Module.Free ℤ (Homology X 2)]
    [Module.Finite ℤ (Homology X 2)] [Module.Projective ℤ (boundaries X 1)]
    (B : IntH2Basis X) (hcap : Function.Bijective (capMapLin zM)) :
    IsUnimodular (interMatrix (intFundamentalClassOfHomology zM) B) :=
  interMatrix_isUnimodular_of_intPD _ B (intPoincareDualityOfCapBijective hcap)

end CapBij

/-! ## §5. The usable sufficient condition — a cap-DUAL basis

`IntersectionMatrixBasisChange.interMatrix_capDual` already says: if the `H²` basis `B` is cap-dual to
a family `c` of geometric homology classes (`B i ⌢ [M] = c i`), the whole Gram matrix is the Kronecker
pairing table `⟨B j, c i⟩`. The lemma below says the SAME data, with `c` a *basis* rather than a bare
family, additionally gives the cap iso — hence (via §4) integral Poincaré duality. So on a carrier
where the intersection form is computed in cap-dual coordinates, PD is not an extra residual: it is a
by-product of the basis-hood of the geometric classes the Gram span already has to establish. -/

/-- **The cap is bijective when it carries a basis of `H²(M;ℤ)` to a basis of `H₂(M;ℤ)`.** A linear
map sending a basis to a basis is the basis-transport equivalence `Module.Basis.equiv`, hence
bijective. Stated with an arbitrary index type: no rank or finiteness hypothesis is needed here — the
finiteness enters only downstream (§4). -/
theorem capBijective_of_capDualBasis {zM : Homology X 4} {ι : Type*}
    (B : Module.Basis ι ℤ (Cohomology X 2)) (c : Module.Basis ι ℤ (Homology X 2))
    (hdual : ∀ i, capHInt 2 1 (B i) zM = c i) :
    Function.Bijective (capMapLin zM) := by
  have hmap : capMapLin zM = (B.equiv c (Equiv.refl ι)).toLinearMap := by
    refine B.ext fun i => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, capMapLin_apply, hdual]
  rw [hmap]
  exact (B.equiv c (Equiv.refl ι)).bijective

/-- **Integral Poincaré duality from a cap-dual BASIS** — the packaged form of §5 for consumers: a
basis of `H²(M;ℤ)` whose cap-images form a basis of `H₂(M;ℤ)` delivers the whole
`IntPoincareDuality` datum. This is the honest discharge route for any carrier where geometric
homology classes (spheres, descended tori, half-sums …) are exhibited together with cohomological
cap-duals. -/
noncomputable def intPoincareDualityOfCapDualBasis {zM : Homology X 4} {ι : Type*}
    [Module.Free ℤ (Homology X 2)] [Module.Finite ℤ (Homology X 2)]
    [Module.Projective ℤ (boundaries X 1)]
    (B : Module.Basis ι ℤ (Cohomology X 2)) (c : Module.Basis ι ℤ (Homology X 2))
    (hdual : ∀ i, capHInt 2 1 (B i) zM = c i) :
    IntPoincareDuality (intFundamentalClassOfHomology zM) :=
  intPoincareDualityOfCapBijective (capBijective_of_capDualBasis B c hdual)

end SKEFTHawking.IntPDCapOnly
