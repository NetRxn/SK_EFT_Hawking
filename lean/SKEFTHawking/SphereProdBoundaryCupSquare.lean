/-
# Phase 5q.H — the boundary mod-2 cohomology cup-square vanishing for `∂(S²×D³) ≃ S²×S²`

Discharges `SphereProdP23WuVanish.BoundaryCupSquareVanishes` — the ONE remaining geometric feeder of
`hv2` (the `(2,3)` Wu-class vanishing) — WITHOUT any Künneth/EZ input. The statement is

  `∀ c : Cohomology (sub sphereDiskBoundarySet) 2, cupH24 c c = 0`.

## The EZ-free route (lead re-triage, 2026-07-20)

Everything transports to the actual product `S²×S²` along the boundary homeomorphism
`sphereDiskInclHomeo : SphereProd ≃ₜ sub sphereDiskBoundarySet` (`cohomologyHomeoEquiv`,
`cohomologyPullback_cupH24` naturality), so it suffices to show

  `∀ d : Cohomology (S²×S²;ℤ/2) 2, cupH24 d d = 0`.

On `SphereProd = TwoSphere × TwoSphere` (a LITERAL product) the two factor-pullback classes
`g₁ = pr₁*g`, `g₂ = pr₂*g` (`g` the nonzero generator of `H²(S²)`, `dim = 1`) satisfy:

* **squares vanish**: `gᵢ ∪ gᵢ = prᵢ*(g ∪ g) = prᵢ*(0) = 0` (`cohomologyPullback_cupH24` +
  `g ∪ g ∈ H⁴(S²;ℤ/2) = 0`, since `H₄(S²)=0` by `sphere_homology_high` + UC);
* **basis**: `{g₁, g₂}` is a basis of `H²(S²×S²;ℤ/2)` (`dim = 2`, `finrank_cohomology_eq_homology` +
  `finrank_sphereProd_homologyMod2_two`), linearly independent via the sections
  `σ₁(x)=(x,y₀)`, `σ₂(y)=(x₀,y)`: `σᵢ*gᵢ = g ≠ 0` (`prᵢ∘σᵢ = id`) and `σ₁*g₂ = σ₂*g₁ = 0`
  (`prⱼ∘σᵢ` constant, the constant-map pullback vanishes through the acyclic disk).

The squaring map `d ↦ cupH24 d d` is `ℤ/2`-additive (char-2 cross-term cancellation via `cupH24_symm`,
`x+x=0`), so a `Submodule.span_induction` over the basis closes `cupH24 d d = 0` for every `d`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SphereProdP23WuVanish
import SKEFTHawking.SphereProdP23Nondeg
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeSteenrodSq2
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
open SKEFTHawking.SingularUniversalCoeff
open SKEFTHawking.SingularSphereHighDegree (sphere_homology_high)
open SKEFTHawking.SingularDiskAcyclic (Disk)
open SKEFTHawking.SphereProdP23WuVanish (BoundaryCupSquareVanishes)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SphereProdBoundaryCupSquare

noncomputable section

/-! ## §0. Acyclic-disk cohomology vanishing (for the constant-map pullback). -/

/-- **`H₂(Dⁿ;ℤ/2) = 0`** — the disk is acyclic (straight-line contraction,
`SingularDiskAcyclic.cycle_mem_boundaries`). -/
theorem disk_homology_two_eq_zero {n : ℕ} (x : Homology (Disk n) 2) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
  exact SKEFTHawking.SingularDiskAcyclic.cycle_mem_boundaries 1 z.1 z.2

/-- **`H²(Dⁿ;ℤ/2) = 0`** — the UC flip of `disk_homology_two_eq_zero` (`cohomology_eq_zero_of_kroneckerH`). -/
theorem disk_cohomology_two_eq_zero {n : ℕ} (ω : Cohomology (Disk n) 2) : ω = 0 :=
  cohomology_eq_zero_of_kroneckerH 1 ω (fun β => by rw [disk_homology_two_eq_zero β]; simp)

/-! ## §1. Constant-map cohomology pullback vanishing on `H²(S²)`. -/

/-- **A constant map kills positive-degree cohomology**: `(const y₀)* = 0` on `H²(S²;ℤ/2)`, since it
factors through the acyclic disk `D⁰`. -/
theorem constMap_cohomology_two_eq_zero (y₀ : TwoSphere)
    (g : Cohomology (TopCat.of TwoSphere) 2) :
    cohomologyPullback (ContinuousMap.const (↑(TopCat.of TwoSphere)) y₀) 2 g = 0 := by
  have hfact : (ContinuousMap.const (↑(TopCat.of TwoSphere)) y₀ :
        C(↑(TopCat.of TwoSphere), ↑(TopCat.of TwoSphere)))
      = (ContinuousMap.const (↑(Disk 0)) y₀).comp
          (ContinuousMap.const (↑(TopCat.of TwoSphere)) (⟨0, by simp⟩ : ↑(Disk 0))) := by
    apply ContinuousMap.ext; intro x; rfl
  rw [hfact, cohomologyPullback_comp, LinearMap.comp_apply,
    disk_cohomology_two_eq_zero (cohomologyPullback (ContinuousMap.const (↑(Disk 0)) y₀) 2 g),
    map_zero]

/-! ## §2. `H⁴(S²;ℤ/2) = 0` and the cup-square of `H²(S²)`. -/

/-- **`H₄(S²;ℤ/2) = 0`** — `TopCat.of TwoSphere = Sph 2` and `4 > 2` (`sphere_homology_high`). -/
theorem twoSphere_homology_four_eq_zero (β : Homology (TopCat.of TwoSphere) 4) : β = 0 :=
  sphere_homology_high 2 4 (by norm_num) β

/-- **The cup-square vanishes on `H²(S²;ℤ/2)`**: `g ∪ g ∈ H⁴(S²;ℤ/2) = 0`. -/
theorem twoSphere_cupSquare_eq_zero (g : Cohomology (TopCat.of TwoSphere) 2) :
    cupH24 g g = 0 :=
  cohomology_eq_zero_of_kroneckerH 3 (cupH24 g g)
    (fun β => by rw [twoSphere_homology_four_eq_zero β]; simp)

/-! ## §3. The projections and sections of `SphereProd = TwoSphere × TwoSphere`. -/

/-- First projection `pr₁ : S²×S² → S²`. -/
def pr1 : C(↑(TopCat.of SphereProd), ↑(TopCat.of TwoSphere)) := ⟨Prod.fst, continuous_fst⟩

/-- Second projection `pr₂ : S²×S² → S²`. -/
def pr2 : C(↑(TopCat.of SphereProd), ↑(TopCat.of TwoSphere)) := ⟨Prod.snd, continuous_snd⟩

/-- First section `σ₁(x) = (x, y₀)`. -/
def sec1 (y₀ : TwoSphere) : C(↑(TopCat.of TwoSphere), ↑(TopCat.of SphereProd)) :=
  ⟨fun x => (x, y₀), by fun_prop⟩

/-- Second section `σ₂(y) = (x₀, y)`. -/
def sec2 (x₀ : TwoSphere) : C(↑(TopCat.of TwoSphere), ↑(TopCat.of SphereProd)) :=
  ⟨fun y => (x₀, y), by fun_prop⟩

theorem pr1_comp_sec1 (y₀ : TwoSphere) :
    pr1.comp (sec1 y₀) = ContinuousMap.id (↑(TopCat.of TwoSphere)) := by
  apply ContinuousMap.ext; intro x; rfl

theorem pr2_comp_sec1 (y₀ : TwoSphere) :
    pr2.comp (sec1 y₀) = ContinuousMap.const (↑(TopCat.of TwoSphere)) y₀ := by
  apply ContinuousMap.ext; intro x; rfl

theorem pr2_comp_sec2 (x₀ : TwoSphere) :
    pr2.comp (sec2 x₀) = ContinuousMap.id (↑(TopCat.of TwoSphere)) := by
  apply ContinuousMap.ext; intro x; rfl

theorem pr1_comp_sec2 (x₀ : TwoSphere) :
    pr1.comp (sec2 x₀) = ContinuousMap.const (↑(TopCat.of TwoSphere)) x₀ := by
  apply ContinuousMap.ext; intro x; rfl

/-! ## §4. The cup-square vanishing on `H²(S²×S²;ℤ/2)`. -/

/-- **The cup-square vanishes on `H²(S²×S²;ℤ/2)`.** `{g₁ = pr₁*g, g₂ = pr₂*g}` is a basis (dim 2,
independent via the sections), `gᵢ ∪ gᵢ = prᵢ*(g ∪ g) = 0`, and the squaring map is `ℤ/2`-additive
(char-2), so `span_induction` closes `cupH24 d d = 0` for every `d`. -/
theorem sphereProd_cupSquare_eq_zero (d : Cohomology (TopCat.of SphereProd) 2) :
    cupH24 d d = 0 := by
  -- Fix basepoints and a nonzero generator of `H²(S²)`.
  let y₀ : TwoSphere := Classical.arbitrary TwoSphere
  haveI : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of TwoSphere) 2) :=
    SKEFTHawking.SingularMVCohomologyFinite.finiteDimensional_cohomology_of_homology
      (X := TopCat.of TwoSphere) 1
      SKEFTHawking.SphereProdP23.finiteDimensional_twoSphere_homology_two
  have hgpos : 0 < Module.finrank (ZMod 2) (Cohomology (TopCat.of TwoSphere) 2) := by
    have h1 : Module.finrank (ZMod 2) (Cohomology (TopCat.of TwoSphere) 2) = 1 :=
      SphereProdP23Nondeg.finrank_twoSphere_cohomology_two
    omega
  haveI : Nontrivial (Cohomology (TopCat.of TwoSphere) 2) := Module.nontrivial_of_finrank_pos hgpos
  obtain ⟨g, hg⟩ := exists_ne (0 : Cohomology (TopCat.of TwoSphere) 2)
  -- the two factor-pullback classes.
  set g₁ : Cohomology (TopCat.of SphereProd) 2 := cohomologyPullback pr1 2 g with hg1def
  set g₂ : Cohomology (TopCat.of SphereProd) 2 := cohomologyPullback pr2 2 g with hg2def
  -- section pullbacks.
  have hσ11 : cohomologyPullback (sec1 y₀) 2 g₁ = g := by
    rw [hg1def, ← LinearMap.comp_apply, ← cohomologyPullback_comp, pr1_comp_sec1,
      cohomologyPullback_id, LinearMap.id_apply]
  have hσ12 : cohomologyPullback (sec1 y₀) 2 g₂ = 0 := by
    rw [hg2def, ← LinearMap.comp_apply, ← cohomologyPullback_comp, pr2_comp_sec1,
      constMap_cohomology_two_eq_zero]
  have hσ22 : cohomologyPullback (sec2 y₀) 2 g₂ = g := by
    rw [hg2def, ← LinearMap.comp_apply, ← cohomologyPullback_comp, pr2_comp_sec2,
      cohomologyPullback_id, LinearMap.id_apply]
  have hσ21 : cohomologyPullback (sec2 y₀) 2 g₁ = 0 := by
    rw [hg1def, ← LinearMap.comp_apply, ← cohomologyPullback_comp, pr1_comp_sec2,
      constMap_cohomology_two_eq_zero]
  -- squares vanish.
  have hg1sq : cupH24 g₁ g₁ = 0 := by
    have h := cohomologyPullback_cupH24 pr1 g g
    rw [twoSphere_cupSquare_eq_zero g, map_zero] at h
    exact h.symm
  have hg2sq : cupH24 g₂ g₂ = 0 := by
    have h := cohomologyPullback_cupH24 pr2 g g
    rw [twoSphere_cupSquare_eq_zero g, map_zero] at h
    exact h.symm
  -- linear independence via the sections.
  have hli : LinearIndependent (ZMod 2) ![g₁, g₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (cohomologyPullback (sec1 y₀) 2) hst
    have h2 := congrArg (cohomologyPullback (sec2 y₀) 2) hst
    rw [map_add, map_smul, map_smul, hσ11, hσ12, smul_zero, add_zero, map_zero] at h1
    rw [map_add, map_smul, map_smul, hσ21, hσ22, smul_zero, zero_add, map_zero] at h2
    refine ⟨?_, ?_⟩
    · rcases smul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hg
    · rcases smul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hg
  -- the basis spans.
  have hcard : Fintype.card (Fin 2)
      = Module.finrank (ZMod 2) (Cohomology (TopCat.of SphereProd) 2) := by
    rw [Fintype.card_fin,
      PoincareLefschetzRelFundClassCylinderSuspension.finrank_cohomology_eq_homology
        (X := TopCat.of SphereProd) 1,
      SphereProdHTwoMod2.finrank_sphereProd_homologyMod2_two]
  have hspan : Submodule.span (ZMod 2) (Set.range ![g₁, g₂]) = ⊤ := by
    have hb := (basisOfLinearIndependentOfCardEqFinrank hli hcard).span_eq
    rwa [coe_basisOfLinearIndependentOfCardEqFinrank] at hb
  have hmem : d ∈ Submodule.span (ZMod 2) (Set.range ![g₁, g₂]) := by
    rw [hspan]; exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    fin_cases i
    · simpa using hg1sq
    · simpa using hg2sq
  | zero => simp
  | add x y _ _ hx hy =>
    have hxy : cupH24 (x + y) (x + y) = cupH24 x y + cupH24 y x := by
      simp only [map_add, LinearMap.add_apply, hx, hy]; abel
    rw [hxy, cupH24_symm y x, ← two_smul (ZMod 2) (cupH24 x y), show (2 : ZMod 2) = 0 by decide,
      zero_smul]
  | smul a x _ hx =>
    simp only [map_smul, LinearMap.smul_apply, hx, smul_zero]

/-! ## §5. Transport to the boundary — `BoundaryCupSquareVanishes`. -/

/-- **`cohomologyHomeoEquiv` intertwines the cup-square** — ABSTRACT over the homeomorphism `e`
(so no whnf blowup on the concrete `sphereDiskInclHomeo`): the homeo-transport is the pullback of
`⟨e, e.continuous⟩`, which is `cupH24`-multiplicative (`cohomologyPullback_cupH24`). -/
theorem cohomologyHomeoEquiv_cupH24 {X Y : TopCat} (e : (↑X : Type) ≃ₜ (↑Y : Type))
    (a b : Cohomology Y 2) :
    cohomologyHomeoEquiv e 4 (cupH24 a b)
      = cupH24 (cohomologyHomeoEquiv e 2 a) (cohomologyHomeoEquiv e 2 b) := by
  simp only [cohomologyHomeoEquiv, LinearEquiv.ofLinear_apply]
  exact cohomologyPullback_cupH24 _ a b

/-- **The boundary mod-2 cohomology cup-square vanishing on `∂(S²×D³) ≃ S²×S²`** — the discharge of
`SphereProdP23WuVanish.BoundaryCupSquareVanishes`. Transports `sphereProd_cupSquare_eq_zero` along the
boundary homeomorphism `sphereDiskInclHomeo` via `cohomologyHomeoEquiv_cupH24`. -/
theorem boundaryCupSquareVanishes : BoundaryCupSquareVanishes := by
  intro c
  apply (cohomologyHomeoEquiv sphereDiskInclHomeo 4).injective
  rw [map_zero, cohomologyHomeoEquiv_cupH24]
  exact sphereProd_cupSquare_eq_zero _

/-! ## §6. Unconditional discharge of the `(2,3)` `relSq2`/Wu-class vanishing. -/

/-- **`relSq2 = 0` on `H³(S²×D³, S²×S²; ℤ/2)`, UNCONDITIONALLY** — `SphereProdP23WuVanish`'s conditional
`sphereDiskRelSq2_eq_zero` with its boundary cup-square feeder now DISCHARGED
(`boundaryCupSquareVanishes`). -/
theorem sphereDiskRelSq2_eq_zero
    (b : RelativeCohomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3) :
    relSq2 (X := TopCat.of SphereDisk) b = 0 :=
  SphereProdP23WuVanish.sphereDiskRelSq2_eq_zero boundaryCupSquareVanishes b

/-- **`hv2` — the `(2,3)` Wu-class vanishing for the `S²×D³` datum, UNCONDITIONALLY.** For any
Lefschetz–Wu datum `P₂₃` on `(S²×D³, S²×S²)` whose `sqOp` is the genuine relative Steenrod square
`relSq2` (in particular every `LefschetzWuDatum.ofRelFund23 D …`), the middle Wu class vanishes:
`wuClass P₂₃ = 0`. The boundary cup-square feeder is discharged, so this composes with the (in-flight)
`nondeg` feeder + relative-fundamental-class the moment the concrete `sphereDiskP23` datum lands. -/
theorem sphereDiskWuClass23_eq_zero
    (P₂₃ : LefschetzWuDatum (TopCat.of SphereDisk) sphereDiskBoundarySet 2 3 5)
    (hsq : P₂₃.sqOp = relSq2 (X := TopCat.of SphereDisk)) :
    wuClass P₂₃ = 0 :=
  SphereProdP23WuVanish.sphereDiskWuClass23_eq_zero boundaryCupSquareVanishes P₂₃ hsq

end

end SKEFTHawking.SphereProdBoundaryCupSquare
