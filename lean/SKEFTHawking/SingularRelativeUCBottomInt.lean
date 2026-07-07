/-
# Phase 5q.H (E1 CSC-PD tower) — the integral relative UCT at the BOTTOM degree (`H¹`)

The degree-1 companion of `SingularRelativeUCInt.relKroneckerHInt_injective_of_free` /
`relCohomology_eq_zero_of_relHomology_two_vanishInt`, whose indexing (`ω : RelCohom (M+2)`) cannot reach
degree 1. At the bottom the cycle convention degenerates — `relCyclesInt S 0 = ⊤` (every 0-chain is a
cycle) — so the `C₀ ↠ Z₀` retraction is the identity and the boundary-functional extension needs ONLY
`Hₒ = RelHomologyInt S 0` free (no `relBoundariesInt S (-1)` projectivity, which doesn't exist).

`relCohomology_one_eq_zero_of_relHomology_bottom_vanishInt`: `H¹(X,S;ℤ) = 0` when `H₁ = 0` (Hom term) and
`H₀ = 0` (⟹ free ⟹ `Ext(H₀) = 0`). The exact shape the `k = 1` CSC-vanishing (`cscOpen_one_eq_zero_of_
chartConvexInt`) needs at each convex-compact stage (`H₁(K'ᶜ) = 0` by `relHomology_one_convexCompactInt`,
`H₀(K'ᶜ) = 0` since `ℝⁿ∖K` meets `ℝⁿ`'s only component).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelativeUCInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt

namespace SKEFTHawking.SingularRelativeUCBottomInt

variable {X : TopCat} (S : Set ↑X)

/-- **Boundary-functional extension at the bottom** — a functional on `B₀ = relBoundariesInt S 0` extends
to all of `C₀ = RelativeChainInt S 0`, provided `H₀` is free. Bottom companion of
`SingularRelativeUCInt.exists_functional_extension_boundaries`: since `relCyclesInt S 0 = ⊤`, the `C₀ ↠ Z₀`
retraction is the identity, so only the `Z₀ ↠ B₀` retraction (`exists_boundaries_in_cycles_retraction`,
needs `H₀` free) is used. -/
theorem exists_functional_extension_boundaries_bottomInt
    [Module.Free ℤ (RelHomologyInt S 0)]
    (g : relBoundariesInt S 0 →ₗ[ℤ] ℤ) :
    ∃ F : RelativeChainInt S 0 →ₗ[ℤ] ℤ,
      ∀ b : relBoundariesInt S 0, F (b : RelativeChainInt S 0) = g b := by
  obtain ⟨ρ, hρ⟩ := SingularRelativeUCInt.exists_boundaries_in_cycles_retraction S (N := 0)
  have hcoe : ∀ w : (relBoundariesInt S 0).submoduleOf (relCyclesInt S 0),
      ((w : relCyclesInt S 0) : RelativeChainInt S 0) ∈ relBoundariesInt S 0 :=
    fun w => Submodule.mem_comap.mp w.2
  refine ⟨g.comp
    ({ toFun := fun c => ⟨((ρ ⟨c, Submodule.mem_top⟩ : relCyclesInt S 0) : RelativeChainInt S 0),
          hcoe (ρ ⟨c, Submodule.mem_top⟩)⟩
       map_add' := fun a b => by
         apply Subtype.ext
         rw [show (⟨a + b, Submodule.mem_top⟩ : relCyclesInt S 0)
             = ⟨a, Submodule.mem_top⟩ + ⟨b, Submodule.mem_top⟩ from rfl, map_add]
         rfl
       map_smul' := fun t a => by
         apply Subtype.ext
         rw [show (⟨t • a, Submodule.mem_top⟩ : relCyclesInt S 0)
             = t • ⟨a, Submodule.mem_top⟩ from rfl, map_smul]
         rfl } :
      RelativeChainInt S 0 →ₗ[ℤ] relBoundariesInt S 0), ?_⟩
  intro b
  rw [LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  show ((ρ ⟨(b : RelativeChainInt S 0), Submodule.mem_top⟩ : relCyclesInt S 0) : RelativeChainInt S 0)
    = (b : RelativeChainInt S 0)
  have hbsubmem : (⟨(b : RelativeChainInt S 0), Submodule.mem_top⟩ : relCyclesInt S 0)
      ∈ (relBoundariesInt S 0).submoduleOf (relCyclesInt S 0) := Submodule.mem_comap.mpr b.2
  rw [hρ ⟨_, hbsubmem⟩]

/-- **`κ` is injective at degree 1 when `H₀` is free** (the `Ext(H₀) = 0` half at the bottom): a relative
`H¹` class pairing to `0` with every `H₁` class is `0`. Bottom mirror of
`SingularRelativeUCInt.relKroneckerHInt_injective_of_free`, using the bottom boundary extension. -/
theorem relKroneckerHInt_injective_bottomInt
    [Module.Free ℤ (RelHomologyInt S 0)]
    (ω : RelativeCohomologyInt S 1)
    (h : ∀ β : RelHomologyInt S 1, SingularRelativeUCInt.relKroneckerHInt S ω β = 0) : ω = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ ω
  set φ : RelativeChainInt S 1 →ₗ[ℤ] ℤ := SingularRelativeUCInt.relKroneckerInt S a.1 with hφ
  have hvanish : LinearMap.ker (relBoundaryInt S 0) ≤ LinearMap.ker φ := by
    intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    rw [hφ]
    have hzcyc : z ∈ relCyclesInt S 1 := hz
    have hh := h (RelHomologyInt.mk S 1 ⟨z, hzcyc⟩)
    rwa [show (Submodule.Quotient.mk a : RelativeCohomologyInt S 1)
        = RelativeCohomologyInt.mk S 1 a from rfl, SingularRelativeUCInt.relKroneckerHInt_mk_mk] at hh
  set dlm := relBoundaryInt S 0 with hdlm
  set gbar : dlm.range →ₗ[ℤ] ℤ :=
    (Submodule.liftQ (LinearMap.ker dlm) φ hvanish).comp
      (LinearMap.quotKerEquivRange dlm).symm.toLinearMap with hgbar
  have hgbar_apply : ∀ c : RelativeChainInt S 1,
      gbar ⟨relBoundaryInt S 0 c, ⟨c, rfl⟩⟩ = φ c := by
    intro c
    have hrr : (LinearMap.quotKerEquivRange dlm).symm ⟨relBoundaryInt S 0 c, ⟨c, rfl⟩⟩
        = Submodule.Quotient.mk c := by
      apply (LinearMap.quotKerEquivRange dlm).injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      rfl
    rw [hgbar, LinearMap.comp_apply, LinearEquiv.coe_coe, hrr, Submodule.liftQ_apply]
  obtain ⟨g, hg⟩ := exists_functional_extension_boundaries_bottomInt S gbar
  obtain ⟨b, hb⟩ := SingularRelativeUCInt.exists_relCochainInt_of_functional S g
  have hcobound : (a : relCochainsInt S 1) = relCoboundaryIntₗ S 0 b := by
    apply Subtype.ext
    show (a.1 : SingularCochainInt X 1) = coboundary X 0 b.1
    funext σ
    have e1 : kronecker a.1.1 (Finsupp.single σ 1) = a.1.1 σ := by rw [kronecker_single, one_mul]
    have e2 : kronecker (coboundary X 0 b.1) (Finsupp.single σ 1)
        = coboundary X 0 b.1 σ := by rw [kronecker_single, one_mul]
    rw [← e1, ← e2]
    have hlhs : kronecker a.1.1 (Finsupp.single σ 1)
        = φ (RelativeChainInt.mk S 1 (Finsupp.single σ 1)) := by
      rw [hφ, SingularRelativeUCInt.relKroneckerInt_mk]
    have hrhs : kronecker (coboundary X 0 b.1) (Finsupp.single σ 1)
        = φ (RelativeChainInt.mk S 1 (Finsupp.single σ 1)) := by
      rw [show coboundary X 0 b.1 = (relCoboundaryIntₗ S 0 b).1 from rfl,
        ← SingularRelativeUCInt.relKroneckerInt_mk S (relCoboundaryIntₗ S 0 b) (Finsupp.single σ 1),
        ← SingularRelativeUCInt.relKroneckerInt_relBoundary, relBoundaryInt_mk]
      rw [show SingularRelativeUCInt.relKroneckerInt S b (RelativeChainInt.mk S 0
            (chainBoundary X 0 (Finsupp.single σ 1)))
          = g (RelativeChainInt.mk S 0 (chainBoundary X 0 (Finsupp.single σ 1)))
          from congrFun (congrArg DFunLike.coe hb) _]
      have hbdmk : RelativeChainInt.mk S 0 (chainBoundary X 0 (Finsupp.single σ 1))
          = relBoundaryInt S 0 (RelativeChainInt.mk S 1 (Finsupp.single σ 1)) := by
        rw [relBoundaryInt_mk]
      rw [hbdmk, hg ⟨relBoundaryInt S 0 (RelativeChainInt.mk S 1 (Finsupp.single σ 1)),
        ⟨_, rfl⟩⟩]
      exact hgbar_apply (RelativeChainInt.mk S 1 (Finsupp.single σ 1))
    rw [hlhs, hrhs]
  refine (RelativeCohomologyInt.mk_eq_zero_iff S 1 a).mpr ?_
  rw [hcobound]
  exact ⟨b, rfl⟩

/-- **`H¹(X, S; ℤ) = 0` from `H₁ = 0` and `H₀ = 0`** (bottom UCT vanishing) — the degree-1 mirror of
`SingularRelativeUCVanishInt.relCohomology_eq_zero_of_relHomology_two_vanishInt`. `H₀ = 0 ⟹ free ⟹
Ext(H₀) = 0` (injectivity); `H₁ = 0` kills the Hom term. -/
theorem relCohomology_one_eq_zero_of_relHomology_bottom_vanishInt
    (hH0 : ∀ β : RelHomologyInt S 0, β = 0)
    (hH1 : ∀ β : RelHomologyInt S 1, β = 0)
    (ω : RelativeCohomologyInt S 1) : ω = 0 := by
  haveI : Subsingleton (RelHomologyInt S 0) := ⟨fun a b => (hH0 a).trans (hH0 b).symm⟩
  haveI : Module.Free ℤ (RelHomologyInt S 0) := Module.Free.of_subsingleton ℤ _
  exact relKroneckerHInt_injective_bottomInt S ω (fun β => by rw [hH1 β, map_zero])

end SKEFTHawking.SingularRelativeUCBottomInt
