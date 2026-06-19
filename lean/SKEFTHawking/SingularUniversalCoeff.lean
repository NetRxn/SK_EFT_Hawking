/-
# Phase 5q.F (brick 72c-PD4a) — cohomology-side universal coefficients over ℤ/2

The **dual** of `PoincareDualityConstruct.homology_eq_zero_of_kroneckerH` (the homology-side
universal-coefficients fact: a homology class pairing to `0` with every cohomology class is `0`).
Here we prove the cohomology-side statement: a cohomology class `ω` pairing to `0` with every
*homology* class `β` under the descended Kronecker pairing `kroneckerH` is `0`.

This is the universal-coefficients fact needed for `Hⁿ(M|x) ≅ ℤ/2` (the local cohomology, dual to
`SingularLocalHomology.manifoldLocalIso`) in the Poincaré-duality base case.

The harder UC direction (the **factoring**): a cohomology class is a cocycle `f`; pairing to `0`
with every cycle means the chain-functional `⟨f, ·⟩` vanishes on `ker ∂`, so — over the field `ℤ/2`
— it factors through `∂` as `⟨f, ·⟩ = g ∘ₗ ∂` for a functional `g`; realizing `g` as a cochain `gc`
(`exists_cochain_of_functional`) and using the cap–coboundary adjunction
(`kronecker_coboundary_chainBoundary`) gives `f = δ gc`, i.e. `f` is a coboundary, so `ω = 0`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularHomologyMod2

namespace SKEFTHawking.SingularUniversalCoeff

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2

/-- **Factoring through a linear map over a field.** A functional `φ : M →ₗ K` that vanishes on
`ker ψ` (for `ψ : M →ₗ N`) factors through `ψ`: there is a functional `g : N →ₗ K` with
`g ∘ₗ ψ = φ`. Routed over the field `K`: `φ` descends to `M ⧸ ker ψ` (`Submodule.liftQ`); pull back
along `ψ.quotKerEquivRange.symm` to a functional on `range ψ`; extend to all of `N` by
`LinearMap.exists_extend`. -/
theorem exists_factor_of_ker_le_ker {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (ψ : M →ₗ[K] N) (φ : M →ₗ[K] K)
    (h : LinearMap.ker ψ ≤ LinearMap.ker φ) : ∃ g : N →ₗ[K] K, g ∘ₗ ψ = φ := by
  -- `φ` descends to `M ⧸ ker ψ`.
  set φbar : (M ⧸ LinearMap.ker ψ) →ₗ[K] K := Submodule.liftQ (LinearMap.ker ψ) φ h with hφbar
  -- pull back along `ψ.quotKerEquivRange.symm : range ψ ≃ₗ (M ⧸ ker ψ)`.
  set φrange : (LinearMap.range ψ) →ₗ[K] K :=
    φbar.comp ψ.quotKerEquivRange.symm.toLinearMap with hφrange
  -- extend to all of `N`.
  obtain ⟨g, hg⟩ := LinearMap.exists_extend φrange
  refine ⟨g, ?_⟩
  ext m
  have hmem : ψ m ∈ LinearMap.range ψ := ⟨m, rfl⟩
  have hsub : (LinearMap.range ψ).subtype ⟨ψ m, hmem⟩ = ψ m := rfl
  have key : g (ψ m) = φrange ⟨ψ m, hmem⟩ := by
    have := LinearMap.congr_fun hg ⟨ψ m, hmem⟩
    rwa [LinearMap.comp_apply, hsub] at this
  rw [LinearMap.comp_apply, key, hφrange, LinearMap.comp_apply]
  have hsymm : ψ.quotKerEquivRange.symm ⟨ψ m, hmem⟩ = Submodule.Quotient.mk m := by
    apply ψ.quotKerEquivRange.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [LinearMap.quotKerEquivRange_apply_mk]
  rw [LinearEquiv.coe_coe, hsymm, hφbar, Submodule.liftQ_apply]

/-- **Every chain functional is `kronecker` of a cochain** (the dual of `Finsupp` is the full
function space): `φ = ⟨f, ·⟩` for `f σ = φ (single σ 1)`. The cochain-realization counterpart, used
to turn the abstract factoring functional `g` back into a singular cochain `δ`-preimage. (Mirrors
`PoincareDualityConstruct.exists_cochain_of_functional`; inlined here to keep the import set to
`SingularHomologyMod2`.) -/
theorem exists_cochain_of_functional {X : TopCat} {n : ℕ}
    (φ : SingularChain X n →ₗ[ZMod 2] ZMod 2) :
    ∃ f : SingularCochain X n, ∀ c : SingularChain X n, kronecker f c = φ c := by
  refine ⟨fun σ => φ (Finsupp.single σ 1), fun c => ?_⟩
  induction c using Finsupp.induction_linear with
  | zero => simp [kronecker_apply]
  | add c d hc hd => rw [kronecker_add_right, map_add, hc, hd]
  | single σ s =>
      rw [kronecker_single,
        show Finsupp.single σ s = s • Finsupp.single σ (1 : ZMod 2) by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one],
        map_smul, smul_eq_mul]

/-- **The Kronecker pairing is non-degenerate in the cohomology argument** (universal coefficients
over the field `ℤ/2`): a cohomology class `ω` in degree `N+1` that pairs to `0` with every homology
class is `0`. The dual of `PoincareDualityConstruct.homology_eq_zero_of_kroneckerH`. -/
theorem cohomology_eq_zero_of_kroneckerH {X : TopCat} (N : ℕ) (ω : Cohomology X (N + 1))
    (h : ∀ β : Homology X (N + 1), kroneckerH (X := X) (N + 1) ω β = 0) : ω = 0 := by
  -- `ω = [f]` for a cocycle `f`.
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ ω
  -- the cochain functional `φ = ⟨f.1, ·⟩` vanishes on cycles `ker ∂`.
  set φ : SingularChain X (N + 1) →ₗ[ZMod 2] ZMod 2 := kroneckerₗ (N + 1) f.1 with hφ
  have hvanish : LinearMap.ker (chainBoundary X N) ≤ LinearMap.ker φ := by
    intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    rw [hφ, kroneckerₗ_apply]
    -- `z` is a cycle, so it represents a homology class; apply `h`.
    have hzcyc : z ∈ cycles X (N + 1) := hz
    have := h (Homology.mk X (N + 1) ⟨z, hzcyc⟩)
    rwa [Homology.mk, kroneckerH_mk_mk] at this
  -- factor `φ = g ∘ₗ ∂`.
  obtain ⟨g, hg⟩ := exists_factor_of_ker_le_ker (chainBoundary X N) φ hvanish
  -- realize `g` as a cochain `gc`.
  obtain ⟨gc, hgc⟩ := exists_cochain_of_functional g
  -- `f.1 = δ gc`, so `f.1` is a coboundary.
  have hcobound : f.1 = coboundary X N gc := by
    funext σ
    -- evaluate both `kronecker` functionals at the basis `single σ 1`.
    have e1 : kronecker f.1 (Finsupp.single σ 1) = f.1 σ := by
      rw [kronecker_single, one_mul]
    have e2 : kronecker (coboundary X N gc) (Finsupp.single σ 1) = coboundary X N gc σ := by
      rw [kronecker_single, one_mul]
    rw [← e1, ← e2]
    -- `⟨δ gc, c⟩ = ⟨gc, ∂c⟩ = g (∂c) = φ c = ⟨f.1, c⟩`.
    rw [kronecker_coboundary_chainBoundary, hgc, ← LinearMap.comp_apply, hg, hφ, kroneckerₗ_apply]
  -- conclude `[f] = 0`: `f.1 ∈ coboundaryRange X (N+1) = range (coboundaryₗ X N)`.
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  exact ⟨gc, hcobound.symm⟩

end SKEFTHawking.SingularUniversalCoeff
