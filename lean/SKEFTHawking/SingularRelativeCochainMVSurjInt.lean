/-
# Phase 5q.H (E1 integral topology) — the relative COCHAIN MV `Sum` is surjective (CONCRETE)

The relative-cohomology Mayer–Vietoris middle-exactness chase needs, directly on the concrete cochain
level (no dual-space transport, no compatibility bookkeeping), that every `g : relCochainsInt (U∩V) n`
splits as `g = gU - gV` with `gU ∈ relCochainsInt U`, `gV ∈ relCochainsInt V`.

The split is the **indicator split** conditioned on the geometric Prop `range(realize σ) ⊆ U`:
  `gU σ := if range(realize σ) ⊆ U then 0 else g σ`,  `gV := gU - g`.
Membership is then immediate from the support characterisation of `subspaceChainsInt`
(`range_of_mem_subspaceChainsInt` / `mem_subspaceChainsInt_of_support`), with NO need for a
"factors-through-U ↔ image-⊆-U" iso:
- `gU ∈ relCochainsInt U`: a support simplex of a `C(U)`-chain has image ⊆ U, so `gU` kills it.
- `gV ∈ relCochainsInt V`: a support simplex of a `C(V)`-chain has image ⊆ V; either its image ⊆ U
  (then `gU σ = 0` and — image ⊆ U∩V so `g` vanishes — `gV σ = 0`), or not (then `gV σ = g σ − g σ = 0`).

This is the field-UC-free, torsion-safe input for `relCohomMv_exact_middleInt` (the ℤ analogue of the
mod-2 `SingularCSCMayerVietoris` cochain surjectivity, avoiding the universal-coefficient theorem).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularRelHomologyInt
import SKEFTHawking.SingularEuclideanCapIsoInt
import SKEFTHawking.SingularExcisionIsoInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularExcisionIsoInt

namespace SKEFTHawking.SingularRelativeCochainMVSurjInt

variable {M : TopCat}

/-- **`kronecker` vanishes on a chain the cochain kills simplex-by-simplex.** If `f σ = 0` for every
support simplex `σ` of `c`, then `⟨f, c⟩ = 0`. -/
theorem kronecker_eq_zero_of_support {n : ℕ} (f : SingularCochainInt M n) (c : SingularChainInt M n)
    (h : ∀ σ ∈ c.support, f σ = 0) : kronecker f c = 0 := by
  rw [kronecker_apply]
  exact Finset.sum_eq_zero (fun σ hσ => by simp only [h σ hσ, mul_zero])

/-- **The concrete relative-cochain MV `Sum` is surjective.** Every `g : relCochainsInt (U∩V) n`
splits as `g = gU − gV` with `gU ∈ relCochainsInt U`, `gV ∈ relCochainsInt V`. -/
theorem relCochainMvSum_surjectiveInt (U V : Set M) (n : ℕ)
    (g : relCochainsInt (U ∩ V) n) :
    ∃ (gU : relCochainsInt U n) (gV : relCochainsInt V n),
      ((gU : SingularCochainInt M n) - (gV : SingularCochainInt M n))
        = (g : SingularCochainInt M n) := by
  classical
  -- the geometric predicate on a simplex: its image lands in U
  set P : (TopCat.toSSet.obj M).obj (op (SimplexCategory.mk n)) → Prop :=
    fun σ => Set.range (M.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) ⊆ U with hP
  -- the indicator split
  set gUf : SingularCochainInt M n :=
    fun σ => if P σ then 0 else (g : SingularCochainInt M n) σ with hgUf
  set gVf : SingularCochainInt M n :=
    gUf - (g : SingularCochainInt M n) with hgVf
  -- gU ∈ relCochainsInt U
  have hgU : gUf ∈ relCochainsInt U n := by
    rw [mem_relCochainsInt]
    intro c hc
    refine kronecker_eq_zero_of_support _ _ (fun σ hσ => ?_)
    have hPσ : P σ := range_of_mem_subspaceChainsInt hc hσ
    rw [hgUf]; simp only [hPσ, if_true]
  -- gV ∈ relCochainsInt V
  have hgV : gVf ∈ relCochainsInt V n := by
    rw [mem_relCochainsInt]
    intro c hc
    refine kronecker_eq_zero_of_support _ _ (fun σ hσ => ?_)
    have hVσ : Set.range (M.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) ⊆ V :=
      range_of_mem_subspaceChainsInt hc hσ
    rw [hgVf]
    simp only [Pi.sub_apply, hgUf]
    by_cases hPσ : P σ
    · -- image ⊆ U and ⊆ V ⟹ ⊆ U∩V ⟹ g σ = 0
      have hUV : Finsupp.single σ (1 : ℤ) ∈ subspaceChainsInt (U ∩ V) n := by
        refine mem_subspaceChainsInt_of_support (fun τ hτ => ?_)
        rw [Finsupp.support_single_ne_zero _ (one_ne_zero)] at hτ
        rw [Finset.mem_singleton] at hτ; subst hτ
        exact Set.subset_inter hPσ hVσ
      have hg0 : (g : SingularCochainInt M n) σ = 0 := by
        have := g.2 _ hUV
        rwa [kronecker_single, one_mul] at this
      simp only [hPσ, if_true, hg0, sub_zero]
    · simp only [hPσ, if_false, sub_self]
  -- assemble: (gUf) - (gUf - g) = g
  refine ⟨⟨gUf, hgU⟩, ⟨gVf, hgV⟩, ?_⟩
  show gUf - gVf = (g : SingularCochainInt M n)
  rw [hgVf]; ext σ; simp only [Pi.sub_apply]; ring

end SKEFTHawking.SingularRelativeCochainMVSurjInt
