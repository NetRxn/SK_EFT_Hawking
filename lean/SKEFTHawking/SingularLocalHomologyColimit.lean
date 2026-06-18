/-
# Phase 5q.F (w₂-foundation) — `Hᵢ(M | K)` direct-limit surjectivity

The **surjectivity half** of the `Hᵢ(M | K)` direct limit (Hatcher 3.27, step 3): every class of
`Hᵢ(M | K) = Hᵢ(M, M∖K)` factors through `Hᵢ(M | C)` for a **compact neighbourhood** `C ⊇ K`.

A relative class `α ∈ Hₖ₊₁(M | K)` is represented by a singular chain `c` whose boundary `∂c` lies
in `M∖K` (the relative-cycle condition). The boundary's image is compact and disjoint from `K`; in a
locally-compact Hausdorff space `K` and `chainImage (∂c)` are separated by a compact neighbourhood `C`
of `K` with `∂c` still in `M∖C` (`exists_compact_boundary_avoiding`, brick 72c-4d). Then `[c]_{Cᶜ}` is
a relative cycle for the pair `(M, M∖C)`, and the inclusion-of-pairs map
`relIncl : Hₖ₊₁(M|C) → Hₖ₊₁(M|K)` (induced by `Cᶜ ⊆ Kᶜ`) sends `[c]_{Cᶜ} ↦ [c]_{Kᶜ} = α`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}` only).
-/
import Mathlib
import SKEFTHawking.SingularRelativeMV
import SKEFTHawking.SingularChainSupport

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeFunctoriality SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularChainSupport

namespace SKEFTHawking.SingularLocalHomologyColimit

/-- **`Hᵢ(M | K)` direct-limit surjectivity** (Hatcher 3.27, step 3): every relative homology class
`α ∈ Hₖ₊₁(M, M∖K)` is the image, under the inclusion-of-pairs map `relIncl : Hₖ₊₁(M|C) → Hₖ₊₁(M|K)`,
of a class `β ∈ Hₖ₊₁(M, M∖C)` over a **compact neighbourhood** `C` of `K`. So `Hᵢ(M|K)` is the direct
limit of `Hᵢ(M|C)` over compact `C ⊇ K`. -/
theorem exists_factor_through_compact {X : TopCat} [T2Space ↑X] [LocallyCompactSpace ↑X]
    {K : Set ↑X} (hK : IsCompact K) {k : ℕ} (α : RelativeHomology Kᶜ (k + 1)) :
    ∃ C : Set ↑X, IsCompact C ∧ ∃ (hKC : K ⊆ interior C),
      ∃ β : RelativeHomology Cᶜ (k + 1),
        relIncl (Set.compl_subset_compl.mpr (hKC.trans interior_subset)) (k + 1) β = α := by
  -- Step 1: α = [z₀] for a relative cycle z₀.
  obtain ⟨z₀, rfl⟩ := Submodule.Quotient.mk_surjective _ α
  -- Step 2: z₀ has a representative singular chain c.
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z₀ : RelativeChain Kᶜ (k + 1))
  -- Step 3: the relative-cycle condition forces ∂c ∈ subspaceChains Kᶜ k.
  have hz₀cyc : relBoundary Kᶜ k (z₀ : RelativeChain Kᶜ (k + 1)) = 0 := LinearMap.mem_ker.mp z₀.2
  have hbd : chainBoundary X k c ∈ subspaceChains Kᶜ k := by
    rw [← RelativeChain.mk_eq_zero_iff]
    have : relBoundary Kᶜ k (RelativeChain.mk Kᶜ (k + 1) c) = 0 := by
      rw [show RelativeChain.mk Kᶜ (k + 1) c = (z₀ : RelativeChain Kᶜ (k + 1)) from hc, hz₀cyc]
    rwa [relBoundary_mk] at this
  -- Step 4: separate ∂c from K by a compact neighbourhood C.
  obtain ⟨C, hCcompact, hKC, hbdC⟩ := exists_compact_boundary_avoiding hK hbd
  refine ⟨C, hCcompact, hKC, ?_⟩
  -- Step 5: [c]_{Cᶜ} is a relative cycle for (M, M∖C); take β := its homology class.
  have hcyc : RelativeChain.mk Cᶜ (k + 1) c ∈ relCycles Cᶜ (k + 1) := by
    rw [relCycles, LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff]
    exact hbdC
  refine ⟨RelativeHomology.mk Cᶜ (k + 1) ⟨RelativeChain.mk Cᶜ (k + 1) c, hcyc⟩, ?_⟩
  -- Step 6: relIncl sends [c]_{Cᶜ} to [c]_{Kᶜ} = α (id_# is the factor map; underlying chains agree).
  rw [relIncl_mk]
  refine congrArg (RelativeHomology.mk Kᶜ (k + 1)) (Subtype.ext ?_)
  rw [relCyclesMap_coe, relMapChain_id_mk]
  exact hc

end SKEFTHawking.SingularLocalHomologyColimit
