import Mathlib
import SKEFTHawking.SingularOpenDualityMVSquare
import SKEFTHawking.SingularH0PathConnected

/-!
# Phase 5q.F (w₂-foundation, G1 PD track A) — the `H₀` Mayer–Vietoris end exactness

The degree-`0` end of the homology Mayer–Vietoris ladder:
`subHomSum U V 0 : H₀(sub U) × H₀(sub V) → H₀(sub (U∪V))` is **surjective** (over `ℤ/2` the
sum/difference distinction is trivial). Chain-level argument: every `0`-chain of `sub (U∪V)` is a
`ℤ/2`-combination of `0`-simplices; a `0`-simplex is the constant simplex at its point
(`SingularH0PathConnected.eq_constSimplex`), and that point lies in `U` or in `V`, so each generator
lifts along `homOfSubset` to `sub U` or `sub V`. Every `0`-chain is a cycle (`cycles _ 0 = ⊤`), so
the generators assemble by `Finsupp.induction_linear` into range-membership of every class.

This is the `H₀` end the Poincaré-duality 5-lemma needs where the homology MV long exact sequence
runs out of connecting maps (Hatcher 3.36, bottom row).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularSubsetHomology
  SKEFTHawking.SingularHomotopyInvariance SKEFTHawking.SingularH0PathConnected
  SKEFTHawking.SingularOpenDualityMVSquare

namespace SKEFTHawking.SingularSubHomSumEnd

variable {X : TopCat}

/-! ## §1. Degree-`0` homology classes of arbitrary `0`-chains -/

/-- The degree-`0` homology class of an arbitrary `0`-chain — every `0`-chain is a cycle
(`cycles _ 0 = ⊤`), so no cycle condition is needed. -/
noncomputable def h0Class (Y : TopCat) (c : SingularChain Y 0) : Homology Y 0 :=
  Homology.mk Y 0 ⟨c, Submodule.mem_top⟩

/-- `h0Class` of the zero chain is `0`. -/
theorem h0Class_zero (Y : TopCat) : h0Class Y 0 = 0 := by
  rw [h0Class, show (⟨0, Submodule.mem_top⟩ : cycles Y 0) = 0 from Subtype.ext rfl]
  exact Submodule.Quotient.mk_zero _

/-- `h0Class` is additive. -/
theorem h0Class_add (Y : TopCat) (c d : SingularChain Y 0) :
    h0Class Y (c + d) = h0Class Y c + h0Class Y d := by
  rw [h0Class, h0Class, h0Class, show (⟨c + d, Submodule.mem_top⟩ : cycles Y 0)
    = ⟨c, Submodule.mem_top⟩ + ⟨d, Submodule.mem_top⟩ from Subtype.ext rfl]
  exact Submodule.Quotient.mk_add _

/-- **Every degree-`0` homology class is `h0Class` of a `0`-chain** (`cycles _ 0 = ⊤`, so the
quotient-mk surjectivity forgets the cycle subtype). -/
theorem h0Class_surjective (Y : TopCat) (y : Homology Y 0) : ∃ c, h0Class Y c = y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨z.1, congrArg (Homology.mk Y 0) (Subtype.ext rfl)⟩

/-- **`homOfSubset` computes on `h0Class` by the chain-level pushforward**: the subspace-inclusion
map on degree-`0` homology sends the class of `c` to the class of `mapChain (subInclCM h) 0 c`. -/
theorem homOfSubset_h0Class {K K' : Set ↑X} (h : K ⊆ K') (c : SingularChain (sub K) 0) :
    homOfSubset h 0 (h0Class (sub K) c) = h0Class (sub K') (mapChain (subInclCM h) 0 c) := by
  rw [h0Class, h0Class, homOfSubset, Homology.map_mk]
  exact congrArg (Homology.mk (sub K') 0) (Subtype.ext rfl)

/-! ## §2. Lifting `0`-simplices across the cover -/

/-- **The pushforward of a constant simplex is the constant simplex at the image point** — the
`mapSimplex` analogue of `mapSimplex_const` (post-composing a constant map is constant). -/
theorem mapSimplex_constSimplex {Y Z : TopCat} (φ : C(↑Y, ↑Z)) (b : ↑Y) (k : ℕ) :
    mapSimplex φ (constSimplex b k) = constSimplex (φ b) k := by
  apply (Z.toSSetObjEquiv (op (SimplexCategory.mk k))).injective
  rw [mapSimplex, constSimplex, constSimplex, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact ContinuousMap.ext fun t => rfl

/-- **Every degree-`0` generator of `H₀(sub (U∪V))` lifts across the cover**: the class of a single
`0`-simplex `σ` is in the range of `subHomSum U V 0`. The point of `σ` lies in `U` or `V`; the
constant simplex at that point (which *is* `σ`, by `eq_constSimplex`) lives in `sub U` resp. `sub V`
and pushes forward to `σ` along the subspace inclusion. -/
theorem h0Class_single_mem_range (U V : Set ↑X)
    (σ : (TopCat.toSSet.obj (sub (U ∪ V))).obj (op (SimplexCategory.mk 0))) (a : ZMod 2) :
    h0Class (sub (U ∪ V)) (Finsupp.single σ a) ∈ LinearMap.range (subHomSum U V 0) := by
  rcases (simplexPoint σ).2 with hpU | hpV
  · refine ⟨(h0Class (sub U)
      (Finsupp.single (constSimplex (⟨(simplexPoint σ).1, hpU⟩ : ↥U) 0) a), 0), ?_⟩
    rw [subHomSum, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, map_zero, sub_zero, homOfSubset_h0Class,
      mapChain_single, mapSimplex_constSimplex]
    exact congrArg (fun τ => h0Class (sub (U ∪ V)) (Finsupp.single τ a)) (eq_constSimplex σ).symm
  · refine ⟨(0, h0Class (sub V)
      (Finsupp.single (constSimplex (⟨(simplexPoint σ).1, hpV⟩ : ↥V) 0) a)), ?_⟩
    rw [subHomSum, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, map_zero, zero_sub, homOfSubset_h0Class,
      mapChain_single, mapSimplex_constSimplex, ← neg_one_smul (ZMod 2)]
    rw [show (-1 : ZMod 2) = 1 from rfl, one_smul]
    exact congrArg (fun τ => h0Class (sub (U ∪ V)) (Finsupp.single τ a)) (eq_constSimplex σ).symm

/-! ## §3. The `H₀` MV end exactness -/

/-- **The `H₀` Mayer–Vietoris end exactness**: `subHomSum U V 0 : H₀(sub U) × H₀(sub V) →
H₀(sub (U∪V))` is surjective. Every class is `h0Class` of a `0`-chain (`cycles _ 0 = ⊤`); by
`Finsupp.induction_linear` it suffices to lift the single-simplex generators, which is
`h0Class_single_mem_range` (each `0`-simplex is constant at a point of `U` or of `V`). -/
theorem subHomSum_zero_surjective (U V : Set ↑X) :
    Function.Surjective (subHomSum U V 0) := by
  intro y
  obtain ⟨c, rfl⟩ := h0Class_surjective (sub (U ∪ V)) y
  suffices hmem : h0Class (sub (U ∪ V)) c ∈ LinearMap.range (subHomSum U V 0) from hmem
  induction c using Finsupp.induction_linear with
  | zero => rw [h0Class_zero]; exact zero_mem _
  | add c d hc hd => rw [h0Class_add]; exact add_mem hc hd
  | single σ a => exact h0Class_single_mem_range U V σ a

end SKEFTHawking.SingularSubHomSumEnd
