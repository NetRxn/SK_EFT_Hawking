/-
# Closed manifolds are homologically `n`-dimensional: `Hₚ(M;ℤ) = 0` for `p > n`, `Hₙ(M;ℤ)` free

Every top-degree vanishing argument in this project so far has been *hand-built per space*: a 4-chart
good-cover telescope for `ℝP³` (`KummerRP3GoodCoverTelescope`), a two-set circle peel for the
punctured 4-torus (`KummerPuncturedTorusHighVanish`), a weld Mayer–Vietoris for the free quotient
(`KummerQTopVanish`). Yet the Poincaré-duality lane already contains the general machine: the
Hatcher-3.27 good-compact stage `SingularGoodCompactInt.vanishAboveInt` together with its geometric
cofinality `SingularCSCVanishAboveGeomInt.vanishAbove_cofinalInt`.

For a **compact** charted manifold that machine collapses to an absolute statement in one step. Run
the cofinality with `W = K = univ`: the compact `K'` it produces satisfies `univ ⊆ K'`, hence is all
of `M`; and `univᶜ = ∅`, where `SingularRelativeEmptyInt.relHomologyEmptyEquivInt` identifies
`Hᵢ(M | ∅;ℤ)` with the absolute `Hᵢ(M;ℤ)`. So the stage reads off as

    `Hₚ(M;ℤ) = 0` for every `p > n`   and   `Hₙ(M;ℤ)` is **free**,

for a compact Hausdorff `n`-manifold `M` (`n = m + 2`), the second being the freeness half of the
same cofinal stage. In dimension 4 the tower's ball-freeness input is the *theorem*
`SingularTopHomologyFreeUnionInt.hballFreeInt_dim4`, so `*_dim4` below carry **no** hypotheses
beyond the manifold structure itself.

## What this is not

It is not Poincaré duality and it does not need an orientation: only the charted structure,
Hausdorffness and compactness enter. That is what makes it usable *upstream* of orientability
questions (its first consumer, `KummerQTopVanish`, applies it to the welded `K3` precisely to avoid
circularity with the open `orientInput`).

It also says nothing below the top degree, and it is **not** available for manifolds with boundary —
`ChartedSpace (EuclideanSpace ℝ (Fin n))` is boundaryless. A compact-with-boundary piece must still
be reached through an ambient closed manifold (as `KummerQTopVanish` reaches `Q` through `K3`).

## Vacuity attack

Neither conclusion is vacuous or threshold-slack. `Hₚ(S³;ℤ)` is `ℤ` at `p = 3`
(`KummerRP3HomologyUnconditional`'s input tables) and `H₄(T⁴;ℤ) ≅ ℤ ≠ 0`
(`KummerHomologyT4Full.torusFourH4EquivInt`), so `p > n` cannot be weakened to `p ≥ n`; and the
freeness half is not automatic — `H₃(ℝP³;ℤ) ≅ ℤ` is free but `H₁(ℝP³;ℤ) ≅ ℤ/2` is not, so freeness
genuinely is a top-degree phenomenon rather than a property of the space.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.SingularCSCVanishAboveGeomInt
import SKEFTHawking.SingularRelativeEmptyInt

namespace SKEFTHawking.SingularCompactManifoldTopVanishInt

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularRelHomologyInt (RelHomologyInt)
open SKEFTHawking.SingularGoodCompactInt (vanishAboveInt)
open SKEFTHawking.SingularTopHomologyFreeUnionInt (HballFreeInt hballFreeInt_dim4)
open SKEFTHawking.SingularCSCVanishAboveGeomInt (vanishAbove_cofinalInt)
open SKEFTHawking.SingularRelativeEmptyInt (relHomologyEmptyEquivInt)

noncomputable section

variable {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]

/-- **The whole-manifold good-compact stage of a compact charted manifold.** The Hatcher-3.27
cofinality `vanishAbove_cofinalInt` run at `W = K = univ` must return `K' = M` itself, so its two
conclusions become absolute statements about `M` via `univᶜ = ∅` and `Hᵢ(M | ∅;ℤ) ≅ Hᵢ(M;ℤ)`. -/
theorem compactManifold_stage (hballFree : HballFreeInt m M) :
    (∀ p, m + 2 < p → ∀ x : Homology (TopCat.of M) p, x = 0) ∧
      Module.Free ℤ (Homology (TopCat.of M) (m + 2)) := by
  obtain ⟨K', hKK', hvan, hfree⟩ :=
    vanishAbove_cofinalInt (m := m) (M := M) hballFree (W := (Set.univ : Set M))
      isOpen_univ ⟨⟨Set.univ, isCompact_univ⟩, le_rfl⟩
  have hu : (↑K'.1 : Set M) = Set.univ := Set.univ_subset_iff.mp hKK'
  rw [hu] at hvan hfree
  rw [Set.compl_univ] at hfree
  refine ⟨fun p hp x => ?_, Module.Free.of_equiv (relHomologyEmptyEquivInt (X := TopCat.of M)
    (m + 2))⟩
  refine (relHomologyEmptyEquivInt (X := TopCat.of M) p).symm.injective ?_
  rw [map_zero]
  have hy := hvan p hp
  rw [Set.compl_univ] at hy
  exact hy _

/-- **A compact Hausdorff `n`-manifold has no homology above degree `n`** (`n = m + 2`, integral
coefficients). No orientation, no duality — only the charted structure. -/
theorem homology_high (hballFree : HballFreeInt m M) (p : ℕ) (hp : m + 2 < p)
    (x : Homology (TopCat.of M) p) : x = 0 :=
  (compactManifold_stage hballFree).1 p hp x

/-- **The top integral homology of a compact Hausdorff `n`-manifold is free.** In particular it is
torsion-free, which is how the degree-`n` half of a Mayer–Vietoris window kills torsion in a piece. -/
theorem top_homology_free (hballFree : HballFreeInt m M) :
    Module.Free ℤ (Homology (TopCat.of M) (m + 2)) :=
  (compactManifold_stage hballFree).2

/-! ## The dimension-4 specialisations — hypothesis-free

`HballFreeInt 2` is the theorem `hballFreeInt_dim4`, so at the dimension the 16-convergence runs in
these carry nothing but the manifold structure. -/

section Dim4

variable {N : Type} [TopologicalSpace N] [T2Space N] [CompactSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) N]

/-- **`Hₚ(N;ℤ) = 0` for every `p ≥ 5` on a compact Hausdorff smooth-model 4-manifold.** -/
theorem homology_high_dim4 (p : ℕ) (hp : 4 < p) (x : Homology (TopCat.of N) p) : x = 0 :=
  homology_high (m := 2) hballFreeInt_dim4 p hp x

/-- **`H₄(N;ℤ)` is free on a compact Hausdorff smooth-model 4-manifold.** -/
theorem top_homology_free_dim4 : Module.Free ℤ (Homology (TopCat.of N) 4) :=
  top_homology_free (m := 2) (M := N) hballFreeInt_dim4

end Dim4

end

end SKEFTHawking.SingularCompactManifoldTopVanishInt
