/-
# Phase 5q.H — the subdivision-to-cover engine (homologous split)

The **subdivision-to-cover engine** consumed by the capstone's last cover-glue splits. Given a
singular chain `f` supported in the union `U ∪ V` of a two-set *open* cover, barycentric subdivision
`Sd` makes `f` cover-fine after finitely many steps, so `Sdᵐ f` splits as `fU + fV` with `fU`
supported in `U` and `fV` in `V` (`SingularConnSquareCloseNC.exists_iterate_cover_split_amb`). This
module packages that raw split *together with* the subdivision chain-homotopy
(`SingularSubdivision.iterHomotopy_chainHomotopy`), so the split chain `fU + fV` is exhibited as
**homologous to `f`** with an explicit, controlled boundary correction — the precise object the
co-adapted seam splits ride on (`f ~ fU + fV`, split, controlled `∂`).

The two headline forms:
* `exists_cover_split_homologous` — the general chain: `f + (fU + fV) = ∂(Dₘ f) + Dₘ(∂f)`.
* `exists_cover_split_homologous_cycle` — a cycle (`∂f = 0`): the correction collapses to a pure
  boundary `∂(Dₘ f)`, so `fU + fV` and `f` are genuinely homologous.

Nothing here introduces new geometry: it is a faithful repackaging of the in-tree excision /
subdivision internals into the single consumable the disk-core `hbd`/`hdetAB` residuals need.
-/
import Mathlib
import SKEFTHawking.SingularConnSquareCloseNC

namespace SKEFTHawking.SingularSubdivisionToCover

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularSubdivision
open SKEFTHawking.SingularExcision

variable {X : TopCat} [T2Space ↑X]

/-- **The subdivision-to-cover engine (homologous split).** For a singular `(n+1)`-chain `f`
supported in the union `U ∪ V` of a two-set open cover, there is a subdivision count `μ` and a split
`Sdᵘ f = fU + fV` with `fU` supported in `U` and `fV` in `V` (the raw cover-fine split), together
with the subdivision chain-homotopy identity exhibiting `fU + fV` as homologous to `f`:
`f + (fU + fV) = ∂(Dᵤ f) + Dᵤ(∂f)`, where `Dᵤ = iterHomotopy X · μ` is the iterated prism operator.
The controlled-boundary split the capstone cover-glue residuals consume. -/
theorem exists_cover_split_homologous {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V) {n : ℕ}
    (f : SingularChain X (n + 1)) (hf : f ∈ subspaceChains (U ∪ V) (n + 1)) :
    ∃ (μ : ℕ) (fU fV : SingularChain X (n + 1)),
      fU ∈ subspaceChains U (n + 1) ∧ fV ∈ subspaceChains V (n + 1)
      ∧ (⇑(singularSd X (n + 1)))^[μ] f = fU + fV
      ∧ f + (fU + fV)
        = chainBoundary X (n + 1) (iterHomotopy X (n + 1) μ f)
          + iterHomotopy X n μ (chainBoundary X n f) := by
  obtain ⟨μ, fU, fV, hfU, hfV, hsplit⟩ :=
    SingularConnSquareCloseNC.exists_iterate_cover_split_amb hU hV f hf
  refine ⟨μ, fU, fV, hfU, hfV, hsplit, ?_⟩
  rw [← hsplit]
  exact (iterHomotopy_chainHomotopy X μ n f).symm

/-- **The subdivision-to-cover engine for a cycle.** When `f` is a cycle (`∂f = 0`) the boundary
correction of `exists_cover_split_homologous` collapses to a pure boundary: `f + (fU + fV) = ∂(Dᵤ f)`.
So the cover-fine split `fU + fV` is genuinely homologous to `f`. This is the form the seam cycles
(`z@⊤`, `∂cHa` — both cycles) ride on. -/
theorem exists_cover_split_homologous_cycle {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V) {n : ℕ}
    (f : SingularChain X (n + 1)) (hf : f ∈ subspaceChains (U ∪ V) (n + 1))
    (hcyc : chainBoundary X n f = 0) :
    ∃ (μ : ℕ) (fU fV : SingularChain X (n + 1)),
      fU ∈ subspaceChains U (n + 1) ∧ fV ∈ subspaceChains V (n + 1)
      ∧ (⇑(singularSd X (n + 1)))^[μ] f = fU + fV
      ∧ f + (fU + fV) = chainBoundary X (n + 1) (iterHomotopy X (n + 1) μ f) := by
  obtain ⟨μ, fU, fV, hfU, hfV, hsplit⟩ :=
    SingularConnSquareCloseNC.exists_iterate_cover_split_amb hU hV f hf
  refine ⟨μ, fU, fV, hfU, hfV, hsplit, ?_⟩
  rw [← hsplit]
  exact add_singularSd_iterate_eq_boundary hcyc μ

end SKEFTHawking.SingularSubdivisionToCover
