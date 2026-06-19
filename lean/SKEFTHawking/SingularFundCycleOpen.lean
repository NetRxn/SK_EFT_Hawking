import Mathlib
import SKEFTHawking.SingularExcision

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-C0a) — the `{W, Kᶜ}` excisive cover of a compact in an open

The first step of the **fund-cycle-in-an-open** representation (`C0`): a relative cycle for `(M, Kᶜ)`
(a representative of the fundamental class `μ_K ∈ Hₙ(M|K)`) has, after subdivision, a representative
**supported in any open `W ⊇ K`**. This needs the two-set cover `𝒰 = {W, Kᶜ}` to be **excisive** — its
interiors cover `M` — which holds exactly because a compact `K` in a Hausdorff space is closed (so
`Kᶜ` is open, `interior Kᶜ = Kᶜ`) and `K ⊆ W` open (so `interior W = W` and `W ∪ Kᶜ = univ`).

This is the geometric input that makes `relativeDualityK` instantiable in the inductive open-cover
Poincaré-duality proof (Hatcher 3.36): the fund cycle of `K` lives in `C(W)` for the open `W`, so the
cap lands in `H_{n-k}(sub W)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2

namespace SKEFTHawking.SingularFundCycleOpen

variable {X : TopCat} [T2Space ↑X]

/-- **The `{W, Kᶜ}` interiors cover `M`** when `K` is compact and `K ⊆ W` with `W` open: `interior W = W`
(open), `interior Kᶜ = Kᶜ` (`K` compact ⟹ closed ⟹ `Kᶜ` open), and `W ∪ Kᶜ = univ` (from `K ⊆ W`). This
is the excisiveness needed by `exists_iterate_smallChains` to subdivide a relative cycle into one
supported in `W`. -/
theorem interiors_cover_of_compact_subset_open {K W : Set ↑X} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) :
    (⋃ U ∈ ({W, Kᶜ} : Set (Set ↑X)), interior U) = Set.univ := by
  have hKcl : IsClosed K := hK.isClosed
  rw [Set.biUnion_insert, Set.biUnion_singleton, hW.interior_eq, hKcl.isOpen_compl.interior_eq]
  rw [Set.eq_univ_iff_forall]
  intro x
  by_cases hx : x ∈ K
  · exact Set.mem_union_left _ (hKW hx)
  · exact Set.mem_union_right _ hx

end SKEFTHawking.SingularFundCycleOpen
