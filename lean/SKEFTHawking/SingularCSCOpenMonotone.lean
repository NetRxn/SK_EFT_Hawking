import Mathlib
import SKEFTHawking.SingularCompactlySupportedOpen

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6c) — the open-monotone maps of `Hᵏ_c`

For opens `W ⊆ W'`, every compact `K ⊆ W` is a compact `K ⊆ W'`, so the inclusion of index posets
`CompactsIn W → CompactsIn W'` induces the **extension-by-zero map**
  `cscOpenMonotone : Hᵏ_c(W) → Hᵏ_c(W')`
on the colimits (a `Module.DirectLimit.lift`, well-defined by `of_f`). These are the maps of the
compactly-supported-cohomology Mayer–Vietoris sequence
  `Hᵏ_c(U∩V) → Hᵏ_c(U) ⊕ Hᵏ_c(V) → Hᵏ_c(U∪V)`
(the diagonal `(U∩V → U, U∩V → V)` and the difference `(U → U∪V) − (V → U∪V)`), the top row of the
Poincaré-duality `5`-lemma ladder.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularCohomologyColimit SKEFTHawking.SingularCompactsInOpen
  SKEFTHawking.SingularCompactlySupportedOpen

namespace SKEFTHawking.SingularCSCOpenMonotone

variable {M : TopCat}

/-- The index-poset inclusion `CompactsIn W → CompactsIn W'` for `W ⊆ W'` (a compact in `W` is a compact
in `W'`). -/
def compactsInIncl {W W' : Set ↑M} (hWW' : W ⊆ W') (K : CompactsIn W) : CompactsIn W' :=
  ⟨K.1, K.2.trans hWW'⟩

/-- **Compatibility of the colimit cocone with the index inclusion**: `of_{W'}` of the included `K'` after
the `W`-transition equals `of_{W'}` of the included `K` — because the `W`- and `W'`-transition maps are
the *same* `relCohomRestrict` (`cohomFW` depends only on the underlying compacts, proof-irrelevantly), so
this is `Module.DirectLimit.of_f`. The well-definedness of `cscOpenMonotone`. -/
theorem cscOpenMonotone_compat {W W' : Set ↑M} (hWW' : W ⊆ W') (k : ℕ) (K K' : CompactsIn W)
    (h : K ≤ K') (x : cohomGW W k K) :
    Module.DirectLimit.of (ZMod 2) (CompactsIn W') (cohomGW W' k) (cohomFW W' k)
        (compactsInIncl hWW' K') (cohomFW W k K K' h x)
      = Module.DirectLimit.of (ZMod 2) (CompactsIn W') (cohomGW W' k) (cohomFW W' k)
          (compactsInIncl hWW' K) x := by
  have hf : cohomFW W k K K' h x
      = cohomFW W' k (compactsInIncl hWW' K) (compactsInIncl hWW' K') h x := rfl
  rw [hf]
  exact Module.DirectLimit.of_f

/-- **The open-monotone (extension-by-zero) map** `Hᵏ_c(W) → Hᵏ_c(W')` for `W ⊆ W'`: the colimit lift of
`x ↦ of_{W'} (K viewed in W') x`, well-defined by `cscOpenMonotone_compat`. -/
noncomputable def cscOpenMonotone {W W' : Set ↑M} (hWW' : W ⊆ W') (k : ℕ) :
    CompactlySupportedCohomologyOpen W k →ₗ[ZMod 2] CompactlySupportedCohomologyOpen W' k :=
  Module.DirectLimit.lift (ZMod 2) (CompactsIn W) (cohomGW W k) (cohomFW W k)
    (fun K => Module.DirectLimit.of (ZMod 2) (CompactsIn W') (cohomGW W' k) (cohomFW W' k)
      (compactsInIncl hWW' K))
    (fun K K' h x => cscOpenMonotone_compat hWW' k K K' h x)

/-- **Computation rule**: on a `K`-stage class `of_W K x`, the open-monotone map is `of_{W'} (K in W') x`. -/
@[simp] theorem cscOpenMonotone_of {W W' : Set ↑M} (hWW' : W ⊆ W') (k : ℕ) (K : CompactsIn W)
    (x : cohomGW W k K) :
    cscOpenMonotone hWW' k
        (Module.DirectLimit.of (ZMod 2) (CompactsIn W) (cohomGW W k) (cohomFW W k) K x)
      = Module.DirectLimit.of (ZMod 2) (CompactsIn W') (cohomGW W' k) (cohomFW W' k)
          (compactsInIncl hWW' K) x :=
  Module.DirectLimit.lift_of _ _ x

end SKEFTHawking.SingularCSCOpenMonotone
