import Mathlib
import SKEFTHawking.SingularCompactlySupportedOpenInt

/-!
# Phase 5q.H (E1 CSC-PD tower) — the integral open-monotone maps of `Hᵏ_c(·;ℤ)`

Integral (`ZMod 2 → ℤ`) mirror of `SingularCSCOpenMonotone`.

For opens `W ⊆ W'`, every compact `K ⊆ W` is a compact `K ⊆ W'`, so the inclusion of index posets
`CompactsIn W → CompactsIn W'` induces the **extension-by-zero map**
  `cscOpenMonotoneInt : Hᵏ_c(W;ℤ) → Hᵏ_c(W';ℤ)`
on the colimits (a `Module.DirectLimit.lift`, well-defined by `of_f`). These are the maps of the
integral compactly-supported-cohomology Mayer–Vietoris sequence
  `Hᵏ_c(U∩V;ℤ) → Hᵏ_c(U;ℤ) ⊕ Hᵏ_c(V;ℤ) → Hᵏ_c(U∪V;ℤ)`
(the diagonal `(U∩V → U, U∩V → V)` and the difference `(U → U∪V) − (V → U∪V)`), the top row of the
integral Poincaré-duality `5`-lemma ladder.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularCohomologyColimitInt SKEFTHawking.SingularCompactsInOpen
  SKEFTHawking.SingularCompactlySupportedOpenInt

namespace SKEFTHawking.SingularCSCOpenMonotoneInt

variable {M : TopCat}

/-- The index-poset inclusion `CompactsIn W → CompactsIn W'` for `W ⊆ W'` (a compact in `W` is a compact
in `W'`). -/
def compactsInIncl {W W' : Set ↑M} (hWW' : W ⊆ W') (K : CompactsIn W) : CompactsIn W' :=
  ⟨K.1, K.2.trans hWW'⟩

/-- **Compatibility of the colimit cocone with the index inclusion**: `of_{W'}` of the included `K'` after
the `W`-transition equals `of_{W'}` of the included `K` — because the `W`- and `W'`-transition maps are
the *same* `relCohomRestrictInt` (`cohomFWInt` depends only on the underlying compacts, proof-irrelevantly),
so this is `Module.DirectLimit.of_f`. The well-definedness of `cscOpenMonotoneInt`. -/
theorem cscOpenMonotoneInt_compat {W W' : Set ↑M} (hWW' : W ⊆ W') (k : ℕ) (K K' : CompactsIn W)
    (h : K ≤ K') (x : cohomGWInt W k K) :
    Module.DirectLimit.of ℤ (CompactsIn W') (cohomGWInt W' k) (cohomFWInt W' k)
        (compactsInIncl hWW' K') (cohomFWInt W k K K' h x)
      = Module.DirectLimit.of ℤ (CompactsIn W') (cohomGWInt W' k) (cohomFWInt W' k)
          (compactsInIncl hWW' K) x := by
  have hf : cohomFWInt W k K K' h x
      = cohomFWInt W' k (compactsInIncl hWW' K) (compactsInIncl hWW' K') h x := rfl
  rw [hf]
  exact Module.DirectLimit.of_f

/-- **The integral open-monotone (extension-by-zero) map** `Hᵏ_c(W;ℤ) → Hᵏ_c(W';ℤ)` for `W ⊆ W'`: the
colimit lift of `x ↦ of_{W'} (K viewed in W') x`, well-defined by `cscOpenMonotoneInt_compat`. -/
noncomputable def cscOpenMonotoneInt {W W' : Set ↑M} (hWW' : W ⊆ W') (k : ℕ) :
    CompactlySupportedCohomologyOpenInt W k →ₗ[ℤ] CompactlySupportedCohomologyOpenInt W' k :=
  Module.DirectLimit.lift ℤ (CompactsIn W) (cohomGWInt W k) (cohomFWInt W k)
    (fun K => Module.DirectLimit.of ℤ (CompactsIn W') (cohomGWInt W' k) (cohomFWInt W' k)
      (compactsInIncl hWW' K))
    (fun K K' h x => cscOpenMonotoneInt_compat hWW' k K K' h x)

/-- **Computation rule**: on a `K`-stage class `of_W K x`, the open-monotone map is `of_{W'} (K in W') x`. -/
@[simp] theorem cscOpenMonotoneInt_of {W W' : Set ↑M} (hWW' : W ⊆ W') (k : ℕ) (K : CompactsIn W)
    (x : cohomGWInt W k K) :
    cscOpenMonotoneInt hWW' k
        (Module.DirectLimit.of ℤ (CompactsIn W) (cohomGWInt W k) (cohomFWInt W k) K x)
      = Module.DirectLimit.of ℤ (CompactsIn W') (cohomGWInt W' k) (cohomFWInt W' k)
          (compactsInIncl hWW' K) x :=
  Module.DirectLimit.lift_of _ _ x

/-- **Functoriality of the open-monotone maps**: `Hᵏ_c(W;ℤ) → Hᵏ_c(W';ℤ) → Hᵏ_c(W'';ℤ)` is the single map
`Hᵏ_c(W;ℤ) → Hᵏ_c(W'';ℤ)` (the index inclusions compose). -/
theorem cscOpenMonotoneInt_comp {W W' W'' : Set ↑M} (h1 : W ⊆ W') (h2 : W' ⊆ W'') (k : ℕ) :
    (cscOpenMonotoneInt h2 k).comp (cscOpenMonotoneInt h1 k) = cscOpenMonotoneInt (h1.trans h2) k := by
  ext x
  refine Module.DirectLimit.induction_on x (fun K y => ?_)
  simp only [LinearMap.comp_apply, cscOpenMonotoneInt_of]
  rfl

end SKEFTHawking.SingularCSCOpenMonotoneInt
