import Mathlib
import SKEFTHawking.SingularPDWindow2
import SKEFTHawking.SingularPDWindow
import SKEFTHawking.SingularSurfaceIntersectionForm
import SKEFTHawking.SingularFundamentalDualityEndpoint
import SKEFTHawking.SingularDualityEmpty
import SKEFTHawking.SingularOpenDualityMVConnSquare

/-!
# W-A (new-build 3) — the surface intersection form's non-degeneracy is UNCONDITIONAL

Discharges the `SingularSurfaceIntersectionForm` footnote's remaining obligation: the closed-4-
manifold deg-4 window tower (`pdWindowP`/`pdWindowP4`) has a dim-2 mirror (`SingularPDWindow2.
pdWindowP2`, the `m = 0` finite-chart-cover assembly), so `openDuality (k := 1) (m := 0)` is
bijective (in particular injective) on `univ` for a compact charted-on-`E²` surface. Composed with
the two ALREADY-generic bridges (`fundamentalDuality_injective_of_openDuality_univ_injective`,
`capH_injective_of_fundamentalDuality_injective`, both `{k m : ℕ}`-generic, no dim-2 work needed)
and the fundamental-class identification, this discharges
`intersectionForm_nondeg_of_cap_injective`'s hypothesis unconditionally.

**`intersectionForm_nondeg`**: for any closed (compact, `T2`, `Nonempty`, charted-on-`E²`) surface
`Σ`, the mod-2 intersection form on `H¹(Σ;ℤ/2)` is non-degenerate. No hypothesis-structure remains.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.SingularFundamentalClass SKEFTHawking.SingularChartBridge

namespace SKEFTHawking.SingularSurfaceIntersectionFormInstances

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (0 + 2))) M]

/-- The `P₂(univ)` package at a fundamental-class chain representative: the master cycle, its
boundary/cycle data, the local-generator property, and the class identification. The dim-2 mirror
of `SingularPD4Instances.exists_fundClass_P4_data` — no `castChain` junction is needed (the `m = 0`
window already lives at the fundamental class's native degree `0 + 2`). -/
theorem exists_fundClass_P2_data :
    ∃ (zM : SingularChain (TopCat.of M) (0 + 1 + 0 + 1))
      (hzM : chainBoundary (TopCat.of M) (0 + 1 + 0) zM = 0)
      (hcyc : zM ∈ cycles (TopCat.of M) (0 + 2)),
      (∀ x : M, SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
          (X := TopCat.of M) x (0 + 2) (Homology.mk (TopCat.of M) (0 + 2) ⟨zM, hcyc⟩)
        = (manifoldLocalIso x).symm 1)
      ∧ Homology.mk (TopCat.of M) (0 + 2) ⟨zM, hcyc⟩
        = SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 0) (M := M) := by
  obtain ⟨zc, hzc⟩ := Submodule.Quotient.mk_surjective _
    (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 0) (M := M))
  refine ⟨zc.1, LinearMap.mem_ker.mp zc.2, zc.2, ?_, ?_⟩
  · intro x
    have hclass : Homology.mk (TopCat.of M) (0 + 2) ⟨zc.1, zc.2⟩
        = SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 0) (M := M) := hzc
    rw [hclass]
    exact SKEFTHawking.SingularFundamentalClass.fundamentalClass_restricts x
  · exact hzc

/-- **The middle-dimension non-degeneracy of the closed charted surface, hypothesis-free.**
The unconditional discharge of `SingularSurfaceIntersectionForm`'s footnote: `openDuality
(k := 1) (m := 0)` bijective on `univ` (`SingularPDWindow2.pdWindowP2_univ`) feeds the two
ALREADY-generic bridges (no new dim-2 mathematics beyond the window tower itself), identifying
the resulting `capH`-injectivity's raw cycle presentation with the genuine fundamental class
`[Σ]` via `exists_fundClass_P2_data`. -/
theorem intersectionForm_nondeg :
    Function.Injective
      ⇑(SKEFTHawking.SingularSurfaceIntersectionForm.intersectionForm (M := M)) := by
  obtain ⟨zM, hzM, hcyc, hloc, hclass⟩ := exists_fundClass_P2_data (M := M)
  have hP2 := SKEFTHawking.SingularPDWindow2.pdWindowP2_univ zM hzM hcyc hloc isOpen_univ
  refine SKEFTHawking.SingularSurfaceIntersectionForm.intersectionForm_nondeg_of_cap_injective ?_
  have hinjD :=
    SKEFTHawking.SingularPDWindow.fundamentalDuality_injective_of_openDuality_univ_injective
      (M := TopCat.of M) (k := 0 + 1) (m := 0) isOpen_univ zM hzM hP2.1.injective
  have hinj := SKEFTHawking.SingularFundamentalDualityEndpoint.capH_injective_of_fundamentalDuality_injective
    (M := TopCat.of M) (k := 0 + 1) (m := 0) zM hzM hinjD
  convert hinj using 3
  exact hclass.symm

end SKEFTHawking.SingularSurfaceIntersectionFormInstances
