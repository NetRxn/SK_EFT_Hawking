/-
# Phase 5q.H — detection is a relative-homology invariant (the homologous-perturbation transfer)

The straddle/interior detection `relClassOf T m c ≠ 0` is a property of the *relative homology class*
of the almost-cycle `c`, not of the chosen representative. `SingularRelativeCoverMV` already records
the **away-chain** invariance (`relClassOf_eq_of_congr`: `c = p + e` with `e` supported off `T`). This
module adds the **boundary** invariance — the piece the away-chain form is missing:

* `relClassOf_boundary_eq_zero` — a boundary `∂w` has zero relative class (it is a relative boundary).
* `relClassOf_eq_of_homologous` — the full homologous-perturbation transfer: `c = p + ∂w + e` with
  `e` supported in `E ⊆ T` gives `relClassOf T c = relClassOf T p`.

This is the load-bearing tool that lets a *controlled* representative (one whose boundary is
computable) inherit the interior-generator detection of a canonical `.choose` representative to which
it is homologous: the two differ by a boundary `∂w` plus a chain supported in the boundary support
`E ⊆ {y}ᶜ`, so detection transfers point-by-point. It also transfers detection across barycentric
subdivision (`c + Sdᵐ c = ∂(Dₘ c)` — the subdivision-to-cover engine's homotopy correction).
-/
import Mathlib
import SKEFTHawking.SingularRelativeCoverMV

namespace SKEFTHawking.SingularRelClassHomologous

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularRelativeCoverMV

variable {X : TopCat}

/-- **A boundary has zero relative class.** The almost-cycle `∂w` is a relative boundary
(`relBoundary [w] = [∂w]`), so its `(X, T)`-class vanishes for every `T`. -/
theorem relClassOf_boundary_eq_zero (T : Set ↑X) (m : ℕ) (w : SingularChain X (m + 3))
    (hbw : chainBoundary X (m + 1) (chainBoundary X (m + 2) w) ∈ subspaceChains T (m + 1)) :
    relClassOf T m (chainBoundary X (m + 2) w) hbw = 0 := by
  rw [relClassOf, RelativeHomology.mk_eq_zero_iff]
  exact ⟨RelativeChain.mk T (m + 3) w, relBoundary_mk T (m + 2) w⟩

/-- **Homologous-perturbation transfer of the relative class.** If `c` differs from `p` by a boundary
`∂w` and a chain `e` supported in a subspace `E ⊆ T`, then `c` and `p` have the same `(X, T)`-class.
With `T = {y}ᶜ` and `E` the boundary support of the interior point `y`, this transfers the local
interior-generator detection from any homologous representative `p` to `c` — the tool a controlled
disk representative uses to inherit `diskDetectChain`'s detection while exposing a computable boundary.
Generalises `relClassOf_eq_of_congr` (the `w = 0` case). -/
theorem relClassOf_eq_of_homologous {T E : Set ↑X} (hET : E ⊆ T) (m : ℕ)
    {c p e : SingularChain X (m + 2)} {w : SingularChain X (m + 3)}
    (hcongr : c = p + chainBoundary X (m + 2) w + e) (he : e ∈ subspaceChains E (m + 2))
    (hc : chainBoundary X (m + 1) c ∈ subspaceChains T (m + 1))
    (hp : chainBoundary X (m + 1) p ∈ subspaceChains T (m + 1)) :
    relClassOf T m c hc = relClassOf T m p hp := by
  have hbe : chainBoundary X (m + 1) e ∈ subspaceChains T (m + 1) :=
    subspaceChains_mono hET (m + 1)
      (SingularRelativeHomologyMod2.chainBoundary_mem_subspaceChains (S := E) (m + 1) e he)
  have hbw : chainBoundary X (m + 1) (chainBoundary X (m + 2) w) ∈ subspaceChains T (m + 1) := by
    rw [chainBoundary_chainBoundary_apply]; exact Submodule.zero_mem _
  have hpw : chainBoundary X (m + 1) (p + chainBoundary X (m + 2) w) ∈ subspaceChains T (m + 1) := by
    rw [map_add]; exact Submodule.add_mem _ hp hbw
  subst hcongr
  rw [relClassOf_add T m (p + chainBoundary X (m + 2) w) e hpw hbe,
    relClassOf_add T m p (chainBoundary X (m + 2) w) hp hbw,
    relClassOf_boundary_eq_zero T m w hbw,
    relClassOf_eq_zero_of_subspace hET m e he hbe, add_zero, add_zero]

end SKEFTHawking.SingularRelClassHomologous
