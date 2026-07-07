/-
# Phase 5q.H (E1 CSC-PD tower) — the middle sphere homology vanishes (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularSphereMiddle`: `H_j(Sⁿ;ℤ) = 0` for `0 < j < n`.

* `sphere_homology_oneInt` (`H₁(Sⁿ;ℤ) = 0`, `n ≥ 2`): the bottom suspension iso `bottomSuspEquivInt`
  identifies `H₁(Sⁿ;ℤ)` with `ker ε̄` of the doubly-punctured sphere, which is path-connected (`n ≥ 2`,
  `restr_doubly_punctured_pathConnected`, coeff-agnostic), so `ε̄` is injective (`augHInt_injective_
  pathConnected`) and the kernel is `⊥`.
* `sphere_homology_middleInt`: downward `dimReductionEquivInt` induction on `j`, terminating at
  `sphere_homology_oneInt`.

This is the `sphere_homology_middle` input of `vanishMiddle_convexCompactInt` (the base-case B3 CSC-vanishing).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSphereMiddle
import SKEFTHawking.SingularH0PathConnectedInt
import SKEFTHawking.SingularSphereHomologyInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularLineMinusPointInt (augHInt bottomSuspMapInt bottomSuspMapInt_injective
  bottomSuspMapInt_range)
open SKEFTHawking.SingularSphereAcyclic (Sph antipode ne_antipode)
open SKEFTHawking.SingularSphereBottom (basePoint)
open SKEFTHawking.SingularSphereMiddle (restr_doubly_punctured_pathConnected)
open SKEFTHawking.SingularH0PathConnectedInt (augHInt_injective_pathConnected)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularSphereMiddleInt

/-- **`H₁(Sⁿ;ℤ) = 0`** for `n ≥ 2`: the doubly-punctured sphere is path-connected, so `ε̄` is injective,
`ker ε̄ = ⊥`, and the bottom suspension (into `ker ε̄`) is `0`; injective ⟹ `x = 0`. -/
theorem sphere_homology_oneInt {n : ℕ} (hn : 2 ≤ n) (x : Homology (Sph n) 1) : x = 0 := by
  set v := basePoint n with hv
  have hpc : IsPathConnected (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)) :=
    restr_doubly_punctured_pathConnected n hn v
  haveI : PathConnectedSpace ↑(sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))) :=
    isPathConnected_iff_pathConnectedSpace.mp hpc
  have hker : LinearMap.ker (augHInt (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)))) = ⊥ :=
    LinearMap.ker_eq_bot.mpr augHInt_injective_pathConnected
  have h0 : bottomSuspMapInt n v x = 0 := by
    have hmem : bottomSuspMapInt n v x
        ∈ LinearMap.ker (augHInt (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)))) := by
      rw [← bottomSuspMapInt_range]; exact ⟨x, rfl⟩
    rw [hker] at hmem
    exact hmem
  exact bottomSuspMapInt_injective (by rw [h0, map_zero])

/-- **The middle sphere homology vanishes** (integral): `H_j(Sⁿ;ℤ) = 0` for `0 < j < n`, by downward
`dimReductionEquivInt` induction on `j` terminating at `sphere_homology_oneInt`. -/
theorem sphere_homology_middleInt :
    ∀ (j n : ℕ), 0 < j → j < n → ∀ x : Homology (Sph n) j, x = 0 := by
  intro j
  induction j with
  | zero => intro n h0 _ _; exact absurd h0 (lt_irrefl 0)
  | succ k ih =>
    intro n _ hlt x
    match k, n, hlt with
    | 0, n, hlt =>
      exact sphere_homology_oneInt (by omega) x
    | k + 1, n + 1, hlt =>
      have hred := SingularSphereHomologyInt.dimReductionEquivInt (n := n + 1) (basePoint (n + 1)) k
      rw [← LinearEquiv.map_eq_zero_iff hred]
      exact ih n (Nat.succ_pos k) (by omega) (hred x)

end SKEFTHawking.SingularSphereMiddleInt
