/-
# Route (c′) P1 — the pair-LES connecting map is injective at the top, and detects on `S²×S²`

Route (c′) detects `a₀ ⌢ cls ≠ 0` by pushing through the homology pair long-exact-sequence
connecting map `δ : Hₙ₊₁(X,S) → Hₙ(sub S)` to the CLOSED boundary. The connecting map
(`SingularPairLES.connecting`) and its exactness leg
(`SingularPairLES.exact_homProj_connecting : Function.Exact (homProj S (n+1)) (connecting S n)`) are
already banked. This module adds the one missing corollary and its instantiation:

* **generic** `injective_connecting_of_subsingleton` — `Subsingleton (Hₙ₊₁(X)) ⟹ δ injective`
  (exactness: `homProj` is then the zero map, so `ker δ = im homProj = 0`); and
* **instantiated** at `X = SphereDisk = S²×D³`, `n = 4` with the banked
  `sphereDisk_homology_five_eq_zero` (`H₅(S²×D³;ℤ/2) = 0`): `δ = connecting sphereDiskBoundarySet 4`
  is injective, so `δ cls ≠ 0` for every `cls ≠ 0` in `H₅(S²×D³, S²×S²)`. The value `δ cls = [∂cls]`
  lives in `H₄(sub sphereDiskBoundarySet) = H₄(S²×S²)` (the closed boundary), where P3/P4 detect it.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SingularPairLES
import SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularPairLES
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots

namespace SKEFTHawking.SphereDiskConnectingDetect

/-- **The pair-LES connecting map is injective when the ambient homology vanishes.** If
`Hₙ₊₁(X;ℤ/2) = 0` (`Subsingleton`), the connecting map `δ : Hₙ₊₁(X,S) → Hₙ(sub S)` is injective: by
`exact_homProj_connecting`, `ker δ = im(homProj S (n+1))`, and `homProj` from a trivial group is the
zero map, so `ker δ = 0`. Pure exactness — reusable for ANY pair `(X, S)`. The injectivity companion of
`PinPlusKTSphereProdHomologyRoots.subsingleton_relativeHomology_of_squeeze`. -/
theorem injective_connecting_of_subsingleton {X : TopCat} (S : Set X) (n : ℕ)
    [Subsingleton (Homology X (n + 1))] :
    Function.Injective (connecting S n) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, hx⟩ := (exact_homProj_connecting S n y).mp hy
  rw [← hx, Subsingleton.elim x 0, map_zero]

/-- **The `SphereDisk` connecting map is injective at the top.** `δ = connecting sphereDiskBoundarySet 4
: H₅(S²×D³, S²×S²) → H₄(S²×S²)` is injective (from `H₅(S²×D³) = 0`). Proved inline (exactness + the
banked `sphereDisk_homology_five_eq_zero`) to avoid instance-synthesis blowup on the concrete type. -/
theorem connecting_sphereDiskBoundary_injective :
    Function.Injective (connecting (X := TopCat.of SphereDisk) sphereDiskBoundarySet 4) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, hx⟩ := (exact_homProj_connecting (X := TopCat.of SphereDisk) sphereDiskBoundarySet 4 y).mp hy
  rw [← hx, sphereDisk_homology_five_eq_zero x, map_zero]

/-- **The connecting map sends nonzero relative classes to nonzero boundary classes.** For
`cls ≠ 0` in `H₅(S²×D³, S²×S²)`, `[∂cls] = connecting sphereDiskBoundarySet 4 cls ≠ 0` in `H₄(S²×S²)` —
the detection handle P3/P4 consume. -/
theorem connecting_sphereDiskBoundary_ne_zero
    (cls : RelativeHomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 5) (h : cls ≠ 0) :
    connecting (X := TopCat.of SphereDisk) sphereDiskBoundarySet 4 cls ≠ 0 := by
  intro hc
  apply h
  exact connecting_sphereDiskBoundary_injective (by rw [hc, map_zero])

end SKEFTHawking.SphereDiskConnectingDetect
