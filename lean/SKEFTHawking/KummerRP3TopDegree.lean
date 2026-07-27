/-
# Phase 5q.H — the antipodal double cover is INJECTIVE on top integral homology

The seam-transport link that no in-tree module records: for the pinned antipodal covering
`p = mkRP3 : S³ → ℝP³`, the induced map

    p_* : H₃(S³;ℤ) → H₃(ℝP³;ℤ)

is **injective** (concretely it is multiplication by `±2` under the banked identifications
`s3H3EquivInt : H₃(S³;ℤ) ≅ ℤ` and `rp3H3EquivInt_unconditional : H₃(ℝP³;ℤ) ≅ ℤ`, but injectivity
is all the transport needs and it comes without pinning a sign).

## Route — no new geometry, only the banked transfer relation

`KummerRP3TransferHomology.projHomRP3_transferHml` gives `p_* ∘ tr_* = 2` in **every** degree. In
degree 3 both groups are `≅ ℤ`, so:

* `w := tr_*(u)` for a generator `u` of `H₃(ℝP³;ℤ)` has `p_* w = 2u ≠ 0`, hence `w ≠ 0`;
* in a `ℤ`-coordinatised group any two elements `x, w` satisfy `m • x = n • w` with
  `m = ⟦w⟧, n = ⟦x⟧`; applying `p_*` to `m • x = n • w` with `p_* x = 0` forces `2n • u = 0`,
  hence `n = 0`, hence `x = 0`.

The degree-2 defect of the covering therefore does **not** obstruct transporting a ℤ-linear
relation among boundary `S³` classes to the corresponding relation among boundary `ℝP³` classes:
`p_*` loses no information at all in top degree.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerRP3TransferHomology
import SKEFTHawking.KummerRP3HomologyUnconditional
import SKEFTHawking.KummerRP3SphereHomeo

namespace SKEFTHawking.KummerRP3TopDegree

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.KummerRP3Covering (S3top RP3top projHomRP3)
open SKEFTHawking.KummerRP3TransferHomology (transferHml projHomRP3_transferHml)
open SKEFTHawking.KummerRP3SphereHomeo (s3H3EquivInt)
open SKEFTHawking.KummerRP3HomologyUnconditional (rp3H3EquivInt_unconditional)

noncomputable section

/-! ## §1. A generator of `H₃(ℝP³;ℤ)` whose transfer is nonzero -/

/-- The `ℤ`-generator of `H₃(ℝP³;ℤ)` picked out by the banked coordinatisation. -/
def rp3Gen : Homology RP3top 3 := rp3H3EquivInt_unconditional.symm 1

/-- The generator has coordinate `1`. -/
theorem rp3H3EquivInt_rp3Gen : rp3H3EquivInt_unconditional rp3Gen = 1 := by
  simp only [rp3Gen, LinearEquiv.apply_symm_apply]

/-- **`H₃(ℝP³;ℤ)` detects integer multiples of the generator**: `k • rp3Gen = 0 → k = 0`. -/
theorem eq_zero_of_smul_rp3Gen_eq_zero {k : ℤ} (h : k • rp3Gen = 0) : k = 0 := by
  have h2 : rp3H3EquivInt_unconditional (k • rp3Gen) = 0 := by rw [h, map_zero]
  rwa [map_smul, rp3H3EquivInt_rp3Gen, smul_eq_mul, mul_one] at h2

/-- **`2 · rp3Gen ≠ 0`** — `H₃(ℝP³;ℤ) ≅ ℤ` is torsion-free and the generator is nonzero. -/
theorem two_smul_rp3Gen_ne_zero : (2 : ℤ) • rp3Gen ≠ 0 := fun h => by
  have := eq_zero_of_smul_rp3Gen_eq_zero h
  omega

/-- **The transfer of the generator is nonzero in `H₃(S³;ℤ)`** — it pushes forward to `2·rp3Gen`. -/
theorem transferHml_rp3Gen_ne_zero : transferHml 3 rp3Gen ≠ 0 := by
  intro h
  refine two_smul_rp3Gen_ne_zero ?_
  rw [← projHomRP3_transferHml 3 rp3Gen, h]
  exact map_zero _

/-! ## §2. Injectivity of `p_*` in top degree -/

/-- **THE TOP-DEGREE DOUBLE-COVER PUSHFORWARD IS INJECTIVE**:
`p_* : H₃(S³;ℤ) → H₃(ℝP³;ℤ)` has trivial kernel.

This is the link the seam transport needs: a ℤ-linear relation among boundary `S³` classes cannot
be destroyed by pushing it forward along the free `ℤ/2` covering, even though `p_*` is only
"multiplication by 2" on fundamental classes. -/
theorem projHomRP3_three_injective : Function.Injective (projHomRP3 3) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  set w : Homology S3top 3 := transferHml 3 rp3Gen with hw
  set m : ℤ := s3H3EquivInt w with hm
  set n : ℤ := s3H3EquivInt x with hn
  -- In a `ℤ`-coordinatised group, `m • x = n • w`.
  have hmx : m • x = n • w := by
    refine s3H3EquivInt.injective ?_
    rw [map_smul, map_smul, ← hm, ← hn, smul_eq_mul, smul_eq_mul, mul_comm]
  -- Pushing forward kills the left side and doubles the right.
  have hpush : (0 : Homology RP3top 3) = ((2 : ℤ) * n) • rp3Gen := by
    have h1 : projHomRP3 3 (m • x) = projHomRP3 3 (n • w) := by rw [hmx]
    rw [map_smul, hx, smul_zero, map_smul, hw, projHomRP3_transferHml, smul_smul] at h1
    rw [h1, mul_comm]
  -- `H₃(ℝP³;ℤ) ≅ ℤ` is torsion-free, so `2n = 0`, i.e. `n = 0`.
  have hn0 : n = 0 := by
    have h2 := eq_zero_of_smul_rp3Gen_eq_zero hpush.symm
    omega
  -- Hence `x = 0`.
  refine s3H3EquivInt.injective ?_
  rw [← hn, hn0, map_zero]

/-- **The `ℤ`-linear reading**: `p_*` is injective on top homology, so any relation detected on the
sphere side survives to the projective side. Packaged as the statement the seam transport consumes:
a nonzero top class of `S³` has nonzero image. -/
theorem projHomRP3_three_ne_zero {x : Homology S3top 3} (hx : x ≠ 0) : projHomRP3 3 x ≠ 0 :=
  fun h => hx (projHomRP3_three_injective (by rw [h, map_zero]))

end

end SKEFTHawking.KummerRP3TopDegree
