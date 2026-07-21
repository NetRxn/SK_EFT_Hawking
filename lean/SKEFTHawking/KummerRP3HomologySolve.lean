import Mathlib
import SKEFTHawking.KummerRP3SmithSES

/-!
# `H₂(ℝP³;ℤ) = 0` and `H₁(ℝP³;ℤ) ≅ ℤ/2` — the low-degree Smith solve

The payoff of the transfer engine: chaining the SES-III long exact sequence
(`… → Hₙ(S³) → Hₙ(ℝP³) --δ--> Hₙ₋₁(B) → …`) against the banked inputs

* `H₂(S³;ℤ) = H₁(S³;ℤ) = 0` (`KummerRP3SphereHomeo`),
* `H₁(B;ℤ) = 0`, `H₀(B;ℤ) ≅ ℤ/2`, `H₀(B) → H₀(S³) = 0` (`KummerRP3SmithSES`),

gives the K7-consumable headliners:

* **`rp3_homology_two_eq_zero`** — `H₂(ℝP³;ℤ) = 0`: the seam carrier contributes NOTHING to the
  `b₂ = 22` accounting (each of the 16 seam `ℝP³`s), the priority target of the K7 opener;
* **`seam_homology_two_eq_zero`** — the seam-level corollary through
  `eIndexProdHnEquivInt`: `H₂(seam;ℤ) = 0` for the full 16-copy seam `EIndex × ℝP³`;
* **`rp3H1EquivZMod2`** — `H₁(ℝP³;ℤ) ≅ ℤ/2`: the connecting map `δ₀` is an isomorphism onto the
  norm-parity group `H₀(B;ℤ) ≅ ℤ/2`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerRP3Covering (S3top RP3top)
open SKEFTHawking.SingularHomologyInt (chainBoundary Homology)
open SKEFTHawking.ChainComplexLESInt
open SKEFTHawking.KummerRP3SmithSES

namespace SKEFTHawking.KummerRP3HomologySolve

noncomputable section

/-! ## §1. `H₂(ℝP³;ℤ) = 0` -/

/-- Engine form: `Hml`-`H₂(ℝP³;ℤ) = 0`. In the SES-III LES,
`H₂(S³) → H₂(ℝP³) --δ₁--> H₁(B)` has both flanks zero. -/
theorem hml_rp3_two_eq_zero (x : Hml (chainBoundary RP3top) 2) : x = 0 := by
  have hdel : deltaIII 1 x = 0 := hmlB_one_eq_zero _
  obtain ⟨y, hy⟩ := (exact_projH_deltaIII 1 x).mp hdel
  rw [← hy, hml_s3_two_eq_zero y, map_zero]

/-- **`H₂(ℝP³;ℤ) = 0`** — the K7 seam carrier has no integral second homology: the seam
contributes `0` to the `b₂ = 22` Mayer–Vietoris accounting. THE priority target of the
`H_*(ℝP³)` program. -/
theorem rp3_homology_two_eq_zero (x : Homology (TopCat.of RP3) 2) : x = 0 := by
  have h := hml_rp3_two_eq_zero ((hmlEquivHomology RP3top 2).symm x)
  have h2 := congrArg (hmlEquivHomology RP3top 2) h
  rwa [LinearEquiv.apply_symm_apply, map_zero] at h2

/-- **`H₂(seam;ℤ) = 0`** — the full 16-copy K7 seam `EIndex × ℝP³` has no integral second
homology, through the banked seam splitting `eIndexProdHnEquivInt`. This is the seam input the
K7 `b₂` accounting consumes. -/
theorem seam_homology_two_eq_zero
    (x : Homology (TopCat.of (SKEFTHawking.KummerWeld.EIndex × RP3)) 2) : x = 0 := by
  set e := SKEFTHawking.SingularFiniteProdDiscreteHnInt.eIndexProdHnEquivInt 2
  have hcomp : e x = 0 := by
    funext i
    exact rp3_homology_two_eq_zero (e x i)
  have h2 := congrArg e.symm hcomp
  rwa [LinearEquiv.symm_apply_apply, map_zero] at h2

/-! ## §2. `H₁(ℝP³;ℤ) ≅ ℤ/2` -/

/-- The SES-III connecting `δ₀ : H₁(ℝP³) → H₀(B)` is injective (`H₁(S³) = 0`). -/
theorem deltaIII_zero_injective : Function.Injective (deltaIII 0) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  obtain ⟨y, hy⟩ := (exact_projH_deltaIII 0 x).mp hx
  rw [← hy, hml_s3_one_eq_zero y, map_zero]

/-- The SES-III connecting `δ₀ : H₁(ℝP³) → H₀(B)` is surjective (`H₀(B) → H₀(S³)` is zero). -/
theorem deltaIII_zero_surjective : Function.Surjective (deltaIII 0) := by
  intro k
  exact (exact_deltaIII_inclBH 0 k).mp (inclBH_zero k)

/-- Engine form: `δ₀ : H₁(ℝP³;ℤ) ≅ H₀(B;ℤ)`. -/
def deltaIIIZeroEquiv : Hml (chainBoundary RP3top) 1 ≃ₗ[ℤ] Hml dB 0 :=
  LinearEquiv.ofBijective (deltaIII 0) ⟨deltaIII_zero_injective, deltaIII_zero_surjective⟩

/-- **`H₁(ℝP³;ℤ) ≅ ℤ/2`** — the fundamental group's abelianization is the deck group: the
connecting map onto the norm-parity group `H₀(B;ℤ) ≅ ℤ/2`. -/
def rp3H1EquivZMod2 : Homology (TopCat.of RP3) 1 ≃ₗ[ℤ] ZMod 2 :=
  ((hmlEquivHomology RP3top 1).symm.trans deltaIIIZeroEquiv).trans hmlB_zero_equiv

/-- **`H₁(seam;ℤ) ≅ (ℤ/2)¹⁶`** — the full 16-copy K7 seam's integral first homology, one deck
class per exceptional copy, through the banked seam splitting `eIndexProdHnEquivInt`. -/
def seamH1EquivPi :
    Homology (TopCat.of (SKEFTHawking.KummerWeld.EIndex × RP3)) 1
      ≃ₗ[ℤ] (SKEFTHawking.KummerWeld.EIndex → ZMod 2) :=
  (SKEFTHawking.SingularFiniteProdDiscreteHnInt.eIndexProdHnEquivInt 1).trans
    (LinearEquiv.piCongrRight (fun _ => rp3H1EquivZMod2))

end

end SKEFTHawking.KummerRP3HomologySolve
