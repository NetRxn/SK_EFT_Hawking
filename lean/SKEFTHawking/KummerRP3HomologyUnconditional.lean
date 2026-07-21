/-
# The unconditional `H_*(ℝP³;ℤ)` table: `H₃ ≅ ℤ` and `Hₙ = 0` for `n ≥ 4` — the FEED

Discharges the two geometric termination hypotheses of `KummerRP3HomologyTop`
(`h4 : H₄(ℝP³;ℤ) = 0`, `h5 : H₅(ℝP³;ℤ) = 0`) and ships the **unconditional** top half of the
`H_*(ℝP³;ℤ)` table on the pinned `ℂ²`-carrier `RP3top`:

* the Euclidean-carrier vanishing (`KummerRP3GoodCoverTelescope.rp3E_homology_high`, the 4-chart
  good-cover Mayer–Vietoris telescope) transports along the **descended coordinate
  homeomorphism** `transportHomeo : ℝP³_𝔼 ≃ₜ ℝP³` — `sphToS3` intertwines the Euclidean antipode
  with `negS3` (`sphToS3_neg_smul`), so it descends to a continuous open bijection of the
  antipodal quotients (open via the banked covering map `rp3_isCoveringMap`);
* **`rp3_homology_four_eq_zero` / `rp3_homology_five_eq_zero`** — the discharged inputs;
* **`rp3_homology_high_unconditional`** — `Hₙ(ℝP³;ℤ) = 0` for all `n ≥ 4`, hypothesis-free, by
  feeding the discharged inputs to `KummerRP3HomologyTop.rp3_homology_high`;
* **`rp3H3EquivInt_unconditional : H₃(ℝP³;ℤ) ≃ₗ[ℤ] ℤ`** — the fundamental class of the closed
  orientable `3`-manifold, hypothesis-free, by feeding the same inputs to
  `KummerRP3HomologyTop.rp3H3EquivInt`.

Together with the banked unconditional `H₀ ≅ ℤ` (`KummerK7Opener`), `H₁ ≅ ℤ/2`
(`KummerRP3H1Pin`), and `H₂ = 0` (`KummerRP3HomologySolve`), this completes the unconditional
integral homology table of `ℝP³` on the project's pinned carrier.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.KummerRP3GoodCoverTelescope
import SKEFTHawking.KummerRP3HomologyTop
import SKEFTHawking.SingularFiniteProdDiscreteHnInt

open Metric Topology
open SKEFTHawking.KummerK7Opener (eucToC2)
open SKEFTHawking.KummerResolutionPiece (S3 RP3 mkRP3 negS3 mkRP3_neg continuous_mkRP3)
open SKEFTHawking.KummerRP3Covering (S3top RP3top)
open SKEFTHawking.KummerRP3SphereHomeo (sphToS3 sphToS3_injective sphToS3_surjective sphHomeoS3)
open SKEFTHawking.KummerRP3CoveringMap (rp3_isCoveringMap fiber_pair)
open SKEFTHawking.KummerRP3EuclCharts
open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFiniteProdDiscreteHnInt (homologyCongrInt)
open SKEFTHawking.KummerRP3GoodCoverTelescope (rp3E_homology_high)

namespace SKEFTHawking.KummerRP3HomologyUnconditional

noncomputable section

/-! ## §1. The equivariant descent `ℝP³_𝔼 ≃ₜ ℝP³` -/

/-- The coordinate map is odd: `eucToC2 (-w)` is the componentwise negation. -/
theorem eucToC2_neg (w : EuclideanSpace ℝ (Fin 4)) :
    eucToC2 (-w) = (-(eucToC2 w).1, -(eucToC2 w).2) := by
  unfold SKEFTHawking.KummerK7Opener.eucToC2
  have hk : ∀ k : Fin 4, (-w) k = -(w k) := fun _ => rfl
  refine Prod.ext ?_ ?_
  · show Complex.equivRealProdCLM.symm ((-w) 0, (-w) 1) = _
    rw [hk 0, hk 1, show ((-(w 0), -(w 1)) : ℝ × ℝ) = -((w 0, w 1) : ℝ × ℝ) from rfl,
      map_neg]
  · show Complex.equivRealProdCLM.symm ((-w) 2, (-w) 3) = _
    rw [hk 2, hk 3, show ((-(w 2), -(w 3)) : ℝ × ℝ) = -((w 2, w 3) : ℝ × ℝ) from rfl,
      map_neg]

/-- **Equivariance**: `sphToS3` intertwines the Euclidean antipode with `negS3`. -/
theorem sphToS3_neg_smul (v : S3E) : sphToS3 ((-1 : ℤˣ) • v) = negS3 (sphToS3 v) := by
  apply Subtype.ext
  show eucToC2 (((-1 : ℤˣ) • v : S3E) : EuclideanSpace ℝ (Fin 4)) = (negS3 (sphToS3 v) : ℂ × ℂ)
  have hcoe : (((-1 : ℤˣ) • v : S3E) : EuclideanSpace ℝ (Fin 4))
      = -(v : EuclideanSpace ℝ (Fin 4)) := by
    rw [smul_coe]
    norm_num
  rw [hcoe, eucToC2_neg]
  rfl

/-- The class-level transport `ℝP³_𝔼 → ℝP³`, descending `mkRP3 ∘ sphToS3`. -/
def transportFun : RP3E → RP3 :=
  Quotient.lift (fun v : S3E => mkRP3 (sphToS3 v)) (by
    intro a b hab
    obtain ⟨u, hu⟩ := hab
    have hu' : u • b = a := hu
    rcases Int.units_eq_one_or u with h1 | h1
    · rw [h1, one_smul] at hu'
      rw [hu']
    · rw [h1] at hu'
      show mkRP3 (sphToS3 a) = mkRP3 (sphToS3 b)
      rw [← hu', sphToS3_neg_smul, mkRP3_neg])

@[simp] theorem transportFun_mkE (v : S3E) : transportFun (mkE v) = mkRP3 (sphToS3 v) := rfl

theorem continuous_transportFun : Continuous transportFun :=
  Continuous.quotient_lift (continuous_mkRP3.comp
    SKEFTHawking.KummerRP3SphereHomeo.continuous_sphToS3) _

theorem transportFun_injective : Function.Injective transportFun := by
  intro p q h
  obtain ⟨a, rfl⟩ := mkE_surjective p
  obtain ⟨b, rfl⟩ := mkE_surjective q
  rw [transportFun_mkE, transportFun_mkE] at h
  rcases fiber_pair h with heq | heq
  · rw [sphToS3_injective heq]
  · have hab : a = (-1 : ℤˣ) • b := sphToS3_injective (by rw [heq, ← sphToS3_neg_smul])
    rw [hab, mkE_neg_smul]

theorem transportFun_surjective : Function.Surjective transportFun := by
  intro q
  obtain ⟨x, hx⟩ := Quotient.exists_rep q
  obtain ⟨v, rfl⟩ := sphToS3_surjective x
  exact ⟨mkE v, hx⟩

theorem isOpenMap_transportFun : IsOpenMap transportFun := by
  intro W hW
  have himg : transportFun '' W = mkRP3 '' (sphToS3 '' (mkE ⁻¹' W)) := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨v, rfl⟩ := mkE_surjective p
      exact ⟨sphToS3 v, ⟨v, hp, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨mkE v, hv, rfl⟩
  rw [himg]
  have h1 : IsOpen (mkE ⁻¹' W) := hW.preimage continuous_mkE
  have h2 : IsOpen (sphToS3 '' (mkE ⁻¹' W)) := by
    have h3 := sphHomeoS3.isOpenMap _ h1
    exact h3
  exact rp3_isCoveringMap.isOpenMap _ h2

/-- **The descended homeomorphism `ℝP³_𝔼 ≃ₜ ℝP³`** — continuous open bijection of the antipodal
quotients. -/
def transportHomeo : (↑RP3Etop : Type) ≃ₜ (↑RP3top : Type) :=
  (Equiv.ofBijective transportFun
    ⟨transportFun_injective, transportFun_surjective⟩).toHomeomorphOfContinuousOpen
    continuous_transportFun isOpenMap_transportFun

/-- Degreewise homology transport along the descent. -/
def rp3HomologyTransport (n : ℕ) : Homology RP3Etop n ≃ₗ[ℤ] Homology RP3top n :=
  homologyCongrInt (X := RP3Etop) (Y := RP3top) transportHomeo n

/-! ## §2. The discharged termination inputs on the pinned carrier -/

/-- **`H₄(ℝP³;ℤ) = 0`** — the first geometric termination input, unconditional. -/
theorem rp3_homology_four_eq_zero (x : Homology RP3top 4) : x = 0 := by
  have h : (rp3HomologyTransport 4).symm x = 0 := rp3E_homology_high 4 (by omega) _
  have h2 := congrArg (rp3HomologyTransport 4) h
  rwa [LinearEquiv.apply_symm_apply, map_zero] at h2

/-- **`H₅(ℝP³;ℤ) = 0`** — the second geometric termination input, unconditional. -/
theorem rp3_homology_five_eq_zero (x : Homology RP3top 5) : x = 0 := by
  have h : (rp3HomologyTransport 5).symm x = 0 := rp3E_homology_high 5 (by omega) _
  have h2 := congrArg (rp3HomologyTransport 5) h
  rwa [LinearEquiv.apply_symm_apply, map_zero] at h2

/-! ## §3. The unconditional table -/

/-- **`Hₙ(ℝP³;ℤ) = 0` for every `n ≥ 4`, unconditional** — the two-step Smith recursion of
`KummerRP3HomologyTop.rp3_homology_high`, fed the discharged termination inputs. -/
theorem rp3_homology_high_unconditional (n : ℕ) (hn : 4 ≤ n) (x : Homology RP3top n) : x = 0 :=
  SKEFTHawking.KummerRP3HomologyTop.rp3_homology_high rp3_homology_four_eq_zero
    rp3_homology_five_eq_zero n hn x

/-- **`H₃(ℝP³;ℤ) ≃ₗ[ℤ] ℤ`, unconditional** — the fundamental class of the closed orientable
`3`-manifold, `KummerRP3HomologyTop.rp3H3EquivInt` fed the discharged termination inputs. -/
def rp3H3EquivInt_unconditional : Homology RP3top 3 ≃ₗ[ℤ] ℤ :=
  SKEFTHawking.KummerRP3HomologyTop.rp3H3EquivInt rp3_homology_four_eq_zero
    rp3_homology_five_eq_zero

end

end SKEFTHawking.KummerRP3HomologyUnconditional
