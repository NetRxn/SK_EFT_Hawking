import Mathlib
import SKEFTHawking.SingularConvexRadialRetract
import SKEFTHawking.SingularReducedH0
import SKEFTHawking.SingularH0PathConnected
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularGoodCompactEuclidean

/-!
# Phase 5q.G (G1 (1,2)-window extension, X1) — the complement of a convex compact is
path-connected; `H₁(ℝᵐ⁺² | K) = 0`

For a convex compact `K ⊂ ℝᵐ⁺²`: every point of `Kᶜ` joins its radial projection onto a large
sphere `S(O, R+1) ⊇ K`-enclosing (the radial segment stays out of `K` — outward legs by
convexity (`convex_radial_not_mem`), inward legs by staying outside `closedBall O R`), and the
sphere is path-connected in rank `≥ 2` (`isPathConnected_sphere`). Hence `Kᶜ` is path-connected,
`H̃₀(Kᶜ) = 0`, and the bottom pair-LES (`SingularReducedH0`) kills `H₁(ℝᵐ⁺² | K)` — the missing
`i = 1` companion of `vanishMiddle_convexCompact`, the base-case input of the `(1,2)`-window.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularEuclideanAcyclic SKEFTHawking.SingularConvexRadialRetract
open SKEFTHawking.SingularReducedH0 SKEFTHawking.SingularH0 SKEFTHawking.SingularPairLES

namespace SKEFTHawking.SingularConvexComplementConnected

variable {n : ℕ}

/-- **The radial-segment membership**: for `x ∉ K` (`K` convex ∋ `O`, `K ⊆ closedBall O R`) and
any scale `s` that is `≥ 1` or `≥ (R+1)·‖x-O‖⁻¹`, the point `O + s•(x-O)` stays out of `K` —
outward by convexity, inward by norm. -/
theorem radial_point_not_mem {K : Set (EuclideanSpace ℝ (Fin n))} (hKconv : Convex ℝ K)
    {O x : EuclideanSpace ℝ (Fin n)} (hOK : O ∈ K) (hx : x ∉ K) (hxO : x ≠ O)
    {R : ℝ} (hKR : K ⊆ Metric.closedBall O R)
    {s : ℝ} (hs : (R + 1) * ‖x - O‖⁻¹ ≤ s ∨ 1 ≤ s) :
    O + s • (x - O) ∉ K := by
  rcases hs with hs | hs
  · rcases le_total 1 s with h1 | h1
    · exact convex_radial_not_mem hKconv hOK hx h1
    · intro hmem
      have hball := hKR hmem
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs] at hball
      have hnpos : (0 : ℝ) < ‖x - O‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxO)
      have hRpos : (0 : ℝ) < R + 1 := by
        have h0R : (0 : ℝ) ≤ R := by
          have := hKR hOK
          rw [Metric.mem_closedBall, dist_self] at this
          exact this
        linarith
      have hspos : (0 : ℝ) ≤ s :=
        le_trans (le_of_lt (mul_pos hRpos (inv_pos.mpr hnpos))) hs
      rw [abs_of_nonneg hspos] at hball
      have hge : R + 1 ≤ s * ‖x - O‖ := by
        have := mul_le_mul_of_nonneg_right hs hnpos.le
        rwa [mul_assoc, inv_mul_cancel₀ hnpos.ne', mul_one] at this
      linarith
  · exact convex_radial_not_mem hKconv hOK hx hs

/-- **Every point of `Kᶜ` joins its sphere projection within `Kᶜ`**: the radial path
`t ↦ O + (1 + t·(a-1))•(x-O)` (`a := (R+1)·‖x-O‖⁻¹`) from `x` to `O + a•(x-O) ∈ S(O, R+1)`. -/
theorem joinedIn_sphereProj {K : Set (EuclideanSpace ℝ (Fin n))} (hKconv : Convex ℝ K)
    {O x : EuclideanSpace ℝ (Fin n)} (hOK : O ∈ K) (hx : x ∈ Kᶜ)
    {R : ℝ} (hKR : K ⊆ Metric.closedBall O R) :
    JoinedIn (Kᶜ) x (O + ((R + 1) * ‖x - O‖⁻¹) • (x - O)) := by
  have hxO : x ≠ O := fun h => hx (h ▸ hOK)
  set a : ℝ := (R + 1) * ‖x - O‖⁻¹ with hadef
  have hcont : Continuous (fun t : unitInterval => O + (1 + (t : ℝ) * (a - 1)) • (x - O)) :=
    continuous_const.add ((continuous_const.add
      ((continuous_subtype_val).mul continuous_const)).smul continuous_const)
  refine ⟨⟨⟨fun t => O + (1 + (t : ℝ) * (a - 1)) • (x - O), hcont⟩, ?_, ?_⟩, fun t => ?_⟩
  · show O + ((1 : ℝ) + 0 * (a - 1)) • (x - O) = x
    rw [zero_mul, add_zero, one_smul, add_sub_cancel]
  · show O + ((1 : ℝ) + 1 * (a - 1)) • (x - O) = O + a • (x - O)
    rw [one_mul]
    ring_nf
  · show O + (1 + (t : ℝ) * (a - 1)) • (x - O) ∈ Kᶜ
    refine radial_point_not_mem hKconv hOK hx hxO hKR ?_
    rcases le_total a 1 with ha | ha
    · left
      have h1 : (t : ℝ) * (a - 1) ≥ 1 * (a - 1) :=
        mul_le_mul_of_nonpos_right (unitInterval.le_one t) (by linarith)
      rw [← hadef]
      linarith
    · right
      have h1 : (0 : ℝ) ≤ (t : ℝ) * (a - 1) :=
        mul_nonneg (unitInterval.nonneg t) (by linarith)
      linarith

/-- **The complement of a convex compact in `ℝᵐ⁺²` is path-connected** — through the enclosing
sphere `S(O, R+1)`, which is path-connected in rank `m+2 ≥ 2`. -/
theorem isPathConnected_compl_convexCompact {m : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hKconv : Convex ℝ K) (hKcomp : IsCompact K) (hKne : K.Nonempty) :
    IsPathConnected (Kᶜ) := by
  obtain ⟨O, hOK⟩ := hKne
  obtain ⟨R, hKR⟩ := hKcomp.isBounded.subset_closedBall O
  have hR0 : (0 : ℝ) ≤ R := by
    have := hKR hOK
    rwa [Metric.mem_closedBall, dist_self] at this
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (m + 2))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < m + 2)
  have hsphere : IsPathConnected (Metric.sphere O (R + 1)) :=
    isPathConnected_sphere hrank O (by linarith)
  have hsphere_sub : Metric.sphere O (R + 1) ⊆ Kᶜ := by
    intro q hq
    intro hqK
    have := hKR hqK
    rw [Metric.mem_closedBall] at this
    rw [Metric.mem_sphere] at hq
    linarith
  -- the projection of any complement point lies on the sphere
  have hproj_mem : ∀ x, x ∈ Kᶜ →
      O + ((R + 1) * ‖x - O‖⁻¹) • (x - O) ∈ Metric.sphere O (R + 1) := by
    intro x hx
    have hxO : x ≠ O := fun h => hx (h ▸ hOK)
    have hnpos : (0 : ℝ) < ‖x - O‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxO)
    rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), mul_assoc, inv_mul_cancel₀ hnpos.ne', mul_one]
  -- base point: any sphere point
  obtain ⟨p₀, hp₀⟩ := hsphere.nonempty
  refine ⟨p₀, hsphere_sub hp₀, fun y hy => ?_⟩
  have hyj := joinedIn_sphereProj hKconv hOK hy hKR
  have hsj : JoinedIn (Kᶜ) p₀ (O + ((R + 1) * ‖y - O‖⁻¹) • (y - O)) :=
    (hsphere.joinedIn p₀ hp₀ _ (hproj_mem y hy)).mono hsphere_sub
  exact hsj.trans hyj.symm

/-- **X1: `H₁(ℝᵐ⁺² | K) = 0` for a convex compact `K`** — the bottom pair-LES: the connecting
`δ : H₁(ℝⁿ, ℝⁿ∖K) → H₀(ℝⁿ∖K)` is injective (`H₁(ℝⁿ) = 0`) with range `ker ε̄` (`ε̄_{ℝⁿ}`
injective), and `ε̄_{ℝⁿ∖K}` is injective (the complement is path-connected), so `δx = 0`. -/
theorem relHomology_one_convexCompact {m : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hKconv : Convex ℝ K) (hKcomp : IsCompact K)
    (x : RelativeHomology (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ) (0 + 1)) :
    x = 0 := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · -- `K = ∅`: the pair is `(ℝⁿ, ℝⁿ)`, whose relative homology vanishes
    subst hKe
    exact SKEFTHawking.SingularGoodCompactEuclidean.relativeHomology_compl_empty_eq_zero
      (X := SingularEuclideanAcyclic.Eucl (m + 2)) (0 + 1) x
  · haveI hpcs : PathConnectedSpace
        ↥(sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ)) :=
      isPathConnected_iff_pathConnectedSpace.mp
        (isPathConnected_compl_convexCompact hKconv hKcomp hKne)
    have hδinj : Function.Injective
        (connecting (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ) 0) :=
      connecting_zero_injective_of_acyclic (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ)
        (fun w => SKEFTHawking.SingularManifoldFundamentalClass.eucl_homology_zero (m + 2) 0 w)
    have hrange := connecting_zero_range_of_augH_injective
      (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ) (eucl_augH_injective (m + 2))
    have haug : Function.Injective
        (augH (sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ))) :=
      SKEFTHawking.SingularH0PathConnected.augH_injective
    have h0 : connecting (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ) 0 x = 0 := by
      have hker : connecting (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ) 0 x
          ∈ LinearMap.ker (augH (sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ))) := by
        rw [← hrange]
        exact LinearMap.mem_range_self _ x
      exact haug (by rw [LinearMap.mem_ker.mp hker, map_zero])
    exact hδinj (by rw [h0, map_zero])

end SKEFTHawking.SingularConvexComplementConnected
