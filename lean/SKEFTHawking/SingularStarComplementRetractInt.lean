import Mathlib
import SKEFTHawking.SingularEuclideanSphereInt
import SKEFTHawking.SingularLocalHomologyInt
import SKEFTHawking.SingularSphereMiddleInt

/-!
# `ℝⁿ ∖ K ≃ Sⁿ⁻¹` for a star-shaped body `K` strictly inside the unit ball, and `Hₖ(ℝⁿ, ℝⁿ∖K) = 0`

`SingularConvexComplementRetract` does **not** apply to a *flat* disk `D² × {0} ⊆ ℝ⁴`: it requires
`0 ∈ interior A`, and a flat disk in `ℝ⁴` has empty interior. But the radial retraction
`p ↦ p/‖p‖` and the straight-line-in-scale homotopy `H(p,t) = t•p + (1−t)•(p/‖p‖)` — the very maps
of `SingularPuncturedRetract` — *do* work on `ℝⁿ ∖ K`, because every intermediate point is a
**positive rescaling** `s • p` with either `s ≥ 1` (so `p` would be a `[0,1]`-rescaling of `s•p`,
contradicting star-shapedness) or `‖s • p‖ ≥ 1` (contradicting `K ⊆ ball 0 1`). No interior needed —
only star-shapedness about `0` and a norm bound.

Consequently, for `K` a star-shaped body strictly inside the unit ball of `ℝᵐ⁺¹`:

* `homology_mapInt_normalizeK_bijective` — `Hₖ₊₁(ℝᵐ⁺¹ ∖ K; ℤ) ≅ Hₖ₊₁(Sᵐ; ℤ)`;
* `homology_compl_eq_zero` — `Hⱼ₊₁(ℝᵐ⁺¹ ∖ K; ℤ) = 0` for `j + 1 < m`;
* `relHomology_compl_eq_zero` — **`Hⱼ₊₂(ℝᵐ⁺¹, ℝᵐ⁺¹ ∖ K; ℤ) = 0` for `j + 2 ≤ m`** (pair LES with
  `ℝᵐ⁺¹` acyclic).

At `m = 3` (`ℝ⁴`) the last one reads `H₂(ℝ⁴ | K) = H₃(ℝ⁴ | K) = 0` — the local-homology vanishing of
a flat 2-disk in a 4-chart, which is the input the local-homology Mayer–Vietoris
(`SingularRelativeMVLESInt.relMvDeltaEquivInt`) needs at each hemisphere of a zero section.

`flatDisk n m r` (the closed flat radius-`r` `m`-disk in the first `m` coordinates of `ℝⁿ`) is
supplied as the concrete witness: `starInBall_flatDisk`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularPuncturedRetract (Sph)
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularFunctorialityInt

namespace SKEFTHawking.SingularStarComplementRetractInt

variable {n : ℕ}

/-- A **star-shaped body strictly inside the unit ball** of `ℝⁿ`: it contains the origin, is closed
under scaling by `[0,1]`, and every point has norm `< 1`.

Deliberately *not* asking for `0 ∈ interior K` — that is exactly the hypothesis
`SingularConvexComplementRetract` needs and a flat disk fails. -/
structure StarInBall (K : Set (EuclideanSpace ℝ (Fin n))) : Prop where
  zero_mem : (0 : EuclideanSpace ℝ (Fin n)) ∈ K
  smul_mem : ∀ p ∈ K, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → s • p ∈ K
  norm_lt : ∀ p ∈ K, ‖p‖ < 1

variable {K : Set (EuclideanSpace ℝ (Fin n))}

/-- A point of the complement is nonzero (the origin lies in `K`). -/
theorem ne_zero_of_mem_compl (hK : StarInBall K) {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ Kᶜ) :
    p ≠ 0 := fun h => hp (h ▸ hK.zero_mem)

theorem norm_ne_zero_of_mem_compl (hK : StarInBall K) {p : EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ Kᶜ) : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr (ne_zero_of_mem_compl hK hp)

/-- **The scaling lemma** — the engine of the whole module. A positive rescaling `s • p` of a
complement point stays in the complement as soon as *either* `s ≥ 1` (rescale back by `s⁻¹ ∈ [0,1]`
and use star-shapedness) *or* `‖s • p‖ ≥ 1` (the norm bound). -/
theorem smul_mem_compl (hK : StarInBall K) {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ Kᶜ) {s : ℝ}
    (hs : 0 < s) (hor : 1 ≤ s ∨ 1 ≤ s * ‖p‖) : s • p ∈ Kᶜ := by
  intro hmem
  rcases hor with h1 | h2
  · refine hp ?_
    have : s⁻¹ • (s • p) = p := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul]
    rw [← this]
    exact hK.smul_mem _ hmem _ (le_of_lt (inv_pos.mpr hs))
      ((inv_le_one₀ hs).mpr h1)
  · have hnorm : ‖s • p‖ = s * ‖p‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    exact absurd (hK.norm_lt _ hmem) (by rw [hnorm]; exact not_lt.mpr h2)

/-! ## §1. The deformation retract `ℝⁿ ∖ K ≃ Sⁿ⁻¹` -/

/-- `p/‖p‖` is in the complement (its norm is `1`, and every point of `K` has norm `< 1`). -/
theorem normalize_mem_compl (hK : StarInBall K) {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ Kᶜ) :
    ‖p‖⁻¹ • p ∈ Kᶜ := by
  refine smul_mem_compl hK hp (inv_pos.mpr (norm_pos_iff.mpr (ne_zero_of_mem_compl hK hp)))
    (Or.inr ?_)
  rw [inv_mul_cancel₀ (norm_ne_zero_of_mem_compl hK hp)]

/-- The **retraction** `ℝⁿ ∖ K → Sⁿ⁻¹`, `p ↦ p/‖p‖`. -/
noncomputable def normalizeK (hK : StarInBall K) : C(↑(sub (X := Eucl n) Kᶜ), ↑(Sph n)) where
  toFun p := ⟨‖(p : EuclideanSpace ℝ (Fin n))‖⁻¹ • (p : EuclideanSpace ℝ (Fin n)),
    SingularPuncturedRetract.normalize_mem_sphere ⟨(p : EuclideanSpace ℝ (Fin n)),
      ne_zero_of_mem_compl hK p.2⟩⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.smul ?_ continuous_subtype_val) _
    exact (continuous_norm.comp continuous_subtype_val).inv₀
      (fun p => norm_ne_zero_of_mem_compl hK p.2)

/-- The **inclusion** `Sⁿ⁻¹ ↪ ℝⁿ ∖ K` (norm-1 points miss `K`). -/
noncomputable def inclK (hK : StarInBall K) : C(↑(Sph n), ↑(sub (X := Eucl n) Kᶜ)) where
  toFun x := ⟨(x : EuclideanSpace ℝ (Fin n)), fun hmem => by
    have := hK.norm_lt _ hmem
    rw [mem_sphere_zero_iff_norm.mp x.2] at this
    exact lt_irrefl _ this⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

theorem normalizeK_comp_inclK (hK : StarInBall K) :
    (normalizeK hK).comp (inclK hK) = ContinuousMap.id _ := by
  refine ContinuousMap.ext fun x => Subtype.ext ?_
  show ‖(x : EuclideanSpace ℝ (Fin n))‖⁻¹ • (x : EuclideanSpace ℝ (Fin n)) = (x : _)
  rw [mem_sphere_zero_iff_norm.mp x.2, inv_one, one_smul]

/-- The straight-line-in-scale homotopy point `t•p + (1−t)•(p/‖p‖) = s • p` with
`s = t + (1−t)‖p‖⁻¹ > 0` stays in the complement: if `‖p‖ ≥ 1` then `s‖p‖ ≥ 1`, and if `‖p‖ < 1`
then `s ≥ 1`. -/
theorem starHomotopy_mem_compl (hK : StarInBall K) (p : ↥(Kᶜ : Set ↑(Eucl n))) (t : unitInterval) :
    (t : ℝ) • (p : EuclideanSpace ℝ (Fin n))
        + (1 - (t : ℝ)) • (‖(p : EuclideanSpace ℝ (Fin n))‖⁻¹ • (p : EuclideanSpace ℝ (Fin n)))
      ∈ Kᶜ := by
  have hnp : (0 : ℝ) < ‖(p : EuclideanSpace ℝ (Fin n))‖ :=
    norm_pos_iff.mpr (ne_zero_of_mem_compl hK p.2)
  have hinv : (0 : ℝ) < ‖(p : EuclideanSpace ℝ (Fin n))‖⁻¹ := inv_pos.mpr hnp
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hrw : (t : ℝ) • (p : EuclideanSpace ℝ (Fin n))
      + (1 - (t : ℝ)) • (‖(p : EuclideanSpace ℝ (Fin n))‖⁻¹ • (p : EuclideanSpace ℝ (Fin n)))
    = ((t : ℝ) + (1 - (t : ℝ)) * ‖(p : EuclideanSpace ℝ (Fin n))‖⁻¹)
        • (p : EuclideanSpace ℝ (Fin n)) := by
    rw [smul_smul, ← add_smul]
  rw [hrw]
  set s : ℝ := (t : ℝ) + (1 - (t : ℝ)) * ‖(p : EuclideanSpace ℝ (Fin n))‖⁻¹ with hs
  have hspos : 0 < s := by
    rcases eq_or_lt_of_le ht0 with h | h
    · rw [hs, ← h]; simpa using hinv
    · have : (0 : ℝ) ≤ (1 - (t : ℝ)) * ‖(p : EuclideanSpace ℝ (Fin n))‖⁻¹ :=
        mul_nonneg (by linarith) hinv.le
      rw [hs]; linarith
  refine smul_mem_compl hK p.2 hspos ?_
  rcases le_or_gt 1 ‖(p : EuclideanSpace ℝ (Fin n))‖ with hbig | hsmall
  · refine Or.inr ?_
    have hmul : s * ‖(p : EuclideanSpace ℝ (Fin n))‖
        = (t : ℝ) * ‖(p : EuclideanSpace ℝ (Fin n))‖ + (1 - (t : ℝ)) := by
      rw [hs, add_mul, mul_assoc, inv_mul_cancel₀ (ne_of_gt hnp), mul_one]
    rw [hmul]
    nlinarith
  · refine Or.inl ?_
    have hinv1 : (1 : ℝ) ≤ ‖(p : EuclideanSpace ℝ (Fin n))‖⁻¹ :=
      (one_le_inv_iff₀).mpr ⟨hnp, hsmall.le⟩
    rw [hs]
    nlinarith

/-- The **deformation-retract homotopy** on `ℝⁿ ∖ K`. -/
noncomputable def starHomotopy (hK : StarInBall K) :
    C(↑(sub (X := Eucl n) Kᶜ) × unitInterval, ↑(sub (X := Eucl n) Kᶜ)) where
  toFun q := ⟨(q.2 : ℝ) • (q.1 : EuclideanSpace ℝ (Fin n))
      + (1 - (q.2 : ℝ)) • (‖(q.1 : EuclideanSpace ℝ (Fin n))‖⁻¹
        • (q.1 : EuclideanSpace ℝ (Fin n))),
    starHomotopy_mem_compl hK q.1 q.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.add (Continuous.smul ?_ ?_) (Continuous.smul ?_ ?_)) _
    · exact continuous_subtype_val.comp continuous_snd
    · exact continuous_subtype_val.comp continuous_fst
    · exact continuous_const.sub (continuous_subtype_val.comp continuous_snd)
    · exact ((continuous_norm.comp (continuous_subtype_val.comp continuous_fst)).inv₀
        (fun q => norm_ne_zero_of_mem_compl hK q.1.2)).smul
          (continuous_subtype_val.comp continuous_fst)

theorem slice_starHomotopy_zero (hK : StarInBall K) :
    slice (starHomotopy hK) 0 = (inclK hK).comp (normalizeK hK) := by
  refine ContinuousMap.ext fun p => Subtype.ext ?_
  show ((0 : unitInterval) : ℝ) • (p : EuclideanSpace ℝ (Fin n))
      + (1 - ((0 : unitInterval) : ℝ)) • (‖(p : EuclideanSpace ℝ (Fin n))‖⁻¹ • (p : _))
    = ‖(p : EuclideanSpace ℝ (Fin n))‖⁻¹ • (p : EuclideanSpace ℝ (Fin n))
  simp

theorem slice_starHomotopy_one (hK : StarInBall K) :
    slice (starHomotopy hK) 1 = ContinuousMap.id _ := by
  refine ContinuousMap.ext fun p => Subtype.ext ?_
  show ((1 : unitInterval) : ℝ) • (p : EuclideanSpace ℝ (Fin n))
      + (1 - ((1 : unitInterval) : ℝ)) • (‖(p : EuclideanSpace ℝ (Fin n))‖⁻¹ • (p : _))
    = (p : EuclideanSpace ℝ (Fin n))
  simp

/-- **`ℝⁿ ∖ K` deformation-retracts onto `Sⁿ⁻¹`** (integral homology): the retraction induces an
isomorphism `Hₖ₊₁(ℝⁿ ∖ K; ℤ) ≅ Hₖ₊₁(Sⁿ⁻¹; ℤ)`. -/
theorem homology_mapInt_normalizeK_bijective (hK : StarInBall K) (k : ℕ) :
    Function.Bijective (Homology.mapInt (normalizeK hK) (k + 1)) :=
  Homology.mapInt_bijective_of_homotopyEquiv (normalizeK hK) (inclK hK) (starHomotopy hK)
    (slice_starHomotopy_zero hK) (slice_starHomotopy_one hK)
    SingularPuncturedRetract.constHomotopy
    ((SingularPuncturedRetract.slice_constHomotopy 0).trans (normalizeK_comp_inclK hK).symm)
    (SingularPuncturedRetract.slice_constHomotopy 1) k

/-! ## §2. Vanishing of the complement's homology and of the local homology -/

/-- **`Hⱼ₊₁(ℝᵐ⁺¹ ∖ K; ℤ) = 0` for `j + 1 < m`** — the complement has the homology of `Sᵐ`, which
vanishes in the middle degrees. -/
theorem homology_compl_eq_zero {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (hK : StarInBall K) (j : ℕ) (hj : j + 1 < m)
    (x : Homology (sub (X := Eucl (m + 1)) Kᶜ) (j + 1)) : x = 0 := by
  refine (homology_mapInt_normalizeK_bijective hK j).injective ?_
  rw [map_zero]
  exact SingularSphereMiddleInt.sphere_homology_middleInt (j + 1) m (Nat.succ_pos j) hj _

/-- **`Hⱼ₊₂(ℝᵐ⁺¹, ℝᵐ⁺¹ ∖ K; ℤ) = 0` for `j + 2 ≤ m`.** The pair LES with `ℝᵐ⁺¹` integrally acyclic
makes `δ : Hⱼ₊₂(ℝᵐ⁺¹, ℝᵐ⁺¹∖K) → Hⱼ₊₁(ℝᵐ⁺¹∖K)` bijective, and the target vanishes.

At `m = 3` this is `H₂(ℝ⁴ | K) = H₃(ℝ⁴ | K) = 0` for any star-shaped body `K` strictly inside the
unit ball of `ℝ⁴` — in particular for a **closed flat 2-disk**, which
`SingularConvexComplementRetract` cannot reach (empty interior). -/
theorem relHomology_compl_eq_zero {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (hK : StarInBall K) (j : ℕ) (hj : j + 2 ≤ m)
    (x : RelHomologyInt (X := Eucl (m + 1)) Kᶜ (j + 2)) : x = 0 := by
  refine (SingularLocalHomologyInt.connectingInt_bijective_of_acyclic
    (X := Eucl (m + 1)) Kᶜ (j + 1)
    (SingularLocalHomologyInt.eucl_homology_trivialInt (m + 1) (j + 1))
    (SingularLocalHomologyInt.eucl_homology_trivialInt (m + 1) j)).injective ?_
  rw [map_zero]
  exact homology_compl_eq_zero hK j (by omega) _

/-! ## §3. The concrete witness: a closed flat disk -/

/-- The **closed flat radius-`r` `m`-disk** inside `ℝⁿ`: the points of norm `≤ r` supported on the
first `m` coordinates. For `n = 4`, `m = 2` this is the flat 2-disk `D² × {0} ⊆ ℝ⁴`, which has
**empty interior**. -/
def flatDisk (n m : ℕ) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {p | ‖p‖ ≤ r ∧ ∀ i : Fin n, m ≤ (i : ℕ) → p i = 0}

/-- A flat disk is **closed** — a norm sublevel set intersected with coordinate hyperplanes. -/
theorem isClosed_flatDisk (n m : ℕ) (r : ℝ) : IsClosed (flatDisk n m r) := by
  have hset : flatDisk n m r
      = {p : EuclideanSpace ℝ (Fin n) | ‖p‖ ≤ r}
        ∩ ⋂ i : Fin n, {p : EuclideanSpace ℝ (Fin n) | m ≤ (i : ℕ) → p i = 0} := by
    ext p
    simp only [flatDisk, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine IsClosed.inter (isClosed_le continuous_norm continuous_const) (isClosed_iInter fun i => ?_)
  by_cases hi : m ≤ (i : ℕ)
  · have : {p : EuclideanSpace ℝ (Fin n) | m ≤ (i : ℕ) → p i = 0}
        = {p : EuclideanSpace ℝ (Fin n) | p i = 0} := by
      ext p; exact ⟨fun h => h hi, fun h _ => h⟩
    rw [this]
    exact isClosed_eq (by fun_prop) continuous_const
  · have : {p : EuclideanSpace ℝ (Fin n) | m ≤ (i : ℕ) → p i = 0} = Set.univ := by
      ext p; exact ⟨fun _ => trivial, fun _ h => absurd h hi⟩
    rw [this]
    exact isClosed_univ

/-- A flat disk of radius `r ∈ [0, 1)` is a star-shaped body strictly inside the unit ball. -/
theorem starInBall_flatDisk (n m : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    StarInBall (flatDisk n m r) where
  zero_mem := ⟨by simpa using hr0, fun _ _ => rfl⟩
  smul_mem := by
    rintro p ⟨hpn, hpz⟩ s hs0 hs1
    refine ⟨?_, fun i hi => ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
      calc s * ‖p‖ ≤ 1 * ‖p‖ := by
              exact mul_le_mul_of_nonneg_right hs1 (norm_nonneg p)
        _ = ‖p‖ := one_mul _
        _ ≤ r := hpn
    · rw [PiLp.smul_apply, smul_eq_mul, hpz i hi, mul_zero]
  norm_lt := fun _ hp => lt_of_le_of_lt hp.1 hr1

/-- **A flat disk has empty interior** — precisely the hypothesis `SingularConvexComplementRetract`
requires (`0 ∈ interior A`) and cannot get here. Every ball around `0` contains the off-slab point
`single ⟨m, _⟩ (ε/2)`, which is not in the disk. This is what forces the star-shaped route of this
module rather than the convex-complement one; it is a genuine obstruction, not a packaging choice. -/
theorem zero_notMem_interior_flatDisk {n m : ℕ} (hm : m < n) (r : ℝ) :
    (0 : EuclideanSpace ℝ (Fin n)) ∉ interior (flatDisk n m r) := by
  intro h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 h
  set v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (⟨m, hm⟩ : Fin n) (ε / 2) with hv
  have hnorm : ‖v‖ = ε / 2 := by
    rw [hv, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hmemball : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε := by
    rw [Metric.mem_ball, dist_zero_right, hnorm]; linarith
  have hvmem : v ∈ flatDisk n m r := interior_subset (hball hmemball)
  have hzero := hvmem.2 (⟨m, hm⟩ : Fin n) le_rfl
  rw [hv, PiLp.single_apply] at hzero
  simp only [if_pos] at hzero
  linarith

/-- **The flat-2-disk local-homology vanishing in `ℝ⁴`**: `H₂(ℝ⁴, ℝ⁴ ∖ D) = H₃(ℝ⁴, ℝ⁴ ∖ D) = 0` for
the closed flat 2-disk `D` of radius `1/2`. The two degrees are exactly the hemisphere inputs the
local-homology Mayer–Vietoris assembly (`SingularRelativeMVLESInt.relMvDeltaEquivInt`) consumes. -/
theorem relHomology_flatDisk_four_eq_zero (j : ℕ) (hj : j ≤ 1)
    (x : RelHomologyInt (X := Eucl 4) (flatDisk 4 2 (1 / 2))ᶜ (j + 2)) : x = 0 :=
  relHomology_compl_eq_zero (m := 3) (starInBall_flatDisk 4 2 (by norm_num) (by norm_num)) j
    (by omega) x

end SKEFTHawking.SingularStarComplementRetractInt
