import Mathlib
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.SingularPuncturedRetract

/-!
# Phase 5q.F (w₂-foundation, brick 6e) — the convex-complement radial retract

For `A ⊆ ℝⁿ` compact convex with `0 ∈ interior A`, the complement `ℝⁿ ∖ A` deformation-retracts to
`ℝⁿ ∖ 0`: the inclusion `f : ℝⁿ∖A ↪ ℝⁿ∖0` is a homotopy equivalence, with inverse
`g(x) = (1 + 1/gauge A x) • x` (pushing each point radially out past `∂A`). This mirrors
`SingularPuncturedRetract` (the `ℝⁿ∖0 ≃ Sⁿ⁻¹` normalize-retract) but for the convex complement, using
Mathlib's `gauge`. It gives `Hₖ(ℝⁿ∖A) ≅ Hₖ(ℝⁿ∖0)`, the homotopy input to the convex base case of the
Hatcher 3.27 fundamental-class induction. Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularPuncturedRetract SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.SingularConvexComplementRetract

variable {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))}

/-- `x ∉ A ↔ gauge A x > 1` (for `A` closed convex with `0 ∈ interior`). -/
theorem not_mem_iff_one_lt_gauge (hAc : Convex ℝ A) (hAcomp : IsCompact A)
    (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    x ∉ A ↔ 1 < gauge A x := by
  rw [← not_le, gauge_le_one_iff_mem_closure hAc hA0, hAcomp.isClosed.closure_eq]

/-- `gauge A x > 0` for `x ≠ 0`. -/
theorem gauge_pos_of (hAcomp : IsCompact A)
    (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n))) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    0 < gauge A x :=
  (gauge_pos (absorbent_nhds_zero hA0) (hAcomp.totallyBounded.isVonNBounded ℝ)).2 hx

/-- The radial push-out scalar `1 + s/gauge A x` is `≥ 1 > 0`. -/
theorem one_le_radial (hAcomp : IsCompact A) (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n)))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    1 ≤ 1 + s * (gauge A x)⁻¹ := by
  have := gauge_pos_of hAcomp hA0 hx
  nlinarith [mul_nonneg hs (inv_nonneg.2 this.le)]

/-- **The radial push-out** `(x, s) ↦ (1 + s/gauge A x) • x` has `gauge` value `gauge A x + s`
(`gauge` is positively homogeneous). For `x ∉ A` (`gauge x > 1`) and `s ≥ 0` it stays out of `A`;
for `x ≠ 0` and the scalar `> 0` it stays nonzero. -/
theorem gauge_radial (hAcomp : IsCompact A) (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n)))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    gauge A ((1 + s * (gauge A x)⁻¹) • x) = gauge A x + s := by
  have hp := gauge_pos_of hAcomp hA0 hx
  rw [gauge_smul_of_nonneg (zero_le_one.trans (one_le_radial hAcomp hA0 hx hs)), smul_eq_mul,
    add_mul, one_mul, mul_assoc, inv_mul_cancel₀ hp.ne', mul_one]

/-- `x ∉ A ⟹ x ≠ 0` (since `0 ∈ A`). -/
theorem ne_zero_of_not_mem (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n)))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ A) : x ≠ 0 := fun he => hx (he ▸ mem_of_mem_nhds hA0)

/-- The radial-homotopy underlying map `(y, t) ↦ (1 + (1-t)/gauge A y) • y`, continuous on `ℝⁿ ∖ 0`. -/
theorem continuous_radialHomotopy (hAc : Convex ℝ A) (hAcomp : IsCompact A)
    (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n))) :
    Continuous (fun p : {x : EuclideanSpace ℝ (Fin n) // x ≠ 0} × unitInterval =>
      (1 + (1 - (p.2 : ℝ)) * (gauge A (p.1 : EuclideanSpace ℝ (Fin n)))⁻¹)
        • (p.1 : EuclideanSpace ℝ (Fin n))) := by
  have hg : Continuous (fun p : {x : EuclideanSpace ℝ (Fin n) // x ≠ 0} × unitInterval =>
      gauge A (p.1 : EuclideanSpace ℝ (Fin n))) :=
    (continuous_gauge hAc hA0).comp (continuous_subtype_val.comp continuous_fst)
  have hinv : Continuous (fun p : {x : EuclideanSpace ℝ (Fin n) // x ≠ 0} × unitInterval =>
      (gauge A (p.1 : EuclideanSpace ℝ (Fin n)))⁻¹) :=
    hg.inv₀ (fun p => (gauge_pos_of hAcomp hA0 p.1.2).ne')
  exact ((continuous_const.add
    (((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul hinv))).smul
    (continuous_subtype_val.comp continuous_fst))

/-- The complement subspace `ℝⁿ ∖ A`. -/
abbrev ComplA (A : Set (EuclideanSpace ℝ (Fin n))) : TopCat :=
  TopCat.of {x : EuclideanSpace ℝ (Fin n) // x ∉ A}

/-- The inclusion `f : ℝⁿ∖A ↪ ℝⁿ∖0` (`0 ∈ A`). -/
def inclMap (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n))) :
    C(↑(ComplA A), ↑(Punc n)) where
  toFun p := ⟨(p : EuclideanSpace ℝ (Fin n)), ne_zero_of_not_mem hA0 p.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

/-- The radial push-out `g(x) = (1 + 1/gauge A x) • x : ℝⁿ∖0 → ℝⁿ∖A`. -/
noncomputable def pushMap (hAc : Convex ℝ A) (hAcomp : IsCompact A)
    (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n))) : C(↑(Punc n), ↑(ComplA A)) where
  toFun q := ⟨(1 + (gauge A (q : EuclideanSpace ℝ (Fin n)))⁻¹) • (q : EuclideanSpace ℝ (Fin n)),
    by
      rw [not_mem_iff_one_lt_gauge hAc hAcomp hA0,
        show (1 : ℝ) + (gauge A (q : EuclideanSpace ℝ (Fin n)))⁻¹
          = 1 + 1 * (gauge A (q : EuclideanSpace ℝ (Fin n)))⁻¹ by rw [one_mul],
        gauge_radial hAcomp hA0 q.2 zero_le_one]
      linarith [gauge_pos_of hAcomp hA0 q.2]⟩
  continuous_toFun := by
    have h := continuous_radialHomotopy hAc hAcomp hA0
    refine Continuous.subtype_mk
      ((h.comp (Continuous.prodMk continuous_id (continuous_const (y := (0 : unitInterval))))).congr
        (fun q => ?_)) _
    simp

/-- The radial homotopy `(q, t) ↦ (1 + (1-t)/gauge A q) • q` on `ℝⁿ ∖ 0` (witnesses `f ∘ g ≃ id`). -/
noncomputable def homotopyPunc (hAc : Convex ℝ A) (hAcomp : IsCompact A)
    (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n))) :
    C(↑(Punc n) × unitInterval, ↑(Punc n)) where
  toFun p := ⟨(1 + (1 - (p.2 : ℝ)) * (gauge A (p.1 : EuclideanSpace ℝ (Fin n)))⁻¹)
      • (p.1 : EuclideanSpace ℝ (Fin n)),
    smul_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one
      (one_le_radial hAcomp hA0 p.1.2 (sub_nonneg.2 (unitInterval.le_one p.2))))) p.1.2⟩
  continuous_toFun := Continuous.subtype_mk (continuous_radialHomotopy hAc hAcomp hA0) _

/-- The radial homotopy keeps `ℝⁿ ∖ A` invariant: for `x ∉ A` and `t ∈ I`, the pushed point stays out
of `A` (its `gauge` is `gauge x + (1-t) ≥ gauge x > 1`). -/
theorem radial_not_mem (hAc : Convex ℝ A) (hAcomp : IsCompact A)
    (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n))) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ A)
    (t : unitInterval) : (1 + (1 - (t : ℝ)) * (gauge A x)⁻¹) • x ∉ A := by
  rw [not_mem_iff_one_lt_gauge hAc hAcomp hA0,
    gauge_radial hAcomp hA0 (ne_zero_of_not_mem hA0 hx) (sub_nonneg.2 (unitInterval.le_one t))]
  have hg := (not_mem_iff_one_lt_gauge hAc hAcomp hA0 x).mp hx
  have ht : (0 : ℝ) ≤ 1 - (t : ℝ) := sub_nonneg.2 (unitInterval.le_one t)
  linarith

/-- The radial homotopy on `ℝⁿ ∖ A` (witnesses `g ∘ f ≃ id`). -/
noncomputable def homotopyComplA (hAc : Convex ℝ A) (hAcomp : IsCompact A)
    (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n))) :
    C(↑(ComplA A) × unitInterval, ↑(ComplA A)) where
  toFun p := ⟨(1 + (1 - (p.2 : ℝ)) * (gauge A (p.1 : EuclideanSpace ℝ (Fin n)))⁻¹)
      • (p.1 : EuclideanSpace ℝ (Fin n)), radial_not_mem hAc hAcomp hA0 p.1.2 p.2⟩
  continuous_toFun :=
    Continuous.subtype_mk ((continuous_radialHomotopy hAc hAcomp hA0).comp
      (Continuous.prodMk ((inclMap hA0).continuous.comp continuous_fst) continuous_snd)) _

/-- **The complement inclusion `f : ℝⁿ∖A ↪ ℝⁿ∖0` is a homology isomorphism** (positive degree): the
radial retract `g` (`pushMap`) is a homotopy inverse. The homotopy input to the convex base case. -/
theorem homology_map_inclMap_bijective (hAc : Convex ℝ A) (hAcomp : IsCompact A)
    (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin n))) (k : ℕ) :
    Function.Bijective (Homology.map (inclMap hA0) (k + 1)) := by
  refine Homology.map_bijective_of_homotopyEquiv (inclMap hA0) (pushMap hAc hAcomp hA0)
    (homotopyComplA hAc hAcomp hA0) ?_ ?_ (homotopyPunc hAc hAcomp hA0) ?_ ?_ k
  · refine ContinuousMap.ext fun p => Subtype.ext ?_
    show (1 + (1 - ((0 : unitInterval) : ℝ)) * _) • _ = (1 + _) • (p : EuclideanSpace ℝ (Fin n))
    simp [inclMap]
  · refine ContinuousMap.ext fun p => Subtype.ext ?_
    show (1 + (1 - ((1 : unitInterval) : ℝ)) * _) • (p : EuclideanSpace ℝ (Fin n)) = _
    simp
  · refine ContinuousMap.ext fun q => Subtype.ext ?_
    show (1 + (1 - ((0 : unitInterval) : ℝ)) * _) • _ = (1 + _) • (q : EuclideanSpace ℝ (Fin n))
    simp
  · refine ContinuousMap.ext fun q => Subtype.ext ?_
    show (1 + (1 - ((1 : unitInterval) : ℝ)) * _) • (q : EuclideanSpace ℝ (Fin n)) = _
    simp

end SKEFTHawking.SingularConvexComplementRetract
