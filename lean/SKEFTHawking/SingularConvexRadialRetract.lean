import Mathlib
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.SingularEuclideanAcyclic
import SKEFTHawking.SingularRelativeHomologyMod2

/-!
# Phase 5q.F (w₂-foundation, brick 72c-4f) — the all-dimensional convex-complement radial retract

For ANY convex compact `K ⊆ ℝⁿ` and a point `O ∈ K` (**no interior-point assumption** — `K` may be
lower-dimensional), the inclusion `ℝⁿ ∖ K ↪ ℝⁿ ∖ {O}` is a homotopy equivalence, hence induces an
isomorphism on `Hₖ(·; ℤ/2)`. The retract is **radial from `O`**: `g(x) = O + max(1, (R+1)/‖x-O‖)·(x-O)`
pushes every point of `ℝⁿ ∖ {O}` radially out past the ball `closedBall O R ⊇ K`. Both composites are
witnessed by the straight-line radial homotopy `H(x, t) = O + (1 + t·(s(x)-1))·(x-O)` (interpolating the
radial scale `1 ↦ s(x)`); it stays off `O` (the scale is `≥ 1 > 0`) and stays out of `K` (the segment
runs radially outward from `O` past `x ∉ K`, and `K` convex with `O ∈ K` keeps such points out).

This generalizes the full-dimensional gauge retract `SingularConvexComplementRetract` (`0 ∈ int K`) to
all dimensions — the lower-dimensional convex base case the Hatcher 3.27 fundamental-class induction
needs. Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularEuclideanAcyclic SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.SingularConvexRadialRetract

variable {n : ℕ}

/-- The radial scale `s(x) = max 1 ((R+1)/‖x-O‖)` for the push-out from `O`. -/
noncomputable def rscale (O : EuclideanSpace ℝ (Fin n)) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  max 1 ((R + 1) * ‖x - O‖⁻¹)

theorem one_le_rscale (O : EuclideanSpace ℝ (Fin n)) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    1 ≤ rscale O R x := le_max_left _ _

/-- The time-`t` interpolated radial scale `1 + (1-t)·(s(x)-1) ∈ [1, s(x)]`. -/
noncomputable def htScale (O : EuclideanSpace ℝ (Fin n)) (R : ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := 1 + (1 - t) * (rscale O R x - 1)

/-- The interpolated scale is `≥ 1` for `t ∈ I` (since `1-t ≥ 0` and `s(x)-1 ≥ 0`). -/
theorem one_le_htScale (O : EuclideanSpace ℝ (Fin n)) (R : ℝ) {t : ℝ} (ht : t ≤ 1)
    (x : EuclideanSpace ℝ (Fin n)) : 1 ≤ htScale O R t x := by
  have h1 : (0 : ℝ) ≤ 1 - t := by linarith
  have h2 : (0 : ℝ) ≤ rscale O R x - 1 := by linarith [one_le_rscale O R x]
  have := mul_nonneg h1 h2
  rw [htScale]; linarith

/-- A radially-outward point `O + s•(x-O)` (`s ≥ 1`, `x ≠ O`) is `≠ O`. -/
theorem radial_ne (O : EuclideanSpace ℝ (Fin n)) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ O)
    {s : ℝ} (hs : 1 ≤ s) : O + s • (x - O) ≠ O := by
  intro h
  have hz : s • (x - O) = 0 := by rwa [add_eq_left] at h
  rcases smul_eq_zero.mp hz with hs0 | hxO
  · rw [hs0] at hs; norm_num at hs
  · exact hx (sub_eq_zero.mp hxO)

/-- **The radial "stays out of `K`" lemma** (the mathematical crux). If `K` is convex, `O ∈ K`,
`x ∉ K` and `s ≥ 1`, then the radially-outward point `O + s•(x - O)` is also `∉ K`: were it in `K`,
then `x = O + (1/s)•((O + s•(x-O)) - O)` is a convex combination of `O ∈ K` and that point (since
`1/s ∈ [0,1]`), forcing `x ∈ K`. -/
theorem convex_radial_not_mem {K : Set (EuclideanSpace ℝ (Fin n))} (hKconv : Convex ℝ K)
    {O x : EuclideanSpace ℝ (Fin n)} (hOK : O ∈ K) (hx : x ∉ K) {s : ℝ} (hs : 1 ≤ s) :
    O + s • (x - O) ∉ K := by
  intro hmem
  apply hx
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
  have hticc : s⁻¹ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt (inv_pos.mpr hs0), inv_le_one_of_one_le₀ hs⟩
  have key := hKconv.add_smul_sub_mem hOK hmem hticc
  have hsimp : O + s⁻¹ • ((O + s • (x - O)) - O) = x := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (ne_of_gt hs0), one_smul, add_sub_cancel]
  rwa [hsimp] at key

/-- The full push-out `O + s(x)•(x-O)` lands **outside** `closedBall O R`: its distance to `O` is
`s(x)·‖x-O‖ = max(‖x-O‖, R+1) ≥ R+1 > R`. -/
theorem pushOut_not_mem_closedBall (O : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ O) :
    O + rscale O R x • (x - O) ∉ Metric.closedBall O R := by
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (le_trans zero_le_one (one_le_rscale O R x))]
  have hpos : (0 : ℝ) < ‖x - O‖ := by rw [norm_pos_iff]; exact sub_ne_zero.mpr hx
  have hmax : rscale O R x * ‖x - O‖ = max ‖x - O‖ (R + 1) := by
    rw [rscale, max_mul_of_nonneg _ _ hpos.le, one_mul, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
  rw [hmax]
  have hle : R + 1 ≤ max ‖x - O‖ (R + 1) := le_max_right _ _
  linarith

/-- Hence the push-out lands **outside `K`** (`K ⊆ closedBall O R`). -/
theorem pushOut_not_mem {K : Set (EuclideanSpace ℝ (Fin n))} (O : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (hKR : K ⊆ Metric.closedBall O R) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ O) :
    O + rscale O R x • (x - O) ∉ K := fun h => pushOut_not_mem_closedBall O R hx (hKR h)

/-- The radial-homotopy underlying map `(y, t) ↦ O + (1 + (1-t)·(s(y)-1))•(y-O)`, continuous on
`ℝⁿ ∖ {O}` (the scale is a continuous function of `‖y-O‖⁻¹`, well-defined for `y ≠ O`). -/
theorem continuous_radialHomotopy (O : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    Continuous (fun p : {x : EuclideanSpace ℝ (Fin n) // x ≠ O} × unitInterval =>
      O + htScale O R (p.2 : ℝ) (p.1 : EuclideanSpace ℝ (Fin n))
        • ((p.1 : EuclideanSpace ℝ (Fin n)) - O)) := by
  have hsub : Continuous (fun p : {x : EuclideanSpace ℝ (Fin n) // x ≠ O} × unitInterval =>
      (p.1 : EuclideanSpace ℝ (Fin n)) - O) :=
    (continuous_subtype_val.comp continuous_fst).sub continuous_const
  have hinv : Continuous (fun p : {x : EuclideanSpace ℝ (Fin n) // x ≠ O} × unitInterval =>
      ‖(p.1 : EuclideanSpace ℝ (Fin n)) - O‖⁻¹) :=
    hsub.norm.inv₀ (fun p => by rw [norm_ne_zero_iff]; exact sub_ne_zero.mpr p.1.2)
  have hrscale : Continuous (fun p : {x : EuclideanSpace ℝ (Fin n) // x ≠ O} × unitInterval =>
      rscale O R (p.1 : EuclideanSpace ℝ (Fin n))) := by
    simp only [rscale]; exact continuous_const.max (continuous_const.mul hinv)
  simp only [htScale]
  exact continuous_const.add ((continuous_const.add
    ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
      (hrscale.sub continuous_const))).smul hsub)

/-- The radial homotopy keeps `ℝⁿ ∖ {O}` invariant (the scale is `≥ 1 > 0`, `y ≠ O`). -/
theorem htRadial_ne (O : EuclideanSpace ℝ (Fin n)) (R : ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ≠ O) (t : unitInterval) :
    O + htScale O R (t : ℝ) x • (x - O) ≠ O :=
  radial_ne O hx (one_le_htScale O R (unitInterval.le_one t) x)

/-- The radial homotopy keeps `ℝⁿ ∖ K` invariant: for `x ∉ K` and `t ∈ I`, the interpolated point
`O + htScale•(x-O)` stays out of `K` (`htScale ≥ 1`, `convex_radial_not_mem`). -/
theorem htRadial_not_mem {K : Set (EuclideanSpace ℝ (Fin n))} (hKconv : Convex ℝ K) (R : ℝ)
    {O x : EuclideanSpace ℝ (Fin n)} (hOK : O ∈ K) (hx : x ∉ K) (t : unitInterval) :
    O + htScale O R (t : ℝ) x • (x - O) ∉ K :=
  convex_radial_not_mem hKconv hOK hx (one_le_htScale O R (unitInterval.le_one t) x)

/-! ## The complement subspaces and the retract maps -/

/-- `Kᶜ ⊆ {O}ᶜ` (since `O ∈ K`): a point outside `K` is `≠ O`. -/
theorem compl_subset {K : Set (EuclideanSpace ℝ (Fin n))} {O : EuclideanSpace ℝ (Fin n)}
    (hOK : O ∈ K) : (Kᶜ : Set ↑(Eucl n)) ⊆ ({O}ᶜ : Set ↑(Eucl n)) := by
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro he; subst he; exact hx hOK

/-- A point of `sub ({O}ᶜ)` is `≠ O`. -/
theorem ne_of_mem_punc {O : EuclideanSpace ℝ (Fin n)} (q : ↥({O}ᶜ : Set ↑(Eucl n))) :
    (q : EuclideanSpace ℝ (Fin n)) ≠ O := by
  have := q.2; simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using this

/-- A point of `sub (Kᶜ)` is `∉ K`. -/
theorem not_mem_of_mem_compl {K : Set (EuclideanSpace ℝ (Fin n))} (p : ↥(Kᶜ : Set ↑(Eucl n))) :
    (p : EuclideanSpace ℝ (Fin n)) ∉ K := p.2

/-- **The inclusion `f : ℝⁿ∖K ↪ ℝⁿ∖{O}`** (`O ∈ K`). -/
def inclMapRadial {K : Set (EuclideanSpace ℝ (Fin n))} {O : EuclideanSpace ℝ (Fin n)}
    (hOK : O ∈ K) : C(↑(sub (Kᶜ : Set ↑(Eucl n))), ↑(sub ({O}ᶜ : Set ↑(Eucl n)))) :=
  ⟨Set.inclusion (compl_subset hOK), continuous_inclusion (compl_subset hOK)⟩

/-- **The radial push-out** `g(q) = O + s(q)•(q-O) : ℝⁿ∖{O} → ℝⁿ∖K`. -/
noncomputable def pushMap {K : Set (EuclideanSpace ℝ (Fin n))} {O : EuclideanSpace ℝ (Fin n)}
    (R : ℝ) (hKR : K ⊆ Metric.closedBall O R) :
    C(↑(sub ({O}ᶜ : Set ↑(Eucl n))), ↑(sub (Kᶜ : Set ↑(Eucl n)))) where
  toFun q := ⟨O + rscale O R (q : EuclideanSpace ℝ (Fin n)) • ((q : EuclideanSpace ℝ (Fin n)) - O),
    pushOut_not_mem O R hKR (ne_of_mem_punc q)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk
      (((continuous_radialHomotopy O R).comp
        (Continuous.prodMk continuous_id
          (continuous_const (y := (0 : unitInterval))))).congr (fun q => ?_)) _
    simp [htScale]

/-- The radial homotopy `(q, t) ↦ O + htScale•(q-O)` on `ℝⁿ ∖ {O}` (witnesses `f ∘ g ≃ id`). -/
noncomputable def homotopyPunc {O : EuclideanSpace ℝ (Fin n)} (R : ℝ) :
    C(↑(sub ({O}ᶜ : Set ↑(Eucl n))) × unitInterval, ↑(sub ({O}ᶜ : Set ↑(Eucl n)))) where
  toFun p := ⟨O + htScale O R (p.2 : ℝ) (p.1 : EuclideanSpace ℝ (Fin n))
      • ((p.1 : EuclideanSpace ℝ (Fin n)) - O),
    htRadial_ne O R (ne_of_mem_punc p.1) p.2⟩
  continuous_toFun := Continuous.subtype_mk (continuous_radialHomotopy O R) _

/-- The radial homotopy on `ℝⁿ ∖ K` (witnesses `g ∘ f ≃ id`). -/
noncomputable def homotopyComplK {K : Set (EuclideanSpace ℝ (Fin n))} {O : EuclideanSpace ℝ (Fin n)}
    (hKconv : Convex ℝ K) (R : ℝ) (hOK : O ∈ K) :
    C(↑(sub (Kᶜ : Set ↑(Eucl n))) × unitInterval, ↑(sub (Kᶜ : Set ↑(Eucl n)))) where
  toFun p := ⟨O + htScale O R (p.2 : ℝ) (p.1 : EuclideanSpace ℝ (Fin n))
      • ((p.1 : EuclideanSpace ℝ (Fin n)) - O),
    htRadial_not_mem hKconv R hOK (not_mem_of_mem_compl p.1) p.2⟩
  continuous_toFun :=
    Continuous.subtype_mk ((continuous_radialHomotopy O R).comp
      (Continuous.prodMk ((inclMapRadial hOK).continuous.comp continuous_fst) continuous_snd)) _

/-- **The all-dimensional convex-complement inclusion `f : ℝⁿ∖K ↪ ℝⁿ∖{O}` is a homology isomorphism**
(positive degree) for ANY convex compact `K` and `O ∈ K` — no interior-point assumption. The radial
push-out `g` (`pushMap`, with `R` from `K ⊆ closedBall O R`) is a homotopy inverse. This is the
lower-dimensional convex base case of the Hatcher 3.27 fundamental-class induction. -/
theorem homology_map_inclMapRadial_bijective {K : Set (EuclideanSpace ℝ (Fin n))}
    {O : EuclideanSpace ℝ (Fin n)} (hKconv : Convex ℝ K) (hKcomp : IsCompact K) (hOK : O ∈ K)
    (k : ℕ) : Function.Bijective (Homology.map (inclMapRadial hOK) (k + 1)) := by
  obtain ⟨R, hRpos, hKR⟩ := hKcomp.isBounded.subset_closedBall_lt 0 O
  refine Homology.map_bijective_of_homotopyEquiv (inclMapRadial hOK) (pushMap R hKR)
    (homotopyComplK hKconv R hOK) ?_ ?_ (homotopyPunc R) ?_ ?_ k
  · refine ContinuousMap.ext fun p => Subtype.ext ?_
    show O + htScale O R ((0 : unitInterval) : ℝ) (p : EuclideanSpace ℝ (Fin n)) • _
      = O + rscale O R (p : EuclideanSpace ℝ (Fin n)) • _
    simp [htScale, inclMapRadial, Set.inclusion]
  · refine ContinuousMap.ext fun p => Subtype.ext ?_
    show O + htScale O R ((1 : unitInterval) : ℝ) (p : EuclideanSpace ℝ (Fin n)) • _
      = (p : EuclideanSpace ℝ (Fin n))
    simp [htScale]
  · refine ContinuousMap.ext fun q => Subtype.ext ?_
    show O + htScale O R ((0 : unitInterval) : ℝ) (q : EuclideanSpace ℝ (Fin n)) • _
      = O + rscale O R (q : EuclideanSpace ℝ (Fin n)) • _
    simp [htScale]
  · refine ContinuousMap.ext fun q => Subtype.ext ?_
    show O + htScale O R ((1 : unitInterval) : ℝ) (q : EuclideanSpace ℝ (Fin n)) • _
      = (q : EuclideanSpace ℝ (Fin n))
    simp [htScale]

end SKEFTHawking.SingularConvexRadialRetract
