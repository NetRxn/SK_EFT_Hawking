/-
# Phase 5q.H — K6′b Leg 6: the Q-side of the seam is a product collar `ℝP³ × [1/2, 5/8]`

The mirror of `KummerSeamCollarE` on the free-quotient side: the `Q = T⁴°/τ` neighbourhood of a
boundary component `∂Q_c` is *literally* a product `ℝP³ × [1/2, 5/8]`, with the `[1/2]` face carried
onto the seam `∂Q_c = range (qBdryMap c)`.

**Why this is the right shape.** `KummerShellChart` banks the punctured-torus collar of a boundary
sphere as the Euclidean exterior shell `{1/2 ≤ ‖w‖ < 3/4}` (`shellImage_mem_puncturedTorus`,
`collarSet`). The in-chart involution is `τ = −id` (`centeredChartParam_involution`), which acts on
the shell by negating the *direction* only and fixes the radius — so the quotient shell is
`(S³/±1) × [radius]= ℝP³ × [1/2, 5/8]`, radially. That is exactly the `S³/±1` presentation the weld
is pinned to, and it makes the collar parameter (radius) an honest coordinate on `Q` near `∂Q`.

**Contents.** §1 the chart-vector scaling `scale4` and its `sqNorm` / antipode laws; §2 the shell
point `qShellPoint a s` at radius `s`, with the `puncturedTorus` membership routed through
`KummerShellChart.shellImage_mem_puncturedTorus`; §3 the descended collar map `qCollar c` on
`ℝP³ × [1/2, 5/8]`, its injectivity (via `centeredChartParam_injOn_threeQuarters` — the radius `5/8`
is inside the chart's extended injectivity radius `3/4`) and its range; §4 the collar homeomorphism
`qCollarHomeo` and the identification of the `s = 1/2` face with the seam map `qBdryMap`.

Together with `KummerSeamCollarE.eCollarHomeo` this gives BOTH halves of the seam double collar,
each as an explicit `ℝP³ × [interval]` product, sharing the same `ℝP³` factor — the pinned
`S³/±1` presentation on both ends. The remaining residual for chart family 3/3 is the glue itself:
the two halves must be joined into one `ℝP³ × (−δ, δ)` chart across `bdryMapRP3` / `qBdryMap`, whose
smooth compatibility is `KummerSeamSmooth.contMDiff_bdryMapRP3`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamCollarE
import SKEFTHawking.KummerShellChart

namespace SKEFTHawking.KummerSeamCollarQ

open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerInvolution
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerFreeQuotient
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerWeld
open SKEFTHawking.KummerShellChart (toE4 ofE4 ofE4_toE4 norm_toE4 shellImage_mem_puncturedTorus
  centeredChartParam_injOn_threeQuarters)
open SKEFTHawking.KummerWeldQInterior (scaleToChart_surjOn range_qBdryMap_eq_boundaryComponent)

noncomputable section

/-! ## §1. Scaling a chart vector -/

/-- **Radial scaling of a chart vector** `u · t` on `ℝ⁴ = ℝ × ℝ × ℝ × ℝ`. -/
def scale4 (u : ℝ) (t : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (u * t.1, u * t.2.1, u * t.2.2.1, u * t.2.2.2)

@[simp] theorem sqNorm_scale4 (u : ℝ) (t : ℝ × ℝ × ℝ × ℝ) :
    sqNorm (scale4 u t) = u ^ 2 * sqNorm t := by
  simp only [sqNorm, scale4]; ring

/-- Scaling commutes with the in-chart antipode `τ = −id`. -/
theorem chartNeg_scale4 (u : ℝ) (t : ℝ × ℝ × ℝ × ℝ) :
    chartNeg (scale4 u t) = scale4 u (chartNeg t) := by
  simp only [chartNeg, scale4, mul_neg]

theorem scale4_injective {u : ℝ} (hu : u ≠ 0) : Function.Injective (scale4 u) := by
  intro t t' h
  simp only [scale4, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact Prod.ext (mul_left_cancel₀ hu h1) (Prod.ext (mul_left_cancel₀ hu h2)
    (Prod.ext (mul_left_cancel₀ hu h3) (mul_left_cancel₀ hu h4)))

theorem scale4_scale4 (u v : ℝ) (t : ℝ × ℝ × ℝ × ℝ) :
    scale4 u (scale4 v t) = scale4 (u * v) t := by
  simp only [scale4]; refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only [] <;> ring

theorem scale4_one (t : ℝ × ℝ × ℝ × ℝ) : scale4 1 t = t := by
  simp only [scale4, one_mul]

theorem continuous_scale4 :
    Continuous (fun p : ℝ × (ℝ × ℝ × ℝ × ℝ) => scale4 p.1 p.2) := by
  unfold scale4; fun_prop

/-! ## §2. The shell point at radius `s` -/

/-- **The chart-shell point at radius `s`** in the direction of `a ∈ S³`. Since `scaleToChart a` has
square-norm `ρ² = 1/4`, the factor `2s` puts `qShellPoint a s` at square-norm exactly `s²`. -/
def qShellPoint (a : S3) (s : ℝ) : ℝ × ℝ × ℝ × ℝ := scale4 (2 * s) (scaleToChart a)

/-- **The radius law**: `sqNorm (qShellPoint a s) = s²`. -/
@[simp] theorem sqNorm_qShellPoint (a : S3) (s : ℝ) : sqNorm (qShellPoint a s) = s ^ 2 := by
  rw [qShellPoint, sqNorm_scale4, sqNorm_scaleToChart]
  show (2 * s) ^ 2 * ((1 : ℝ) / 2) ^ 2 = s ^ 2
  ring

/-- **The `s = 1/2` slice is the boundary sphere vector** — `qShellPoint a (1/2) = scaleToChart a`,
so the collar's inner face is the pinned seam presentation. -/
@[simp] theorem qShellPoint_half (a : S3) : qShellPoint a (1 / 2) = scaleToChart a := by
  rw [qShellPoint, show 2 * ((1 : ℝ) / 2) = 1 by norm_num, scale4_one]

/-- **The antipode acts on the direction only** — `qShellPoint (negS3 a) s = chartNeg (qShellPoint a s)`.
This is what makes the collar descend through the `τ`-quotient with the radius untouched. -/
theorem qShellPoint_negS3 (a : S3) (s : ℝ) :
    qShellPoint (negS3 a) s = chartNeg (qShellPoint a s) := by
  rw [qShellPoint, qShellPoint, scaleToChart_negS3, chartNeg_scale4]

/-- **The shell point lies on the punctured-torus side** — routed through `KummerShellChart`'s
geometric heart `shellImage_mem_puncturedTorus` (a shell point at radius `< 3/4` around a fixed
point avoids every excised ball). -/
theorem qShellPoint_mem_puncturedTorus (c : EIndex) (a : S3) {s : ℝ}
    (h1 : 1 / 2 ≤ s) (h2 : s < 3 / 4) :
    centeredChartParam c.1 (qShellPoint a s) ∈ puncturedTorus := by
  have hnorm : ‖toE4 (qShellPoint a s)‖ = s := by
    rw [norm_toE4, sqNorm_qShellPoint, Real.sqrt_sq (by linarith)]
  have hmem := shellImage_mem_puncturedTorus (eIndex_fixedSet c)
    (w := toE4 (qShellPoint a s)) (by rw [hnorm]; exact h1) (by rw [hnorm]; exact h2)
  rwa [ofE4_toE4] at hmem

/-! ## §3. The descended collar map on `ℝP³ × [1/2, 5/8]` -/

/-- The collar's radial parameter range `[1/2, 5/8]` — inside the chart's extended injectivity
radius `3/4` (`centeredChartParam_injOn_threeQuarters`). -/
def qParam : Set ℝ := Set.Icc (1 / 2) (5 / 8)

theorem qParam_lower {s : ↥qParam} : 1 / 2 ≤ (s : ℝ) := s.2.1

theorem qParam_lt_threeQuarters {s : ↥qParam} : (s : ℝ) < 3 / 4 := lt_of_le_of_lt s.2.2 (by norm_num)

theorem qParam_pos {s : ↥qParam} : (0 : ℝ) < (s : ℝ) := lt_of_lt_of_le (by norm_num) s.2.1

instance instCompactSpaceQParam : CompactSpace ↥qParam :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- The collar map before descent: `(a, s) ↦ qmk (centeredChartParam c (qShellPoint a s))`. -/
def qCollarS3 (c : EIndex) (a : S3) (s : ↥qParam) : FreeQuotient :=
  qmk ⟨centeredChartParam c.1 (qShellPoint a (s : ℝ)),
    qShellPoint_mem_puncturedTorus c a qParam_lower qParam_lt_threeQuarters⟩

/-- **The collar map descends through the antipode** — the `τ`-gluing on `Q` absorbs `negS3` exactly
as it does on the boundary sphere (`KummerWeld.s3ToQ_negS3`), with the radius untouched. -/
theorem qCollarS3_negS3 (c : EIndex) (a : S3) (s : ↥qParam) :
    qCollarS3 c (negS3 a) s = qCollarS3 c a s := by
  apply Quotient.sound
  refine ⟨-1, ?_⟩
  apply Subtype.ext
  rw [neg_one_smul_val]
  show torusFourInvolution (centeredChartParam c.1 (qShellPoint a (s : ℝ)))
    = centeredChartParam c.1 (qShellPoint (negS3 a) (s : ℝ))
  rw [centeredChartParam_involution c.1 (eIndex_fixedSet c), qShellPoint_negS3]

/-- **The Q-side collar map** `ℝP³ × [1/2, 5/8] → Q`. -/
def qCollar (c : EIndex) (p : RP3 × ↥qParam) : FreeQuotient :=
  Quotient.liftOn p.1 (fun a => qCollarS3 c a p.2) (fun a b h => by
    rcases h with rfl | rfl
    · rfl
    · exact (qCollarS3_negS3 c a p.2).symm)

@[simp] theorem qCollar_mk (c : EIndex) (a : S3) (s : ↥qParam) :
    qCollar c (mkRP3 a, s) = qCollarS3 c a s := rfl

theorem continuous_qCollarS3 (c : EIndex) :
    Continuous (fun p : S3 × ↥qParam => qCollarS3 c p.1 p.2) := by
  refine continuous_quotient_mk'.comp (Continuous.subtype_mk ?_ _)
  refine (continuous_centeredChartParam c.1).comp ?_
  refine continuous_scale4.comp (Continuous.prodMk ?_ ?_)
  · exact (continuous_const.mul (continuous_subtype_val.comp continuous_snd))
  · exact continuous_scaleToChart.comp continuous_fst

theorem continuous_qCollar (c : EIndex) : Continuous (qCollar c) := by
  have hq : Topology.IsQuotientMap (Quotient.mk antipSetoid) := isQuotientMap_quotient_mk'
  exact hq.continuous_lift_prod_left (continuous_qCollarS3 c)

/-- **The `s = 1/2` face of the Q-collar is the seam map** — `qCollar c (r, 1/2) = qBdryMap c r`. -/
@[simp] theorem qCollar_half (c : EIndex) (r : RP3) :
    qCollar c (r, ⟨1 / 2, by constructor <;> norm_num⟩) = qBdryMap c r := by
  induction r using Quotient.inductionOn with
  | _ a =>
    show qCollarS3 c a _ = s3ToQ c a
    exact congrArg qmk (Subtype.ext (by
      show centeredChartParam c.1 (qShellPoint a (1 / 2)) = centeredChartParam c.1 (scaleToChart a)
      rw [qShellPoint_half]))

/-- **The Q-collar map is injective.** The chart is injective out to radius `3/4`
(`centeredChartParam_injOn_threeQuarters`) and `5/8 < 3/4`, so both `qmk`-fiber cases (`x` vs `τx`)
resolve: the radius is pinned by `sqNorm`, and the direction by `scaleToChart`-injectivity, up to
the antipode that `ℝP³` absorbs. -/
theorem qCollar_injective (c : EIndex) : Function.Injective (qCollar c) := by
  rintro ⟨r, s⟩ ⟨r', s'⟩ h
  induction r using Quotient.inductionOn with | _ a =>
  induction r' using Quotient.inductionOn with | _ a' =>
  have hdom : ∀ (b : S3) (u : ↥qParam), qShellPoint b (u : ℝ) ∈ {t | sqNorm t ≤ (3 / 4) ^ 2} := by
    intro b u
    show sqNorm (qShellPoint b (u : ℝ)) ≤ (3 / 4) ^ 2
    rw [sqNorm_qShellPoint]
    nlinarith [u.2.1, u.2.2]
  have hdomneg : ∀ (b : S3) (u : ↥qParam),
      chartNeg (qShellPoint b (u : ℝ)) ∈ {t | sqNorm t ≤ (3 / 4) ^ 2} := by
    intro b u
    show sqNorm (chartNeg (qShellPoint b (u : ℝ))) ≤ (3 / 4) ^ 2
    rw [sqNorm_chartNeg]; exact hdom b u
  -- in both fiber cases we obtain an equation of chart vectors
  have key : qShellPoint a (s : ℝ) = qShellPoint a' (s' : ℝ)
      ∨ qShellPoint a (s : ℝ) = qShellPoint (negS3 a') (s' : ℝ) := by
    rcases (qmk_eq_iff _ _).mp h with heq | heq
    · exact Or.inl (centeredChartParam_injOn_threeQuarters c.1 (hdom a s) (hdom a' s')
        (congrArg Subtype.val heq))
    · right
      have hval : centeredChartParam c.1 (qShellPoint a (s : ℝ))
          = torusFourInvolution (centeredChartParam c.1 (qShellPoint a' (s' : ℝ))) := by
        have hv := congrArg Subtype.val heq
        rwa [neg_one_smul_val] at hv
      rw [centeredChartParam_involution c.1 (eIndex_fixedSet c)] at hval
      rw [qShellPoint_negS3 a' (s' : ℝ)]
      exact centeredChartParam_injOn_threeQuarters c.1 (hdom a s) (hdomneg a' s') hval
  -- the radius is pinned first, then the direction
  have hrad : (s : ℝ) = (s' : ℝ) := by
    have hsq : (s : ℝ) ^ 2 = (s' : ℝ) ^ 2 := by
      rcases key with hk | hk
      · rw [← sqNorm_qShellPoint a (s : ℝ), ← sqNorm_qShellPoint a' (s' : ℝ), hk]
      · rw [← sqNorm_qShellPoint a (s : ℝ), ← sqNorm_qShellPoint (negS3 a') (s' : ℝ), hk]
    nlinarith [qParam_pos (s := s), qParam_pos (s := s')]
  have hs : s = s' := Subtype.ext hrad
  subst hs
  have hne : (2 : ℝ) * (s : ℝ) ≠ 0 := by
    have := qParam_pos (s := s); positivity
  refine Prod.ext ?_ rfl
  rcases key with hk | hk
  · have : scaleToChart a = scaleToChart a' :=
      scale4_injective hne (by rw [← qShellPoint, ← qShellPoint, hk])
    exact congrArg mkRP3 (scaleToChart_injective this)
  · have : scaleToChart a = scaleToChart (negS3 a') :=
      scale4_injective hne (by rw [← qShellPoint, ← qShellPoint, hk])
    rw [scaleToChart_injective this]
    exact mkRP3_neg a'

/-! ## §4. The Q-collar region and the collar homeomorphism -/

/-- **The Q-side collar region of the seam** — the `qmk`-image of the punctured-torus shell of
radii `[1/2, 5/8]` around the fixed point `c`. -/
def qCollarSet (c : EIndex) : Set FreeQuotient :=
  qmk '' {x : ↥puncturedTorus | ∃ t : ℝ × ℝ × ℝ × ℝ,
    1 / 4 ≤ sqNorm t ∧ sqNorm t ≤ (5 / 8) ^ 2 ∧ centeredChartParam c.1 t = x.1}

/-- **The collar map's range IS the collar region** — every shell point of radius in `[1/2, 5/8]` is
`qShellPoint a s` for a unique direction/radius pair (via `scaleToChart_surjOn`, the new
surjectivity of the pinned `S³ → ℝ⁴` presentation). -/
theorem range_qCollar (c : EIndex) : Set.range (qCollar c) = qCollarSet c := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨⟨r, s⟩, rfl⟩
    induction r using Quotient.inductionOn with | _ a =>
    refine ⟨⟨_, qShellPoint_mem_puncturedTorus c a qParam_lower qParam_lt_threeQuarters⟩,
      ⟨qShellPoint a (s : ℝ), ?_, ?_, rfl⟩, rfl⟩
    · rw [sqNorm_qShellPoint]; nlinarith [qParam_lower (s := s)]
    · rw [sqNorm_qShellPoint]; nlinarith [qParam_lower (s := s), s.2.2]
  · rintro _ ⟨x, ⟨t, h1, h2, hteq⟩, rfl⟩
    set s : ℝ := Real.sqrt (sqNorm t) with hs
    have hsnn : 0 ≤ s := Real.sqrt_nonneg _
    have hssq : s ^ 2 = sqNorm t := Real.sq_sqrt (sqNorm_nonneg t)
    have hslow : 1 / 2 ≤ s := by nlinarith
    have hshigh : s ≤ 5 / 8 := by nlinarith
    have hspos : (0 : ℝ) < s := by linarith
    -- unscale `t` to the pinned boundary-sphere radius `ρ = 1/2`
    have hsc : sqNorm (scale4 (1 / (2 * s)) t) = ((1 : ℝ) / 2) ^ 2 := by
      rw [sqNorm_scale4, ← hssq]
      field_simp
    obtain ⟨a, ha⟩ := scaleToChart_surjOn hsc
    refine ⟨(mkRP3 a, ⟨s, hslow, hshigh⟩), ?_⟩
    show qCollarS3 c a ⟨s, hslow, hshigh⟩ = qmk x
    refine congrArg qmk (Subtype.ext ?_)
    show centeredChartParam c.1 (qShellPoint a s) = x.1
    rw [← hteq]
    refine congrArg (centeredChartParam c.1) ?_
    rw [qShellPoint, ha, scale4_scale4]
    rw [show 2 * s * (1 / (2 * s)) = 1 by field_simp, scale4_one]

/-- The collar map restricted to its region, as a map of subtypes. -/
def qCollarRestrict (c : EIndex) (p : RP3 × ↥qParam) : ↥(qCollarSet c) :=
  ⟨qCollar c p, range_qCollar c ▸ Set.mem_range_self p⟩

theorem continuous_qCollarRestrict (c : EIndex) : Continuous (qCollarRestrict c) :=
  Continuous.subtype_mk (continuous_qCollar c) _

theorem bijective_qCollarRestrict (c : EIndex) : Function.Bijective (qCollarRestrict c) := by
  constructor
  · exact fun p q h => qCollar_injective c (congrArg Subtype.val h)
  · rintro ⟨y, hy⟩
    obtain ⟨p, hp⟩ : y ∈ Set.range (qCollar c) := by rw [range_qCollar]; exact hy
    exact ⟨p, Subtype.ext hp⟩

/-- **THE Q-SIDE OF THE SEAM IS A PRODUCT COLLAR** `ℝP³ × [1/2, 5/8] ≃ₜ qCollarSet c`, with the
`s = 1/2` face carried onto the seam `∂Q_c` (`qCollar_half`, `qCollarHomeo_half_face`). Continuous
bijection from a compact space to a Hausdorff one (`Q` is `T2` — the properly-discontinuous free
quotient), so a homeomorphism.

This is the **Q half of the seam double collar**; `KummerSeamCollarE.eCollarHomeo` is the E half,
over the SAME `ℝP³` factor (both ends are the pinned `S³/±1` presentation). -/
def qCollarHomeo (c : EIndex) : (RP3 × ↥qParam) ≃ₜ ↥(qCollarSet c) :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ (bijective_qCollarRestrict c))
    (continuous_qCollarRestrict c)

@[simp] theorem qCollarHomeo_apply (c : EIndex) (p : RP3 × ↥qParam) :
    (qCollarHomeo c p : FreeQuotient) = qCollar c p := rfl

/-- **The Q-collar's inner face is exactly the seam** — the `s = 1/2` slice is `qBdryMap c`, whose
range is the whole boundary component `∂Q_c` (`range_qBdryMap_eq_boundaryComponent`). -/
theorem qCollarHomeo_half_face (c : EIndex) :
    (fun r : RP3 => ((qCollarHomeo c (r, ⟨1 / 2, by constructor <;> norm_num⟩)) : FreeQuotient))
      = qBdryMap c :=
  funext (qCollar_half c)

/-- **The Q-collar contains the whole boundary component `∂Q_c`** — the collar is a genuine
neighbourhood of the *entire* seam component, not of a piece of it. Uses the new surjectivity
`range_qBdryMap_eq_boundaryComponent`. -/
theorem boundaryComponent_subset_qCollarSet (c : EIndex) :
    boundaryComponent c.1 ⊆ qCollarSet c := by
  rw [← range_qBdryMap_eq_boundaryComponent, ← qCollarHomeo_half_face c]
  rintro _ ⟨r, rfl⟩
  exact (qCollarHomeo c _).2

end

end SKEFTHawking.KummerSeamCollarQ
