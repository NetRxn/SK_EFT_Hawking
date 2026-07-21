/-
# Phase 5q.H — K6′b Leg 9b: the seam neighbourhood, ONE COMPONENT AT A TIME

Leg 8 (`KummerSeamOpenNbhd`) produced an open two-sided neighbourhood of the seam by taking **all
sixteen components at once** — the saturation of the sixteen-fold union is free, whereas the
saturation of a single component needs

    `∂Q_{c₀} ∩ (the c-collar) = ∅`   for `c₀ ≠ c`,

which Leg 8 explicitly declined to prove. A chart, however, is a *local* object: chart family 3/3
needs the collar of ONE seam component to be open, not the union of sixteen.

This module discharges that separation obligation and builds the per-component open collar.

**§1 — the separation.** The sixteen fixed points of `τ` are pairwise at distance `≥ 2`
(`fixedSet_dist_ge`); the `c`-collar lives at chart radius `< 5/8` from `c`, and `∂Q_{c₀}` at chart
radius exactly `1/2` from `c₀` — *both* of its two `qmk`-preimages, because `τ` is an isometry
fixing `c₀` (`dist_involution_fixed`). So a common point would force `dist c c₀ < 5/8 + 1/2 = 9/8`,
contradicting `2 ≤ dist c c₀`. The `9/8 < 2` slack is what makes the separation true; it is not a
near miss.

**§2 — the Q side, strictly.** `qOpenCollarSet c` is exactly the `qCollar`-image of the *half-open*
radius range `[1/2, 5/8)`: the `range_qCollar` argument run with a strict upper bound (and the lower
bound `1/4 ≤ sqNorm t` supplied by the puncture — a smaller-radius point would lie in the excised
ball `chartBall c`).

**§3 — the per-component open collar.** With §1, the single-component carrier
`inl '' qOpenCollarSet c ∪ inr '' ({c} ×ˢ eOpenSet)` **is** saturated, hence its weld image
`seamCompNbhd c` is open in `K3`.

**§4 — it IS the double collar's interior.** `seamCompNbhd c = dblCollar c '' (ℝP³ × (−1/8, 1/2))`,
so the open set carries the product structure `ℝP³ × (−1/8, 1/2)` that the seam chart transports the
`ℝP³` atlas across.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamOpenNbhd

namespace SKEFTHawking.KummerSeamComponentOpen

open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerInvolution
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerFreeQuotient
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerWeldFiberFlow
open SKEFTHawking.KummerWeld
open SKEFTHawking.KummerSeamOpenNbhd
open SKEFTHawking.KummerWeldQInterior (scaleToChart_surjOn)
open SKEFTHawking.KummerSeamCollarE (eCollar fiberNorm_eCollar eCollar_surjOn)
open SKEFTHawking.KummerSeamCollarQ (qParam qCollar qShellPoint sqNorm_qShellPoint qCollarS3
  scale4 sqNorm_scale4 scale4_scale4 scale4_one qParam_lower)
open SKEFTHawking.KummerSeamDoubleCollar (dblParam dblCollar clampE clampQ eBranch qBranch
  dblCollar_of_nonneg dblCollar_of_neg clampE_coe clampQ_coe)

noncomputable section

/-! ## §1. The separation: a seam component meets only its own collar -/

/-- Every point of the `c`-collar ball is within chart radius `5/8` of the fixed point `c`. -/
theorem dist_lt_of_mem_qOpenBall {c : EIndex} {x : TorusFour} (hx : x ∈ qOpenBall c) :
    dist x c.1 < 5 / 8 := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact dist_centeredChartParam_lt c.1 (by norm_num) ht

/-- Both `qmk`-preimages of a seam point of `∂Q_{c₀}` are at chart distance exactly `≤ 1/2` from
`c₀`: the pinned representative because the seam sphere has radius `1/2`, and its `τ`-partner
because `τ` is an isometry fixing `c₀`. -/
theorem dist_le_of_qmk_eq_qBdryMap {c₀ : EIndex} {a : S3} {z : ↥puncturedTorus}
    (hz : qmk z = s3ToQ c₀ a) : dist (z : TorusFour) c₀.1 ≤ 1 / 2 := by
  set y : ↥puncturedTorus := ⟨centeredChartParam c₀.1 (scaleToChart a),
    sphere_subset_puncturedTorus (eIndex_fixedSet c₀)
      ⟨scaleToChart a, sqNorm_scaleToChart a, rfl⟩⟩ with hy
  have hdy : dist (y : TorusFour) c₀.1 ≤ 1 / 2 := by
    refine dist_centeredChartParam_le c₀.1 (by norm_num) ?_
    rw [sqNorm_scaleToChart]
    norm_num [excisionRadius]
  rcases (qmk_eq_iff z y).mp hz with rfl | hτ
  · exact hdy
  · have : (z : TorusFour) = torusFourInvolution (y : TorusFour) := by
      rw [hτ]; exact neg_one_smul_val y
    rw [this, dist_involution_fixed (eIndex_fixedSet c₀)]
    exact hdy

/-- **THE SEPARATION.** A point of the seam component `∂Q_{c₀}` lies in the open `c`-collar only if
`c₀ = c`. Distinct fixed points are `2` apart, while a common point would put them within
`5/8 + 1/2 = 9/8`. This is the obligation `KummerSeamOpenNbhd` avoided by saturating all sixteen
components at once; discharging it is what makes a *single-component* chart possible. -/
theorem seam_separation {c c₀ : EIndex} {r : RP3} (h : qBdryMap c₀ r ∈ qOpenCollarSet c) :
    c₀ = c := by
  induction r using Quotient.inductionOn with
  | _ a =>
    obtain ⟨z, hz, hzq⟩ := h
    have hd0 : dist (z : TorusFour) c₀.1 ≤ 1 / 2 := dist_le_of_qmk_eq_qBdryMap hzq
    have hdc : dist (z : TorusFour) c.1 < 5 / 8 := dist_lt_of_mem_qOpenBall hz
    by_contra hne
    have hsep : (2 : ℝ) ≤ dist c₀.1 c.1 :=
      fixedSet_dist_ge (eIndex_fixedSet c₀) (eIndex_fixedSet c) (fun hc => hne (Subtype.ext hc))
    have htri : dist c₀.1 c.1 ≤ dist c₀.1 (z : TorusFour) + dist (z : TorusFour) c.1 :=
      dist_triangle _ _ _
    rw [dist_comm c₀.1 (z : TorusFour)] at htri
    linarith

/-! ## §2. The Q side of the component collar, at strictly-smaller radius -/

/-- A punctured-torus point in the `c`-collar ball has chart radius in `[1/2, 5/8)`: the upper bound
is the ball, the lower bound is the puncture (a smaller radius would put it in `chartBall c`). -/
theorem sqNorm_bounds_of_mem_qOpenShell {c : EIndex} {z : ↥puncturedTorus} (hz : z ∈ qOpenShell c) :
    ∃ t : ℝ × ℝ × ℝ × ℝ, 1 / 4 ≤ sqNorm t ∧ sqNorm t < (5 / 8) ^ 2 ∧
      centeredChartParam c.1 t = (z : TorusFour) := by
  obtain ⟨t, ht, hteq⟩ := hz
  refine ⟨t, ?_, ht, hteq⟩
  by_contra hlow
  rw [not_le] at hlow
  refine z.2 (Set.mem_iUnion₂.mpr ⟨c.1, eIndex_fixedSet c, ?_⟩)
  exact ⟨t, by rw [excisionRadius]; norm_num; linarith, hteq⟩

/-- **The Q-side open collar IS the `qCollar` image of the half-open radius range `[1/2, 5/8)`.**
The `range_qCollar` argument with a strict upper bound. -/
theorem qOpenCollarSet_eq_qCollar_image (c : EIndex) :
    qOpenCollarSet c = qCollar c '' {p : RP3 × ↥qParam | (p.2 : ℝ) < 5 / 8} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨t, h1, h2, hteq⟩ := sqNorm_bounds_of_mem_qOpenShell hz
    set s : ℝ := Real.sqrt (sqNorm t) with hs
    have hssq : s ^ 2 = sqNorm t := Real.sq_sqrt (sqNorm_nonneg t)
    have hslow : 1 / 2 ≤ s := by nlinarith [Real.sqrt_nonneg (sqNorm t)]
    have hshigh : s < 5 / 8 := by nlinarith [Real.sqrt_nonneg (sqNorm t)]
    have hspos : (0 : ℝ) < s := by linarith
    have hsc : sqNorm (scale4 (1 / (2 * s)) t) = ((1 : ℝ) / 2) ^ 2 := by
      rw [sqNorm_scale4, ← hssq]; field_simp
    obtain ⟨a, ha⟩ := scaleToChart_surjOn hsc
    refine ⟨(mkRP3 a, ⟨s, hslow, hshigh.le⟩), hshigh, ?_⟩
    show qCollarS3 c a ⟨s, hslow, hshigh.le⟩ = qmk z
    refine congrArg qmk (Subtype.ext ?_)
    show centeredChartParam c.1 (qShellPoint a s) = (z : TorusFour)
    rw [← hteq]
    refine congrArg (centeredChartParam c.1) ?_
    rw [qShellPoint, ha, scale4_scale4,
      show 2 * s * (1 / (2 * s)) = 1 by field_simp, scale4_one]
  · rintro _ ⟨p, hp, rfl⟩
    exact qCollar_mem_qOpenCollarSet c p hp

/-! ## §3. The per-component saturated carrier and the open collar -/

/-- **The single-component seam carrier**: the Q-side open collar of `∂Q_c` together with the
E-side open collar of the `c`-th copy only. -/
def seamCompCarrier (c : EIndex) : Set WeldCarrier :=
  Sum.inl '' qOpenCollarSet c ∪ Sum.inr '' ({c} ×ˢ eOpenSet)

theorem isOpen_seamCompCarrier (c : EIndex) : IsOpen (seamCompCarrier c) :=
  (isOpenMap_inl _ (isOpen_qOpenCollarSet c)).union
    (isOpenMap_inr _ ((isOpen_discrete _).prod isOpen_eOpenSet))

/-- **THE SINGLE-COMPONENT CARRIER IS SATURATED** — thanks to §1. The `inl` end of a weld pair in
the carrier is `qBdryMap c₀ r₀ ∈ qOpenCollarSet c`, which by `seam_separation` forces `c₀ = c`, so
the partner `inr (c, bdryMapRP3 r₀)` is in the (copy-`c`-only) E part; conversely the `inr` end
being in the copy-`c` part gives `c₀ = c` directly, and `qBdryMap c r₀` is in the Q part. -/
theorem preimage_image_seamCompCarrier (c : EIndex) :
    weldMk ⁻¹' (weldMk '' seamCompCarrier c) = seamCompCarrier c := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro a ⟨b, hb, hab⟩
  rcases Quotient.exact hab with he | ⟨c₀, r₀, hb1, h2⟩ | ⟨c₀, r₀, h1, hb2⟩
  · exact he ▸ hb
  · -- `SeamJoin b a` : `b` is the `inl` end, `a = inr (c₀, bdryMapRP3 r₀)`
    have hmem : qBdryMap c₀ r₀ ∈ qOpenCollarSet c := by
      rcases hb with ⟨q, hq, hqe⟩ | ⟨q, _, hqe⟩
      · have : q = qBdryMap c₀ r₀ := Sum.inl.inj (hqe.trans hb1)
        exact this ▸ hq
      · exact absurd (hqe.trans hb1) (by simp)
    have hc : c₀ = c := seam_separation hmem
    subst hc
    exact Or.inr ⟨(c₀, bdryMapRP3 r₀),
      ⟨rfl, bdryMapRP3_mem_eOpenSet r₀⟩, h2.symm⟩
  · -- `SeamJoin a b` : `a = inl (qBdryMap c₀ r₀)`, `b` is the `inr` end
    have hc : c₀ = c := by
      rcases hb with ⟨q, _, hqe⟩ | ⟨q, hq, hqe⟩
      · exact absurd (hqe.trans hb2).symm (by simp)
      · have : q = (c₀, bdryMapRP3 r₀) := Sum.inr.inj (hqe.trans hb2)
        exact (this ▸ hq).1
    subst hc
    exact Or.inl ⟨qBdryMap c₀ r₀, qBdryMap_mem_qOpenCollarSet c₀ r₀, h1.symm⟩

/-- **THE OPEN TWO-SIDED NEIGHBOURHOOD OF ONE SEAM COMPONENT.** Chart family 3/3's chart source. -/
def seamCompNbhd (c : EIndex) : Set KummerK3 := weldMk '' seamCompCarrier c

/-- **The single-component seam neighbourhood is OPEN in `K3`** — §1 (separation) plus §3
(saturation) plus openness upstairs, through the quotient map `weldMk`. -/
theorem isOpen_seamCompNbhd (c : EIndex) : IsOpen (seamCompNbhd c) := by
  have hqm : Topology.IsQuotientMap (weldMk : WeldCarrier → KummerK3) := isQuotientMap_quotient_mk'
  refine hqm.isOpen_preimage.mp ?_
  show IsOpen (weldMk ⁻¹' (weldMk '' seamCompCarrier c))
  rw [preimage_image_seamCompCarrier]
  exact isOpen_seamCompCarrier c

/-- The `c`-th seam component lies inside its own open neighbourhood. -/
theorem seamComponent_subset_seamCompNbhd (c : EIndex) (r : RP3) :
    weldMk (Sum.inr (c, bdryMapRP3 r)) ∈ seamCompNbhd c :=
  ⟨Sum.inr (c, bdryMapRP3 r), Or.inr ⟨(c, bdryMapRP3 r),
    ⟨rfl, bdryMapRP3_mem_eOpenSet r⟩, rfl⟩, rfl⟩

/-! ## §4. The open collar IS the double collar's interior -/

/-- The OPEN double-collar parameter range `(−1/8, 1/2)` inside `dblParam = [−1/8, 1/2]`. -/
def dblOpenParam : Set ↥dblParam := {v | -(1 / 8 : ℝ) < (v : ℝ) ∧ (v : ℝ) < 1 / 2}

theorem isOpen_dblOpenParam : IsOpen dblOpenParam :=
  (isOpen_lt continuous_const continuous_subtype_val).inter
    (isOpen_lt continuous_subtype_val continuous_const)

/-- The collar's open parameter box `ℝP³ × (−1/8, 1/2)` (the same for every component). -/
def collarBox : Set (RP3 × ↥dblParam) := (Set.univ : Set RP3) ×ˢ dblOpenParam

theorem isOpen_collarBox : IsOpen collarBox := isOpen_univ.prod isOpen_dblOpenParam

/-- **THE OPEN COMPONENT NEIGHBOURHOOD IS EXACTLY THE DOUBLE COLLAR'S INTERIOR.**

Forward: the E half of the carrier is the fiber-radius-`> 1/2` locus, which `eCollar_surjOn`
parametrises as `v = 1 − fiberNorm ∈ [0, 1/2)`; the Q half is the chart-radius-`[1/2, 5/8)` locus,
which §2 parametrises as `v = 1/2 − s ∈ (−1/8, 0]`. The two halves overlap exactly on the seam
`v = 0`, where the weld identifies them (`weldMk_seam`). Backward: `dblCollar_mem_seamNbhd`'s
argument, refined to the single component `c`. -/
theorem seamCompNbhd_eq_dblCollar_image (c : EIndex) :
    seamCompNbhd c = dblCollar c '' collarBox := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨b, hb, rfl⟩
    rcases hb with ⟨y, hy, rfl⟩ | ⟨⟨c', w⟩, hcw, rfl⟩
    · -- Q side: chart radius `s ∈ [1/2, 5/8)`, collar parameter `v = 1/2 − s`
      rw [qOpenCollarSet_eq_qCollar_image] at hy
      obtain ⟨⟨r, s⟩, hs, rfl⟩ := hy
      have hshigh : (s : ℝ) < 5 / 8 := hs
      have hslow : (1 : ℝ) / 2 ≤ (s : ℝ) := s.2.1
      have hmem : 1 / 2 - (s : ℝ) ∈ dblParam := ⟨by linarith, by linarith⟩
      set v : ↥dblParam := ⟨1 / 2 - (s : ℝ), hmem⟩ with hvdef
      refine ⟨(r, v), ⟨Set.mem_univ _, ⟨by simpa [hvdef] using (by linarith : -(1 / 8 : ℝ) <
        1 / 2 - (s : ℝ)), by simpa [hvdef] using (by linarith : 1 / 2 - (s : ℝ) < 1 / 2)⟩⟩, ?_⟩
      by_cases hv : (0 : ℝ) ≤ (v : ℝ)
      · -- the `v = 0` seam slice: `s = 1/2`
        have hs2 : (s : ℝ) = 1 / 2 := by
          have : (0 : ℝ) ≤ 1 / 2 - (s : ℝ) := hv
          linarith
        have hsE : clampE v = 1 := by
          apply Subtype.ext
          show 1 - max (1 / 2 - (s : ℝ)) 0 = ((1 : unitInterval) : ℝ)
          rw [hs2]; norm_num
        rw [dblCollar_of_nonneg c hv]
        show weldMk (Sum.inr (c, eCollar (r, clampE v))) = _
        rw [hsE, SKEFTHawking.KummerSeamCollarE.eCollar_one, ← weldMk_seam c r]
        refine congrArg (fun q => weldMk (Sum.inl q)) ?_
        rw [← SKEFTHawking.KummerSeamCollarQ.qCollar_half c r]
        exact congrArg (fun t : ↥qParam => qCollar c (r, t)) (Subtype.ext hs2.symm)
      · have hsQ : clampQ v = s := by
          apply Subtype.ext
          show 1 / 2 - min (1 / 2 - (s : ℝ)) 0 = (s : ℝ)
          rw [min_eq_left (le_of_not_ge hv)]; ring
        rw [dblCollar_of_neg c hv]
        show weldMk (Sum.inl (qCollar c (r, clampQ v))) = _
        rw [hsQ]
    · -- E side: fiber radius `t ∈ (1/2, 1]`, collar parameter `v = 1 − t`
      have hc' : c' = c := hcw.1
      have hw : (1 : ℝ) / 2 < fiberNorm w := hcw.2
      rw [hc']
      obtain ⟨⟨r, t⟩, hEq, hnorm⟩ := eCollar_surjOn (lt_trans (by norm_num) hw)
      have ht1 : (1 : ℝ) / 2 < (t : ℝ) := by rw [hnorm]; exact hw
      have ht2 : (t : ℝ) ≤ 1 := t.2.2
      have hmem : 1 - (t : ℝ) ∈ dblParam := ⟨by linarith, by linarith⟩
      set v : ↥dblParam := ⟨1 - (t : ℝ), hmem⟩ with hvdef
      refine ⟨(r, v), ⟨Set.mem_univ _, ⟨by simpa [hvdef] using (by linarith : -(1 / 8 : ℝ) <
        1 - (t : ℝ)), by simpa [hvdef] using (by linarith : 1 - (t : ℝ) < 1 / 2)⟩⟩, ?_⟩
      have hv : (0 : ℝ) ≤ (v : ℝ) := by show (0 : ℝ) ≤ 1 - (t : ℝ); linarith
      have hE : clampE v = t := by
        apply Subtype.ext
        show 1 - max (1 - (t : ℝ)) 0 = (t : ℝ)
        rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - (t : ℝ))]; ring
      rw [dblCollar_of_nonneg c hv]
      show weldMk (Sum.inr (c, eCollar (r, clampE v))) = _
      rw [hE, hEq]
  · rintro _ ⟨p, ⟨-, hlo, hhi⟩, rfl⟩
    by_cases hv : (0 : ℝ) ≤ (p.2 : ℝ)
    · rw [dblCollar_of_nonneg c hv]
      refine ⟨Sum.inr (c, eCollar (p.1, clampE p.2)),
        Or.inr ⟨_, ⟨Set.mem_singleton _, ?_⟩, rfl⟩, rfl⟩
      show (1 : ℝ) / 2 < fiberNorm (eCollar (p.1, clampE p.2))
      rw [fiberNorm_eCollar, clampE_coe, max_eq_left hv]
      linarith
    · rw [dblCollar_of_neg c hv]
      refine ⟨Sum.inl (qCollar c (p.1, clampQ p.2)),
        Or.inl ⟨_, qCollar_mem_qOpenCollarSet c _ ?_, rfl⟩, rfl⟩
      show (clampQ p.2 : ℝ) < 5 / 8
      rw [clampQ_coe, min_eq_left (le_of_not_ge hv)]
      linarith

/-! ## §5. The seam chart's parametrization is an OPEN EMBEDDING -/

/-- Any open piece of the collar box has open image in `K3`.

`dblCollarHomeo` makes the image open *in the subspace* `range (dblCollar c)`; §4 upgrades that to
open in `K3`, because the whole collar-box image `seamCompNbhd c` is itself open in `K3` and sits
inside that range. -/
theorem isOpen_dblCollar_image {c : EIndex} {V : Set (RP3 × ↥dblParam)} (hV : IsOpen V)
    (hsub : V ⊆ collarBox) : IsOpen (dblCollar c '' V) := by
  have hrange : seamCompNbhd c ⊆ Set.range (dblCollar c) := by
    rw [seamCompNbhd_eq_dblCollar_image]
    rintro _ ⟨p, -, rfl⟩
    exact Set.mem_range_self p
  have himg : dblCollar c '' V ⊆ seamCompNbhd c := by
    rw [seamCompNbhd_eq_dblCollar_image]
    exact Set.image_mono hsub
  have hopen : IsOpen (SKEFTHawking.KummerSeamDoubleCollar.dblCollarHomeo c '' V) :=
    (SKEFTHawking.KummerSeamDoubleCollar.dblCollarHomeo c).isOpenMap V hV
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp hopen
  have key : dblCollar c '' V = W ∩ seamCompNbhd c := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      refine ⟨?_, himg ⟨p, hp, rfl⟩⟩
      have : (⟨dblCollar c p, Set.mem_range_self p⟩ :
          ↥(Set.range (dblCollar c))) ∈ Subtype.val ⁻¹' W := by
        rw [hWeq]; exact ⟨p, hp, rfl⟩
      exact this
    · rintro x ⟨hxW, hxN⟩
      have hbox : x ∈ dblCollar c '' collarBox := by
        rw [← seamCompNbhd_eq_dblCollar_image]; exact hxN
      obtain ⟨p, -, rfl⟩ := hbox
      have hmem : (⟨dblCollar c p, Set.mem_range_self p⟩ : ↥(Set.range (dblCollar c)))
          ∈ SKEFTHawking.KummerSeamDoubleCollar.dblCollarHomeo c '' V := by
        rw [← hWeq]; exact hxW
      obtain ⟨q, hq, hqe⟩ := hmem
      have hqp : q = p :=
        SKEFTHawking.KummerSeamDoubleCollar.dblCollar_injective c (congrArg Subtype.val hqe)
      exact ⟨p, hqp ▸ hq, rfl⟩
  rw [key]
  exact hW.inter (isOpen_seamCompNbhd c)

/-- **CHART FAMILY 3/3'S PARAMETRIZATION IS AN OPEN EMBEDDING** —
`ℝP³ × (−1/8, 1/2) ↪ K3` is an open embedding onto `seamCompNbhd c`.

This is the seam-chart brick: composing its inverse with the `ℝP³` atlas
(`KummerRP3Smooth.instChartedSpaceRP3`, `ℝP³` charted on `𝓔³`) and the inclusion
`(−1/8, 1/2) ↪ ℝ` gives an `OpenPartialHomeomorph K3 (𝓔³ × ℝ)` at every seam point — the third
chart family, on the *untagged* product model that `ManifoldModelTransport.prodRealEquivEuclidean`
carries to `𝓡 4`. -/
theorem isOpenEmbedding_collarRestrict (c : EIndex) :
    Topology.IsOpenEmbedding (collarBox.restrict (dblCollar c)) := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    ((SKEFTHawking.KummerSeamDoubleCollar.continuous_dblCollar c).comp continuous_subtype_val)
    (fun p q h => Subtype.ext
      (SKEFTHawking.KummerSeamDoubleCollar.dblCollar_injective c h)) ?_
  intro U hU
  have himg : collarBox.restrict (dblCollar c) '' U = dblCollar c '' (Subtype.val '' U) := by
    rw [Set.image_image]; rfl
  rw [himg]
  refine isOpen_dblCollar_image (isOpen_collarBox.isOpenMap_subtype_val U hU) ?_
  rintro _ ⟨p, -, rfl⟩
  exact p.2

/-- **The range of the seam parametrization is the open component neighbourhood.** -/
theorem range_collarRestrict (c : EIndex) :
    Set.range (collarBox.restrict (dblCollar c)) = seamCompNbhd c := by
  rw [seamCompNbhd_eq_dblCollar_image, Set.range_restrict]

end

end SKEFTHawking.KummerSeamComponentOpen
