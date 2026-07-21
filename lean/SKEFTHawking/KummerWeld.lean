/-
# Phase 5q.H — the Kummer K3 generator, K6′b (Route B): the 16-fold boundary weld

The closed smooth 4-manifold carrier `K3 := Q ∪_{16 × ℝP³} (16 × E)`, welding the free quotient
`Q := T⁴°/τ` (`KummerFreeQuotient` — `∂Q = 16 × ℝP³`) to 16 copies of the concrete Euler−2 disk
bundle `E := ResE` (`KummerResolutionPiece` — `∂E ≅ ℝP³`) along their common `ℝP³` boundaries.

Read the binding Route-B design doc `docs/dev-loops/Phase5qH/KUMMER_K4K10_DESIGN.md` (K6′b row).
**No van Kampen / π₁** (design fact 1). The `∂E ≅ ℝP³` and `∂Q_c ≅ ℝP³` identifications are BOTH
in the pinned `S³/±1` antipodal presentation (Design Risk #2, now passed): the Q-side in-chart
involution is `chartNeg = −id` on `ℝ⁴` and `chartSphere c` is the round `S³` at radius `ρ = 1/2`;
the E-side is `negS3 = −id` on `S³ ⊂ ℂ²`. The composite seam identification is
`RP3 --qBdryMap c--> ∂Q_c` on the Q-side and `RP3 --bdryMapRP3--> ∂E` on the E-side.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerFreeQuotient
import SKEFTHawking.KummerResolutionPiece

namespace SKEFTHawking.KummerWeld

open Metric Set
open scoped Manifold
open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerInvolution
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerFreeQuotient
open SKEFTHawking.KummerResolutionPiece

/-! ## §1. The 16-element index of E-copies (one per fixed point of `τ`) -/

/-- **The index of the 16 `E`-copies** — the fixed points of `τ` (`{±1}⁴`). Each `E`-copy is welded
to the boundary component `∂Q_c` of its fixed point `c`. `Fintype.card = 16` (`eIndex_card`), so
`EIndex × ResE ≃ Fin 16 × ResE`. -/
abbrev EIndex : Type := {c : TorusFour // c ∈ fixedFinset}

/-- Each index is a genuine `τ`-fixed point (`c ∈ fixedSet`). -/
theorem eIndex_fixedSet (c : EIndex) : c.1 ∈ fixedSet := (mem_fixedFinset c.1).mp c.2

/-- **The 16 of `16 × E`**: exactly 16 `E`-copies (`fixedFinset.card = 16`). -/
theorem eIndex_card : Fintype.card EIndex = 16 := by
  rw [Fintype.card_coe]; exact fixedFinset_card

/-! ## §2. The scale map `S³ ⊂ ℂ² → ℝ⁴` — the shared `S³/±1` presentation bridge -/

/-- **The scale/reindex map** `S³ ⊂ ℂ² → ℝ⁴`, `(a, b) ↦ ρ · (re a, im a, re b, im b)` with
`ρ = excisionRadius = 1/2`. Sends the unit `S³ ⊂ ℂ²` (E-side presentation) onto the round chart
`S³` of radius `ρ` (Q-side presentation), intertwining `negS3 = −id` with `chartNeg = −id`. -/
noncomputable def scaleToChart (a : S3) : ℝ × ℝ × ℝ × ℝ :=
  (excisionRadius * a.1.1.re, excisionRadius * a.1.1.im,
   excisionRadius * a.1.2.re, excisionRadius * a.1.2.im)

/-- `re² + im² = ‖·‖²` for a complex number. -/
theorem re_sq_add_im_sq (z : ℂ) : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
  have := Complex.sq_norm_sub_sq_im z; linarith

/-- **The scaled `S³ ⊂ ℂ²` lands on the round chart `S³` of radius `ρ`**: `sqNorm (scaleToChart a) =
ρ²`. (Uses `‖a.1‖² + ‖a.2‖² = 1`.) So `centeredChartParam c (scaleToChart a) ∈ chartSphere c`. -/
theorem sqNorm_scaleToChart (a : S3) : sqNorm (scaleToChart a) = excisionRadius ^ 2 := by
  have h1 : a.1.1.re ^ 2 + a.1.1.im ^ 2 = ‖a.1.1‖ ^ 2 := re_sq_add_im_sq a.1.1
  have h2 : a.1.2.re ^ 2 + a.1.2.im ^ 2 = ‖a.1.2‖ ^ 2 := re_sq_add_im_sq a.1.2
  have hs : ‖a.1.1‖ ^ 2 + ‖a.1.2‖ ^ 2 = 1 := a.2
  have key : a.1.1.re ^ 2 + a.1.1.im ^ 2 + a.1.2.re ^ 2 + a.1.2.im ^ 2 = 1 := by
    rw [show a.1.1.re ^ 2 + a.1.1.im ^ 2 + a.1.2.re ^ 2 + a.1.2.im ^ 2
        = (a.1.1.re ^ 2 + a.1.1.im ^ 2) + (a.1.2.re ^ 2 + a.1.2.im ^ 2) from by ring, h1, h2]
    exact hs
  simp only [sqNorm, scaleToChart]
  nlinarith [key]

/-- **The scale map intertwines the two antipodes** `negS3 = −id ↔ chartNeg = −id`:
`scaleToChart (negS3 a) = chartNeg (scaleToChart a)`. The bridge that carries the E-side antipodal
quotient to the Q-side one (Design Risk #2). -/
theorem scaleToChart_negS3 (a : S3) : scaleToChart (negS3 a) = chartNeg (scaleToChart a) := by
  simp only [scaleToChart, chartNeg, negS3, Complex.neg_re, Complex.neg_im, mul_neg]

/-- **The scale map is injective** (`ρ ≠ 0`, and a complex number is determined by `re`/`im`). -/
theorem scaleToChart_injective : Function.Injective scaleToChart := by
  intro a a' h
  simp only [scaleToChart, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hρ : excisionRadius ≠ 0 := ne_of_gt excisionRadius_pos
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact Complex.ext (mul_left_cancel₀ hρ h1) (mul_left_cancel₀ hρ h2)
  · exact Complex.ext (mul_left_cancel₀ hρ h3) (mul_left_cancel₀ hρ h4)

/-- **The scale map is continuous.** -/
theorem continuous_scaleToChart : Continuous scaleToChart := by
  unfold scaleToChart
  fun_prop

/-! ## §3. The Q-side seam map `RP3 → ∂Q_c ⊆ Q` (the composite identification, one end) -/

/-- **The composite `S³ → ∂Q_c`**: `a ↦ qmk (centeredChartParam c (scaleToChart a))`. Lands on the
boundary sphere `∂B_c` (the round `S³` at radius `ρ` in the centered chart at `c`), whose `qmk`-image
is `∂Q_c = S³/±1`. The Q-side end of the pinned identification. -/
noncomputable def s3ToQ (c : EIndex) (a : S3) : FreeQuotient :=
  qmk ⟨centeredChartParam c.1 (scaleToChart a),
    sphere_subset_puncturedTorus (eIndex_fixedSet c)
      ⟨scaleToChart a, sqNorm_scaleToChart a, rfl⟩⟩

/-- **The composite descends through `±1`** — `s3ToQ c (negS3 a) = s3ToQ c a`. The E-side antipode
`negS3` becomes the Q-side `τ`-gluing (`qmk` identifies `x ~ τx`), via `scaleToChart_negS3` +
`centeredChartParam_involution`. This is why the map descends to `ℝP³`. -/
theorem s3ToQ_negS3 (c : EIndex) (a : S3) : s3ToQ c (negS3 a) = s3ToQ c a := by
  apply Quotient.sound
  refine ⟨-1, ?_⟩
  apply Subtype.ext
  rw [neg_one_smul_val]
  show torusFourInvolution (centeredChartParam c.1 (scaleToChart a))
    = centeredChartParam c.1 (scaleToChart (negS3 a))
  rw [centeredChartParam_involution c.1 (eIndex_fixedSet c), scaleToChart_negS3]

/-- **The Q-side boundary map** `ℝP³ → ∂Q_c ⊆ Q`. Well-defined by antipodal descent
(`s3ToQ_negS3`). The explicit composite the K6′b weld glues along (Q-side). -/
noncomputable def qBdryMap (c : EIndex) : RP3 → FreeQuotient :=
  Quotient.lift (s3ToQ c) (fun a b h => by
    rcases h with rfl | rfl
    · rfl
    · exact (s3ToQ_negS3 c a).symm)

@[simp] theorem qBdryMap_mk (c : EIndex) (a : S3) : qBdryMap c (mkRP3 a) = s3ToQ c a := rfl

/-- **The Q-side seam map is continuous.** -/
theorem continuous_s3ToQ (c : EIndex) : Continuous (s3ToQ c) :=
  continuous_quotient_mk'.comp
    (Continuous.subtype_mk ((continuous_centeredChartParam c.1).comp continuous_scaleToChart) _)

/-- **`qBdryMap c` is continuous** (descends the continuous `s3ToQ c`). -/
theorem continuous_qBdryMap (c : EIndex) : Continuous (qBdryMap c) :=
  Continuous.quotient_lift (continuous_s3ToQ c) _

/-- **The Q-side seam map lands in `∂Q_c`** (`= qmk '' boundarySphere c`, the component of the
fixed point `c`). -/
theorem qBdryMap_mem_boundaryComponent (c : EIndex) (r : RP3) :
    qBdryMap c r ∈ boundaryComponent c.1 := by
  induction r using Quotient.inductionOn with
  | _ a => exact Set.mem_image_of_mem qmk ⟨scaleToChart a, sqNorm_scaleToChart a, rfl⟩

/-- **The Q-side seam map is injective** (`ℝP³ ↪ ∂Q_c`). Uses the chart-injectivity on the closed ball
(`centeredChartParam_injOn`) and `scaleToChart_injective`, with the two `qmk`-fiber cases (`x` vs `τx`)
resolving to `mkRP3`-equality (the second via `mkRP3_neg`). -/
theorem qBdryMap_injective (c : EIndex) : Function.Injective (qBdryMap c) := by
  intro r r'
  induction r using Quotient.inductionOn with | _ a =>
  induction r' using Quotient.inductionOn with | _ a' =>
  intro h
  have hdom : ∀ b : S3, scaleToChart b ∈ {t | sqNorm t ≤ excisionRadius ^ 2} := fun b =>
    le_of_eq (sqNorm_scaleToChart b)
  rcases (qmk_eq_iff _ _).mp h with heq | heq
  · have hval : centeredChartParam c.1 (scaleToChart a) = centeredChartParam c.1 (scaleToChart a') :=
      congrArg Subtype.val heq
    exact congrArg mkRP3 (scaleToChart_injective (centeredChartParam_injOn c.1 (hdom a) (hdom a') hval))
  · have hval : centeredChartParam c.1 (scaleToChart a)
        = torusFourInvolution (centeredChartParam c.1 (scaleToChart a')) := by
      have hv := congrArg Subtype.val heq
      rwa [neg_one_smul_val] at hv
    rw [centeredChartParam_involution c.1 (eIndex_fixedSet c)] at hval
    have hdom' : chartNeg (scaleToChart a') ∈ {t | sqNorm t ≤ excisionRadius ^ 2} := by
      show sqNorm (chartNeg (scaleToChart a')) ≤ excisionRadius ^ 2
      rw [sqNorm_chartNeg]; exact le_of_eq (sqNorm_scaleToChart a')
    have hsc := centeredChartParam_injOn c.1 (hdom a) hdom' hval
    rw [← scaleToChart_negS3] at hsc
    rw [scaleToChart_injective hsc]
    exact mkRP3_neg a'

/-- **The two ends determine the same seam class**: if the Q-side images agree
(`qBdryMap c₁ r₁ = qBdryMap c₂ r₂`) then the component and class agree. Disjointness of the 16
boundary components pins `c₁ = c₂`; `qBdryMap`-injectivity then pins `r₁ = r₂`. -/
theorem seam_q_inj {c₁ c₂ : EIndex} {r₁ r₂ : RP3}
    (h : qBdryMap c₁ r₁ = qBdryMap c₂ r₂) : c₁ = c₂ ∧ r₁ = r₂ := by
  have hc : c₁.1 = c₂.1 := by
    by_contra hne
    have hmem1 : qBdryMap c₁ r₁ ∈ boundaryComponent c₁.1 := qBdryMap_mem_boundaryComponent c₁ r₁
    have hmem2 : qBdryMap c₁ r₁ ∈ boundaryComponent c₂.1 := by
      rw [h]; exact qBdryMap_mem_boundaryComponent c₂ r₂
    exact Set.disjoint_left.mp
      (boundaryComponent_disjoint (eIndex_fixedSet c₁) (eIndex_fixedSet c₂) hne) hmem1 hmem2
  have hc' : c₁ = c₂ := Subtype.ext hc
  subst hc'
  exact ⟨rfl, qBdryMap_injective c₁ h⟩

/-! ## §4. The glued carrier `K3 := Q ∪_{16 × ℝP³} (16 × E)` -/

/-- **The pre-weld disjoint sum** `Q ⊔ (16 × E)`. The 16 `E`-copies are indexed by the fixed
points (`EIndex`, `Fintype.card = 16`). -/
abbrev WeldCarrier : Type := FreeQuotient ⊕ (EIndex × ResE)

/-- **The seam join** — `a` is a Q-side boundary point and `b` its E-side partner under the pinned
`ℝP³` identification: `a = inl (qBdryMap c r)`, `b = inr (c, bdryMapRP3 r)`. -/
def SeamJoin (a b : WeldCarrier) : Prop :=
  ∃ (c : EIndex) (r : RP3), a = Sum.inl (qBdryMap c r) ∧ b = Sum.inr (c, bdryMapRP3 r)

/-- **The weld relation**: equal, or joined by a seam (either orientation). Identifies each Q-side
boundary point `qBdryMap c r ∈ ∂Q_c` with the E-side point `bdryMapRP3 r ∈ ∂E` of the `c`-th copy,
and nothing else. -/
def weldRel (a b : WeldCarrier) : Prop := a = b ∨ SeamJoin a b ∨ SeamJoin b a

theorem weldRel_refl (a : WeldCarrier) : weldRel a a := Or.inl rfl

theorem weldRel_symm {a b : WeldCarrier} (h : weldRel a b) : weldRel b a := by
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem weldRel_trans {a b d : WeldCarrier} (hab : weldRel a b) (hbd : weldRel b d) :
    weldRel a d := by
  rcases hab with rfl | hab | hab
  · exact hbd
  · -- SeamJoin a b: a = inl(q c₁ r₁), b = inr(c₁, bdry r₁)
    obtain ⟨c₁, r₁, ha, hb⟩ := hab
    rcases hbd with rfl | hbd | hbd
    · exact Or.inr (Or.inl ⟨c₁, r₁, ha, hb⟩)
    · -- SeamJoin b d: b = inl(...), contradiction with b = inr(...)
      obtain ⟨c₂, r₂, hb', _⟩ := hbd
      exact absurd (hb'.symm.trans hb) (by simp)
    · -- SeamJoin d b: d = inl(q c₂ r₂), b = inr(c₂, bdry r₂)
      obtain ⟨c₂, r₂, hd, hb'⟩ := hbd
      have hbe : Sum.inr (c₁, bdryMapRP3 r₁) = (Sum.inr (c₂, bdryMapRP3 r₂) : WeldCarrier) :=
        hb.symm.trans hb'
      have hcr : c₁ = c₂ ∧ bdryMapRP3 r₁ = bdryMapRP3 r₂ := by
        have := Sum.inr.injEq (c₁, bdryMapRP3 r₁) (c₂, bdryMapRP3 r₂) ▸ hbe
        exact Prod.mk.injEq _ _ _ _ ▸ this
      obtain ⟨hcc, hrr⟩ := hcr
      have : r₁ = r₂ := bdryMapRP3_injective hrr
      subst hcc; subst this
      exact Or.inl (ha.trans hd.symm)
  · -- SeamJoin b a: b = inl(q c₁ r₁), a = inr(c₁, bdry r₁)
    obtain ⟨c₁, r₁, hb, ha⟩ := hab
    rcases hbd with rfl | hbd | hbd
    · exact Or.inr (Or.inr ⟨c₁, r₁, hb, ha⟩)
    · -- SeamJoin b d: b = inl(q c₂ r₂), d = inr(c₂, bdry r₂)
      obtain ⟨c₂, r₂, hb', hd⟩ := hbd
      have hbe : Sum.inl (qBdryMap c₁ r₁) = (Sum.inl (qBdryMap c₂ r₂) : WeldCarrier) :=
        hb.symm.trans hb'
      have hq : qBdryMap c₁ r₁ = qBdryMap c₂ r₂ := Sum.inl.inj hbe
      obtain ⟨hcc, hrr⟩ := seam_q_inj hq
      subst hcc; subst hrr
      exact Or.inl (ha.trans hd.symm)
    · -- SeamJoin d b: d = inl(...), b = inr(...); contradiction with b = inl(...)
      obtain ⟨c₂, r₂, _, hb'⟩ := hbd
      exact absurd (hb.symm.trans hb') (by simp)

/-- **The weld setoid.** -/
def weldSetoid : Setoid WeldCarrier where
  r := weldRel
  iseqv := ⟨weldRel_refl, weldRel_symm, weldRel_trans⟩

/-- **`K3` — the glued carrier** `Q ∪_{16 × ℝP³} (16 × E)`. The closed 4-manifold carrier of the
Kummer K3 (Route B): the free quotient `Q = T⁴°/τ` welded to 16 copies of the Euler−2 disk bundle
`E` along their common `ℝP³` boundaries. Carries the quotient topology. -/
abbrev KummerK3 : Type := Quotient weldSetoid

/-- The weld quotient map `Q ⊔ (16 × E) ↠ K3`. -/
abbrev weldMk (a : WeldCarrier) : KummerK3 := Quotient.mk weldSetoid a

theorem continuous_weldMk : Continuous weldMk := continuous_quotient_mk'

theorem weldMk_surjective : Function.Surjective weldMk := Quotient.mk_surjective

/-- **The explicit 16-fold seam identification.** For each fixed point `c` and each `ℝP³`-class `r`,
the Q-side boundary point `qBdryMap c r ∈ ∂Q_c` is identified in `K3` with the E-side point
`bdryMapRP3 r ∈ ∂E` of the `c`-th `E`-copy. This is the composite of the two pinned presentations
(`qBdryMap` on the Q-side, `bdryMapRP3` on the E-side), both `S³/±1`. -/
theorem weldMk_seam (c : EIndex) (r : RP3) :
    weldMk (Sum.inl (qBdryMap c r)) = weldMk (Sum.inr (c, bdryMapRP3 r)) :=
  Quotient.sound (Or.inr (Or.inl ⟨c, r, rfl, rfl⟩))

/-! ### §4b. Instances on the carrier: `Nonempty`, `CompactSpace` -/

instance : Nonempty WeldCarrier := ⟨Sum.inl (Nonempty.some inferInstance)⟩

instance : Nonempty KummerK3 := ⟨weldMk (Nonempty.some inferInstance)⟩

instance : Finite EIndex := inferInstanceAs (Finite {c : TorusFour // c ∈ fixedFinset})

instance : CompactSpace EIndex := ⟨Set.finite_univ.isCompact⟩

instance : CompactSpace WeldCarrier :=
  inferInstanceAs (CompactSpace (FreeQuotient ⊕ (EIndex × ResE)))

/-- **`K3` is compact** — a quotient of the compact `Q ⊔ (16 × E)` (each piece compact: `Q` compact,
`E` compact, 16 finite). -/
instance : CompactSpace KummerK3 :=
  ⟨weldMk_surjective.range_eq ▸ isCompact_range continuous_weldMk⟩

/-! ## §5. `K3` is Hausdorff — the proper-map route (the `instT2SpaceResE` precedent)

The weld quotient map is proper (continuous, closed, finite fibers), so `q × q` is a closed map and
the diagonal of `K3` is closed. The closed-map computation uses that the seam is parametrized by the
compact `ℝP³` on BOTH ends (`qBdryMap` / `bdryMapRP3`), so the saturation of a closed `C` is `C`
together with 16 + 16 continuous-images-of-compact strata — a finite union of closed sets. -/

/-- **The weld quotient map is closed.** The saturation of a closed `C` is `C` plus, for each of the
16 fixed points, the two seam-partner strata (Q-partner-of-E and E-partner-of-Q), each a continuous
image of a closed (hence compact) subset of `ℝP³`. -/
theorem isClosedMap_weldMk : IsClosedMap weldMk := by
  intro C hC
  have hqm := isQuotientMap_quotient_mk' (s := weldSetoid)
  rw [← hqm.isClosed_preimage]
  have hsat : weldMk ⁻¹' (weldMk '' C) =
      C ∪ (⋃ c : EIndex, (fun r => Sum.inr (c, bdryMapRP3 r)) '' {r : RP3 | Sum.inl (qBdryMap c r) ∈ C})
        ∪ (⋃ c : EIndex, (fun r => Sum.inl (qBdryMap c r)) '' {r : RP3 | Sum.inr (c, bdryMapRP3 r) ∈ C}) := by
    ext a
    constructor
    · rintro ⟨b, hbC, hab⟩
      rcases Quotient.exact hab with rfl | hsj | hsj
      · exact Or.inl (Or.inl hbC)
      · obtain ⟨c, r, hb, ha'⟩ := hsj
        subst hb
        exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨c, ⟨r, hbC, ha'.symm⟩⟩))
      · obtain ⟨c, r, ha', hb⟩ := hsj
        subst hb
        exact Or.inr (Set.mem_iUnion.mpr ⟨c, ⟨r, hbC, ha'.symm⟩⟩)
    · rintro ((haC | ha1) | ha2)
      · exact ⟨a, haC, rfl⟩
      · rcases Set.mem_iUnion.mp ha1 with ⟨c, hc⟩
        obtain ⟨r, hrC, rfl⟩ := hc
        exact ⟨Sum.inl (qBdryMap c r), hrC, weldMk_seam c r⟩
      · rcases Set.mem_iUnion.mp ha2 with ⟨c, hc⟩
        obtain ⟨r, hrC, rfl⟩ := hc
        exact ⟨Sum.inr (c, bdryMapRP3 r), hrC, (weldMk_seam c r).symm⟩
  show IsClosed (weldMk ⁻¹' (weldMk '' C))
  rw [hsat]
  refine (hC.union ?_).union ?_
  · refine isClosed_iUnion_of_finite (fun c => ?_)
    have hcl : IsClosed {r : RP3 | Sum.inl (qBdryMap c r) ∈ C} :=
      hC.preimage (continuous_inl.comp (continuous_qBdryMap c))
    exact (hcl.isCompact.image
      (continuous_inr.comp (continuous_const.prodMk continuous_bdryMapRP3))).isClosed
  · refine isClosed_iUnion_of_finite (fun c => ?_)
    have hcl : IsClosed {r : RP3 | Sum.inr (c, bdryMapRP3 r) ∈ C} :=
      hC.preimage (continuous_inr.comp (continuous_const.prodMk continuous_bdryMapRP3))
    exact (hcl.isCompact.image (continuous_inl.comp (continuous_qBdryMap c))).isClosed

/-- **Every fiber of the weld is finite** (`≤ 2` points: a point and its unique seam partner). Each
seam-partner set is a subsingleton — the seam is `1`-to-`1` on `ℝP³` (`seam_q_inj`,
`bdryMapRP3_injective`). -/
theorem finite_weldFiber (y : KummerK3) : (weldMk ⁻¹' {y}).Finite := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep y
  have hsub : weldMk ⁻¹' {weldMk a} ⊆ {a} ∪ {b | SeamJoin a b} ∪ {b | SeamJoin b a} := by
    intro b hb
    rcases Quotient.exact hb with rfl | h | h
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  refine Set.Finite.subset ?_ hsub
  refine ((Set.finite_singleton a).union ?_).union ?_
  · refine Set.Subsingleton.finite (fun b hb b' hb' => ?_)
    obtain ⟨c, r, ha, hbr⟩ := hb
    obtain ⟨c', r', ha', hbr'⟩ := hb'
    obtain ⟨hcc, hrr⟩ := seam_q_inj (Sum.inl.inj (ha.symm.trans ha'))
    subst hcc; subst hrr; rw [hbr, hbr']
  · refine Set.Subsingleton.finite (fun b hb b' hb' => ?_)
    obtain ⟨c, r, hb1, ha1⟩ := hb
    obtain ⟨c', r', hb1', ha1'⟩ := hb'
    have hpair : (c, bdryMapRP3 r) = (c', bdryMapRP3 r') := Sum.inr.inj (ha1.symm.trans ha1')
    have hrr : r = r' := bdryMapRP3_injective (congrArg Prod.snd hpair)
    have hcc : c = c' := congrArg Prod.fst hpair
    subst hcc; subst hrr; rw [hb1, hb1']

/-- **`K3` is Hausdorff (`T2Space`).** The weld map is proper (finite fibers), so `q × q` is closed
and the diagonal — the image of the closed diagonal of the Hausdorff `Q ⊔ (16 × E)` — is closed. -/
instance instT2SpaceKummerK3 : T2Space KummerK3 := by
  have hproper : IsProperMap weldMk :=
    isProperMap_iff_isClosedMap_and_compact_fibers.mpr
      ⟨continuous_weldMk, isClosedMap_weldMk, fun y => (finite_weldFiber y).isCompact⟩
  rw [t2_iff_isClosed_diagonal]
  have hdiag : Set.diagonal KummerK3 = Prod.map weldMk weldMk '' Set.diagonal WeldCarrier := by
    apply Set.eq_of_subset_of_subset
    · rintro ⟨y1, y2⟩ hy
      have hy' : y1 = y2 := hy
      subst hy'
      obtain ⟨a, rfl⟩ := Quotient.exists_rep y1
      exact ⟨(a, a), rfl, rfl⟩
    · rintro ⟨y1, y2⟩ ⟨⟨a, b⟩, hab, heq⟩
      have hab' : a = b := hab
      have h1 : weldMk a = y1 := congrArg Prod.fst heq
      have h2 : weldMk b = y2 := congrArg Prod.snd heq
      show y1 = y2
      rw [← h1, ← h2, hab']
  rw [hdiag]
  exact (hproper.prodMap hproper).isClosedMap _ isClosed_diagonal

/-! ## §6. Set-level structure: the piece decomposition and the welded seam (boundarylessness)

The two closed pieces (`Q` and the 16 `E`'s) cover `K3` and meet exactly along the seam — the 16
former boundary `ℝP³`'s, now IDENTIFIED (each `∂Q_c` glued to `∂E` of the `c`-th copy). This is the
set-level content of "the boundary is welded shut": `seam` is BOTH the image of `∂Q` and the image of
`∂E` (`seam_eq_qBoundary_image`), so every former boundary point is now an interior seam point of the
closed carrier. The stronger smooth statement — that each seam point has an `ℝ⁴` (not half-space)
neighborhood via the glued Q-collar ∪ E-collar double-collar chart — is the K6 charted follow-on
(Priority 4), gated on the collar-chart layers (`KummerQuotientManifold.boundaryChart` on the Q-side
and the E-side `IsManifold` assembly in flight). -/

/-- **The image of `Q` in `K3`** — a closed piece (continuous image of the compact `Q`). -/
def qImage : Set KummerK3 := Set.range (fun q : FreeQuotient => weldMk (Sum.inl q))

/-- **The image of the 16 `E`-copies in `K3`** — a closed piece. -/
def eImage : Set KummerK3 := Set.range (fun p : EIndex × ResE => weldMk (Sum.inr p))

/-- **The welded seam** — the 16 former boundary `ℝP³`'s, expressed via the E-side end
`bdryMapRP3`. -/
def seam : Set KummerK3 :=
  ⋃ c : EIndex, Set.range (fun r : RP3 => weldMk (Sum.inr (c, bdryMapRP3 r)))

theorem isClosed_qImage : IsClosed qImage :=
  (isCompact_range (continuous_weldMk.comp continuous_inl)).isClosed

theorem isClosed_eImage : IsClosed eImage :=
  (isCompact_range (continuous_weldMk.comp continuous_inr)).isClosed

/-- **The two pieces cover `K3`** (every point is the image of a `Q`-point or an `E`-point). -/
theorem qImage_union_eImage : qImage ∪ eImage = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨a, rfl⟩ := weldMk_surjective x
  cases a with
  | inl q => exact Or.inl ⟨q, rfl⟩
  | inr p => exact Or.inr ⟨p, rfl⟩

/-- **The seam's E-copy fibers land in `∂E`**: each `weldMk (inr (c, bdryMapRP3 r))` is the image of a
boundary point of the `c`-th `E`-copy (`bdryMapRP3` has range `∂E`). -/
theorem seam_fiber_subset_eBoundary (c : EIndex) :
    Set.range (fun r : RP3 => weldMk (Sum.inr (c, bdryMapRP3 r)))
      ⊆ weldMk '' (Sum.inr '' ((fun e => (c, e)) '' boundaryE)) := by
  rintro _ ⟨r, rfl⟩
  exact ⟨Sum.inr (c, bdryMapRP3 r),
    ⟨(c, bdryMapRP3 r), ⟨bdryMapRP3 r, range_bdryMapRP3_eq_boundaryE ▸ Set.mem_range_self r, rfl⟩,
      rfl⟩, rfl⟩

/-- **The seam is ALSO the image of `∂Q`** — the two former boundaries `∂Q_c` and `∂E` are the SAME
set in `K3` (the weld identifies them). This is the set-level "boundary welded shut". -/
theorem seam_eq_qBoundary_image :
    seam = ⋃ c : EIndex, Set.range (fun r : RP3 => weldMk (Sum.inl (qBdryMap c r))) := by
  refine Set.iUnion_congr fun c => ?_
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨r, rfl⟩; exact ⟨r, weldMk_seam c r⟩
  · rintro ⟨r, rfl⟩; exact ⟨r, (weldMk_seam c r).symm⟩

/-- **The two pieces meet exactly on the seam**: `qImage ∩ eImage = seam`. So `Q` and the `E`'s are
glued precisely along the 16 welded `ℝP³`'s, and nowhere else. -/
theorem qImage_inter_eImage : qImage ∩ eImage = seam := by
  ext x
  simp only [qImage, eImage, seam, Set.mem_inter_iff, Set.mem_range, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨q, hq⟩, ⟨p, hp⟩⟩
    have hqp : weldMk (Sum.inl q) = weldMk (Sum.inr p) := hq.trans hp.symm
    rcases Quotient.exact hqp with h | h | h
    · exact absurd h (by simp)
    · obtain ⟨c, r, _, hpr⟩ := h
      exact ⟨c, r, by rw [← hpr]; exact hp⟩
    · obtain ⟨c, r, hq', _⟩ := h
      exact absurd hq' (by simp)
  · rintro ⟨c, r, rfl⟩
    exact ⟨⟨qBdryMap c r, weldMk_seam c r⟩, ⟨(c, bdryMapRP3 r), rfl⟩⟩

/-! ## §7. The pieces embed — the interior charts descend (Priority 4, topological floor)

The weld only ever identifies an `inl`-point with an `inr`-point (a Q-boundary point with its E-side
seam partner) — NEVER `inl`-with-`inl` or `inr`-with-`inr`. So `weldMk ∘ inl` and `weldMk ∘ inr` are
GLOBALLY injective, hence (compact source, `T2` target) CLOSED TOPOLOGICAL EMBEDDINGS: `Q` embeds as a
closed subspace and each `E`-copy embeds as a closed subspace of `K3`. This is the topological floor
of Priority 4's "the `Q`-atlas and the `E`-atlases embed"; the smooth chart descent (the seam
double-collar) is the follow-on, gated on the collar-chart layers (`KummerQuotientManifold` Q-side,
the E-side `IsManifold` in flight). -/

/-- **`Q` embeds injectively** — the weld never glues two `Q`-points (only `Q`-boundary to `E`). -/
theorem weldMk_inl_injective : Function.Injective (fun q : FreeQuotient => weldMk (Sum.inl q)) := by
  intro q q' h
  rcases Quotient.exact h with he | hsj | hsj
  · exact Sum.inl.inj he
  · obtain ⟨_, _, _, h2⟩ := hsj; exact absurd h2 (by simp)
  · obtain ⟨_, _, _, h2⟩ := hsj; exact absurd h2 (by simp)

/-- **The 16 `E`-copies embed injectively** — the weld never glues two `E`-points. -/
theorem weldMk_inr_injective :
    Function.Injective (fun p : EIndex × ResE => weldMk (Sum.inr p)) := by
  intro p p' h
  rcases Quotient.exact h with he | hsj | hsj
  · exact Sum.inr.inj he
  · obtain ⟨_, _, h1, _⟩ := hsj; exact absurd h1 (by simp)
  · obtain ⟨_, _, h1, _⟩ := hsj; exact absurd h1 (by simp)

/-- **`Q` embeds as a closed subspace of `K3`** (continuous injective, compact source, `T2` target).
The Q-side interior charts descend as topological charts. -/
theorem isClosedEmbedding_qImage :
    Topology.IsClosedEmbedding (fun q : FreeQuotient => weldMk (Sum.inl q)) :=
  (continuous_weldMk.comp continuous_inl).isClosedEmbedding weldMk_inl_injective

/-- **The 16 `E`-copies embed as a closed subspace of `K3`.** -/
theorem isClosedEmbedding_eImage :
    Topology.IsClosedEmbedding (fun p : EIndex × ResE => weldMk (Sum.inr p)) :=
  (continuous_weldMk.comp continuous_inr).isClosedEmbedding weldMk_inr_injective

/-- **Each single `E`-copy embeds as a closed subspace of `K3`** — the disk bundle `E` sits inside
`K3` as the resolution of the `c`-th `A₁` singularity. -/
theorem isClosedEmbedding_eCopy (c : EIndex) :
    Topology.IsClosedEmbedding (fun e : ResE => weldMk (Sum.inr (c, e))) := by
  have hinj : Function.Injective (fun e : ResE => weldMk (Sum.inr (c, e))) :=
    fun e e' h => congrArg Prod.snd (weldMk_inr_injective h)
  exact (continuous_weldMk.comp
    (continuous_inr.comp (continuous_const.prodMk continuous_id))).isClosedEmbedding hinj

end SKEFTHawking.KummerWeld
