/-
# Phase 5q.H — the Kummer K3 generator, K6′a (Route B): the concrete Euler−2 disk bundle `E`

The A₁-resolution piece of the classical cut-and-paste Kummer construction. Read the **binding
Route-B design doc** `docs/dev-loops/Phase5qH/KUMMER_K4K10_DESIGN.md` (K6′a row) and
`KummerPuncturedTorus.lean`'s pinned **S³/±1 antipodal boundary presentation** (Design Risk #2,
BINDING) first: `K3 := (T⁴°/τ) ∪_{16 × ℝP³} 16 × E`, where `E` is THIS module's object — the
Euler−2 disk bundle over `S²`, welded to the free quotient along `∂E ≅ ℝP³`.

This module ships the **concrete two-chart model of `E`** UNCONDITIONALLY (kernel-pure
`{propext, Classical.choice, Quot.sound}`; no `sorry`/`native_decide`/`maxHeartbeats`/axiom):

**§1 — the 𝒪(−2) clutching transition.** `clutch (z,w) = (z⁻¹, z²·w)` on `ℂ × ℂ`, the transition of
the Euler−2 bundle over the base circle-overlap. Landed facts: it is **its own inverse** on `z ≠ 0`
(`clutch_involutive_on` — the Euler−2 clutching function `z ↦ z²` squares the base flip to the
identity), **real-smooth away from `z = 0`** (`contDiffOn_clutch`, holomorphic on the overlap),
**preserves the fiber norm on the base equator `‖z‖ = 1`** (`clutch_fiber_norm` — so it restricts to
the disk/circle fiber bundle), with a **falsifiable numerical pin** (`clutch (2,3) = (2⁻¹, 12)`).

**§2 — the glued carrier `E`.** `E := ((D²×D²) ⊕ (D²×D²)) / ~`, the two disk-bundle charts glued
along the base equator `‖z‖ = 1` by the clutch. Shipped as a genuine quotient **topological space**
with continuous chart inclusions (`chart0`/`chart1`) and the **falsifiable gluing identity**
(`chart_glue`: `chart0 ⟨z,w⟩ = chart1 (clutch)` for `‖z‖ = 1`); the equivalence relation's classes
are exactly the glued pairs (`resSetoid` is honestly an `Equivalence`, hand-built rather than an
`EqvGen` closure). The smooth-manifold-with-boundary certificate (`∂ = ` the `‖w‖ = 1` locus) is the
K4′-shaped residual.

**§3 — the boundary `∂E ≅ ℝP³` in the pinned S³/±1 presentation (the brick's crux — what K6′b welds
along).** `∂E` = the glued circle bundle (two solid tori `D² × S¹`); `ℝP³ := S³/±1` in the
antipodal-quotient presentation of `KummerPuncturedTorus` (`S³ ⊂ ℂ²`, antipodal `(a,b) ↦ (−a,−b)`,
the `MulAction.orbitRel ℤˣ` template of `RP4Manifold` one dimension down). The **explicit descending
map** is the Hopf-coordinate map `ρ(a,b) = chart0 ⟨a/b, (b/‖b‖)²⟩` (on `‖a‖ ≤ ‖b‖`) /
`chart1 ⟨b/a, (a/‖a‖)²⟩` (on `‖a‖ ≥ ‖b‖`): the **squaring kills the sign** so `ρ` is `±1`-invariant
(`bdryMap_neg` — descends to `ℝP³`), and on the equator overlap the two chart values glue **exactly
through the clutch** (`bdryMap_seam` — the seam-match certificate K6′b consumes).

**§4 — the zero section.** The embedded `S²` (`w = 0` in both charts, glued by `z ↦ z⁻¹` — the
standard two-chart sphere) and its inclusion into `E`. The `(−2)` self-intersection number belongs
to K8, not here; the H₂-generator homology packaging is the residual.
-/
import Mathlib
import SKEFTHawking.KummerPuncturedTorus

namespace SKEFTHawking.KummerResolutionPiece

open scoped Manifold ContDiff RealInnerProductSpace
open Metric Set

noncomputable section

/-! ## §1. The 𝒪(−2) clutching transition `(z, w) ↦ (z⁻¹, z²·w)` -/

/-- **The 𝒪(−2) clutching transition** of the Euler−2 disk bundle over `S²`, on the base
circle-overlap `z` (with `w` the fiber): `clutch (z, w) = (z⁻¹, z²·w)`. Holomorphic away from
`z = 0`; on the base equator `‖z‖ = 1` it preserves the fiber norm, so it restricts to the disk/circle
fiber bundle. -/
def clutch (p : ℂ × ℂ) : ℂ × ℂ := (p.1⁻¹, p.1 ^ 2 * p.2)

@[simp] theorem clutch_fst (p : ℂ × ℂ) : (clutch p).1 = p.1⁻¹ := rfl
@[simp] theorem clutch_snd (p : ℂ × ℂ) : (clutch p).2 = p.1 ^ 2 * p.2 := rfl

/-- **Falsifiable numerical pin**: `clutch (2, 3) = (2⁻¹, 12)` (base `2 ↦ 2⁻¹`, fiber `3 ↦ 4·3 = 12`).
Not `:= True`; the transition's explicit formula evaluated at a concrete point. -/
theorem clutch_pin : clutch (2, 3) = (2⁻¹, 12) := by
  simp only [clutch, Prod.mk.injEq]
  norm_num

/-- **The Euler−2 clutching is its own inverse on the overlap `z ≠ 0`.** `z ↦ z²` squares the base
flip `z ↦ z⁻¹` to the identity: `clutch (clutch (z, w)) = (z, w)`. This involutivity is what makes the
two-chart gluing especially clean (the gluing relation's classes are exactly pairs). -/
theorem clutch_involutive_on {p : ℂ × ℂ} (hp : p.1 ≠ 0) : clutch (clutch p) = p := by
  obtain ⟨z, w⟩ := p
  simp only [clutch, inv_inv, Prod.mk.injEq, true_and]
  field_simp

/-- **Fiber-norm preservation on the base equator `‖z‖ = 1`**: `‖(clutch (z, w)).2‖ = ‖w‖`. On the
equator `‖z²‖ = ‖z‖² = 1`, so the clutch maps the closed disk / unit circle fiber to itself — the
fact that `clutch` restricts to the disk bundle `E` and the circle bundle `∂E`. -/
theorem clutch_fiber_norm {p : ℂ × ℂ} (hz : ‖p.1‖ = 1) : ‖(clutch p).2‖ = ‖p.2‖ := by
  simp only [clutch_snd, norm_mul, norm_pow, hz, one_pow, one_mul]

/-- **The base flip is an isometry**: `‖(clutch (z, w)).1‖ = 1` when `‖z‖ = 1` (`‖z⁻¹‖ = ‖z‖⁻¹`). -/
theorem clutch_base_norm {p : ℂ × ℂ} (hz : ‖p.1‖ = 1) : ‖(clutch p).1‖ = 1 := by
  simp only [clutch_fst, norm_inv, hz, inv_one]

/-- **The clutch is real-smooth away from `z = 0`** (`C^∞`, in fact `C^ω`): holomorphic on the overlap
`z ≠ 0` — `z ↦ z⁻¹` is smooth off `0` and `(z, w) ↦ z²·w` is a polynomial. The explicit transition
smoothness the K6′a design names as the genuinely-new content. -/
theorem contDiffOn_clutch : ContDiffOn ℝ ⊤ clutch {p : ℂ × ℂ | p.1 ≠ 0} :=
  (contDiffOn_fst.inv (fun _ hp => hp)).prodMk ((contDiffOn_fst.pow 2).mul contDiffOn_snd)

/-! ## §2. The glued carrier `E` — two disk-bundle charts welded along the base equator -/

/-- Closed unit disk `D² ⊆ ℂ` (the base chart and the fiber). -/
abbrev Disk : Type := {z : ℂ // ‖z‖ ≤ 1}

/-- A single disk-bundle chart `D² × D²` (base disk × fiber disk). -/
abbrev ResChart : Type := Disk × Disk

/-- **The clutch on disks** — the transition of chart 0 into chart 1, on the base equator
`‖z‖ = 1`. On the equator `‖z⁻¹‖ = 1` and `‖z²·w‖ = ‖w‖`, so it lands in `D² × D²`. Its underlying
`ℂ²` value is exactly `clutch` (§1). -/
def clutchDisk (p : ResChart) (hz : ‖(p.1 : ℂ)‖ = 1) : ResChart :=
  (⟨(p.1 : ℂ)⁻¹, by rw [norm_inv, hz, inv_one]⟩,
   ⟨(p.1 : ℂ) ^ 2 * (p.2 : ℂ), by rw [norm_mul, norm_pow, hz, one_pow, one_mul]; exact p.2.2⟩)

@[simp] theorem clutchDisk_fst_coe (p : ResChart) (hz : ‖(p.1 : ℂ)‖ = 1) :
    ((clutchDisk p hz).1 : ℂ) = (p.1 : ℂ)⁻¹ := rfl
@[simp] theorem clutchDisk_snd_coe (p : ResChart) (hz : ‖(p.1 : ℂ)‖ = 1) :
    ((clutchDisk p hz).2 : ℂ) = (p.1 : ℂ) ^ 2 * (p.2 : ℂ) := rfl

/-- **The gluing predicate** (chart-0 point `p` welds to chart-1 point `q`): `p` is on the base
equator and `q` is its clutch image. Concretely `q = clutchDisk p`. -/
def glued (p q : ResChart) : Prop :=
  ‖(p.1 : ℂ)‖ = 1 ∧ (q.1 : ℂ) = (p.1 : ℂ)⁻¹ ∧ (q.2 : ℂ) = (p.1 : ℂ) ^ 2 * (p.2 : ℂ)

/-- **The core (symmetric) gluing relation** on the two-chart disjoint union: chart-0 `p` welds to
chart-1 `q` iff `glued p q`; same-chart points are never core-related (reflexivity is added in
`resRel`). -/
def gcore : ResChart ⊕ ResChart → ResChart ⊕ ResChart → Prop
  | Sum.inl p, Sum.inr q => glued p q
  | Sum.inr q, Sum.inl p => glued p q
  | _, _ => False

/-- **The gluing equivalence relation**: reflexivity plus the core weld. Because the clutch is an
involution, each non-trivial class is exactly a pair `{inl p, inr (clutchDisk p)}`. -/
def resRel (a b : ResChart ⊕ ResChart) : Prop := a = b ∨ gcore a b

theorem gcore_symm {a b : ResChart ⊕ ResChart} (h : gcore a b) : gcore b a := by
  cases a <;> cases b <;> simp only [gcore] at h ⊢ <;> exact h

/-- The base-coordinate of a glued chart-0 point is nonzero (it lies on the equator). -/
theorem glued_fst_ne_zero {p q : ResChart} (h : glued p q) : (p.1 : ℂ) ≠ 0 := by
  obtain ⟨h1, _, _⟩ := h
  intro h0; rw [h0, norm_zero] at h1; exact one_ne_zero h1.symm

/-- **A chart-0 point welds to at most one chart-1 point** (the clutch is injective): if `p` welds to
both `q` and `q'`, then `q = q'`. -/
theorem glued_right_unique {p q q' : ResChart} (h : glued p q) (h' : glued p q') : q = q' := by
  obtain ⟨_, hq1, hq2⟩ := h
  obtain ⟨_, hq1', hq2'⟩ := h'
  exact Prod.ext (Subtype.ext (by rw [hq1, hq1'])) (Subtype.ext (by rw [hq2, hq2']))

/-- **A chart-1 point is welded from at most one chart-0 point** (the clutch is injective the other
way): if both `p` and `p'` weld to `q`, then `p = p'`. Uses `inv` injectivity on the base flip and
cancellation of `z² ≠ 0` on the fiber. -/
theorem glued_left_unique {p p' q : ResChart} (h : glued p q) (h' : glued p' q) : p = p' := by
  obtain ⟨hz, hq1, hq2⟩ := h
  obtain ⟨hz', hq1', hq2'⟩ := h'
  have hp0 : (p.1 : ℂ) ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have hbase : (p.1 : ℂ) = (p'.1 : ℂ) := by
    have : (p.1 : ℂ)⁻¹ = (p'.1 : ℂ)⁻¹ := by rw [← hq1, ← hq1']
    exact inv_injective this
  have hfib : (p.2 : ℂ) = (p'.2 : ℂ) := by
    have hpow : (p.1 : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hp0
    have : (p.1 : ℂ) ^ 2 * (p.2 : ℂ) = (p.1 : ℂ) ^ 2 * (p'.2 : ℂ) := by
      rw [← hq2, hq2', hbase]
    exact mul_left_cancel₀ hpow this
  exact Prod.ext (Subtype.ext hbase) (Subtype.ext hfib)

theorem resRel_equivalence : Equivalence resRel := by
  refine ⟨fun a => Or.inl rfl, ?_, ?_⟩
  · rintro a b (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr (gcore_symm h)
  · rintro a b c (rfl | hab) (rfl | hbc)
    · exact Or.inl rfl
    · exact Or.inr hbc
    · exact Or.inr hab
    · -- both non-trivial welds: a,b differ in chart; b,c differ in chart; so a,c same chart, a = c
      cases a with
      | inl p =>
        cases b with
        | inl _ => exact (hab : False).elim
        | inr q =>
          cases c with
          | inl p' =>
            have : p = p' := glued_left_unique (hab : glued p q) (hbc : glued p' q)
            exact Or.inl (by rw [this])
          | inr _ => exact (hbc : False).elim
      | inr q =>
        cases b with
        | inr _ => exact (hab : False).elim
        | inl p =>
          cases c with
          | inr q' =>
            have : q = q' := glued_right_unique (hab : glued p q) (hbc : glued p q')
            exact Or.inl (by rw [this])
          | inl _ => exact (hbc : False).elim

/-- The gluing setoid on the two-chart disjoint union. -/
def resSetoid : Setoid (ResChart ⊕ ResChart) := ⟨resRel, resRel_equivalence⟩

/-- **The glued carrier `E`** — the Euler−2 disk bundle over `S²`, as a quotient topological space:
two `D² × D²` charts welded along the base equator by the 𝒪(−2) clutch. -/
def ResE : Type := Quotient resSetoid

instance : TopologicalSpace ResE := inferInstanceAs (TopologicalSpace (Quotient resSetoid))

instance : Nonempty ResE :=
  ⟨Quotient.mk resSetoid (Sum.inl (⟨0, by simp⟩, ⟨0, by simp⟩))⟩

/-- **Chart-0 inclusion** `D² × D² → E`. -/
def chart0 (p : ResChart) : ResE := Quotient.mk resSetoid (Sum.inl p)

/-- **Chart-1 inclusion** `D² × D² → E`. -/
def chart1 (p : ResChart) : ResE := Quotient.mk resSetoid (Sum.inr p)

theorem continuous_chart0 : Continuous chart0 :=
  continuous_quotient_mk'.comp continuous_inl

theorem continuous_chart1 : Continuous chart1 :=
  continuous_quotient_mk'.comp continuous_inr

/-- **The gluing identity** (falsifiable, tied to the actual clutch): on the base equator `‖z‖ = 1`,
the chart-0 point `p` and the chart-1 point `clutchDisk p` are the SAME point of `E`. This is the
weld that closes the two `D² × D²` charts into the Euler−2 bundle. -/
theorem chart_glue {p : ResChart} (hz : ‖(p.1 : ℂ)‖ = 1) :
    chart0 p = chart1 (clutchDisk p hz) :=
  Quotient.sound (Or.inr (show glued p (clutchDisk p hz) from ⟨hz, rfl, rfl⟩))

/-! ## §3. The boundary `∂E ≅ ℝP³` in the pinned S³/±1 presentation (the brick's crux)

`∂E` is the fiber-boundary locus `‖w‖ = 1` of `E` (a circle bundle over `S²`, the lens space
`L(2,1)`). `ℝP³ := S³/±1` in the antipodal-quotient presentation pinned by `KummerPuncturedTorus`
(`S³ ⊂ ℂ²`, antipodal `(a,b) ↦ (−a,−b)`). The explicit descending map is the Hopf-coordinate map. -/

/-- **`S³ ⊂ ℂ²`** — the unit 3-sphere in the pinned presentation `‖a‖² + ‖b‖² = 1`. -/
abbrev S3 : Type := {p : ℂ × ℂ // ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 = 1}

/-- **The antipodal map** `(a, b) ↦ (−a, −b)` on `S³` (the free `ℤ/2` action whose quotient is
`ℝP³`). -/
def negS3 (x : S3) : S3 := ⟨(-x.1.1, -x.1.2), by simpa [norm_neg] using x.2⟩

@[simp] theorem negS3_fst (x : S3) : (negS3 x).1.1 = -x.1.1 := rfl
@[simp] theorem negS3_snd (x : S3) : (negS3 x).1.2 = -x.1.2 := rfl

theorem negS3_involutive (x : S3) : negS3 (negS3 x) = x := by
  apply Subtype.ext; simp [negS3]

/-- **The antipodal equivalence relation** `x ~ y ↔ y = x ∨ y = −x`. Classes are exactly the pairs
`{x, −x}` (free action: `x ≠ −x` on the unit sphere). -/
def antipRel (x y : S3) : Prop := y = x ∨ y = negS3 x

theorem antipRel_equivalence : Equivalence antipRel := by
  refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
  · rintro x y (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (negS3_involutive x).symm
  · rintro x y z (rfl | rfl) (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl (negS3_involutive x)

/-- The antipodal setoid on `S³`. -/
def antipSetoid : Setoid S3 := ⟨antipRel, antipRel_equivalence⟩

/-- **`ℝP³ := S³/±1`** — the antipodal quotient, in the presentation pinned by
`KummerPuncturedTorus` (Design Risk #2). This is the boundary model `∂E` must weld to. -/
def RP3 : Type := Quotient antipSetoid

instance : TopologicalSpace RP3 := inferInstanceAs (TopologicalSpace (Quotient antipSetoid))

/-- The quotient map `S³ → ℝP³`. -/
def mkRP3 (x : S3) : RP3 := Quotient.mk antipSetoid x

theorem continuous_mkRP3 : Continuous mkRP3 := continuous_quotient_mk'

/-- **Antipodal descent**: `mkRP3 (−x) = mkRP3 x` (the class of a sphere point equals that of its
antipode) — the `mk_neg` fact of the `RP4Manifold` template, one dimension down. -/
theorem mkRP3_neg (x : S3) : mkRP3 (negS3 x) = mkRP3 x :=
  Quotient.sound (Or.inr (negS3_involutive x).symm)

/-! ### §3.1 The Hopf-coordinate boundary map `S³ → ∂E ⊆ E` -/

/-- **Fiber-boundary normalization**: `‖(c/‖c‖)²‖ = 1` for `c ≠ 0` — the Hopf fiber coordinate lands
on the circle-fiber boundary `‖w‖ = 1` of `E`. -/
theorem fiber_norm_eq_one {c : ℂ} (hc : c ≠ 0) : ‖((c : ℂ) / (‖c‖ : ℂ)) ^ 2‖ = 1 := by
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg c),
    div_self (norm_ne_zero_iff.mpr hc), one_pow]

/-- On the chart-0 hemisphere `‖a‖ ≤ ‖b‖` of `S³`, the base coordinate `b` is nonzero
(`‖b‖ ≥ 1/√2`). -/
theorem S3_snd_ne_zero {x : S3} (h : ‖x.1.1‖ ≤ ‖x.1.2‖) : x.1.2 ≠ 0 := by
  intro hb
  have hx := x.2
  rw [hb, norm_zero] at h hx
  have ha : ‖x.1.1‖ = 0 := le_antisymm h (norm_nonneg _)
  rw [ha] at hx; norm_num at hx

/-- On the chart-1 hemisphere `‖b‖ ≤ ‖a‖` of `S³`, the base coordinate `a` is nonzero. -/
theorem S3_fst_ne_zero {x : S3} (h : ‖x.1.2‖ ≤ ‖x.1.1‖) : x.1.1 ≠ 0 := by
  intro ha
  have hx := x.2
  rw [ha, norm_zero] at h hx
  have hb : ‖x.1.2‖ = 0 := le_antisymm h (norm_nonneg _)
  rw [hb] at hx; norm_num at hx

/-- **The Hopf-coordinate boundary map** `ρ : S³ → E`. On the chart-0 hemisphere `‖a‖ ≤ ‖b‖` it is
`ρ(a,b) = chart0 ⟨a/b, (b/‖b‖)²⟩`; on the chart-1 hemisphere `‖a‖ ≥ ‖b‖` it is
`ρ(a,b) = chart1 ⟨b/a, (a/‖a‖)²⟩`. The base coordinate is the affine `ℂP¹` coordinate and the fiber
coordinate is the **squared** phase (the squaring is what descends through `±1` and produces the
Euler−2 clutching on the equator). Its image lies in the fiber-boundary `‖w‖ = 1` locus `∂E`. -/
def bdryMap (x : S3) : ResE :=
  if h : ‖x.1.1‖ ≤ ‖x.1.2‖ then
    chart0 (⟨x.1.1 / x.1.2, by
        rw [norm_div]; exact (div_le_one (norm_pos_iff.mpr (S3_snd_ne_zero h))).mpr h⟩,
      ⟨(x.1.2 / (‖x.1.2‖ : ℂ)) ^ 2, le_of_eq (fiber_norm_eq_one (S3_snd_ne_zero h))⟩)
  else
    chart1 (⟨x.1.2 / x.1.1, by
        rw [norm_div]
        exact (div_le_one (norm_pos_iff.mpr (S3_fst_ne_zero (not_le.mp h).le))).mpr (not_le.mp h).le⟩,
      ⟨(x.1.1 / (‖x.1.1‖ : ℂ)) ^ 2, le_of_eq (fiber_norm_eq_one (S3_fst_ne_zero (not_le.mp h).le))⟩)

/-- **The Hopf coordinates transform by the Euler−2 clutch on the equator** (the seam-match certificate
K6′b welds along). For `‖a‖ = ‖b‖` (both nonzero), the chart-0 Hopf point `p = ⟨a/b, (b/‖b‖)²⟩` has
`clutchDisk p = ⟨b/a, (a/‖a‖)²⟩` — i.e. the chart-1 Hopf coordinates. Composed with `chart_glue` this
says the two hemisphere formulas define the SAME point of `∂E`. -/
theorem hopf_clutch {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : ‖a‖ = ‖b‖) (p : ResChart)
    (hp1 : (p.1 : ℂ) = a / b) (hp2 : (p.2 : ℂ) = (b / (‖b‖ : ℂ)) ^ 2) (hz : ‖(p.1 : ℂ)‖ = 1) :
    ((clutchDisk p hz).1 : ℂ) = b / a ∧ ((clutchDisk p hz).2 : ℂ) = (a / (‖a‖ : ℂ)) ^ 2 := by
  refine ⟨?_, ?_⟩
  · rw [clutchDisk_fst_coe, hp1, inv_div]
  · rw [clutchDisk_snd_coe, hp1, hp2]
    have hbc : (‖b‖ : ℂ) = (‖a‖ : ℂ) := by exact_mod_cast hab.symm
    have hac : (‖a‖ : ℂ) ≠ 0 := by
      simpa [Complex.ofReal_ne_zero] using norm_ne_zero_iff.mpr ha
    rw [hbc]
    field_simp

/-! ### §3.2 Antipodal descent, the map `ℝP³ → ∂E`, and the boundary locus -/

/-- **The Hopf map is `±1`-invariant** — `ρ(−a, −b) = ρ(a, b)`. The squaring in the fiber coordinate
kills the sign (`(−b/‖−b‖)² = (b/‖b‖)²`) and `(−a)/(−b) = a/b` fixes the base coordinate; the
hemisphere test is `‖·‖`-invariant. This is why `ρ` descends to `ℝP³`. -/
theorem bdryMap_neg (x : S3) : bdryMap (negS3 x) = bdryMap x := by
  have hn1 : ‖(negS3 x).1.1‖ = ‖x.1.1‖ := by simp [negS3]
  have hn2 : ‖(negS3 x).1.2‖ = ‖x.1.2‖ := by simp [negS3]
  unfold bdryMap
  by_cases h : ‖x.1.1‖ ≤ ‖x.1.2‖
  · rw [dif_pos (by rw [hn1, hn2]; exact h), dif_pos h]
    refine congrArg chart0 (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · simp [negS3, neg_div_neg_eq]
    · simp [negS3, neg_div]
  · rw [dif_neg (by rw [hn1, hn2]; exact h), dif_neg h]
    refine congrArg chart1 (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · simp [negS3, neg_div_neg_eq]
    · simp [negS3, neg_div]

/-- **The descended boundary map** `ρ̄ : ℝP³ → E`. Well-defined by antipodal invariance
(`bdryMap_neg`); its image is the boundary `∂E`. This is the explicit `ℝP³ → ∂E` identification the
K6′a design names as the brick's crux — what K6′b welds along. -/
def bdryMapRP3 : RP3 → ResE :=
  Quotient.lift bdryMap (by
    intro a b h
    rcases h with rfl | rfl
    · rfl
    · exact (bdryMap_neg a).symm)

@[simp] theorem bdryMapRP3_mk (x : S3) : bdryMapRP3 (mkRP3 x) = bdryMap x := rfl

/-- **The boundary `∂E`** — the fiber-boundary locus `‖w‖ = 1` of `E` (the circle bundle over `S²`,
the lens space `L(2,1) = ℝP³`). -/
def boundaryE : Set ResE :=
  {y | ∃ p : ResChart, ‖(p.2 : ℂ)‖ = 1 ∧ (y = chart0 p ∨ y = chart1 p)}

/-- **The Hopf map lands in `∂E`**: every `ρ(a,b)` is on the fiber-boundary `‖w‖ = 1` (the fiber
coordinate is `(·/‖·‖)²`, of norm 1). So `ρ : S³ → ∂E` — the boundary is the image. -/
theorem bdryMap_mem_boundary (x : S3) : bdryMap x ∈ boundaryE := by
  unfold bdryMap
  by_cases h : ‖x.1.1‖ ≤ ‖x.1.2‖
  · rw [dif_pos h]
    exact ⟨_, fiber_norm_eq_one (S3_snd_ne_zero h), Or.inl rfl⟩
  · rw [dif_neg h]
    exact ⟨_, fiber_norm_eq_one (S3_fst_ne_zero (not_le.mp h).le), Or.inr rfl⟩

/-! ### §3.3 Point-equality criteria in `E` (quotient unwinding — used by injectivity and K6′b) -/

/-- **Two chart-0 points coincide in `E` iff their coordinates coincide** (the chart-0 inclusion is
injective): same-chart points are never core-welded, so `chart0 p = chart0 q ↔ p = q`. -/
theorem chart0_inj_iff {p q : ResChart} : chart0 p = chart0 q ↔ p = q := by
  constructor
  · intro h
    rcases Quotient.exact h with (heq | hg)
    · exact Sum.inl.inj heq
    · exact (hg : False).elim
  · rintro rfl; rfl

/-- **Two chart-1 points coincide in `E` iff their coordinates coincide.** -/
theorem chart1_inj_iff {p q : ResChart} : chart1 p = chart1 q ↔ p = q := by
  constructor
  · intro h
    rcases Quotient.exact h with (heq | hg)
    · exact Sum.inr.inj heq
    · exact (hg : False).elim
  · rintro rfl; rfl

/-- **A chart-0 point equals a chart-1 point iff they are welded** (`glued`): the only cross-chart
identifications in `E` are the equator welds. -/
theorem chart0_eq_chart1_iff {p q : ResChart} : chart0 p = chart1 q ↔ glued p q := by
  constructor
  · intro h
    rcases Quotient.exact h with (heq | hg)
    · exact absurd heq (by simp)
    · exact hg
  · intro h; exact Quotient.sound (Or.inr h)

/-! ### §3.4 Injectivity of `ℝP³ → ∂E` -/

/-- **The Hopf coordinate recovery lemma** (the algebraic core of injectivity): two unit-sphere points
with the same base ratio `a/b = a'/b'` and the same squared fiber phase `(b/‖b‖)² = (b'/‖b'‖)²` are
equal up to the antipodal sign. The `±` is exactly the square-root ambiguity the `ℝP³` quotient
absorbs. -/
theorem recover {a b a' b' : ℂ} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hn : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (hn' : ‖a'‖ ^ 2 + ‖b'‖ ^ 2 = 1)
    (hbase : a / b = a' / b') (hfib : (b / (‖b‖ : ℂ)) ^ 2 = (b' / (‖b'‖ : ℂ)) ^ 2) :
    (a' = a ∧ b' = b) ∨ (a' = -a ∧ b' = -b) := by
  have haz' : a' = (a / b) * b' := (div_eq_iff hb').mp hbase.symm
  -- ‖b‖ = ‖b'‖ from the sphere constraints and the shared ratio
  have e1 : ‖a‖ ^ 2 = ‖a / b‖ ^ 2 * ‖b‖ ^ 2 := by
    have h : ‖a / b‖ * ‖b‖ = ‖a‖ := by rw [← norm_mul, div_mul_cancel₀ a hb]
    rw [← h]; ring
  have e2 : ‖a'‖ ^ 2 = ‖a / b‖ ^ 2 * ‖b'‖ ^ 2 := by
    have h : ‖a'‖ = ‖a / b‖ * ‖b'‖ := by rw [haz', norm_mul]
    rw [h]; ring
  have hb2 : ‖b‖ ^ 2 = ‖b'‖ ^ 2 := by nlinarith [norm_nonneg (a / b)]
  have hnb : ‖b‖ = ‖b'‖ := by
    have := congrArg Real.sqrt hb2
    rwa [Real.sqrt_sq (norm_nonneg b), Real.sqrt_sq (norm_nonneg b')] at this
  -- b² = b'²  (multiply the fiber equation by ‖b‖²)
  have hbc : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hb
  have hbc' : (‖b'‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hb'
  have hsq : b ^ 2 = b' ^ 2 := by
    have hnbc : (‖b‖ : ℂ) = (‖b'‖ : ℂ) := by exact_mod_cast hnb
    have h := hfib
    rw [hnbc] at h
    field_simp at h
    linear_combination h
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with hbb | hbb
  · left
    refine ⟨?_, hbb.symm⟩
    rw [haz', ← hbb, div_mul_cancel₀ a hb]
  · right
    have hb'eq : b' = -b := by linear_combination hbb
    exact ⟨by rw [haz', hb'eq, mul_neg, div_mul_cancel₀ a hb], hb'eq⟩

/-- Bridge: coordinate agreement (up to antipode) implies equal `ℝP³` classes. -/
theorem mkRP3_of_coords {u v : S3}
    (h : (v.1.1 = u.1.1 ∧ v.1.2 = u.1.2) ∨ (v.1.1 = -u.1.1 ∧ v.1.2 = -u.1.2)) :
    mkRP3 u = mkRP3 v := by
  rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have : v = u := Subtype.ext (Prod.ext e1 e2)
    rw [this]
  · have : v = negS3 u := Subtype.ext (Prod.ext e1 e2)
    rw [this, mkRP3_neg]

/-- **`ρ̄ : ℝP³ → ∂E` is injective.** Two sphere points with equal Hopf image agree up to the
antipode (`recover`), across all four hemisphere combinations — the cross-chart cases route through
the equator weld (`glued` / `hopf_clutch`). So the descended map does not collapse `ℝP³`. -/
theorem bdryMap_eq_imp {x y : S3} (h : bdryMap x = bdryMap y) : mkRP3 x = mkRP3 y := by
  simp only [bdryMap] at h
  by_cases hx : ‖x.1.1‖ ≤ ‖x.1.2‖ <;> by_cases hy : ‖y.1.1‖ ≤ ‖y.1.2‖
  · -- TT: both chart 0
    rw [dif_pos hx, dif_pos hy] at h
    have hpair := chart0_inj_iff.mp h
    have hbase : x.1.1 / x.1.2 = y.1.1 / y.1.2 :=
      congrArg (fun r : ResChart => (r.1 : ℂ)) hpair
    have hfib : (x.1.2 / (‖x.1.2‖ : ℂ)) ^ 2 = (y.1.2 / (‖y.1.2‖ : ℂ)) ^ 2 :=
      congrArg (fun r : ResChart => (r.2 : ℂ)) hpair
    exact mkRP3_of_coords
      (recover (S3_snd_ne_zero hx) (S3_snd_ne_zero hy) x.2 y.2 hbase hfib)
  · -- TF: x chart 0, y chart 1 — equator weld
    rw [dif_pos hx, dif_neg hy] at h
    obtain ⟨hseam, hbeq, hfeq⟩ := chart0_eq_chart1_iff.mp h
    have hxb : x.1.2 ≠ 0 := S3_snd_ne_zero hx
    have hya : y.1.1 ≠ 0 := S3_fst_ne_zero (not_le.mp hy).le
    have hab : ‖x.1.1‖ = ‖x.1.2‖ := by
      rw [show ((⟨x.1.1 / x.1.2, _⟩ : Disk) : ℂ) = x.1.1 / x.1.2 from rfl, norm_div,
        div_eq_one_iff_eq (norm_ne_zero_iff.mpr hxb)] at hseam
      exact hseam
    have hxa : x.1.1 ≠ 0 := by
      intro h0
      have hz1 : ‖x.1.1‖ = 0 := by rw [h0, norm_zero]
      rw [hz1] at hab
      have := x.2; rw [hz1, ← hab] at this; norm_num at this
    have hbase : y.1.2 / y.1.1 = x.1.2 / x.1.1 := by
      have : y.1.2 / y.1.1 = (x.1.1 / x.1.2)⁻¹ := hbeq
      rw [this, inv_div]
    have hfib : (y.1.1 / (‖y.1.1‖ : ℂ)) ^ 2 = (x.1.1 / (‖x.1.1‖ : ℂ)) ^ 2 := by
      have he : (y.1.1 / (‖y.1.1‖ : ℂ)) ^ 2
          = (x.1.1 / x.1.2) ^ 2 * (x.1.2 / (‖x.1.2‖ : ℂ)) ^ 2 := hfeq
      rw [he]
      have hbc : (‖x.1.2‖ : ℂ) = (‖x.1.1‖ : ℂ) := by exact_mod_cast hab.symm
      have hxa1 : (‖x.1.1‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hxa
      rw [hbc]; field_simp
    have hrec := recover hya hxa (by rw [add_comm]; exact y.2) (by rw [add_comm]; exact x.2)
      hbase hfib
    rcases hrec with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact mkRP3_of_coords (Or.inl ⟨e2.symm, e1.symm⟩)
    · exact mkRP3_of_coords (Or.inr ⟨by rw [e2, neg_neg], by rw [e1, neg_neg]⟩)
  · -- FT: x chart 1, y chart 0 — equator weld (mirror of TF)
    rw [dif_neg hx, dif_pos hy] at h
    obtain ⟨hseam, hbeq, hfeq⟩ := chart0_eq_chart1_iff.mp h.symm
    have hyb : y.1.2 ≠ 0 := S3_snd_ne_zero hy
    have hxa : x.1.1 ≠ 0 := S3_fst_ne_zero (not_le.mp hx).le
    have hab : ‖y.1.1‖ = ‖y.1.2‖ := by
      rw [show ((⟨y.1.1 / y.1.2, _⟩ : Disk) : ℂ) = y.1.1 / y.1.2 from rfl, norm_div,
        div_eq_one_iff_eq (norm_ne_zero_iff.mpr hyb)] at hseam
      exact hseam
    have hya : y.1.1 ≠ 0 := by
      intro h0
      have hz1 : ‖y.1.1‖ = 0 := by rw [h0, norm_zero]
      rw [hz1] at hab
      have := y.2; rw [hz1, ← hab] at this; norm_num at this
    have hbase : x.1.2 / x.1.1 = y.1.2 / y.1.1 := by
      have : x.1.2 / x.1.1 = (y.1.1 / y.1.2)⁻¹ := hbeq
      rw [this, inv_div]
    have hfib : (x.1.1 / (‖x.1.1‖ : ℂ)) ^ 2 = (y.1.1 / (‖y.1.1‖ : ℂ)) ^ 2 := by
      have he : (x.1.1 / (‖x.1.1‖ : ℂ)) ^ 2
          = (y.1.1 / y.1.2) ^ 2 * (y.1.2 / (‖y.1.2‖ : ℂ)) ^ 2 := hfeq
      rw [he]
      have hbc : (‖y.1.2‖ : ℂ) = (‖y.1.1‖ : ℂ) := by exact_mod_cast hab.symm
      have hya1 : (‖y.1.1‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hya
      rw [hbc]; field_simp
    have hrec := recover hxa hya (by rw [add_comm]; exact x.2) (by rw [add_comm]; exact y.2)
      hbase hfib
    rcases hrec with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact mkRP3_of_coords (Or.inl ⟨e2, e1⟩)
    · exact mkRP3_of_coords (Or.inr ⟨e2, e1⟩)
  · -- FF: both chart 1
    rw [dif_neg hx, dif_neg hy] at h
    have hpair := chart1_inj_iff.mp h
    have hbase : x.1.2 / x.1.1 = y.1.2 / y.1.1 :=
      congrArg (fun r : ResChart => (r.1 : ℂ)) hpair
    have hfib : (x.1.1 / (‖x.1.1‖ : ℂ)) ^ 2 = (y.1.1 / (‖y.1.1‖ : ℂ)) ^ 2 :=
      congrArg (fun r : ResChart => (r.2 : ℂ)) hpair
    have hrec := recover (S3_fst_ne_zero (not_le.mp hx).le) (S3_fst_ne_zero (not_le.mp hy).le)
      (by rw [add_comm]; exact x.2) (by rw [add_comm]; exact y.2) hbase hfib
    rcases hrec with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact mkRP3_of_coords (Or.inl ⟨e2, e1⟩)
    · exact mkRP3_of_coords (Or.inr ⟨e2, e1⟩)

/-- **`ρ̄ : ℝP³ → ∂E` is injective** (packaged). -/
theorem bdryMapRP3_injective : Function.Injective bdryMapRP3 := by
  refine Quotient.ind fun x => Quotient.ind fun y => ?_
  intro h
  exact bdryMap_eq_imp h

/-! ### §3.5 Surjectivity of `ℝP³ → ∂E` -/

/-- **Complex square root at unit modulus**: every `u` with `‖u‖ = 1` has a unit square root
(`ℂ` is algebraically closed). The `±` ambiguity of the root is what `ℝP³` absorbs. -/
theorem exists_sqrt_unit {u : ℂ} (hu : ‖u‖ = 1) : ∃ w : ℂ, w ^ 2 = u ∧ ‖w‖ = 1 := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq u (n := 2) (by norm_num)
  refine ⟨w, hw, ?_⟩
  have h2 : ‖w‖ ^ 2 = 1 := by rw [← norm_pow, hw, hu]
  nlinarith [norm_nonneg w, h2]

/-- **The explicit `S³` preimage of a boundary Hopf coordinate** `(z, u)` with `‖z‖ ≤ 1`, `‖u‖ = 1`:
`a = z·b`, `b = r·w` with `r = (1 + ‖z‖²)^(-1/2)` and `w` a unit square root of `u`. It lands in the
chart-0 hemisphere `‖a‖ ≤ ‖b‖`, has base ratio `a/b = z`, and squared fiber phase `(b/‖b‖)² = u`. -/
theorem hopf_preimage {z u : ℂ} (hz : ‖z‖ ≤ 1) (hu : ‖u‖ = 1) :
    ∃ x : S3, ‖x.1.1‖ ≤ ‖x.1.2‖ ∧ x.1.1 / x.1.2 = z ∧ (x.1.2 / (‖x.1.2‖ : ℂ)) ^ 2 = u ∧
      x.1.2 ≠ 0 := by
  obtain ⟨w, hw2, hwn⟩ := exists_sqrt_unit hu
  set rr : ℝ := 1 + ‖z‖ ^ 2 with hrr
  have hrrpos : 0 < rr := by positivity
  set r : ℝ := (Real.sqrt rr)⁻¹ with hrdef
  have hrpos : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hrrpos)
  have hr2 : r ^ 2 = rr⁻¹ := by rw [hrdef, inv_pow, Real.sq_sqrt hrrpos.le]
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hrpos
  have hwne : w ≠ 0 := by rw [← norm_ne_zero_iff, hwn]; norm_num
  set b : ℂ := (r : ℂ) * w with hbdef
  set a : ℂ := z * b with hadef
  have hbnorm : ‖b‖ = r := by
    rw [hbdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, hwn, mul_one]
  have hbne : b ≠ 0 := mul_ne_zero hrc hwne
  have hanorm : ‖a‖ = ‖z‖ * r := by rw [hadef, norm_mul, hbnorm]
  have hmem : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
    rw [hanorm, hbnorm, mul_pow, hr2, hrr]; field_simp; ring
  refine ⟨⟨(a, b), hmem⟩, ?_, ?_, ?_, hbne⟩
  · show ‖a‖ ≤ ‖b‖
    rw [hanorm, hbnorm]
    nlinarith [hz, hrpos.le, norm_nonneg z]
  · show a / b = z
    rw [hadef, mul_div_assoc, div_self hbne, mul_one]
  · show (b / (‖b‖ : ℂ)) ^ 2 = u
    rw [hbnorm, hbdef, mul_comm (r : ℂ) w, mul_div_assoc, div_self hrc, mul_one, hw2]

/-- Weld criterion in coordinate form (a convenient repackaging of `chart0_eq_chart1_iff`). -/
theorem chart0_eq_chart1' {q p : ResChart} (hz : ‖(q.1 : ℂ)‖ = 1)
    (h1 : (p.1 : ℂ) = (q.1 : ℂ)⁻¹) (h2 : (p.2 : ℂ) = (q.1 : ℂ) ^ 2 * (q.2 : ℂ)) :
    chart0 q = chart1 p :=
  chart0_eq_chart1_iff.mpr ⟨hz, h1, h2⟩

/-- **Every chart-0 boundary point is in the image of `ρ`** (`chart0` stratum of `∂E` surjectivity). -/
theorem chart0_mem_range {p : ResChart} (hp : ‖(p.2 : ℂ)‖ = 1) :
    ∃ x : S3, bdryMap x = chart0 p := by
  obtain ⟨x, hxle, hbase, hfib, _⟩ := hopf_preimage p.1.2 hp
  refine ⟨x, ?_⟩
  unfold bdryMap
  rw [dif_pos hxle]
  exact congrArg chart0 (Prod.ext (Subtype.ext hbase) (Subtype.ext hfib))

/-- **Every chart-1 boundary point is in the image of `ρ`** (`chart1` stratum). The generic point uses
the swapped preimage in the chart-1 hemisphere; the equator point routes through the weld
(`chart0_eq_chart1'`). -/
theorem chart1_mem_range {p : ResChart} (hp : ‖(p.2 : ℂ)‖ = 1) :
    ∃ x : S3, bdryMap x = chart1 p := by
  obtain ⟨x, hxle, hbase, hfib, hx2⟩ := hopf_preimage p.1.2 hp
  have hswapmem : ‖x.1.2‖ ^ 2 + ‖x.1.1‖ ^ 2 = 1 := by rw [add_comm]; exact x.2
  refine ⟨⟨(x.1.2, x.1.1), hswapmem⟩, ?_⟩
  by_cases hc : ‖x.1.2‖ ≤ ‖x.1.1‖
  · -- equator edge: ‖x.1.1‖ = ‖x.1.2‖; weld chart0 → chart1
    have heq : ‖x.1.1‖ = ‖x.1.2‖ := le_antisymm hxle hc
    have hx1 : x.1.1 ≠ 0 := by rw [← norm_ne_zero_iff, heq]; exact norm_ne_zero_iff.mpr hx2
    unfold bdryMap
    rw [dif_pos hc]
    apply chart0_eq_chart1'
    · show ‖x.1.2 / x.1.1‖ = 1
      rw [norm_div, heq, div_self (norm_ne_zero_iff.mpr hx2)]
    · show (p.1 : ℂ) = (x.1.2 / x.1.1)⁻¹
      rw [inv_div]; exact hbase.symm
    · show (p.2 : ℂ) = (x.1.2 / x.1.1) ^ 2 * (x.1.1 / (‖x.1.1‖ : ℂ)) ^ 2
      rw [← hfib]
      have hac : (‖x.1.1‖ : ℂ) = (‖x.1.2‖ : ℂ) := by exact_mod_cast heq
      have hnc : (‖x.1.2‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx2
      rw [hac]; field_simp
  · -- generic chart-1 point: swapped preimage lands in the chart-1 hemisphere
    unfold bdryMap
    rw [dif_neg hc]
    exact congrArg chart1 (Prod.ext (Subtype.ext hbase) (Subtype.ext hfib))

/-- **The image of the Hopf map is exactly the boundary `∂E`**: `range ρ = ∂E`. Together with
`bdryMap_mem_boundary` (⊆) and the two `mem_range` lemmas (⊇). -/
theorem range_bdryMap_eq_boundaryE : Set.range bdryMap = boundaryE := by
  apply Set.eq_of_subset_of_subset
  · rintro y ⟨x, rfl⟩; exact bdryMap_mem_boundary x
  · rintro y ⟨p, hp2, hy | hy⟩
    · obtain ⟨x, hx⟩ := chart0_mem_range hp2; exact ⟨x, by rw [hx, hy]⟩
    · obtain ⟨x, hx⟩ := chart1_mem_range hp2; exact ⟨x, by rw [hx, hy]⟩

theorem range_bdryMapRP3 : Set.range bdryMapRP3 = Set.range bdryMap := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨mkRP3 x, rfl⟩

/-- **`range ρ̄ = ∂E`** — the descended map surjects exactly onto the boundary locus. -/
theorem range_bdryMapRP3_eq_boundaryE : Set.range bdryMapRP3 = boundaryE :=
  range_bdryMapRP3.trans range_bdryMap_eq_boundaryE

/-- **`ρ̄ : ℝP³ → ∂E` is a bijection onto the boundary `∂E`** (injective + surjective onto `∂E`) —
`bijectivity`, the within-boundary priority of the K6′a design. The homeomorphism packaging
(continuity both ways) is the remaining stretch. -/
theorem bdryMapRP3_bijOn : Set.BijOn bdryMapRP3 Set.univ boundaryE := by
  refine ⟨?_, bdryMapRP3_injective.injOn, ?_⟩
  · intro q _
    rw [← range_bdryMapRP3_eq_boundaryE]; exact ⟨q, rfl⟩
  · rw [Set.SurjOn, Set.image_univ, range_bdryMapRP3_eq_boundaryE]

end

end SKEFTHawking.KummerResolutionPiece
