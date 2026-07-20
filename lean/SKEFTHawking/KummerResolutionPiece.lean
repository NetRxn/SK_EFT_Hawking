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

/-! ## §4. The zero section — the embedded `S²` (`w = 0`), the standard two-chart sphere

The zero section of `E` is the base `S²` sitting at `w = 0`. It is the standard two-chart sphere: two
disks glued by `z ↦ z⁻¹` on the equator (the fiber-`0` restriction of the Euler−2 clutch, which fixes
`w = 0`: `clutch (z, 0) = (z⁻¹, 0)`). The `(−2)` self-intersection number belongs to K8 (not here);
the H₂-generator / deformation-retract homology packaging is the residual. -/

/-- The base gluing `z ↦ z⁻¹` on the equator (the `w = 0` restriction of the clutch). -/
def baseGlued (p q : Disk) : Prop := ‖(p : ℂ)‖ = 1 ∧ (q : ℂ) = (p : ℂ)⁻¹

def baseGcore : Disk ⊕ Disk → Disk ⊕ Disk → Prop
  | Sum.inl p, Sum.inr q => baseGlued p q
  | Sum.inr q, Sum.inl p => baseGlued p q
  | _, _ => False

def baseRel (a b : Disk ⊕ Disk) : Prop := a = b ∨ baseGcore a b

theorem baseGcore_symm {a b : Disk ⊕ Disk} (h : baseGcore a b) : baseGcore b a := by
  cases a <;> cases b <;> simp only [baseGcore] at h ⊢ <;> exact h

theorem baseGlued_right_unique {p q q' : Disk} (h : baseGlued p q) (h' : baseGlued p q') : q = q' :=
  Subtype.ext (by rw [h.2, h'.2])

theorem baseGlued_left_unique {p p' q : Disk} (h : baseGlued p q) (h' : baseGlued p' q) : p = p' := by
  apply Subtype.ext
  have : (p : ℂ)⁻¹ = (p' : ℂ)⁻¹ := by rw [← h.2, ← h'.2]
  exact inv_injective this

theorem baseRel_equivalence : Equivalence baseRel := by
  refine ⟨fun a => Or.inl rfl, ?_, ?_⟩
  · rintro a b (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr (baseGcore_symm h)
  · rintro a b c (rfl | hab) (rfl | hbc)
    · exact Or.inl rfl
    · exact Or.inr hbc
    · exact Or.inr hab
    · cases a with
      | inl p =>
        cases b with
        | inl _ => exact (hab : False).elim
        | inr q =>
          cases c with
          | inl p' => exact Or.inl (by rw [baseGlued_left_unique (hab : baseGlued p q) (hbc : baseGlued p' q)])
          | inr _ => exact (hbc : False).elim
      | inr q =>
        cases b with
        | inr _ => exact (hab : False).elim
        | inl p =>
          cases c with
          | inr q' => exact Or.inl (by rw [baseGlued_right_unique (hab : baseGlued p q) (hbc : baseGlued p q')])
          | inl _ => exact (hbc : False).elim

def baseSetoid : Setoid (Disk ⊕ Disk) := ⟨baseRel, baseRel_equivalence⟩

/-- **The base `S²`** — the standard two-chart sphere (two disks glued by `z ↦ z⁻¹` on the equator),
the zero section's model. -/
def BaseS2 : Type := Quotient baseSetoid

instance : TopologicalSpace BaseS2 := inferInstanceAs (TopologicalSpace (Quotient baseSetoid))

instance : Nonempty BaseS2 := ⟨Quotient.mk baseSetoid (Sum.inl ⟨0, by simp⟩)⟩

def baseChart0 (z : Disk) : BaseS2 := Quotient.mk baseSetoid (Sum.inl z)
def baseChart1 (z : Disk) : BaseS2 := Quotient.mk baseSetoid (Sum.inr z)

theorem continuous_baseChart0 : Continuous baseChart0 := continuous_quotient_mk'.comp continuous_inl
theorem continuous_baseChart1 : Continuous baseChart1 := continuous_quotient_mk'.comp continuous_inr

/-- The origin of the fiber `D²`, as a `Disk` — the zero of the zero section. -/
def zeroFiber : Disk := ⟨0, by simp⟩

/-- The zero-section point at base `z`: `(z, 0)` in a chart of `E`. -/
def zeroPt (z : Disk) : ResChart := (z, zeroFiber)

/-- **The zero-section inclusion** `BaseS2 → E`, `z ↦ (z, 0)`. Well-defined: the base gluing `z ↦ z⁻¹`
maps to `E`'s equator weld because the clutch fixes the zero fiber (`clutch (z, 0) = (z⁻¹, 0)`). -/
def zeroSection : BaseS2 → ResE :=
  Quotient.lift (Sum.elim (fun z => chart0 (zeroPt z)) (fun z => chart1 (zeroPt z))) (by
    rintro a b (rfl | hg)
    · rfl
    · cases a with
      | inl p =>
        cases b with
        | inr q =>
          have hz : ‖((zeroPt p).1 : ℂ)‖ = 1 := hg.1
          show chart0 (zeroPt p) = chart1 (zeroPt q)
          rw [chart_glue hz]
          refine congrArg chart1 (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
          · show ((zeroPt p).1 : ℂ)⁻¹ = (q : ℂ)
            exact hg.2.symm
          · show ((zeroPt p).1 : ℂ) ^ 2 * ((zeroPt p).2 : ℂ) = 0
            simp [zeroPt, zeroFiber]
        | inl _ => exact (hg : False).elim
      | inr q =>
        cases b with
        | inl p =>
          have hz : ‖((zeroPt p).1 : ℂ)‖ = 1 := hg.1
          show chart1 (zeroPt q) = chart0 (zeroPt p)
          rw [chart_glue hz]
          refine congrArg chart1 (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)).symm
          · show ((zeroPt p).1 : ℂ)⁻¹ = (q : ℂ)
            exact hg.2.symm
          · show ((zeroPt p).1 : ℂ) ^ 2 * ((zeroPt p).2 : ℂ) = 0
            simp [zeroPt, zeroFiber]
        | inr _ => exact (hg : False).elim)

@[simp] theorem zeroSection_baseChart0 (z : Disk) : zeroSection (baseChart0 z) = chart0 (zeroPt z) := rfl
@[simp] theorem zeroSection_baseChart1 (z : Disk) : zeroSection (baseChart1 z) = chart1 (zeroPt z) := rfl

theorem continuous_zeroSection : Continuous zeroSection := by
  apply Continuous.quotient_lift
  apply Continuous.sumElim
  · exact continuous_chart0.comp (Continuous.prodMk continuous_id continuous_const)
  · exact continuous_chart1.comp (Continuous.prodMk continuous_id continuous_const)

/-- **The zero-section locus** — the `w = 0` sphere inside `E`. -/
def zeroLocus : Set ResE :=
  {y | ∃ z : Disk, y = chart0 (zeroPt z) ∨ y = chart1 (zeroPt z)}

/-- **The zero section lands in the `w = 0` locus** and covers it: `range zeroSection = zeroLocus`. The
embedded `S²` sits inside `E` at `w = 0`. -/
theorem range_zeroSection_eq_zeroLocus : Set.range zeroSection = zeroLocus := by
  apply Set.eq_of_subset_of_subset
  · rintro y ⟨q, rfl⟩
    obtain ⟨a, rfl⟩ := Quotient.exists_rep q
    cases a with
    | inl z => exact ⟨z, Or.inl rfl⟩
    | inr z => exact ⟨z, Or.inr rfl⟩
  · rintro y ⟨z, hy | hy⟩
    · exact ⟨baseChart0 z, hy.symm⟩
    · exact ⟨baseChart1 z, hy.symm⟩

/-- **Falsifiable pin**: the clutch fixes the zero fiber — `clutch (z, 0) = (z⁻¹, 0)`. This is why the
zero section is well-defined (the base gluing `z ↦ z⁻¹` is exactly the `w = 0` restriction). -/
theorem clutch_zero_fiber (z : ℂ) : clutch (z, 0) = (z⁻¹, 0) := by
  simp only [clutch, mul_zero]

/-! ## §5. Compactness of `E`, `S³`, `ℝP³` (the compact-to-T2 homeomorphism prerequisites)

The two-chart carrier `E`, the sphere `S³`, and the antipodal quotient `ℝP³` are all compact:
`D²` is a closed ball (compact), `E` and `ℝP³` are quotients of compact spaces, and `S³` is a
closed bounded subset of the finite-dimensional `ℂ²`. Compactness of `ℝP³` (source) plus
Hausdorffness of `E` (target, §6) is what upgrades the continuous bijection `ρ̄` to a homeomorphism
(`Continuous.homeoOfEquivCompactToT2`). -/

/-- The closed fiber/base disk `D²` is compact (a closed ball in `ℂ`). -/
instance : CompactSpace Disk := by
  have hset : {z : ℂ | ‖z‖ ≤ 1} = Metric.closedBall 0 1 := by
    ext z; simp [Metric.mem_closedBall, dist_eq_norm]
  have : IsCompact {z : ℂ | ‖z‖ ≤ 1} := by rw [hset]; exact isCompact_closedBall 0 1
  exact isCompact_iff_compactSpace.mp this

/-- A single disk-bundle chart `D² × D²` is compact. -/
instance : CompactSpace ResChart := inferInstanceAs (CompactSpace (Disk × Disk))

/-- The two-chart disjoint union is compact. -/
instance : CompactSpace (ResChart ⊕ ResChart) := inferInstanceAs (CompactSpace (ResChart ⊕ ResChart))

/-- **`E` is compact** — a quotient of the compact two-chart disjoint union. -/
instance : CompactSpace ResE := inferInstanceAs (CompactSpace (Quotient resSetoid))

/-- **`S³ ⊂ ℂ²` is compact** — a closed, bounded subset of the finite-dimensional (proper) `ℂ²`. -/
instance : CompactSpace S3 := by
  have hcont : Continuous fun p : ℂ × ℂ => ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 :=
    ((continuous_norm.comp continuous_fst).pow 2).add ((continuous_norm.comp continuous_snd).pow 2)
  have hclosed : IsClosed {p : ℂ × ℂ | ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 = 1} :=
    isClosed_eq hcont continuous_const
  have hsub : {p : ℂ × ℂ | ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 = 1} ⊆ Metric.closedBall 0 1 := by
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def, max_le_iff]
    constructor <;> nlinarith [norm_nonneg p.1, norm_nonneg p.2, sq_nonneg ‖p.1‖, sq_nonneg ‖p.2‖]
  have hbdd : Bornology.IsBounded {p : ℂ × ℂ | ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 = 1} :=
    Metric.isBounded_closedBall.subset hsub
  exact isCompact_iff_compactSpace.mp (Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩)

/-- **`ℝP³` is compact** — a quotient of the compact `S³`. -/
instance : CompactSpace RP3 := inferInstanceAs (CompactSpace (Quotient antipSetoid))

/-! ## §6. Continuity of the boundary map `ρ : S³ → E` and its descent `ρ̄ : ℝP³ → E`

`bdryMap` is defined piecewise on the two hemispheres `‖a‖ ≤ ‖b‖` / `‖a‖ ≥ ‖b‖`, glued at the
equator seam `‖a‖ = ‖b‖`. Continuity is by pasting the two chart branches over the closed
hemisphere cover; the seam agreement is exactly the weld (`hopf_clutch` + `chart_glue`). Descent to
`ρ̄` is then automatic (`Continuous.quotient_lift`). -/

/-- **The chart-1 closed form of `ρ` on the hemisphere `‖b‖ ≤ ‖a‖`.** On the whole closed
hemisphere (INCLUDING the seam `‖a‖ = ‖b‖`, where `bdryMap` uses the chart-0 branch), `bdryMap x`
equals the single chart-1 value `chart1 ⟨b/a, (a/‖a‖)²⟩`; on the seam this is the weld
(`chart_glue` ∘ `hopf_clutch`). This is what makes `bdryMap` continuous on the chart-1 hemisphere. -/
theorem bdryMap_chart1_of_snd_le {x : S3} (h : ‖x.1.2‖ ≤ ‖x.1.1‖) :
    bdryMap x = chart1 (⟨x.1.2 / x.1.1, by
        rw [norm_div]; exact (div_le_one (norm_pos_iff.mpr (S3_fst_ne_zero h))).mpr h⟩,
      ⟨(x.1.1 / (‖x.1.1‖ : ℂ)) ^ 2, le_of_eq (fiber_norm_eq_one (S3_fst_ne_zero h))⟩) := by
  have ha : x.1.1 ≠ 0 := S3_fst_ne_zero h
  by_cases hc : ‖x.1.1‖ ≤ ‖x.1.2‖
  · -- seam `‖a‖ = ‖b‖`: `bdryMap` uses chart 0; weld it to chart 1
    have hab : ‖x.1.1‖ = ‖x.1.2‖ := le_antisymm hc h
    have hb : x.1.2 ≠ 0 := by
      rw [← norm_ne_zero_iff, ← hab]; exact norm_ne_zero_iff.mpr ha
    unfold bdryMap
    rw [dif_pos hc]
    set p : ResChart := (⟨x.1.1 / x.1.2, by
        rw [norm_div]; exact (div_le_one (norm_pos_iff.mpr hb)).mpr hc⟩,
      ⟨(x.1.2 / (‖x.1.2‖ : ℂ)) ^ 2, le_of_eq (fiber_norm_eq_one hb)⟩) with hp
    have hz : ‖(p.1 : ℂ)‖ = 1 := by
      show ‖x.1.1 / x.1.2‖ = 1
      rw [norm_div, hab, div_self (norm_ne_zero_iff.mpr hb)]
    rw [chart_glue hz]
    obtain ⟨hc1, hc2⟩ := hopf_clutch ha hb hab p rfl rfl hz
    exact congrArg chart1 (Prod.ext (Subtype.ext hc1) (Subtype.ext hc2))
  · -- interior `‖b‖ < ‖a‖`: `bdryMap` uses the chart-1 branch directly
    unfold bdryMap
    rw [dif_neg hc]

/-- **`ρ : S³ → E` is continuous.** By pasting the two chart branches over the closed hemisphere
cover `{‖a‖ ≤ ‖b‖} ∪ {‖b‖ ≤ ‖a‖} = S³`; the branches agree on the seam by `bdryMap_chart1_of_snd_le`.
-/
theorem continuous_bdryMap : Continuous bdryMap := by
  have hnf : Continuous fun x : S3 => ‖x.1.1‖ :=
    continuous_norm.comp (continuous_fst.comp continuous_subtype_val)
  have hns : Continuous fun x : S3 => ‖x.1.2‖ :=
    continuous_norm.comp (continuous_snd.comp continuous_subtype_val)
  have hAclosed : IsClosed {x : S3 | ‖x.1.1‖ ≤ ‖x.1.2‖} := isClosed_le hnf hns
  have hBclosed : IsClosed {x : S3 | ‖x.1.2‖ ≤ ‖x.1.1‖} := isClosed_le hns hnf
  -- chart-0 branch is continuous on the `‖a‖ ≤ ‖b‖` hemisphere
  have hcontA : ContinuousOn bdryMap {x : S3 | ‖x.1.1‖ ≤ ‖x.1.2‖} := by
    rw [continuousOn_iff_continuous_restrict]
    have hne : ∀ x : {x : S3 // ‖x.1.1‖ ≤ ‖x.1.2‖}, x.1.1.2 ≠ 0 := fun x => S3_snd_ne_zero x.2
    have hbase : Continuous fun x : {x : S3 // ‖x.1.1‖ ≤ ‖x.1.2‖} => x.1.1.1 / x.1.1.2 :=
      Continuous.div
        (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))
        (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)) hne
    have hfib : Continuous fun x : {x : S3 // ‖x.1.1‖ ≤ ‖x.1.2‖} =>
        (x.1.1.2 / (‖x.1.1.2‖ : ℂ)) ^ 2 := by
      refine Continuous.pow (Continuous.div
        (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))
        (Complex.continuous_ofReal.comp
          (continuous_norm.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))))
        (fun x => ?_)) 2
      simpa [Complex.ofReal_ne_zero] using norm_ne_zero_iff.mpr (hne x)
    refine (continuous_chart0.comp (Continuous.prodMk
      (hbase.subtype_mk (fun x => by
        rw [norm_div]; exact (div_le_one (norm_pos_iff.mpr (hne x))).mpr x.2))
      (hfib.subtype_mk (fun x => by exact le_of_eq (fiber_norm_eq_one (hne x)))))).congr (fun x => ?_)
    rw [Set.restrict_apply, Function.comp_apply]
    unfold bdryMap
    rw [dif_pos x.2]
  -- chart-1 branch is continuous on the `‖b‖ ≤ ‖a‖` hemisphere
  have hcontB : ContinuousOn bdryMap {x : S3 | ‖x.1.2‖ ≤ ‖x.1.1‖} := by
    rw [continuousOn_iff_continuous_restrict]
    have hne : ∀ x : {x : S3 // ‖x.1.2‖ ≤ ‖x.1.1‖}, x.1.1.1 ≠ 0 := fun x => S3_fst_ne_zero x.2
    have hbase : Continuous fun x : {x : S3 // ‖x.1.2‖ ≤ ‖x.1.1‖} => x.1.1.2 / x.1.1.1 :=
      Continuous.div
        (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))
        (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)) hne
    have hfib : Continuous fun x : {x : S3 // ‖x.1.2‖ ≤ ‖x.1.1‖} =>
        (x.1.1.1 / (‖x.1.1.1‖ : ℂ)) ^ 2 := by
      refine Continuous.pow (Continuous.div
        (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))
        (Complex.continuous_ofReal.comp
          (continuous_norm.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))))
        (fun x => ?_)) 2
      simpa [Complex.ofReal_ne_zero] using norm_ne_zero_iff.mpr (hne x)
    refine (continuous_chart1.comp (Continuous.prodMk
      (hbase.subtype_mk (fun x => by
        rw [norm_div]; exact (div_le_one (norm_pos_iff.mpr (hne x))).mpr x.2))
      (hfib.subtype_mk (fun x => by exact le_of_eq (fiber_norm_eq_one (hne x)))))).congr (fun x => ?_)
    rw [Set.restrict_apply]
    exact (bdryMap_chart1_of_snd_le x.2).symm
  -- paste over the closed cover
  rw [continuous_iff_continuousAt]
  intro x
  rcases le_total ‖x.1.1‖ ‖x.1.2‖ with h | h
  · by_cases hb : ‖x.1.2‖ ≤ ‖x.1.1‖
    · have huniv : {x : S3 | ‖x.1.1‖ ≤ ‖x.1.2‖} ∪ {x : S3 | ‖x.1.2‖ ≤ ‖x.1.1‖} = Set.univ := by
        ext y; simp [le_total]
      rw [← continuousWithinAt_univ, ← huniv]
      exact continuousWithinAt_union.mpr ⟨hcontA x h, hcontB x hb⟩
    · refine hcontA.continuousAt (Filter.mem_of_superset
        ((isOpen_lt hnf hns).mem_nhds (lt_of_le_of_ne h (fun he => hb (le_of_eq he.symm)))) ?_)
      exact Set.setOf_subset_setOf.2 fun _ hy => le_of_lt hy
  · by_cases ha : ‖x.1.1‖ ≤ ‖x.1.2‖
    · have huniv : {x : S3 | ‖x.1.1‖ ≤ ‖x.1.2‖} ∪ {x : S3 | ‖x.1.2‖ ≤ ‖x.1.1‖} = Set.univ := by
        ext y; simp [le_total]
      rw [← continuousWithinAt_univ, ← huniv]
      exact continuousWithinAt_union.mpr ⟨hcontA x ha, hcontB x h⟩
    · refine hcontB.continuousAt (Filter.mem_of_superset
        ((isOpen_lt hns hnf).mem_nhds (lt_of_le_of_ne h (fun he => ha (le_of_eq he.symm)))) ?_)
      exact Set.setOf_subset_setOf.2 fun _ hy => le_of_lt hy

/-- **`ρ̄ : ℝP³ → E` is continuous** — the descent of the continuous `ρ` through the antipodal
quotient (`Continuous.quotient_lift`). -/
theorem continuous_bdryMapRP3 : Continuous bdryMapRP3 :=
  continuous_bdryMap.quotient_lift _

/-! ## §7. The homeomorphism `ℝP³ ≃ₜ ∂E` (compact-to-T2 upgrade of the continuous bijection)

`ρ̄ : ℝP³ → E` is a continuous injection whose image is exactly `∂E` (`bdryMapRP3_bijOn`,
`continuous_bdryMapRP3`). Corestricted to `∂E` it is a continuous bijection from the compact `ℝP³`;
the compact-to-Hausdorff principle (`Continuous.homeoOfEquivCompactToT2`) upgrades it to a
homeomorphism as soon as the target subspace `∂E ⊆ E` is Hausdorff — which holds once `E` is (§8). -/

/-- The corestriction of `ρ̄` to its image `∂E`, as an equivalence `ℝP³ ≃ ∂E`. -/
def bdryEquivRP3 : RP3 ≃ ↥boundaryE :=
  Equiv.ofBijective
    (fun q => ⟨bdryMapRP3 q, by rw [← range_bdryMapRP3_eq_boundaryE]; exact ⟨q, rfl⟩⟩)
    ⟨fun a b h => bdryMapRP3_injective (Subtype.ext_iff.mp h), fun y => by
      have hy : y.1 ∈ Set.range bdryMapRP3 := by rw [range_bdryMapRP3_eq_boundaryE]; exact y.2
      obtain ⟨q, hq⟩ := hy
      exact ⟨q, Subtype.ext hq⟩⟩

theorem continuous_bdryEquivRP3 : Continuous bdryEquivRP3 :=
  continuous_bdryMapRP3.subtype_mk _

/-! ## §8. `E` is Hausdorff (`T2Space ResE`), and the boundary homeomorphism `ℝP³ ≃ₜ ∂E`

`E` is the quotient of the compact Hausdorff two-chart disjoint union by the clutch gluing. The
quotient map is a **closed map** (the saturation of a closed set stays closed — the weld is along the
compact equator circle), so it is proper; its square is then proper, hence closed, and the diagonal
of `E` is the image of the (closed) gluing relation under it, hence closed — i.e. `E` is Hausdorff.
This upgrades `bdryHomeoRP3` from conditional to unconditional. -/

/-- On the unit circle `‖z‖ = 1`, complex conjugation coincides with inversion. -/
theorem conj_eq_inv_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : (starRingEnd ℂ) z = z⁻¹ := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  refine eq_inv_of_mul_eq_one_left ?_
  rw [mul_comm, Complex.mul_conj]
  have : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [this]; norm_num

/-- **The total continuous glue map** on `D² × D²`: the equator weld `clutchDisk`, extended
continuously to the whole chart by using `conj` (which equals `⁻¹` on the equator, but — unlike `⁻¹`
— is continuous everywhere). The fiber component is the same polynomial `z² · w`. Its totality +
continuity is what makes saturations of closed sets closed. -/
def gtot (p : ResChart) : ResChart :=
  (⟨(starRingEnd ℂ) (p.1 : ℂ), by rw [Complex.norm_conj]; exact p.1.2⟩,
   ⟨(p.1 : ℂ) ^ 2 * (p.2 : ℂ), by
     rw [norm_mul, norm_pow]
     nlinarith [p.1.2, p.2.2, norm_nonneg (p.1 : ℂ), norm_nonneg (p.2 : ℂ)]⟩)

theorem continuous_gtot : Continuous gtot := by
  refine Continuous.prodMk (Continuous.subtype_mk ?_ ?_) (Continuous.subtype_mk ?_ ?_)
  · exact Complex.continuous_conj.comp (continuous_subtype_val.comp continuous_fst)
  · intro p
    simp only [Complex.norm_conj]
    exact p.1.2
  · exact ((continuous_subtype_val.comp continuous_fst).pow 2).mul
      (continuous_subtype_val.comp continuous_snd)
  · intro p
    simp only [norm_mul, norm_pow]
    nlinarith [p.1.2, p.2.2, norm_nonneg (p.1 : ℂ), norm_nonneg (p.2 : ℂ)]

/-- On the equator `‖z‖ = 1`, the total glue `gtot` coincides with the clutch weld `clutchDisk`. -/
theorem gtot_eq_clutchDisk {p : ResChart} (hz : ‖(p.1 : ℂ)‖ = 1) : gtot p = clutchDisk p hz :=
  Prod.ext (Subtype.ext (conj_eq_inv_of_norm_one hz)) (Subtype.ext rfl)

/-- **Every equator point `p` welds to its total-glue image**: `glued p (gtot p)` for `‖p.1‖ = 1`.
The weld relation `gcore` is exactly `glued` on the two cross-chart constructor cases. -/
theorem glued_gtot {p : ResChart} (hz : ‖(p.1 : ℂ)‖ = 1) : glued p (gtot p) :=
  ⟨hz, conj_eq_inv_of_norm_one hz, rfl⟩

/-- **The quotient map `E`'s projection is a closed map.** For a closed `C`, its saturation
`q⁻¹(q '' C)` equals `C` together with the two chart-swap partner strata (the images of `C`'s equator
points under the total glue `gtot`); each stratum is the continuous image of a compact set, hence
closed. This is the "gluing is along a compact circle" fact that makes `E` Hausdorff. -/
theorem isClosedMap_quotientMk : IsClosedMap (Quotient.mk resSetoid) := by
  intro C hC
  have hEqClosed : IsClosed {p : ResChart | ‖(p.1 : ℂ)‖ = 1} :=
    isClosed_eq (continuous_norm.comp (continuous_subtype_val.comp continuous_fst)) continuous_const
  have hInl : IsClosed ((Sum.inl : ResChart → ResChart ⊕ ResChart) ''
      {p : ResChart | ‖(p.1 : ℂ)‖ = 1 ∧ Sum.inr (gtot p) ∈ C}) := by
    have hK : IsCompact {p : ResChart | ‖(p.1 : ℂ)‖ = 1 ∧ Sum.inr (gtot p) ∈ C} :=
      IsClosed.isCompact (hEqClosed.inter (hC.preimage (continuous_inr.comp continuous_gtot)))
    exact (hK.image continuous_inl).isClosed
  have hInr : IsClosed ((Sum.inr : ResChart → ResChart ⊕ ResChart) ''
      (gtot '' {p : ResChart | ‖(p.1 : ℂ)‖ = 1 ∧ Sum.inl p ∈ C})) := by
    have hK : IsCompact {p : ResChart | ‖(p.1 : ℂ)‖ = 1 ∧ Sum.inl p ∈ C} :=
      IsClosed.isCompact (hEqClosed.inter (hC.preimage continuous_inl))
    exact ((hK.image continuous_gtot).image continuous_inr).isClosed
  rw [← (isQuotientMap_quotient_mk' (s := resSetoid)).isClosed_preimage]
  have hsat : Quotient.mk resSetoid ⁻¹' (Quotient.mk resSetoid '' C) =
      C ∪ Sum.inl '' {p : ResChart | ‖(p.1 : ℂ)‖ = 1 ∧ Sum.inr (gtot p) ∈ C} ∪
        Sum.inr '' (gtot '' {p : ResChart | ‖(p.1 : ℂ)‖ = 1 ∧ Sum.inl p ∈ C}) := by
    ext a
    constructor
    · intro ha
      rw [Set.mem_preimage, Set.mem_image] at ha
      obtain ⟨b, hbC, hab⟩ := ha
      rcases (Quotient.exact hab : resRel b a) with rfl | hg
      · exact Set.mem_union_left _ (Set.mem_union_left _ hbC)
      · cases b with
        | inl p =>
          cases a with
          | inl p' => exact (hg : False).elim
          | inr q =>
            have hglued : glued p q := hg
            have hz : ‖(p.1 : ℂ)‖ = 1 := hglued.1
            have hgt : gtot p = q := by
              rw [gtot_eq_clutchDisk hz]
              exact Prod.ext (Subtype.ext hglued.2.1.symm) (Subtype.ext hglued.2.2.symm)
            exact Set.mem_union_right _
              (Set.mem_image_of_mem (Sum.inr : ResChart → ResChart ⊕ ResChart) ⟨p, ⟨hz, hbC⟩, hgt⟩)
        | inr q =>
          cases a with
          | inl p =>
            have hglued : glued p q := hg
            have hz : ‖(p.1 : ℂ)‖ = 1 := hglued.1
            have hgt : gtot p = q := by
              rw [gtot_eq_clutchDisk hz]
              exact Prod.ext (Subtype.ext hglued.2.1.symm) (Subtype.ext hglued.2.2.symm)
            exact Set.mem_union_left _ (Set.mem_union_right _
              (Set.mem_image_of_mem (Sum.inl : ResChart → ResChart ⊕ ResChart)
                ⟨hz, by rw [hgt]; exact hbC⟩))
          | inr q' => exact (hg : False).elim
    · intro ha
      rw [Set.mem_preimage, Set.mem_image]
      rcases ha with (haC | ha_inl) | ha_inr
      · exact ⟨a, haC, rfl⟩
      · obtain ⟨p, ⟨hz, hmem⟩, rfl⟩ := ha_inl
        exact ⟨Sum.inr (gtot p), hmem, Quotient.sound (Or.inr (glued_gtot hz))⟩
      · obtain ⟨y, ⟨p, ⟨hz, hpC⟩, hgt⟩, rfl⟩ := ha_inr
        subst hgt
        exact ⟨Sum.inl p, hpC, Quotient.sound (Or.inr (glued_gtot hz))⟩
  show IsClosed (Quotient.mk resSetoid ⁻¹' (Quotient.mk resSetoid '' C))
  rw [hsat]
  exact (hC.union hInl).union hInr

/-- A weld determines the chart-1 partner: `glued p q → q = gtot p`. -/
theorem glued_right_eq_gtot {p q : ResChart} (h : glued p q) : q = gtot p := by
  rw [gtot_eq_clutchDisk h.1]
  exact Prod.ext (Subtype.ext h.2.1) (Subtype.ext h.2.2)

/-- A weld determines the chart-0 partner: `glued p q → p = gtot q` (the clutch is an involution
on the equator). -/
theorem glued_left_eq_gtot {p q : ResChart} (h : glued p q) : p = gtot q := by
  have hq : ‖(q.1 : ℂ)‖ = 1 := by rw [h.2.1, norm_inv, h.1, inv_one]
  have hp0 : (p.1 : ℂ) ≠ 0 := by rw [← norm_ne_zero_iff, h.1]; norm_num
  rw [gtot_eq_clutchDisk hq]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · show (p.1 : ℂ) = (q.1 : ℂ)⁻¹
    rw [h.2.1, inv_inv]
  · show (p.2 : ℂ) = (q.1 : ℂ) ^ 2 * (q.2 : ℂ)
    rw [h.2.1, h.2.2]; field_simp

/-- **Every fiber of `E`'s projection is finite** (a gluing class has at most two points: the point
and its unique equator partner). Hence the fibers are compact — the last ingredient for properness. -/
theorem finite_fiber (y : ResE) : (Quotient.mk resSetoid ⁻¹' {y}).Finite := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep y
  refine Set.Finite.subset ((Set.finite_singleton (Sum.elim (fun p => Sum.inr (gtot p))
    (fun q => Sum.inl (gtot q)) a)).insert a) ?_
  intro b hb
  simp only [Set.mem_preimage] at hb
  rcases (Quotient.exact hb.symm : resRel a b) with rfl | hg
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ?_
    rw [Set.mem_singleton_iff]
    cases a with
    | inl p =>
      cases b with
      | inl p' => exact (hg : False).elim
      | inr q =>
        show (Sum.inr q : ResChart ⊕ ResChart) = _
        rw [Sum.elim_inl, glued_right_eq_gtot (hg : glued p q)]
    | inr q =>
      cases b with
      | inl p =>
        show (Sum.inl p : ResChart ⊕ ResChart) = _
        rw [Sum.elim_inr, glued_left_eq_gtot (hg : glued p q)]
      | inr q' => exact (hg : False).elim

/-- **`E` is Hausdorff (`T2Space ResE`).** The projection `q` is proper (continuous, closed map, with
finite hence compact fibers), so `q × q` is proper, hence a closed map; the diagonal of `E` is the
image of the closed diagonal of the (Hausdorff) two-chart union under `q × q`, hence closed. This
discharges the hypothesis of `bdryHomeoRP3` — the boundary homeomorphism `ℝP³ ≃ₜ ∂E` holds outright. -/
instance instT2SpaceResE : T2Space ResE := by
  have hproper : IsProperMap (Quotient.mk resSetoid) :=
    isProperMap_iff_isClosedMap_and_compact_fibers.mpr
      ⟨continuous_quotient_mk', isClosedMap_quotientMk, fun y => (finite_fiber y).isCompact⟩
  rw [t2_iff_isClosed_diagonal]
  have hdiag : Set.diagonal ResE =
      Prod.map (Quotient.mk resSetoid) (Quotient.mk resSetoid) '' Set.diagonal (ResChart ⊕ ResChart) := by
    apply Set.eq_of_subset_of_subset
    · rintro ⟨y1, y2⟩ hy
      have hy' : y1 = y2 := hy
      subst hy'
      obtain ⟨a, rfl⟩ := Quotient.exists_rep y1
      exact ⟨(a, a), rfl, rfl⟩
    · rintro ⟨y1, y2⟩ ⟨⟨a, b⟩, hab, heq⟩
      have hab' : a = b := hab
      have h1 : Quotient.mk resSetoid a = y1 := congrArg Prod.fst heq
      have h2 : Quotient.mk resSetoid b = y2 := congrArg Prod.snd heq
      show y1 = y2
      rw [← h1, ← h2, hab']
  rw [hdiag]
  exact (hproper.prodMap hproper).isClosedMap _ isClosed_diagonal

/-- **`ℝP³ ≃ₜ ∂E`** — the boundary of the Euler−2 disk bundle `E` is homeomorphic to `ℝP³` in the
pinned S³/±1 antipodal presentation. The continuous bijection `ρ̄` from the compact `ℝP³`
(`bdryEquivRP3`, `continuous_bdryEquivRP3`) is a homeomorphism onto the now-Hausdorff subspace `∂E`
(`Continuous.homeoOfEquivCompactToT2`, using `instT2SpaceResE`). This is the `∂E ≅ ℝP³` identification
K6′b welds along — an honest topological homeomorphism (both directions continuous), unconditional. -/
def bdryHomeoRP3 : RP3 ≃ₜ ↥boundaryE :=
  Continuous.homeoOfEquivCompactToT2 (f := bdryEquivRP3) continuous_bdryEquivRP3

/-! ## §9. The fiber-scaling deformation retraction of `E` onto the zero section `S²` (K7 feeder)

`E` deformation-retracts onto its zero section: scale the fiber coordinate `w ↦ t·w` for
`t ∈ [0,1]`. At `t = 1` this is the identity; at `t = 0` it collapses every fiber to `0`, landing on
the zero-section `S²`. The scaling is **fiber-linear**, so it commutes with the Euler−2 clutch
(`t·(z²·w) = z²·(t·w)`) and hence descends to the quotient `E` as a total `Quotient.lift`. Joint
continuity in `(x, t)` is by the locally-compact product-quotient principle
(`IsQuotientMap.continuous_lift_prod_left`, `[0,1]` compact hence locally compact). The base
projection `π : E → S²` (forget the fiber) is the retraction; `π ∘ zeroSection = id` strictly and
`zeroSection ∘ π ≃ id` via this deformation — a genuine homotopy equivalence `E ≃ S²`, the input the
K7 Mayer–Vietoris accounting consumes as `H₂(E;ℤ) ≅ H₂(S²;ℤ)`. -/

/-- **The base projection** `π : E → S²` — forget the fiber. Well-defined: the equator weld
`z ↦ z⁻¹` on the base is exactly the base-`S²` gluing (`baseGlued`). -/
def baseProj : ResE → BaseS2 :=
  Quotient.lift (Sum.elim (fun p => baseChart0 p.1) (fun p => baseChart1 p.1)) (by
    rintro a b (rfl | hg)
    · rfl
    · cases a with
      | inl p =>
        cases b with
        | inr q =>
          exact Quotient.sound (Or.inr (show baseGlued p.1 q.1 from ⟨hg.1, hg.2.1⟩))
        | inl _ => exact (hg : False).elim
      | inr q =>
        cases b with
        | inl p =>
          exact (Quotient.sound (Or.inr (show baseGlued p.1 q.1 from ⟨hg.1, hg.2.1⟩))).symm
        | inr _ => exact (hg : False).elim)

@[simp] theorem baseProj_chart0 (p : ResChart) : baseProj (chart0 p) = baseChart0 p.1 := rfl
@[simp] theorem baseProj_chart1 (p : ResChart) : baseProj (chart1 p) = baseChart1 p.1 := rfl

theorem continuous_baseProj : Continuous baseProj := by
  apply Continuous.quotient_lift
  exact (continuous_baseChart0.comp continuous_fst).sumElim (continuous_baseChart1.comp continuous_fst)

/-- **`π ∘ zeroSection = id`** — the zero section is a genuine section of the base projection. -/
theorem baseProj_zeroSection (x : BaseS2) : baseProj (zeroSection x) = x := by
  induction x using Quotient.ind with
  | _ a => cases a with
    | inl z => rfl
    | inr z => rfl

/-- Scale a fiber `Disk` element by `t ∈ [0,1]`: `w ↦ t·w`, staying in `D²`
(`‖t·w‖ = t‖w‖ ≤ ‖w‖ ≤ 1`). -/
def scaleDisk (t : unitInterval) (w : Disk) : Disk :=
  ⟨((t : ℝ) : ℂ) * (w : ℂ), by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (unitInterval.nonneg t)]
    calc (t : ℝ) * ‖(w : ℂ)‖ ≤ 1 * ‖(w : ℂ)‖ :=
            mul_le_mul_of_nonneg_right (unitInterval.le_one t) (norm_nonneg _)
      _ = ‖(w : ℂ)‖ := one_mul _
      _ ≤ 1 := w.2⟩

@[simp] theorem scaleDisk_coe (t : unitInterval) (w : Disk) :
    ((scaleDisk t w : Disk) : ℂ) = ((t : ℝ) : ℂ) * (w : ℂ) := rfl

theorem continuous_scaleDisk : Continuous (fun p : unitInterval × Disk => scaleDisk p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)

/-- The fiber-scaled point of `E`, before descent: the chart-`i` point `(z, t·w)`. -/
def scaledSum (a : ResChart ⊕ ResChart) (t : unitInterval) : ResE :=
  Sum.elim (fun p => chart0 (p.1, scaleDisk t p.2)) (fun p => chart1 (p.1, scaleDisk t p.2)) a

/-- **Fiber-scaling respects the weld** (fiber-linearity): if `a ~ b` then their fiber-scaled points
coincide in `E`. This is the `t·(z²·w) = z²·(t·w)` identity that makes the deformation descend. -/
theorem scaledSum_respects {a b : ResChart ⊕ ResChart} (t : unitInterval) (h : resRel a b) :
    scaledSum a t = scaledSum b t := by
  rcases h with rfl | hg
  · rfl
  · cases a with
    | inl p =>
      cases b with
      | inr q =>
        obtain ⟨hz, hq1, hq2⟩ := (hg : glued p q)
        refine chart0_eq_chart1' (q := (p.1, scaleDisk t p.2)) (p := (q.1, scaleDisk t q.2))
          hz hq1 ?_
        show ((t : ℝ) : ℂ) * (q.2 : ℂ) = (p.1 : ℂ) ^ 2 * (((t : ℝ) : ℂ) * (p.2 : ℂ))
        rw [hq2]; ring
      | inl _ => exact (hg : False).elim
    | inr q =>
      cases b with
      | inl p =>
        obtain ⟨hz, hq1, hq2⟩ := (hg : glued p q)
        refine (chart0_eq_chart1' (q := (p.1, scaleDisk t p.2)) (p := (q.1, scaleDisk t q.2))
          hz hq1 ?_).symm
        show ((t : ℝ) : ℂ) * (q.2 : ℂ) = (p.1 : ℂ) ^ 2 * (((t : ℝ) : ℂ) * (p.2 : ℂ))
        rw [hq2]; ring
      | inr _ => exact (hg : False).elim

/-- **The fiber-scaling deformation** `H : E × [0,1] → E` — scale the fiber by `t`. `t = 1` is the
identity (`deform_one`); `t = 0` is the zero-section retraction `zeroSection ∘ baseProj`
(`deform_zero`). Descends from `scaledSum` by fiber-linearity (`scaledSum_respects`). -/
def deform : ResE × unitInterval → ResE :=
  fun p => Quotient.liftOn p.1 (fun a => scaledSum a p.2) (fun _ _ h => scaledSum_respects p.2 h)

@[simp] theorem deform_mk (a : ResChart ⊕ ResChart) (t : unitInterval) :
    deform (Quotient.mk resSetoid a, t) = scaledSum a t := rfl

theorem continuous_scaledSum :
    Continuous (fun p : (ResChart ⊕ ResChart) × unitInterval => scaledSum p.1 p.2) := by
  have hg0 : Continuous (fun q : ResChart × unitInterval => chart0 (q.1.1, scaleDisk q.2 q.1.2)) :=
    continuous_chart0.comp (Continuous.prodMk (continuous_fst.comp continuous_fst)
      (continuous_scaleDisk.comp
        (Continuous.prodMk continuous_snd (continuous_snd.comp continuous_fst))))
  have hg1 : Continuous (fun q : ResChart × unitInterval => chart1 (q.1.1, scaleDisk q.2 q.1.2)) :=
    continuous_chart1.comp (Continuous.prodMk (continuous_fst.comp continuous_fst)
      (continuous_scaleDisk.comp
        (Continuous.prodMk continuous_snd (continuous_snd.comp continuous_fst))))
  have hcongr : (fun p : (ResChart ⊕ ResChart) × unitInterval => scaledSum p.1 p.2)
      = (Sum.elim (fun q : ResChart × unitInterval => chart0 (q.1.1, scaleDisk q.2 q.1.2))
          (fun q : ResChart × unitInterval => chart1 (q.1.1, scaleDisk q.2 q.1.2)))
        ∘ Homeomorph.sumProdDistrib := by
    funext p
    obtain ⟨a, t⟩ := p
    cases a with
    | inl q => rfl
    | inr q => rfl
  rw [hcongr]
  exact (hg0.sumElim hg1).comp Homeomorph.sumProdDistrib.continuous

theorem continuous_deform : Continuous deform := by
  have hq : Topology.IsQuotientMap (Quotient.mk resSetoid) := isQuotientMap_quotient_mk'
  exact hq.continuous_lift_prod_left continuous_scaledSum

/-- **`H(·, 1) = id`** — the `t = 1` slice of the deformation is the identity. -/
theorem deform_one (x : ResE) : deform (x, 1) = x := by
  induction x using Quotient.ind with
  | _ a => cases a with
    | inl q =>
      show chart0 (q.1, scaleDisk 1 q.2) = chart0 q
      exact congrArg chart0 (Prod.ext rfl (Subtype.ext (by simp)))
    | inr q =>
      show chart1 (q.1, scaleDisk 1 q.2) = chart1 q
      exact congrArg chart1 (Prod.ext rfl (Subtype.ext (by simp)))

/-- **`H(·, 0) = zeroSection ∘ baseProj`** — the `t = 0` slice collapses every fiber to the zero
section. This is the deformation-retraction endpoint. -/
theorem deform_zero (x : ResE) : deform (x, 0) = zeroSection (baseProj x) := by
  induction x using Quotient.ind with
  | _ a => cases a with
    | inl q =>
      show chart0 (q.1, scaleDisk 0 q.2) = zeroSection (baseChart0 q.1)
      rw [zeroSection_baseChart0]
      exact congrArg chart0 (Prod.ext rfl (Subtype.ext (by simp [zeroPt, zeroFiber])))
    | inr q =>
      show chart1 (q.1, scaleDisk 0 q.2) = zeroSection (baseChart1 q.1)
      rw [zeroSection_baseChart1]
      exact congrArg chart1 (Prod.ext rfl (Subtype.ext (by simp [zeroPt, zeroFiber])))

/-- **The deformation fixes the zero section**: on the zero-locus the fiber is already `0`, so scaling
does nothing — `H(zeroSection z, t) = zeroSection z` for every `t`. (Strong deformation retraction.) -/
theorem deform_zeroSection (z : BaseS2) (t : unitInterval) :
    deform (zeroSection z, t) = zeroSection z := by
  induction z using Quotient.ind with
  | _ a => cases a with
    | inl w =>
      show chart0 ((zeroPt w).1, scaleDisk t (zeroPt w).2) = chart0 (zeroPt w)
      exact congrArg chart0 (Prod.ext rfl (Subtype.ext (by simp [zeroPt, zeroFiber])))
    | inr w =>
      show chart1 ((zeroPt w).1, scaleDisk t (zeroPt w).2) = chart1 (zeroPt w)
      exact congrArg chart1 (Prod.ext rfl (Subtype.ext (by simp [zeroPt, zeroFiber])))

end

end SKEFTHawking.KummerResolutionPiece
