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

end

end SKEFTHawking.KummerResolutionPiece
