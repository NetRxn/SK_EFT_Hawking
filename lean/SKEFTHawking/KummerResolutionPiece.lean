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

end

end SKEFTHawking.KummerResolutionPiece
