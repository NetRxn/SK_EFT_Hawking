/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 1(c), increment 2 — Lemma C.16: the relative-norm solvability iff

Ross–Selinger arXiv:1403.2975v3 **Lemma C.16**: for `ξ ∈ ℤ[√2]`, the equation `t†t = ξ`
(`t ∈ ℤ[ω]`) has a solution **iff** `ξ` is doubly positive and †-decomposable (`t†t ~ ξ` up to an
`ℤ[√2]`-unit, Definition C.15). The unit input is the shipped Lemma C.2
(`zsqrt2_isSquare_of_unit_pos_pos`): the doubly-positive unit relating `t†t` to `ξ` is a square
`v²`, and `v` absorbs into `t` (`ξ = (vt)†(vt)`, since `v` is real).

Infrastructure: the ring embedding `ℤ[√2] →+* ℤ[ω]` (`x + y√2 ↦ ⟨−y, 0, y, x⟩`), its
compatibility with the three conjugations (`conj`-fixed; `σ5 ∘ embed = embed ∘ star`) and with
the complex/real embeddings (`toComplex ∘ embed = ℝ-cast ∘ zsqrt2ToReal`), and the `ℤ[√2]`-valued
relative norm `relNormZsqrt2 t = ⟨(t†t).d, (t†t).c⟩` with `embed (relNormZsqrt2 t) = t†t` and
`Zsqrtd.norm (relNormZsqrt2 t) = ZOmega.norm t` (the norm tower).

The nonvanishing input (`t ≠ 0 ⟹ φ(t†t) > 0`) is by the norm tower + `norm_eq_zero_iff`
(`ZOmegaEuclideanDomain.lean`) — no injectivity of `toComplex` needed.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.

## References

  * Ross–Selinger, arXiv:1403.2975v3, Appendix C.4 (Definitions C.14/C.15, Lemma C.16).
-/

import SKEFTHawking.FKLW.RossSelinger.Zsqrt2Units
import SKEFTHawking.FKLW.RossSelinger.RelativeNorm
import SKEFTHawking.FKLW.RossSelinger.ZOmegaEuclideanDomain

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-! ### The embedding `ℤ[√2] →+* ℤ[ω]` -/

/-- The ring embedding `ℤ[√2] → ℤ[ω]`, `x + y√2 ↦ −y·ω³ + y·ω + x` (`√2 = ω − ω³`). -/
def zsqrt2ToZOmega : Zsqrtd 2 →+* ZOmega where
  toFun ξ := ⟨-ξ.im, 0, ξ.im, ξ.re⟩
  map_one' := by ext <;> rfl
  map_mul' x y := by
    ext <;>
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, ZOmega.mul_a, ZOmega.mul_b, ZOmega.mul_c,
        ZOmega.mul_d] <;>
      ring
  map_zero' := by ext <;> rfl
  map_add' x y := by
    ext <;>
      simp only [Zsqrtd.re_add, Zsqrtd.im_add, ZOmega.add_a, ZOmega.add_b, ZOmega.add_c,
        ZOmega.add_d] <;>
      ring

@[simp] theorem zsqrt2ToZOmega_a (ξ : Zsqrtd 2) : (zsqrt2ToZOmega ξ).a = -ξ.im := rfl
@[simp] theorem zsqrt2ToZOmega_b (ξ : Zsqrtd 2) : (zsqrt2ToZOmega ξ).b = 0 := rfl
@[simp] theorem zsqrt2ToZOmega_c (ξ : Zsqrtd 2) : (zsqrt2ToZOmega ξ).c = ξ.im := rfl
@[simp] theorem zsqrt2ToZOmega_d (ξ : Zsqrtd 2) : (zsqrt2ToZOmega ξ).d = ξ.re := rfl

theorem zsqrt2ToZOmega_injective : Function.Injective zsqrt2ToZOmega := by
  intro x y h
  ext
  · exact congrArg ZOmega.d h
  · exact congrArg ZOmega.c h

/-- Embedded `ℤ[√2]`-elements are `conj`-fixed (real). -/
theorem conj_zsqrt2ToZOmega (ξ : Zsqrtd 2) :
    ZOmega.conj (zsqrt2ToZOmega ξ) = zsqrt2ToZOmega ξ := by
  ext <;> simp [ZOmega.conj]

/-- The embedding intertwines `√2`-conjugation: `σ5 ∘ embed = embed ∘ star`. -/
theorem σ5_zsqrt2ToZOmega (ξ : Zsqrtd 2) :
    ZOmega.σ5 (zsqrt2ToZOmega ξ) = zsqrt2ToZOmega (star ξ) := by
  ext <;> simp [ZOmega.σ5, Zsqrtd.re_star, Zsqrtd.im_star]

/-- The complex embedding restricted to `ℤ[√2]` is the real embedding. -/
theorem toComplex_zsqrt2ToZOmega (ξ : Zsqrtd 2) :
    ZOmega.toComplex (zsqrt2ToZOmega ξ) = ((zsqrt2ToReal ξ : ℝ) : ℂ) := by
  have hs2 : ZOmega.toComplex ZOmega.sqrt2 = ((Real.sqrt 2 : ℝ) : ℂ) := by
    rw [← ZOmegaSqrt2.s2C_def, ZOmegaSqrt2.s2C_eq]
  have hsplit : zsqrt2ToZOmega ξ = (ξ.re : ZOmega) + (ξ.im : ZOmega) * ZOmega.sqrt2 := by
    ext <;>
      simp only [zsqrt2ToZOmega_a, zsqrt2ToZOmega_b, zsqrt2ToZOmega_c, zsqrt2ToZOmega_d,
        ZOmega.add_a, ZOmega.add_b, ZOmega.add_c, ZOmega.add_d,
        ZOmega.mul_a, ZOmega.mul_b, ZOmega.mul_c, ZOmega.mul_d,
        ZOmega.sqrt2_a, ZOmega.sqrt2_b, ZOmega.sqrt2_c, ZOmega.sqrt2_d,
        show ∀ n : ℤ, ((n : ZOmega)).a = 0 from fun _ => rfl,
        show ∀ n : ℤ, ((n : ZOmega)).b = 0 from fun _ => rfl,
        show ∀ n : ℤ, ((n : ZOmega)).c = 0 from fun _ => rfl,
        show ∀ n : ℤ, ((n : ZOmega)).d = n from fun _ => rfl] <;>
      ring
  rw [hsplit, map_add, map_mul, hs2, map_intCast, map_intCast, zsqrt2ToReal_apply]
  push_cast
  ring

/-! ### The `ℤ[√2]`-valued relative norm and the norm tower -/

/-- The `ℤ[√2]`-valued relative norm: `t†t` repackaged as `(t†t).d + (t†t).c·√2`. -/
def relNormZsqrt2 (t : ZOmega) : Zsqrtd 2 := ⟨(ZOmega.normSq t).d, (ZOmega.normSq t).c⟩

/-- The repackaging is faithful: `embed (relNormZsqrt2 t) = t†t`. -/
theorem zsqrt2ToZOmega_relNormZsqrt2 (t : ZOmega) :
    zsqrt2ToZOmega (relNormZsqrt2 t) = ZOmega.normSq t := by
  obtain ⟨a, b, c, d⟩ := t
  show zsqrt2ToZOmega
    ⟨(ZOmega.normSq ⟨a, b, c, d⟩).d, (ZOmega.normSq ⟨a, b, c, d⟩).c⟩ = ZOmega.normSq ⟨a, b, c, d⟩
  rw [normSq_coords]
  ext <;> simp

/-- **The norm tower**: `N_{ℤ[√2]}(relNormZsqrt2 t) = N_{ℤ[ω]}(t)`. -/
theorem zsqrtd_norm_relNormZsqrt2 (t : ZOmega) :
    Zsqrtd.norm (relNormZsqrt2 t) = ZOmega.norm t := by
  rw [Zsqrtd.norm_def, norm_eq_relNorm]
  show (ZOmega.normSq t).d * (ZOmega.normSq t).d
      - 2 * (ZOmega.normSq t).c * (ZOmega.normSq t).c = _
  ring

/-- `relNormZsqrt2` intertwines `σ5` with `star`. -/
theorem relNormZsqrt2_σ5 (t : ZOmega) : relNormZsqrt2 (ZOmega.σ5 t) = star (relNormZsqrt2 t) := by
  apply zsqrt2ToZOmega_injective
  rw [zsqrt2ToZOmega_relNormZsqrt2, ← σ5_zsqrt2ToZOmega, zsqrt2ToZOmega_relNormZsqrt2]
  show ZOmega.normSq (ZOmega.σ5 t) = ZOmega.σ5 (ZOmega.normSq t)
  obtain ⟨a, b, c, d⟩ := t
  ext <;> simp [ZOmega.normSq, ZOmega.σ5, ZOmega.conj] <;> ring

/-- The real embedding of the relative norm is nonnegative (total positivity, via the complex
embedding: `φ(t†t) = |toComplex t|² ≥ 0`). -/
theorem zsqrt2ToReal_relNormZsqrt2_nonneg (t : ZOmega) : 0 ≤ zsqrt2ToReal (relNormZsqrt2 t) := by
  have h := normSq_toComplex_re_nonneg t
  rw [← zsqrt2ToZOmega_relNormZsqrt2, toComplex_zsqrt2ToZOmega] at h
  simpa using h

/-- Strict positivity for `t ≠ 0` (via the norm tower and `norm_eq_zero_iff` — no `toComplex`
injectivity needed). -/
theorem zsqrt2ToReal_relNormZsqrt2_pos {t : ZOmega} (ht : t ≠ 0) :
    0 < zsqrt2ToReal (relNormZsqrt2 t) := by
  rcases lt_or_eq_of_le (zsqrt2ToReal_relNormZsqrt2_nonneg t) with h | h
  · exact h
  · exfalso
    -- φ(relNorm) = 0 with φ·φ∘star = norm ⟹ norm t = 0 ⟹ t = 0
    have hns : zsqrt2ToReal (relNormZsqrt2 t) * zsqrt2ToReal (star (relNormZsqrt2 t))
        = ((Zsqrtd.norm (relNormZsqrt2 t) : ℤ) : ℝ) := by
      rw [← map_mul, ← Zsqrtd.norm_eq_mul_conj]
      exact (map_intCast zsqrt2ToReal _)
    rw [← h] at hns
    simp only [zero_mul] at hns
    have hz : Zsqrtd.norm (relNormZsqrt2 t) = 0 := by exact_mod_cast hns.symm
    rw [zsqrtd_norm_relNormZsqrt2] at hz
    exact ht (ZOmega.norm_eq_zero_iff.mp hz)

theorem zsqrt2ToReal_star_relNormZsqrt2_nonneg (t : ZOmega) :
    0 ≤ zsqrt2ToReal (star (relNormZsqrt2 t)) := by
  rw [← relNormZsqrt2_σ5]
  exact zsqrt2ToReal_relNormZsqrt2_nonneg _

theorem zsqrt2ToReal_star_relNormZsqrt2_pos {t : ZOmega} (ht : t ≠ 0) :
    0 < zsqrt2ToReal (star (relNormZsqrt2 t)) := by
  rw [← relNormZsqrt2_σ5]
  refine zsqrt2ToReal_relNormZsqrt2_pos fun h => ht ?_
  have := congrArg ZOmega.σ5 h
  simpa [show ∀ z, ZOmega.σ5 (ZOmega.σ5 z) = z from fun z => by ext <;> simp [ZOmega.σ5]]
    using this

/-! ### Definitions C.1 / C.15 and Lemma C.16 -/

/-- **Doubly positive** (paper Definition C.1): `ξ ≥ 0 ∧ ξ• ≥ 0` under the real embedding. -/
def DoublyPositive (ξ : Zsqrtd 2) : Prop :=
  0 ≤ zsqrt2ToReal ξ ∧ 0 ≤ zsqrt2ToReal (star ξ)

/-- **†-decomposable** (paper Definition C.15): `t†t ~ ξ` up to an `ℤ[√2]`-unit. -/
def DaggerDecomposable (ξ : Zsqrtd 2) : Prop :=
  ∃ (t : ZOmega) (u : Zsqrtd 2), IsUnit u ∧ u * relNormZsqrt2 t = ξ

/-- The forward direction: a relative norm is doubly positive (Lemma 6.1) and †-decomposable. -/
theorem doublyPositive_decomposable_of_relNorm {ξ : Zsqrtd 2}
    (h : ∃ t : ZOmega, ZOmega.normSq t = zsqrt2ToZOmega ξ) :
    DoublyPositive ξ ∧ DaggerDecomposable ξ := by
  obtain ⟨t, ht⟩ := h
  have hξ : relNormZsqrt2 t = ξ :=
    zsqrt2ToZOmega_injective (by rw [zsqrt2ToZOmega_relNormZsqrt2, ht])
  refine ⟨⟨?_, ?_⟩, ⟨t, 1, isUnit_one, by rw [one_mul, hξ]⟩⟩
  · rw [← hξ]
    exact zsqrt2ToReal_relNormZsqrt2_nonneg t
  · rw [← hξ]
    exact zsqrt2ToReal_star_relNormZsqrt2_nonneg t

/-- **Lemma C.16, the substantive direction**: a doubly-positive †-decomposable `ξ ∈ ℤ[√2]` is a
relative norm `t†t` on the nose — the relating unit is doubly positive, hence a square `v²`
(Lemma C.2 / `zsqrt2_isSquare_of_unit_pos_pos`), and `v` absorbs into `t`. -/
theorem relNorm_of_doublyPositive_decomposable {ξ : Zsqrtd 2}
    (hpos : DoublyPositive ξ) (hdec : DaggerDecomposable ξ) :
    ∃ t : ZOmega, ZOmega.normSq t = zsqrt2ToZOmega ξ := by
  obtain ⟨t, u, hu, heq⟩ := hdec
  by_cases ht0 : t = 0
  · -- ξ = 0, witnessed by t = 0
    refine ⟨0, ?_⟩
    have hr0 : relNormZsqrt2 (0 : ZOmega) = 0 := by
      apply zsqrt2ToZOmega_injective
      rw [zsqrt2ToZOmega_relNormZsqrt2, map_zero]
      show ZOmega.normSq 0 = 0
      exact ZOmega.normSq_zero
    rw [ht0, hr0, mul_zero] at heq
    show ZOmega.normSq 0 = _
    rw [ZOmega.normSq_zero, ← heq, map_zero]
  · -- the unit is doubly positive
    have hrpos := zsqrt2ToReal_relNormZsqrt2_pos ht0
    have hrspos := zsqrt2ToReal_star_relNormZsqrt2_pos ht0
    have hueq : zsqrt2ToReal u * zsqrt2ToReal (relNormZsqrt2 t) = zsqrt2ToReal ξ := by
      rw [← map_mul, heq]
    have hueqs : zsqrt2ToReal (star u) * zsqrt2ToReal (star (relNormZsqrt2 t))
        = zsqrt2ToReal (star ξ) := by
      rw [← map_mul, ← star_mul', heq]
    -- units have nonzero embedding (their norm is ±1)
    have huabs : (Zsqrtd.norm u).natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hu
    have huprod : zsqrt2ToReal u * zsqrt2ToReal (star u)
        = ((Zsqrtd.norm u : ℤ) : ℝ) := by
      rw [← map_mul, ← Zsqrtd.norm_eq_mul_conj]
      exact (map_intCast zsqrt2ToReal _)
    have hune : zsqrt2ToReal u ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at huprod
      have : Zsqrtd.norm u = 0 := by exact_mod_cast huprod.symm
      omega
    have husne : zsqrt2ToReal (star u) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at huprod
      have : Zsqrtd.norm u = 0 := by exact_mod_cast huprod.symm
      omega
    have hupos : 0 < zsqrt2ToReal u := by
      rcases lt_or_gt_of_ne hune with h | h
      · exfalso
        nlinarith [hpos.1]
      · exact h
    have huspos : 0 < zsqrt2ToReal (star u) := by
      rcases lt_or_gt_of_ne husne with h | h
      · exfalso
        nlinarith [hpos.2]
      · exact h
    -- Lemma C.2: the unit is a square, and the square root absorbs
    obtain ⟨v, hv⟩ := zsqrt2_isSquare_of_unit_pos_pos hu hupos huspos
    refine ⟨zsqrt2ToZOmega v * t, ?_⟩
    have hconj : ZOmega.conj (zsqrt2ToZOmega v) = zsqrt2ToZOmega v := conj_zsqrt2ToZOmega v
    show (zsqrt2ToZOmega v * t) * ZOmega.conj (zsqrt2ToZOmega v * t) = _
    rw [ZOmega.conj_mul, hconj]
    have : zsqrt2ToZOmega v * t * (zsqrt2ToZOmega v * ZOmega.conj t)
        = zsqrt2ToZOmega (v * v) * (t * ZOmega.conj t) := by
      rw [map_mul]
      ring
    rw [this, show t * ZOmega.conj t = ZOmega.normSq t from rfl,
      ← zsqrt2ToZOmega_relNormZsqrt2 t, ← map_mul, ← hv, heq]

/-- **Lemma C.16** (Ross–Selinger arXiv:1403.2975v3): `t†t = ξ` is solvable in `ℤ[ω]` iff `ξ` is
doubly positive and †-decomposable.

NOTE (Stage-13): this is the **`ℤ`-level** statement (`ξ ∈ ℤ[√2]`, `t ∈ ℤ[ω]`) — the level at
which the paper's §C.5 (C.19–C.21) and this project's consumers operate. The paper's C.16 is
stated for `𝔻[√2]`/`𝔻[ω]`; the denominator-clearing reduction (paper Lemma C.17) is not
formalized here. -/
theorem relNorm_iff_doublyPositive_decomposable (ξ : Zsqrtd 2) :
    (∃ t : ZOmega, ZOmega.normSq t = zsqrt2ToZOmega ξ) ↔
      DoublyPositive ξ ∧ DaggerDecomposable ξ :=
  ⟨doublyPositive_decomposable_of_relNorm,
    fun ⟨hpos, hdec⟩ => relNorm_of_doublyPositive_decomposable hpos hdec⟩

end SKEFTHawking.RossSelinger
