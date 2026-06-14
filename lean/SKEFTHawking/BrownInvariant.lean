import Mathlib

/-!
# The Arf–Brown–Kervaire (Brown) invariant in `ZMod 8`

Phase 5q.F Wave 1. This module lifts the `ZMod 2`-valued, real (`±1`) Gauss sum of
`SKEFTHawking.Arf` (`ArfInvariant.lean`, which carries the **Arf** invariant `∈ ZMod 2`) to the
`ZMod 4`-valued Gauss sum over the Gaussian integers `ℤ[i]`, which carries the **Arf–Brown–Kervaire
(Brown) invariant** `∈ ZMod 8`.

This is the genuine algebraic heart of the Pin⁺ `ℤ₁₆` bordism invariant: by the
Guillou–Marin / Kirby–Taylor formula the Pin⁺ `ℤ₁₆` of a `4`-manifold is read off a characteristic
**surface** carrying a `ZMod 4`-valued quadratic enhancement, whose Brown invariant is exactly the
phase of the Gauss sum built here. The project's no-go `RokhlinArfNoGo.lean`
(`lattice_arf_bridge_refuted`) proved the mod-`16` is *not* a lattice Arf invariant — it is this
characteristic-surface Brown invariant. See `docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md`.

The Gauss sum is `g(q) = ∑ₓ i^{q(x)} ∈ ℤ[i]` for a `ZMod 4`-quadratic form `q`. For a nondegenerate
refinement `g(q) = √|V| · ζ₈^{β}` with `β = Brown(q) ∈ ZMod 8`; equivalently `g(q)·conj g(q) = |V|`.

All proofs are kernel-pure (`decide` over the finite primitives; no `native_decide`, no axioms).
-/

namespace SKEFTHawking.Brown

open scoped BigOperators

/-- The imaginary unit `i ∈ ℤ[i]`. -/
def I : GaussianInt := ⟨0, 1⟩

@[simp] lemma I_sq : I * I = -1 := by decide

lemma I_pow_two : I ^ 2 = -1 := by
  rw [pow_two]; exact I_sq

@[simp] lemma I_pow_four : I ^ 4 = 1 := by decide

/-- `i^n` for `n : ZMod 4`, well-defined because `i⁴ = 1`. The `ZMod 4`-graded version of the
sign character `signZ : ZMod 2 → ℤ` from `SKEFTHawking.Arf`. -/
def zeta4 (n : ZMod 4) : GaussianInt := I ^ n.val

@[simp] lemma zeta4_zero : zeta4 0 = 1 := by decide

/-- The defining homomorphism property: `i^{a+b} = i^a · i^b` (the `ZMod 4` exponent is
well-defined modulo `i⁴ = 1`). -/
lemma zeta4_add (a b : ZMod 4) : zeta4 (a + b) = zeta4 a * zeta4 b := by
  revert a b; decide

/-- The `ZMod 4` Gauss sum of a quadratic form `q : ι → ZMod 4` over a finite type. -/
def gaussSum4 {ι : Type*} [Fintype ι] (q : ι → ZMod 4) : GaussianInt := ∑ x, zeta4 (q x)

/-- Multiplicativity under orthogonal direct sum (the `ℤ[i]` analogue of
`SKEFTHawking.Arf.gaussSum_orthogonal`). -/
theorem gaussSum4_orthogonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ZMod 4) (g : κ → ZMod 4) :
    gaussSum4 (fun p : ι × κ => f p.1 + g p.2) = gaussSum4 f * gaussSum4 g := by
  unfold gaussSum4
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [zeta4_add]

/-- `zeta4` extends to finite sums: `i^{∑ᵢ fᵢ} = ∏ᵢ i^{fᵢ}` (the ℤ[i] analogue of
`SKEFTHawking.Arf.signZ_sum`). -/
theorem zeta4_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 4) :
    zeta4 (∑ i ∈ s, f i) = ∏ i ∈ s, zeta4 (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [zeta4_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zeta4_add, ih]

/-- **Genus-`g` multiplicativity.** For a block-diagonal form `x ↦ ∑ᵢ qᵢ(xᵢ)` on `∀ i, V i`,
the Gauss sum factorises as `∏ᵢ gaussSum4 qᵢ` (the ℤ[i] analogue of `Arf.gaussSum_pi`). -/
theorem gaussSum4_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
    [∀ i, Fintype (V i)] (q : ∀ i, V i → ZMod 4) :
    gaussSum4 (fun x : (∀ i, V i) => ∑ i, q i (x i)) = ∏ i, gaussSum4 (q i) := by
  unfold gaussSum4
  simp only [zeta4_sum]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- The `1`-dimensional generator: the `ZMod 4`-quadratic form on `ZMod 2` with `q(1) = 1`.
This is the Pin⁻ Möbius/`RP²` generator whose Brown invariant is `+1`. -/
def qGen : ZMod 2 → ZMod 4 := fun x => (x.val : ZMod 4)

/-- The Gauss sum of the generator is `1 + i` (i.e. `√2 · ζ₈`, phase `ζ₈^1`). -/
theorem gaussSum4_qGen : gaussSum4 qGen = 1 + I := by decide

/-- Magnitude of the generator Gauss sum: `(1+i)·conj(1+i) = 2 = |ZMod 2|`. The Gauss-sum
magnitude theorem at the generator — the seed of the general `g·conj g = |V|`. -/
theorem gaussSum4_qGen_normSq : gaussSum4 qGen * star (gaussSum4 qGen) = 2 := by
  rw [gaussSum4_qGen]; decide

/-! ## The genus-`g` standard form and the `ZMod 8` structure of the Brown phase

The orthogonal sum of `g` copies of the generator has Gauss sum `(1+i)^g = (√2 · ζ₈)^g`, phase
`ζ₈^g`. The three power facts below pin the order of the phase to exactly `8`:
`ζ₈² = i` (not real), `ζ₈⁴ = -1` (real but negative), `ζ₈⁸ = 1` (positive real). Hence the Brown
invariant carried by this phase is genuinely `ZMod 8`-valued — not `ZMod 4` or `ZMod 2`. -/

/-- The genus-`g` standard form: the orthogonal sum of `g` copies of the generator `qGen`. -/
def stdForm (g : ℕ) : (Fin g → ZMod 2) → ZMod 4 := fun x => ∑ i, qGen (x i)

/-- The genus-`g` standard Gauss sum is `(1+i)^g`. -/
theorem gaussSum4_stdForm (g : ℕ) : gaussSum4 (stdForm g) = (1 + I) ^ g := by
  unfold stdForm
  rw [gaussSum4_pi (fun _ : Fin g => qGen)]
  simp only [gaussSum4_qGen, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `(1+i)² = 2i`: the Brown phase at genus `2` is imaginary (order does not divide `2`). -/
theorem one_add_I_pow_two : (1 + I) ^ 2 = 2 * I := by decide

/-- `(1+i)⁴ = -4`: the Brown phase at genus `4` is negative real (order does not divide `4`). -/
theorem one_add_I_pow_four : (1 + I) ^ 4 = -4 := by decide

/-- `(1+i)⁸ = 16`: the Brown phase returns to positive real at genus `8` (order divides `8`). -/
theorem one_add_I_pow_eight : (1 + I) ^ 8 = 16 := by decide

/-- **Magnitude of the standard genus-`g` Gauss sum:** `|（1+i)^g|² = 2^g = |(ZMod 2)^g|`.
The Gauss-sum magnitude theorem on the forms that generate the whole `ZMod 8` structure. -/
theorem gaussSum4_stdForm_normSq (g : ℕ) :
    gaussSum4 (stdForm g) * star (gaussSum4 (stdForm g)) = (2 : GaussianInt) ^ g := by
  rw [gaussSum4_stdForm, star_pow, ← mul_pow]
  rw [show (1 + I) * star (1 + I) = (2 : GaussianInt) from by decide]

/-- The genus-`8` standard Gauss sum is the positive real `16` — phase `ζ₈⁸ = 1`. -/
theorem gaussSum4_stdForm_eight : gaussSum4 (stdForm 8) = 16 := by
  rw [gaussSum4_stdForm]; exact one_add_I_pow_eight

/-- **The Brown invariant of the genus-`g` standard form is `g mod 8`.** Its defining property is
the Gauss-sum phase `ζ₈^{brownStd g}`; `brownStd` is additive under orthogonal sum, and genuinely
`ZMod 8`-valued (the generator has order `8`, witnessed by `one_add_I_pow_{two,four,eight}`). -/
def brownStd (g : ℕ) : ZMod 8 := (g : ZMod 8)

/-- Additivity of the standard Brown invariant under orthogonal sum (`stdForm` block-stacking). -/
theorem brownStd_add (g h : ℕ) : brownStd (g + h) = brownStd g + brownStd h := by
  simp [brownStd]

/-- The generator's Brown invariant is `1`. -/
@[simp] theorem brownStd_one : brownStd 1 = 1 := rfl

/-- Genuinely `ZMod 8`-valued: the generator has additive order exactly `8`. -/
theorem brownStd_order_eight : brownStd 8 = 0 ∧ brownStd 4 ≠ 0 ∧ brownStd 2 ≠ 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## General nondegenerate `ZMod 4`-quadratic forms and the magnitude theorem

The well-definedness of the Brown invariant: for a `ZMod 4`-quadratic refinement `q` of a
**nondegenerate** symmetric `ZMod 2`-bilinear form `B` on a finite `ZMod 2`-space, the Gauss sum
satisfies `gaussSum4 q · conj (gaussSum4 q) = |V|`. Hence `gaussSum4 q = √|V| · ζ₈^{β}` with the
Brown invariant `β` the phase. The proof is character orthogonality on `B`: after a translation
reindex the double sum factors as `∑_z i^{q z} · ∑_y (-1)^{B z y}`, and the inner character sum
vanishes for `z ≠ 0` by nondegeneracy. -/

/-- Embed `ZMod 2 ↪ ZMod 4` as `{0,1} ↦ {0,2}` — the polar-form coefficient: the bilinear form
associated to a `ZMod 4`-quadratic form is `2·B`. -/
def embed2 (b : ZMod 2) : ZMod 4 := 2 * (b.val : ZMod 4)

/-- `embed2` is additive (`b ↦ 2b` is a `ZMod 2 → ZMod 4` homomorphism). -/
lemma embed2_add (a b : ZMod 2) : embed2 (a + b) = embed2 a + embed2 b := by revert a b; decide

/-- The `±1` character of `ZMod 2` valued in `ℤ[i]`. -/
def chi2 (b : ZMod 2) : GaussianInt := if b = 0 then 1 else -1

/-- `chi2` is a character: adding `1` toggles the sign. -/
lemma chi2_add_one (b : ZMod 2) : chi2 (b + 1) = -chi2 b := by
  revert b; decide

@[simp] lemma star_I : star I = -I := by decide

@[simp] lemma zeta4_embed2 (b : ZMod 2) : zeta4 (embed2 b) = chi2 b := by
  revert b; decide

lemma star_zeta4 (n : ZMod 4) : star (zeta4 n) = zeta4 (-n) := by
  revert n; decide

lemma star_gaussSum4 {ι : Type*} [Fintype ι] (q : ι → ZMod 4) :
    star (gaussSum4 q) = ∑ x, zeta4 (-q x) := by
  unfold gaussSum4
  rw [star_sum]
  exact Finset.sum_congr rfl (fun x _ => star_zeta4 (q x))

/-- A nondegenerate `ZMod 4`-quadratic form on the finite `ZMod 2`-space `ι → ZMod 2`. The bilinear
form `B` is its polar form (`q(x+y) = q x + q y + 2·B x y`), symmetric, biadditive, nondegenerate. -/
structure Z4Quadratic (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The `ZMod 4`-quadratic form. -/
  q : (ι → ZMod 2) → ZMod 4
  /-- Its polar (associated symmetric bilinear) form, valued in `ZMod 2`. -/
  B : (ι → ZMod 2) → (ι → ZMod 2) → ZMod 2
  /-- `q` refines `B`: `q(x+y) = q x + q y + 2·B x y`. -/
  refine' : ∀ x y, q (x + y) = q x + q y + embed2 (B x y)
  /-- `B` is additive in its left argument. -/
  B_add_left : ∀ x y z, B (x + y) z = B x z + B y z
  /-- `B` is symmetric. -/
  B_symm : ∀ x y, B x y = B y x
  /-- `B` is nondegenerate. -/
  nondeg : ∀ x, (∀ y, B x y = 0) → x = 0

namespace Z4Quadratic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι)

/-- `B 0 y = 0` (left additivity at `0`). -/
lemma B_zero_left (y : ι → ZMod 2) : Q.B 0 y = 0 := by
  have h := Q.B_add_left 0 0 y
  rw [add_zero] at h
  simpa using h.symm

/-- `q 0 = 0`. -/
lemma q_zero : Q.q 0 = 0 := by
  have h := Q.refine' 0 0
  rw [add_zero, Q.B_zero_left, show embed2 (0 : ZMod 2) = 0 from by decide, add_zero] at h
  simpa using h.symm

/-- `B` is additive in its right argument (from symmetry + left additivity). -/
lemma B_add_right (x y z : ι → ZMod 2) : Q.B x (y + z) = Q.B x y + Q.B x z := by
  rw [Q.B_symm x (y + z), Q.B_add_left, Q.B_symm y x, Q.B_symm z x]

/-- **Character orthogonality.** For `z ≠ 0` the `±1` character sum `∑_y (-1)^{B z y}` vanishes
(`y ↦ B z y` is a nonzero `ZMod 2`-functional, balanced by the `y ↦ y + y₀` involution). -/
lemma chi2_B_sum_eq_zero {z : ι → ZMod 2} (hz : z ≠ 0) :
    ∑ y, chi2 (Q.B z y) = 0 := by
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, Q.B z y₀ ≠ 0 := by
    by_contra h
    exact hz (Q.nondeg z (fun y => by simpa using not_exists.mp h y))
  have hy1 : Q.B z y₀ = 1 := by revert hy₀; generalize Q.B z y₀ = b; revert b; decide
  set S := ∑ y, chi2 (Q.B z y) with hS
  have key : S = -S := by
    calc S = ∑ y, chi2 (Q.B z (y + y₀)) := (Equiv.sum_comp (Equiv.addRight y₀) _).symm
      _ = ∑ y, -chi2 (Q.B z y) := by
            refine Finset.sum_congr rfl (fun y _ => ?_)
            rw [Q.B_add_right z y y₀, hy1, chi2_add_one]
      _ = -S := by rw [hS, Finset.sum_neg_distrib]
  have h2 : (2 : GaussianInt) * S = 0 := by rw [two_mul]; nth_rewrite 2 [key]; exact add_neg_cancel S
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h (by decide)
  · exact h

/-- **Magnitude theorem.** `gaussSum4 q · conj (gaussSum4 q) = |V|` for a nondegenerate refinement.
This is the well-definedness of the Brown phase (`gaussSum4 q = √|V| ζ₈^β`). The proof is character
orthogonality: after a translation reindex the double sum factors as `∑_z i^{q z} · ∑_y (-1)^{B z y}`,
whose inner sum vanishes for `z ≠ 0` and is `|V|` at `z = 0`. -/
theorem gaussSum4_normSq :
    gaussSum4 Q.q * star (gaussSum4 Q.q) = (Fintype.card (ι → ZMod 2) : GaussianInt) := by
  have inner : ∀ y, (∑ x, zeta4 (Q.q x + -Q.q y)) = ∑ z, zeta4 (Q.q z) * chi2 (Q.B z y) := by
    intro y
    rw [← Equiv.sum_comp (Equiv.addRight y) (fun x => zeta4 (Q.q x + -Q.q y))]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    simp only [Equiv.coe_addRight]
    rw [Q.refine' z y,
      show Q.q z + Q.q y + embed2 (Q.B z y) + -Q.q y = Q.q z + embed2 (Q.B z y) from by ring,
      zeta4_add, zeta4_embed2]
  rw [star_gaussSum4]
  show (∑ x, zeta4 (Q.q x)) * (∑ y, zeta4 (-Q.q y)) = _
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, ← zeta4_add]
  rw [Finset.sum_comm]
  simp only [inner]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_eq_single (0 : ι → ZMod 2)
      (fun b _ hb => by rw [chi2_B_sum_eq_zero Q hb, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
  rw [q_zero, zeta4_zero, one_mul]
  have hone : ∀ y, chi2 (Q.B 0 y) = (1 : GaussianInt) := fun y => by rw [Q.B_zero_left]; rfl
  rw [Finset.sum_congr rfl (fun y _ => hone y)]
  simp [Finset.card_univ]

end Z4Quadratic

/-! ## Gaussian-integer norm-`2^N` classification → the Brown phase

Every Gaussian integer of norm `2^N` is `i^k · (1+i)^N` — proved elementarily (NO prime theory) via the
explicit `(1+i)`-division `⟨a,b⟩ = (1+i)·⟨(a+b)/2,(b-a)/2⟩` when `a ≡ b mod 2`, by induction on `N`. Since
`gaussSum4 Q.q` has norm `|V| = 2^N` (the magnitude theorem), this pins its ℤ₈ phase and defines
`brown Q ∈ ZMod 8`. -/

@[simp] lemma norm_I : I.norm = 1 := by decide

@[simp] lemma norm_one_add_I : (1 + I : GaussianInt).norm = 2 := by decide

@[simp] lemma norm_zeta4 (k : ZMod 4) : (zeta4 k).norm = 1 := by revert k; decide

@[simp] lemma I_re : I.re = 0 := rfl
@[simp] lemma I_im : I.im = 1 := rfl

/-- The units of `ℤ[i]` are exactly the powers of `i`: norm `1` ⟺ `g = i^k`. -/
lemma eq_zeta4_of_norm_eq_one {g : GaussianInt} (h : g.norm = 1) : ∃ k : ZMod 4, g = zeta4 k := by
  obtain ⟨a, b⟩ := g
  have hab : a * a + b * b = 1 := by
    have := h; simp only [Zsqrtd.norm] at this; linarith
  have ha : -1 ≤ a ∧ a ≤ 1 := ⟨by nlinarith [mul_self_nonneg b], by nlinarith [mul_self_nonneg b]⟩
  have hb : -1 ≤ b ∧ b ≤ 1 := ⟨by nlinarith [mul_self_nonneg a], by nlinarith [mul_self_nonneg a]⟩
  obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
  interval_cases a <;> interval_cases b <;> simp_all <;>
    first
      | exact ⟨0, by decide⟩
      | exact ⟨1, by decide⟩
      | exact ⟨2, by decide⟩
      | exact ⟨3, by decide⟩

@[simp] lemma one_add_I_re : (1 + I : GaussianInt).re = 1 := rfl
@[simp] lemma one_add_I_im : (1 + I : GaussianInt).im = 1 := rfl

/-- `(1+i) ∣ g` whenever `2 ∣ norm g`, via the explicit quotient (no prime theory). -/
lemma one_add_I_dvd_of_two_dvd_norm {g : GaussianInt} (h : (2 : ℤ) ∣ g.norm) : (1 + I) ∣ g := by
  obtain ⟨a, b⟩ := g
  have hn : (2 : ℤ) ∣ (a * a + b * b) := by simpa [Zsqrtd.norm] using h
  have haa : a * a % 2 = a % 2 := by
    rw [Int.mul_emod]; rcases Int.emod_two_eq_zero_or_one a with h' | h' <;> rw [h'] <;> decide
  have hbb : b * b % 2 = b % 2 := by
    rw [Int.mul_emod]; rcases Int.emod_two_eq_zero_or_one b with h' | h' <;> rw [h'] <;> decide
  obtain ⟨p, hp⟩ : (2 : ℤ) ∣ (a + b) := by omega
  obtain ⟨q, hq⟩ : (2 : ℤ) ∣ (b - a) := by omega
  refine ⟨⟨p, q⟩, ?_⟩
  apply Zsqrtd.ext
  · simp only [Zsqrtd.re_mul, one_add_I_re, one_add_I_im]; omega
  · simp only [Zsqrtd.im_mul, one_add_I_re, one_add_I_im]; omega

/-- **Norm-`2^N` classification.** Every `g` with `norm g = 2^N` is `i^k · (1+i)^N`. By induction:
strip one `(1+i)` factor each step via `one_add_I_dvd_of_two_dvd_norm`; base case = units. -/
lemma exists_zeta4_mul_of_norm_eq_pow :
    ∀ (N : ℕ) (g : GaussianInt), g.norm = 2 ^ N → ∃ k : ZMod 4, g = zeta4 k * (1 + I) ^ N := by
  intro N
  induction N with
  | zero =>
    intro g h
    simp only [pow_zero] at h
    obtain ⟨k, rfl⟩ := eq_zeta4_of_norm_eq_one h
    exact ⟨k, by simp⟩
  | succ N ih =>
    intro g h
    have hdvd : (1 + I) ∣ g := one_add_I_dvd_of_two_dvd_norm (by rw [h]; exact ⟨2 ^ N, by ring⟩)
    obtain ⟨g', rfl⟩ := hdvd
    have hg' : g'.norm = 2 ^ N := by
      have hmul : (1 + I : GaussianInt).norm * g'.norm = 2 ^ (N + 1) := by
        rw [← Zsqrtd.norm_mul]; exact h
      rw [norm_one_add_I] at hmul
      have h2 : 2 * g'.norm = 2 * 2 ^ N := by rw [hmul]; ring
      exact mul_left_cancel₀ (by norm_num) h2
    obtain ⟨k, hk⟩ := ih g' hg'
    exact ⟨k, by rw [hk]; ring⟩

/-- `zeta4` is injective (the four units `1,i,-1,-i` are distinct). -/
lemma zeta4_injective : Function.Injective zeta4 := by decide

/-- The unit `k` in the norm-`2^N` decomposition is unique. -/
lemma zeta4_mul_pow_right_inj {k k' : ZMod 4} {N : ℕ}
    (h : zeta4 k * (1 + I) ^ N = zeta4 k' * (1 + I) ^ N) : k = k' :=
  zeta4_injective (mul_right_cancel₀ (pow_ne_zero N (by decide)) h)

/-- `|ι → ZMod 2| = 2^|ι|`. -/
lemma card_fun_zmod2 (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Fintype.card (ι → ZMod 2) = 2 ^ Fintype.card ι := by
  rw [Fintype.card_fun, ZMod.card]

namespace Z4Quadratic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι)

/-- The Gauss sum has norm `2^dim` — the magnitude theorem in `Zsqrtd.norm` form. -/
lemma norm_gaussSum4 : (gaussSum4 Q.q).norm = 2 ^ Fintype.card ι := by
  have hmag : ((gaussSum4 Q.q).norm : GaussianInt) = (Fintype.card (ι → ZMod 2) : GaussianInt) := by
    rw [Zsqrtd.norm_eq_mul_conj]; exact Q.gaussSum4_normSq
  have hcast : (gaussSum4 Q.q).norm = (Fintype.card (ι → ZMod 2) : ℤ) := by exact_mod_cast hmag
  rw [hcast, card_fun_zmod2]; norm_cast

/-- The unit `k` such that `gaussSum4 Q.q = i^k · (1+i)^dim`. -/
noncomputable def brownUnit : ZMod 4 :=
  (exists_zeta4_mul_of_norm_eq_pow (Fintype.card ι) (gaussSum4 Q.q) Q.norm_gaussSum4).choose

lemma gaussSum4_eq_brownUnit :
    gaussSum4 Q.q = zeta4 Q.brownUnit * (1 + I) ^ Fintype.card ι :=
  (exists_zeta4_mul_of_norm_eq_pow (Fintype.card ι) (gaussSum4 Q.q) Q.norm_gaussSum4).choose_spec

/-- **The Brown invariant `∈ ZMod 8`** of a nondegenerate `ZMod 4`-quadratic form: `brown Q = 2·k + dim`
where `gaussSum4 Q.q = i^k·(1+i)^dim` (the `ζ₈`-phase of the Gauss sum, `gaussSum4 = √|V|·ζ₈^{brown}`). -/
noncomputable def brown : ZMod 8 :=
  2 * (Q.brownUnit.val : ZMod 8) + (Fintype.card ι : ZMod 8)

/-- Orthogonal direct sum of two nondegenerate `ZMod 4`-quadratic forms (= disjoint union of the
characteristic surfaces). The Gauss sum multiplies, so the Brown invariant adds. -/
def orthSum {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (Q₁ : Z4Quadratic ι₁) (Q₂ : Z4Quadratic ι₂) : Z4Quadratic (ι₁ ⊕ ι₂) where
  q x := Q₁.q (fun i => x (Sum.inl i)) + Q₂.q (fun i => x (Sum.inr i))
  B x y := Q₁.B (fun i => x (Sum.inl i)) (fun i => y (Sum.inl i))
         + Q₂.B (fun i => x (Sum.inr i)) (fun i => y (Sum.inr i))
  refine' x y := by
    have e1 : (fun i => (x + y) (Sum.inl i)) = (fun i => x (Sum.inl i)) + fun i => y (Sum.inl i) := rfl
    have e2 : (fun i => (x + y) (Sum.inr i)) = (fun i => x (Sum.inr i)) + fun i => y (Sum.inr i) := rfl
    simp only [e1, e2, Q₁.refine', Q₂.refine', embed2_add]; ring
  B_add_left x y z := by
    have e1 : (fun i => (x + y) (Sum.inl i)) = (fun i => x (Sum.inl i)) + fun i => y (Sum.inl i) := rfl
    have e2 : (fun i => (x + y) (Sum.inr i)) = (fun i => x (Sum.inr i)) + fun i => y (Sum.inr i) := rfl
    simp only [e1, e2, Q₁.B_add_left, Q₂.B_add_left]; ring
  B_symm x y := by simp only [Q₁.B_symm (fun i => x (Sum.inl i)), Q₂.B_symm (fun i => x (Sum.inr i))]
  nondeg x hx := by
    have key : ∀ (w₁ : ι₁ → ZMod 2) (w₂ : ι₂ → ZMod 2),
        Q₁.B (fun i => x (Sum.inl i)) w₁ + Q₂.B (fun i => x (Sum.inr i)) w₂ = 0 := by
      intro w₁ w₂; have h := hx (Sum.elim w₁ w₂); simpa using h
    have hl : ∀ w₁, Q₁.B (fun i => x (Sum.inl i)) w₁ = 0 := fun w₁ => by
      have h := key w₁ 0
      rwa [show Q₂.B (fun i => x (Sum.inr i)) 0 = 0 from by rw [Q₂.B_symm]; exact Q₂.B_zero_left _,
        add_zero] at h
    have hr : ∀ w₂, Q₂.B (fun i => x (Sum.inr i)) w₂ = 0 := fun w₂ => by
      have h := key 0 w₂
      rwa [show Q₁.B (fun i => x (Sum.inl i)) 0 = 0 from by rw [Q₁.B_symm]; exact Q₁.B_zero_left _,
        zero_add] at h
    have hxl := Q₁.nondeg _ hl
    have hxr := Q₂.nondeg _ hr
    funext i; cases i with
    | inl i => exact congrFun hxl i
    | inr i => exact congrFun hxr i

/-- The Gauss sum is multiplicative over the orthogonal sum. -/
lemma gaussSum4_orthSum {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (Q₁ : Z4Quadratic ι₁) (Q₂ : Z4Quadratic ι₂) :
    gaussSum4 (orthSum Q₁ Q₂).q = gaussSum4 Q₁.q * gaussSum4 Q₂.q := by
  rw [← gaussSum4_orthogonal Q₁.q Q₂.q]
  exact Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow ι₁ ι₂ (ZMod 2)) _ _ (fun _ => rfl)

/-- The unit summand of the Brown phase adds over the orthogonal sum. -/
lemma brownUnit_orthSum {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (Q₁ : Z4Quadratic ι₁) (Q₂ : Z4Quadratic ι₂) :
    (orthSum Q₁ Q₂).brownUnit = Q₁.brownUnit + Q₂.brownUnit := by
  have h := (orthSum Q₁ Q₂).gaussSum4_eq_brownUnit
  rw [gaussSum4_orthSum, Q₁.gaussSum4_eq_brownUnit, Q₂.gaussSum4_eq_brownUnit, Fintype.card_sum] at h
  refine zeta4_mul_pow_right_inj (N := Fintype.card ι₁ + Fintype.card ι₂) ?_
  rw [← h, zeta4_add, pow_add]; ring

/-- `2·val` is additive `ZMod 4 → ZMod 8` (the wraparound is a multiple of `8`). -/
lemma two_mul_val_add (a b : ZMod 4) :
    (2 * ((a + b).val : ZMod 8)) = 2 * (a.val : ZMod 8) + 2 * (b.val : ZMod 8) := by
  revert a b; decide

/-- **Additivity of the Brown invariant** under orthogonal sum (the property the lower bound's
bordism-invariant `β` needs). -/
lemma brown_orthSum {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (Q₁ : Z4Quadratic ι₁) (Q₂ : Z4Quadratic ι₂) :
    (orthSum Q₁ Q₂).brown = Q₁.brown + Q₂.brown := by
  simp only [brown, brownUnit_orthSum, Fintype.card_sum, Nat.cast_add, two_mul_val_add]
  ring

/-- The generator's per-component refinement: `qGen(a+b) = qGen a + qGen b + 2·(a·b)`. -/
lemma qGen_refine (a b : ZMod 2) : qGen (a + b) = qGen a + qGen b + embed2 (a * b) := by
  revert a b; decide

/-- `embed2` extends to finite sums. -/
lemma embed2_sum {κ : Type*} (s : Finset κ) (f : κ → ZMod 2) :
    embed2 (∑ i ∈ s, f i) = ∑ i ∈ s, embed2 (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [embed2]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, embed2_add, ih]

/-- The genus-`g` standard form as a nondegenerate `Z4Quadratic` (diagonal dot-product polar form). -/
def stdQuadratic (g : ℕ) : Z4Quadratic (Fin g) where
  q := stdForm g
  B x y := ∑ i, x i * y i
  refine' x y := by
    show stdForm g (x + y) = stdForm g x + stdForm g y + embed2 (∑ i, x i * y i)
    simp only [stdForm, Pi.add_apply]
    rw [embed2_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => qGen_refine (x i) (y i))
  B_add_left x y z := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  B_symm x y := by simp only [mul_comm]
  nondeg x hx := by
    funext i
    have h := hx (Pi.single i 1)
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)] at h
    simpa using h

/-- `brownUnit` of the standard form is `0`: its Gauss sum `(1+i)^g` has unit `1 = i^0`. -/
lemma brownUnit_stdQuadratic (g : ℕ) : (stdQuadratic g).brownUnit = 0 := by
  have h := (stdQuadratic g).gaussSum4_eq_brownUnit
  rw [show (stdQuadratic g).q = stdForm g from rfl, gaussSum4_stdForm, Fintype.card_fin] at h
  refine zeta4_mul_pow_right_inj (N := g) ?_
  rw [← h, zeta4_zero, one_mul]

/-- **`brown(stdForm g) = g`** — the general Brown invariant reproduces the genus, hence `brownStd`.
For `g = 1` this is `brown(RP²-form) = 1`, the order-8 generator value of `Ω₂^{Pin⁻}`. -/
lemma brown_stdQuadratic (g : ℕ) : (stdQuadratic g).brown = (g : ZMod 8) := by
  simp only [brown, brownUnit_stdQuadratic, ZMod.val_zero, Nat.cast_zero, mul_zero, zero_add,
    Fintype.card_fin]

/-! ## `Ω₂^{Pin⁻} ≅ ℤ₈` realized by the DERIVED Brown invariant (de-risk capstone)

The Brown invariant `brown` — derived kernel-pure from the genuine ℤ₄-quadratic enhancement of a Pin⁻
surface (W1–W2), **not posited** — realizes the full `ZMod 8` structure of Pin⁻ surface bordism: it is
additive (`brown_orthSum`), **surjective** (every class hit by a standard surface `stdQuadratic g`), and
the generator `stdQuadratic 1` (`= RP²` with its Pin⁻ structure) has additive order exactly **8**. Modulo
the cited completeness of the Arf–Brown–Kervaire invariant for Pin⁻ surface bordism (Kirby–Taylor 1990 /
ABP: `Ω₂^{Pin⁻} ≅ ℤ₈`, generator `RP²`), this is the surface bordism group with the invariant **derived** —
the Level-4 improvement over a posited carrier (contrast `PinPlusManifold4.signature`), at the `ZMod 8`
surface level that feeds the `ZMod 16` Pin⁺ 4-manifold bound. -/

/-- The derived Brown invariant is **surjective** onto `ZMod 8` — every Pin⁻ surface bordism class is
realized by a genuine standard surface. -/
theorem brown_stdQuadratic_surjective : Function.Surjective (fun g : ℕ => (stdQuadratic g).brown) :=
  fun k => ⟨k.val, by show (stdQuadratic k.val).brown = k
                      rw [brown_stdQuadratic, ZMod.natCast_val, ZMod.cast_id]⟩

/-- The standard surfaces realize an **additive** map onto `ZMod 8` (the bordism group structure). -/
theorem brown_stdQuadratic_add (g₁ g₂ : ℕ) :
    (stdQuadratic (g₁ + g₂)).brown = (stdQuadratic g₁).brown + (stdQuadratic g₂).brown := by
  simp only [brown_stdQuadratic, Nat.cast_add]

/-- **The generator `[RP²] = stdQuadratic 1` has additive order exactly 8** — the derived Brown invariant
exhibits the full order-8 cyclic structure of `Ω₂^{Pin⁻} ≅ ℤ₈`. -/
theorem brown_generator_order_eight :
    (8 : ℕ) • (stdQuadratic 1).brown = 0 ∧
      ∀ k : ℕ, 0 < k → k < 8 → k • (stdQuadratic 1).brown ≠ 0 := by
  rw [brown_stdQuadratic]
  exact ⟨by decide, fun k hk0 hk8 => by interval_cases k <;> decide⟩

end Z4Quadratic

end SKEFTHawking.Brown
