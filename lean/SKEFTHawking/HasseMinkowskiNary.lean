import Mathlib
import SKEFTHawking.PadicSquare
import SKEFTHawking.HasseMinkowskiGlobal

/-!
# Hasse–Minkowski rank reduction (`n ≥ 5`) and the general `n`-ary diagonal local–global principle

This module builds the **general-rank** diagonal Hasse–Minkowski theorem on top of the completed
base cases:

* `n = 2` : `PadicSquare.binary_solvable_of_local`
* `n = 3` : `PadicSquare.diag_ternary_solvable_of_local`
* `n = 4` : `HasseMinkowskiGlobal.diag_quaternary_zero_of_local` (the genuinely hard Serre Thm 4 summit)

The remaining content is the classical **Meyer reduction** (`n ≥ 5 → n − 1`, Serre, *Course in
Arithmetic*, IV §3.2, proof of Theorem 8): split off a binary `c₀x₀² + c₁x₁²`, find a global value `a`
represented by it that matches the local square classes of the local zeros at the finite "bad" set, and
descend to the rank-`(n−1)` form `⟨a, c₂, …, c_{n−1}⟩`. The local inputs for the descent are free for
rank `≥ 5`: at good odd primes the residual unit form is isotropic hence universal
(`PadicSquare.exists_diag_nary_zero_odd_padic` + `represents_of_isotropic_diag` below), and over ℝ the
form is indefinite.

## Anti-circularity

Routes through quadratic-form / Hilbert-symbol arithmetic only (reciprocity, Dirichlet, the product
formula, and the completed `n ≤ 4` bases). It does NOT use ABP, the Adams spectral sequence, or Rokhlin's
theorem — `16 ∣ σ` is the eventual conclusion downstream.
-/

namespace SKEFTHawking

open Finset

/-- **Isotropic diagonal form is universal.** Over a field of characteristic `≠ 2`, a diagonal form
`∑ wᵢ xᵢ²` with every coefficient nonzero that has a *nontrivial* zero represents *every* value `t`.
(Concretely: with `∑ wᵢ vᵢ² = 0`, `v ≠ 0`, pick `j` with `vⱼ ≠ 0`; the vector `x = s • v + e_j` has
`q(x) = wⱼ(2 vⱼ s + 1)`, which equals `t` for `s = (t − wⱼ)/(2 wⱼ vⱼ)`.) This is the "good place" engine
of the Meyer rank reduction: at primes where the residual unit form is isotropic it represents any
target value. -/
theorem represents_of_isotropic_diag {K : Type*} [Field K] (hchar : (2 : K) ≠ 0)
    {n : ℕ} (w : Fin n → K) (hw : ∀ i, w i ≠ 0)
    (hiso : ∃ v : Fin n → K, v ≠ 0 ∧ ∑ i, w i * v i ^ 2 = 0) :
    ∀ t : K, ∃ x : Fin n → K, ∑ i, w i * x i ^ 2 = t := by
  obtain ⟨v, hv0, hvz⟩ := hiso
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
  simp only [Pi.zero_apply] at hj
  intro t
  set s : K := (t - w j) / (2 * w j * v j) with hs
  have hwj := hw j
  refine ⟨fun i => v i * s + (if i = j then 1 else 0), ?_⟩
  have key : ∀ i, w i * (v i * s + (if i = j then (1 : K) else 0)) ^ 2
      = w i * v i ^ 2 * s ^ 2 + (if i = j then w j * (2 * v j * s + 1) else 0) := by
    intro i
    by_cases h : i = j
    · simp only [if_pos h]; subst h; ring
    · simp only [if_neg h]; ring
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ j (fun _ => w j * (2 * v j * s + 1))]
  simp only [Finset.mem_univ, if_true]
  have h1 : ∑ i, w i * v i ^ 2 * s ^ 2 = 0 := by rw [← Finset.sum_mul, hvz, zero_mul]
  rw [h1, zero_add, hs]
  field_simp
  ring

/-- **Good odd place: a rank `≥ 3` unit diagonal form over `ℚ_[p]` is universal.** For an odd prime `p`,
`n ≥ 3`, and norm-1 coefficients, `∑ wᵢ xᵢ²` represents every `t ∈ ℚ_[p]`. (The form is isotropic by
`PadicSquare.exists_diag_nary_zero_odd_padic_unit`; `represents_of_isotropic_diag` upgrades isotropy to
universality — `ℚ_[p]` has characteristic `0`, so `(2 : ℚ_[p]) ≠ 0`.) This is the residual-form input at the
good primes of the Meyer rank reduction: outside the finitely many bad primes the rank-`(n−2)` residual unit
form represents the value `−a` chosen for the descent. -/
theorem represents_of_units_odd_padic {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ} (hn : 3 ≤ n)
    (w : Fin n → ℚ_[p]) (hw : ∀ i, ‖w i‖ = 1) (t : ℚ_[p]) :
    ∃ x : Fin n → ℚ_[p], ∑ i, w i * x i ^ 2 = t := by
  refine represents_of_isotropic_diag two_ne_zero w (fun i => ?_) ?_ t
  · exact norm_ne_zero_iff.mp (by rw [hw i]; norm_num)
  · exact exists_diag_nary_zero_odd_padic_unit hp hn w hw

/-- **Rank-reduction assembly (pure algebra).** If the leading binary `⟨c₀, c₁⟩` represents a nonzero value
`a`, and the descended rank-`(m+1)` form `⟨a, R⟩` (over ℚ) is isotropic, then the rank-`(m+2)` form
`⟨c₀, c₁, R⟩` is isotropic. (Substitute `a = c₀ u₀² + c₁ u₁²` into the descended zero `a y₀² + R(y') = 0`
and split the `a`-term: the witness is `x = (u₀ y₀, u₁ y₀, y')`. Nonzero: if `y₀ = 0` the residual tail
`y'` survives; if `y₀ ≠ 0` then `a ≠ 0 ⟹ u₀ ≠ 0 ∨ u₁ ≠ 0` makes a leading coordinate nonzero.) This is the
descent half of the Meyer reduction, isolating the algebra from the global-value construction. -/
theorem reduction_assembly {m : ℕ} {c0 c1 a : ℚ} (ha : a ≠ 0) {R : Fin m → ℚ}
    (hB : ∃ u0 u1 : ℚ, c0 * u0 ^ 2 + c1 * u1 ^ 2 = a)
    (hg : ∃ y : Fin (m + 1) → ℚ, y ≠ 0 ∧ ∑ i, (Fin.cons a R : Fin (m + 1) → ℚ) i * y i ^ 2 = 0) :
    ∃ x : Fin (m + 2) → ℚ, x ≠ 0 ∧
      ∑ i, (Fin.cons c0 (Fin.cons c1 R) : Fin (m + 2) → ℚ) i * x i ^ 2 = 0 := by
  obtain ⟨u0, u1, hBeq⟩ := hB
  obtain ⟨y, hy0, hgeq⟩ := hg
  rw [Fin.sum_univ_succ] at hgeq
  simp only [Fin.cons_zero, Fin.cons_succ] at hgeq
  refine ⟨Fin.cons (u0 * y 0) (Fin.cons (u1 * y 0) (fun i => y i.succ)), ?_, ?_⟩
  · intro hx
    by_cases hy00 : y 0 = 0
    · apply hy0
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hy00
      · have := congrFun hx j.succ.succ
        simpa [hy00] using this
    · have hu : u0 ≠ 0 ∨ u1 ≠ 0 := by
        by_contra h
        simp only [not_or, not_not] at h
        exact ha (by rw [← hBeq, h.1, h.2]; ring)
      rcases hu with hu | hu
      · exact mul_ne_zero hu hy00 (by simpa using congrFun hx 0)
      · exact mul_ne_zero hu hy00 (by simpa using congrFun hx 1)
  · rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hR : ∑ i, R i * y i.succ ^ 2 = -(a * y 0 ^ 2) := by linarith [hgeq]
    rw [hR]
    have hsub : c0 * (u0 * y 0) ^ 2 + c1 * (u1 * y 0) ^ 2 = a * y 0 ^ 2 := by rw [← hBeq]; ring
    linarith [hsub]

/-! ### Rational ⇄ integer coefficient scaling -/

/-- The integer `c.num · c.den` cast into a characteristic-zero field equals `c · (c.den)²`. This is the
identity behind clearing the denominator of a single diagonal coefficient by the variable substitution
`x ↦ c.den · x` (coefficient `c` becomes the integer `c.num · c.den`). -/
theorem cast_num_mul_den {K : Type*} [Field K] [CharZero K] (c : ℚ) :
    ((c.num * (c.den : ℤ) : ℤ) : K) = (c : K) * ((c.den : ℕ) : K) ^ 2 := by
  have hd : ((c.den : ℕ) : K) ≠ 0 := by exact_mod_cast c.den_nz
  push_cast; rw [Rat.cast_def]; field_simp

/-- **Variable scaling preserves isotropy.** Over a field, scaling each variable by a nonzero `dᵢ` carries a
nontrivial zero of `∑ (cᵢ dᵢ²) xᵢ²` to one of `∑ cᵢ xᵢ²` (witness `xᵢ ↦ dᵢ xᵢ`). Used both ways (with `d` or
`1/d`) to convert between rational and integer diagonal coefficients and to clear denominators. -/
theorem diag_scale_var {K : Type*} [Field K] {n : ℕ} (c d : Fin n → K) (hd : ∀ i, d i ≠ 0)
    (hiso : ∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, (c i * d i ^ 2) * x i ^ 2 = 0) :
    ∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, c i * x i ^ 2 = 0 := by
  obtain ⟨x, hx0, hxe⟩ := hiso
  refine ⟨fun i => d i * x i, ?_, ?_⟩
  · intro h
    apply hx0
    funext i
    have := congrFun h i
    simp only [Pi.zero_apply] at this ⊢
    exact (mul_eq_zero.mp this).resolve_left (hd i)
  · rw [← hxe]; apply Finset.sum_congr rfl; intro i _; ring

/-- Isotropy is invariant under multiplying every coefficient by a nonzero square `dᵢ²` (both directions of
`diag_scale_var`). -/
theorem diag_iso_mul_sq {K : Type*} [Field K] {n : ℕ} (c d : Fin n → K) (hd : ∀ i, d i ≠ 0) :
    (∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, c i * x i ^ 2 = 0) ↔
    (∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, (c i * d i ^ 2) * x i ^ 2 = 0) := by
  constructor
  · intro h
    refine diag_scale_var (fun i => c i * d i ^ 2) (fun i => (d i)⁻¹) (fun i => inv_ne_zero (hd i)) ?_
    obtain ⟨x, hx0, hxe⟩ := h
    refine ⟨x, hx0, ?_⟩
    rw [← hxe]; refine Finset.sum_congr rfl (fun i _ => ?_)
    have hdi := hd i; field_simp
  · exact diag_scale_var c d hd

/-- **Rational ⇄ integer coefficients (per place).** Over a characteristic-zero field, the diagonal form with
rational coefficients `c` is isotropic iff the form with integer coefficients `aᵢ = (cᵢ).num · (cᵢ).den` is
(clear each denominator by `xᵢ ↦ (cᵢ).den · xᵢ`). This transports the rational local/global hypotheses to the
integer `n = 4` summit `HasseMinkowskiGlobal.diag_quaternary_zero_of_local`. -/
theorem diag_iso_rat_int {K : Type*} [Field K] [CharZero K] {n : ℕ} (c : Fin n → ℚ) :
    (∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, (c i : K) * x i ^ 2 = 0) ↔
    (∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, (((c i).num * ((c i).den : ℤ) : ℤ) : K) * x i ^ 2 = 0) := by
  rw [diag_iso_mul_sq (fun i => ((c i : ℚ) : K)) (fun i => ((c i).den : K))
      (fun i => by show ((c i).den : K) ≠ 0; exact_mod_cast (c i).den_nz)]
  have hcoef : ∀ i, ((c i : ℚ) : K) * ((c i).den : K) ^ 2 = (((c i).num * ((c i).den : ℤ) : ℤ) : K) :=
    fun i => (cast_num_mul_den (c i)).symm
  simp_rw [hcoef]

/-- **Isotropy is invariant under reindexing the coordinates.** For an equivalence `e : Fin n ≃ Fin n`,
`∑ cᵢ xᵢ²` is isotropic iff `∑ c_{e i} xᵢ²` is (witness `x ↦ x ∘ e`). Lets the rank reduction move any chosen
pair of coordinates (e.g. two of the majority real sign, so the residual stays indefinite over ℝ) to the
front. -/
theorem diag_reindex_iso {K : Type*} [Field K] {n : ℕ} (e : Fin n ≃ Fin n) (c : Fin n → K) :
    (∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, c i * x i ^ 2 = 0) ↔
    (∃ y : Fin n → K, y ≠ 0 ∧ ∑ i, c (e i) * y i ^ 2 = 0) := by
  constructor
  · rintro ⟨x, hx0, hxe⟩
    refine ⟨fun i => x (e i), ?_, ?_⟩
    · intro h; apply hx0; funext k; have := congrFun h (e.symm k); simpa using this
    · rw [← Equiv.sum_comp e (fun i => c i * x i ^ 2)] at hxe; simpa using hxe
  · rintro ⟨y, hy0, hye⟩
    refine ⟨fun k => y (e.symm k), ?_, ?_⟩
    · intro h; apply hy0; funext i; have := congrFun h (e i); simpa using this
    · rw [← Equiv.sum_comp e (fun k => c k * y (e.symm k) ^ 2)]
      simp only [Equiv.symm_apply_apply]; exact hye

/-- **Move two distinct indices to the front.** For distinct `i j : Fin (m+2)` there is a coordinate
permutation sending `0 ↦ i` and `1 ↦ j` (composition of two transpositions). Combined with
`diag_reindex_iso`, this peels any chosen coordinate pair `{i, j}` into the leading binary of the rank
reduction. -/
theorem exists_equiv_zero_one {m : ℕ} (i j : Fin (m + 2)) (hij : i ≠ j) :
    ∃ e : Fin (m + 2) ≃ Fin (m + 2), e 0 = i ∧ e 1 = j := by
  set s := Equiv.swap (0 : Fin (m + 2)) i with hs
  set k := s.symm j with hk
  have hk0 : k ≠ 0 := by
    rw [hk]; intro h
    apply hij
    have h1 : s (s.symm j) = j := s.apply_symm_apply j
    rw [h, hs, Equiv.swap_apply_left] at h1
    exact h1
  set t := Equiv.swap (1 : Fin (m + 2)) k with ht
  refine ⟨t.trans s, ?_, ?_⟩
  · show s (t 0) = i
    have ht0 : t 0 = 0 := by rw [ht, Equiv.swap_apply_of_ne_of_ne (by norm_num) (Ne.symm hk0)]
    rw [ht0, hs, Equiv.swap_apply_left]
  · show s (t 1) = j
    have ht1 : t 1 = k := by rw [ht]; exact Equiv.swap_apply_left 1 k
    rw [ht1, hk]; exact s.apply_symm_apply j

/-- **Indefinite real diagonal form is isotropic.** A coefficient `c i > 0` and another `c j < 0`
(`i ≠ j`) give a nontrivial real zero: `xᵢ = √(−cⱼ)`, `xⱼ = √(cᵢ)`, rest `0`, since
`cᵢ(−cⱼ) + cⱼ cᵢ = 0`. The `∞`-place input of the rank reduction: after peeling two coordinates of the
majority real sign, the residual retains both signs, so the descended form is isotropic over ℝ for free. -/
theorem diag_real_isotropic_of_signs {n : ℕ} (c : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j)
    (hi : 0 < c i) (hj : c j < 0) : ∃ x : Fin n → ℝ, x ≠ 0 ∧ ∑ k, c k * x k ^ 2 = 0 := by
  set x : Fin n → ℝ := fun k => if k = i then Real.sqrt (-c j) else if k = j then Real.sqrt (c i) else 0
    with hx
  have exi : x i = Real.sqrt (-c j) := by rw [hx]; simp
  have exj : x j = Real.sqrt (c i) := by rw [hx]; simp [Ne.symm hij]
  have exo : ∀ k, k ≠ i → k ≠ j → x k = 0 := by intro k h1 h2; rw [hx]; simp [h1, h2]
  refine ⟨x, ?_, ?_⟩
  · intro h
    have h2 : x i = 0 := by rw [h]; rfl
    rw [exi, Real.sqrt_eq_zero (by linarith)] at h2
    linarith
  · rw [← Finset.sum_subset (Finset.subset_univ {i, j})]
    · rw [Finset.sum_pair hij, exi, exj,
        Real.sq_sqrt (by linarith : (0:ℝ) ≤ -c j), Real.sq_sqrt (le_of_lt hi)]
      ring
    · intro k _ hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      rw [exo k hk.1 hk.2]; ring

/-! ### `n ≤ 4` base cases in uniform `∑`-shape -/

/-- A `Fin 2 → K` vector is nonzero iff not both entries vanish. -/
theorem ne_zero_iff_two {K : Type*} [Zero K] (x : Fin 2 → K) :
    x ≠ 0 ↔ ¬(x 0 = 0 ∧ x 1 = 0) := by
  rw [not_iff_not]; constructor
  · intro h; subst h; simp
  · intro ⟨h0, h1⟩; funext i; fin_cases i <;> simpa

/-- A `Fin 3 → K` vector is nonzero iff not all three entries vanish. -/
theorem ne_zero_iff_three {K : Type*} [Zero K] (x : Fin 3 → K) :
    x ≠ 0 ↔ ¬(x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0) := by
  rw [not_iff_not]; constructor
  · intro h; subst h; simp
  · intro ⟨h0, h1, h2⟩; funext i; fin_cases i <;> simpa

/-- A `Fin 4 → K` vector is nonzero iff not all four entries vanish. -/
theorem ne_zero_iff_four {K : Type*} [Zero K] (x : Fin 4 → K) :
    x ≠ 0 ↔ ¬(x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0) := by
  rw [not_iff_not]; constructor
  · intro h; subst h; simp
  · intro ⟨h0, h1, h2, h3⟩; funext i; fin_cases i <;> simpa

/-- **`n = 4` summit in `Fin 4 / ∑`-shape (integer coefficients).** Repackages
`HasseMinkowskiGlobal.diag_quaternary_zero_of_local` with the uniform `∑ i, (a i) xᵢ²` shape used by the
rank-induction spine (bridging via `Fin.sum_univ_four` and `ne_zero_iff_four`). -/
theorem diag_quaternary_zero_sum_int (a : Fin 4 → ℤ) (h0 : a 0 ≠ 0) (h1 : a 1 ≠ 0)
    (h2 : a 2 ≠ 0) (h3 : a 3 ≠ 0)
    (hR : ∃ x : Fin 4 → ℝ, x ≠ 0 ∧ ∑ i, (a i : ℝ) * x i ^ 2 = 0)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin 4 → ℚ_[p], x ≠ 0 ∧ ∑ i, (a i : ℚ_[p]) * x i ^ 2 = 0) :
    ∃ x : Fin 4 → ℚ, x ≠ 0 ∧ ∑ i, (a i : ℚ) * x i ^ 2 = 0 := by
  have hRe : ∃ x y z w : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a 0:ℝ)*x^2 + (a 1:ℝ)*y^2 + (a 2:ℝ)*z^2 + (a 3:ℝ)*w^2 = 0 := by
    obtain ⟨x, hx0, hxe⟩ := hR
    exact ⟨x 0, x 1, x 2, x 3, (ne_zero_iff_four x).mp hx0,
      by rw [Fin.sum_univ_four] at hxe; linarith⟩
  have hloce : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z w : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      (a 0:ℚ_[p])*x^2 + (a 1:ℚ_[p])*y^2 + (a 2:ℚ_[p])*z^2 + (a 3:ℚ_[p])*w^2 = 0 := by
    intro p _
    obtain ⟨x, hx0, hxe⟩ := hloc p
    exact ⟨x 0, x 1, x 2, x 3, (ne_zero_iff_four x).mp hx0,
      by rw [Fin.sum_univ_four] at hxe; linear_combination hxe⟩
  obtain ⟨x, y, z, w, hnz, he⟩ := diag_quaternary_zero_of_local h0 h1 h2 h3 hRe hloce
  refine ⟨![x, y, z, w], (ne_zero_iff_four _).mpr (by simpa using hnz), ?_⟩
  rw [Fin.sum_univ_four]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  linear_combination he

/-- **`n = 2` base in `∑`-shape (rational).** From `PadicSquare.binary_solvable_of_local`. -/
theorem diag_binary_zero_sum (c : Fin 2 → ℚ) (h0 : c 0 ≠ 0)
    (hR : ∃ x : Fin 2 → ℝ, x ≠ 0 ∧ ∑ i, (c i : ℝ) * x i ^ 2 = 0)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin 2 → ℚ_[p], x ≠ 0 ∧ ∑ i, (c i : ℚ_[p]) * x i ^ 2 = 0) :
    ∃ x : Fin 2 → ℚ, x ≠ 0 ∧ ∑ i, c i * x i ^ 2 = 0 := by
  have hRe : ∃ x y : ℝ, ¬(x = 0 ∧ y = 0) ∧ (c 0:ℝ)*x^2 + (c 1:ℝ)*y^2 = 0 := by
    obtain ⟨x, hx0, hxe⟩ := hR
    exact ⟨x 0, x 1, (ne_zero_iff_two x).mp hx0, by rw [Fin.sum_univ_two] at hxe; linarith⟩
  have hloce : ∀ (p : ℕ) [Fact p.Prime], ∃ x y : ℚ_[p], ¬(x = 0 ∧ y = 0) ∧
      (c 0:ℚ_[p])*x^2 + (c 1:ℚ_[p])*y^2 = 0 := by
    intro p _; obtain ⟨x, hx0, hxe⟩ := hloc p
    exact ⟨x 0, x 1, (ne_zero_iff_two x).mp hx0, by rw [Fin.sum_univ_two] at hxe; linear_combination hxe⟩
  obtain ⟨x, y, hnz, he⟩ := binary_solvable_of_local h0 hRe hloce
  refine ⟨![x, y], (ne_zero_iff_two _).mpr (by simpa using hnz), ?_⟩
  rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination he

/-- **`n = 3` base in `∑`-shape (rational).** From `PadicSquare.diag_ternary_solvable_of_local`. -/
theorem diag_ternary_zero_sum (c : Fin 3 → ℚ) (h0 : c 0 ≠ 0) (h1 : c 1 ≠ 0) (h2 : c 2 ≠ 0)
    (hR : ∃ x : Fin 3 → ℝ, x ≠ 0 ∧ ∑ i, (c i : ℝ) * x i ^ 2 = 0)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin 3 → ℚ_[p], x ≠ 0 ∧ ∑ i, (c i : ℚ_[p]) * x i ^ 2 = 0) :
    ∃ x : Fin 3 → ℚ, x ≠ 0 ∧ ∑ i, c i * x i ^ 2 = 0 := by
  have hRe : ∃ x y z : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      (c 0:ℝ)*x^2 + (c 1:ℝ)*y^2 + (c 2:ℝ)*z^2 = 0 := by
    obtain ⟨x, hx0, hxe⟩ := hR
    exact ⟨x 0, x 1, x 2, (ne_zero_iff_three x).mp hx0, by rw [Fin.sum_univ_three] at hxe; linarith⟩
  have hloce : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      (c 0:ℚ_[p])*x^2 + (c 1:ℚ_[p])*y^2 + (c 2:ℚ_[p])*z^2 = 0 := by
    intro p _; obtain ⟨x, hx0, hxe⟩ := hloc p
    exact ⟨x 0, x 1, x 2, (ne_zero_iff_three x).mp hx0,
      by rw [Fin.sum_univ_three] at hxe; linear_combination hxe⟩
  obtain ⟨x, y, z, hnz, he⟩ := diag_ternary_solvable_of_local h0 h1 h2 hRe hloce
  refine ⟨![x, y, z], (ne_zero_iff_three _).mpr (by simpa using hnz), ?_⟩
  rw [Fin.sum_univ_three]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination he

/-- **Rational `n = 4` diagonal Hasse–Minkowski.** ℚ-coefficient form of the rank-4 summit, obtained from
`diag_quaternary_zero_sum_int` by clearing denominators with `diag_iso_rat_int` over each of ℝ, ℚ_p, ℚ. The
`n = 4` base of the rank-induction spine. -/
theorem diag_quaternary_zero_of_local_rat (c : Fin 4 → ℚ) (hc : ∀ i, c i ≠ 0)
    (hR : ∃ x : Fin 4 → ℝ, x ≠ 0 ∧ ∑ i, (c i : ℝ) * x i ^ 2 = 0)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin 4 → ℚ_[p], x ≠ 0 ∧ ∑ i, (c i : ℚ_[p]) * x i ^ 2 = 0) :
    ∃ x : Fin 4 → ℚ, x ≠ 0 ∧ ∑ i, c i * x i ^ 2 = 0 := by
  have ha : ∀ i, (c i).num * ((c i).den : ℤ) ≠ 0 := fun i =>
    mul_ne_zero (Rat.num_ne_zero.mpr (hc i)) (by exact_mod_cast (c i).den_nz)
  have key : ∃ x : Fin 4 → ℚ, x ≠ 0 ∧ ∑ i, (((c i).num * ((c i).den : ℤ) : ℤ) : ℚ) * x i ^ 2 = 0 :=
    diag_quaternary_zero_sum_int _ (ha 0) (ha 1) (ha 2) (ha 3)
      ((diag_iso_rat_int (K := ℝ) c).mp hR)
      (fun p _ => (diag_iso_rat_int (K := ℚ_[p]) c).mp (hloc p))
  exact (diag_iso_rat_int (K := ℚ) c).mpr key

end SKEFTHawking
