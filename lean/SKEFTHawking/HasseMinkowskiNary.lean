import Mathlib
import SKEFTHawking.PadicSquare
import SKEFTHawking.HasseMinkowskiGlobal
import SKEFTHawking.HasseMinkowskiLocal

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

/-- **Majority-sign peel pigeonhole.** If a rank-`≥ 5` real diagonal form (all coefficients nonzero) is
indefinite (`∃` positive, `∃` negative coefficient), there is a coordinate pair `{i, j}` whose removal
leaves the residual still indefinite (a positive coordinate `k` and a negative coordinate `l`, both
distinct from `i, j`). (Pigeonhole: the majority sign has `≥ 3` coordinates; peel two of them.) Peeling such
a pair keeps the descended form isotropic over ℝ for free (`diag_real_isotropic_of_signs`). -/
theorem exists_peel_pair {n : ℕ} (hn : 5 ≤ n) (c : Fin n → ℝ) (hc : ∀ k, c k ≠ 0)
    (hpos : ∃ p, 0 < c p) (hneg : ∃ q, c q < 0) :
    ∃ i j : Fin n, i ≠ j ∧ (∃ k, k ≠ i ∧ k ≠ j ∧ 0 < c k) ∧ (∃ l, l ≠ i ∧ l ≠ j ∧ c l < 0) := by
  classical
  set P := univ.filter (fun k => 0 < c k) with hP
  set N := univ.filter (fun k => c k < 0) with hN
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]; intro k hkP hkN
    rw [hP, Finset.mem_filter] at hkP; rw [hN, Finset.mem_filter] at hkN
    linarith [hkP.2, hkN.2]
  have hcover : P ∪ N = univ := by
    rw [hP, hN, ← Finset.filter_or, Finset.filter_true_of_mem]
    intro k _; rcases lt_or_gt_of_ne (hc k) with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hcard : P.card + N.card = n := by
    rw [← Finset.card_union_of_disjoint hdisj, hcover, Finset.card_univ, Fintype.card_fin]
  rcases (by omega : 3 ≤ P.card ∨ 3 ≤ N.card) with hPc | hNc
  · obtain ⟨p1, p2, p3, h1, h2, h3, d12, d13, d23⟩ :=
      Finset.two_lt_card_iff.mp (show 2 < P.card by omega)
    rw [hP, Finset.mem_filter] at h1 h2 h3
    obtain ⟨q, hq⟩ := hneg
    exact ⟨p1, p2, d12, ⟨p3, d13.symm, d23.symm, h3.2⟩,
      ⟨q, fun h => by rw [h] at hq; linarith [h1.2], fun h => by rw [h] at hq; linarith [h2.2], hq⟩⟩
  · obtain ⟨p1, p2, p3, h1, h2, h3, d12, d13, d23⟩ :=
      Finset.two_lt_card_iff.mp (show 2 < N.card by omega)
    rw [hN, Finset.mem_filter] at h1 h2 h3
    obtain ⟨q, hq⟩ := hpos
    exact ⟨p1, p2, d12,
      ⟨q, fun h => by rw [h] at hq; linarith [h1.2], fun h => by rw [h] at hq; linarith [h2.2], hq⟩,
      ⟨p3, d13.symm, d23.symm, h3.2⟩⟩

/-- **Scaling a `p`-adic number into `ℤ_[p]` by a power of `p`.** For any `u : ℚ_[p]` there is `M` with
`‖p^M · u‖ ≤ 1` (so `p^M · u` lies in the unit ball `ℤ_[p]`). Multiplying the local representation coordinates
`(u₀, u₁)` of a common value by a common `p^M` clears their denominators (`p^{2M}` is a square, so the
square class of the value is preserved) so they can be reduced mod `p^N` and fed to integer CRT. -/
theorem exists_nat_pow_mul_norm_le_one {p : ℕ} [Fact p.Prime] (u : ℚ_[p]) :
    ∃ M : ℕ, ‖(p : ℚ_[p]) ^ M * u‖ ≤ 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rcases eq_or_ne u 0 with rfl | hu
  · exact ⟨0, by simp⟩
  · obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt ‖u‖ hp1
    refine ⟨M, ?_⟩
    have hpM : (0 : ℝ) < (p : ℝ) ^ M := by positivity
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ hpM, mul_one]
    exact hM.le

/-- **Integral `ℤ_[p]` coordinates for a `p`-adic binary representation.** If `c₀ u₀² + c₁ u₁² = w` over
`ℚ_[p]`, scaling both coordinates by a common `p^M` puts them in `ℤ_[p]` while multiplying the value by the
square `(p^M)²`. This is the bridge from a local representation to integer CRT: the integral coordinates
reduce mod `p^N` to give the residue targets, and the value stays in `w`'s square class. -/
theorem exists_padicInt_binary_rep {p : ℕ} [Fact p.Prime] {c0 c1 w : ℚ_[p]}
    (h : ∃ u0 u1 : ℚ_[p], c0 * u0 ^ 2 + c1 * u1 ^ 2 = w) :
    ∃ (M : ℕ) (v0 v1 : ℤ_[p]),
      c0 * (v0 : ℚ_[p]) ^ 2 + c1 * (v1 : ℚ_[p]) ^ 2 = w * ((p : ℚ_[p]) ^ M) ^ 2 := by
  obtain ⟨u0, u1, hu⟩ := h
  obtain ⟨M0, hM0⟩ := exists_nat_pow_mul_norm_le_one (p := p) u0
  obtain ⟨M1, hM1⟩ := exists_nat_pow_mul_norm_le_one (p := p) u1
  set M := max M0 M1 with hM
  have hp1 : ‖(p : ℚ_[p])‖ ≤ 1 := by
    rw [Padic.norm_p]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_le)
  have hpow : ∀ k : ℕ, ‖(p : ℚ_[p]) ^ k‖ ≤ 1 := fun k => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1
  have hv0 : ‖(p : ℚ_[p]) ^ M * u0‖ ≤ 1 := by
    rw [show (p : ℚ_[p]) ^ M * u0 = (p:ℚ_[p])^(M - M0) * ((p:ℚ_[p])^M0 * u0) by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_max_left _ _)], norm_mul]
    exact mul_le_one₀ (hpow _) (norm_nonneg _) hM0
  have hv1 : ‖(p : ℚ_[p]) ^ M * u1‖ ≤ 1 := by
    rw [show (p : ℚ_[p]) ^ M * u1 = (p:ℚ_[p])^(M - M1) * ((p:ℚ_[p])^M1 * u1) by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_max_right _ _)], norm_mul]
    exact mul_le_one₀ (hpow _) (norm_nonneg _) hM1
  refine ⟨M, ⟨_, hv0⟩, ⟨_, hv1⟩, ?_⟩
  show c0 * ((p:ℚ_[p])^M * u0) ^ 2 + c1 * ((p:ℚ_[p])^M * u1) ^ 2 = w * ((p:ℚ_[p])^M)^2
  rw [← hu]; ring

/-- **Integer divisibility from `ℤ_[p]` divisibility.** If `p^N ∣ k` in `ℤ_[p]` (for an integer `k`), then
`p^N ∣ k` in `ℤ`. (The `ℤ_[p]` divisibility bounds `‖k‖ ≤ p^{-N}`, which `PadicInt.norm_int_le_pow_iff_dvd`
reads back as integer divisibility.) -/
theorem int_dvd_of_padicInt_dvd {p : ℕ} [Fact p.Prime] {k : ℤ} {N : ℕ}
    (h : (p : ℤ_[p]) ^ N ∣ (k : ℤ_[p])) : (p : ℤ) ^ N ∣ k := by
  rw [← PadicInt.norm_int_le_pow_iff_dvd]
  have hb : ‖(k : ℤ_[p])‖ ≤ ‖(p : ℤ_[p]) ^ N‖ := by
    obtain ⟨c, hc⟩ := h
    rw [hc, norm_mul]
    calc ‖(p : ℤ_[p]) ^ N‖ * ‖c‖ ≤ ‖(p : ℤ_[p]) ^ N‖ * 1 :=
          mul_le_mul_of_nonneg_left c.2 (norm_nonneg _)
      _ = ‖(p : ℤ_[p]) ^ N‖ := mul_one _
  rw [norm_pow, PadicInt.norm_p, inv_pow] at hb
  rw [zpow_neg, zpow_natCast]; convert hb using 2

/-- **Integer residues of a `ℤ_[p]` binary representation.** If `(T : ℚ_[p]) = c₀ v₀² + c₁ v₁²` with
`v₀, v₁ ∈ ℤ_[p]`, then the integer obtained from the mod-`p^N` residues of `v₀, v₁` is `≡ T (mod p^N)`. This
is the integer-congruence bridge of the bad-prime descent: with `Xᵢ ≡ vᵢ.appr N`, the global integer value
`c₀ X₀² + c₁ X₁²` lands `≡ T (mod p^N)`, in `T`'s `ℚ_[p]`-square class. -/
theorem appr_bridge {p : ℕ} [Fact p.Prime] (c0 c1 : ℤ) (v0 v1 : ℤ_[p]) (T : ℤ) (N : ℕ)
    (hT : (T : ℚ_[p]) = c0 * (v0 : ℚ_[p]) ^ 2 + c1 * (v1 : ℚ_[p]) ^ 2) :
    (p : ℤ) ^ N ∣ (c0 * (v0.appr N : ℤ) ^ 2 + c1 * (v1.appr N : ℤ) ^ 2) - T := by
  apply int_dvd_of_padicInt_dvd
  have hTz : (T : ℤ_[p]) = c0 * v0 ^ 2 + c1 * v1 ^ 2 := by
    apply PadicInt.ext; push_cast; linear_combination hT
  have e0 : (v0.appr N : ℤ_[p]) - v0 ∈ Ideal.span {(p : ℤ_[p]) ^ N} := by
    rw [show (v0.appr N : ℤ_[p]) - v0 = -(v0 - (v0.appr N : ℤ_[p])) by ring]
    exact neg_mem (PadicInt.appr_spec N v0)
  have e1 : (v1.appr N : ℤ_[p]) - v1 ∈ Ideal.span {(p : ℤ_[p]) ^ N} := by
    rw [show (v1.appr N : ℤ_[p]) - v1 = -(v1 - (v1.appr N : ℤ_[p])) by ring]
    exact neg_mem (PadicInt.appr_spec N v1)
  have key : ((c0 * (v0.appr N : ℤ) ^ 2 + c1 * (v1.appr N : ℤ) ^ 2 : ℤ) : ℤ_[p]) - (T : ℤ_[p])
      = c0 * (((v0.appr N : ℤ_[p]) - v0) * ((v0.appr N : ℤ_[p]) + v0))
        + c1 * (((v1.appr N : ℤ_[p]) - v1) * ((v1.appr N : ℤ_[p]) + v1)) := by
    rw [hTz]; push_cast; ring
  rw [← Ideal.mem_span_singleton, Int.cast_sub, key]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ e0))
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ e1))

/-- **Common value of the leading binary and the residual (per place).** Over a field with `Invertible 2`,
if the diagonal form `⟨c₀, c₁, R⟩` (`R : Fin m → K`, `m ≥ 1`, all coefficients nonzero) is isotropic, then
there is a nonzero `w` represented by the binary `⟨c₀, c₁⟩` with `−w` represented by `R`. (From a zero
`(x₀, x₁, x')`: if the binary value `c₀x₀² + c₁x₁² ≠ 0` take it as `w`; otherwise the binary or `R` is
isotropic, hence universal — `binary_isotropic_universal` / `represents_of_isotropic_diag` — and supplies the
missing representation.) The per-place extraction feeding the Meyer descent: applied over each `ℚ_v` it yields
the local common value `w_v` whose square class the global descent value must match. -/
theorem exists_common_value_split {K : Type*} [Field K] [Invertible (2 : K)]
    {m : ℕ} (hm : 0 < m) {c0 c1 : K} (R : Fin m → K) (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0) (hR : ∀ i, R i ≠ 0)
    (hiso : ∃ x : Fin (m + 2) → K, x ≠ 0 ∧
      ∑ i, (Fin.cons c0 (Fin.cons c1 R : Fin (m + 1) → K) : Fin (m + 2) → K) i * x i ^ 2 = 0) :
    ∃ w : K, w ≠ 0 ∧ (∃ u0 u1 : K, c0 * u0 ^ 2 + c1 * u1 ^ 2 = w) ∧
      (∃ y : Fin m → K, ∑ i, R i * y i ^ 2 = -w) := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  obtain ⟨x, hx0, he⟩ := hiso
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at he
  simp only [Fin.cons_zero, Fin.cons_succ] at he
  rw [Fin.succ_zero_eq_one] at he
  set xR : Fin m → K := fun i => x i.succ.succ with hxR
  have hsum : c0 * x 0 ^ 2 + c1 * x 1 ^ 2 + ∑ i, R i * xR i ^ 2 = 0 := by
    rw [hxR]; linear_combination he
  by_cases hB : c0 * x 0 ^ 2 + c1 * x 1 ^ 2 = 0
  · have hRval : ∑ i, R i * xR i ^ 2 = 0 := by linear_combination hsum - hB
    by_cases hxy : x 0 = 0 ∧ x 1 = 0
    · have hxRne : xR ≠ 0 := by
        intro hz
        apply hx0; funext k
        refine Fin.cases ?_ (fun k' => ?_) k
        · exact hxy.1
        · refine Fin.cases ?_ (fun j => ?_) k'
          · exact hxy.2
          · have := congrFun hz j; simpa [hxR] using this
      obtain ⟨y, hy⟩ := represents_of_isotropic_diag h2 R hR ⟨xR, hxRne, hRval⟩ (-c0)
      exact ⟨c0, hc0, ⟨1, 0, by ring⟩, ⟨y, by rw [hy]⟩⟩
    · have hR0 : R ⟨0, hm⟩ ≠ 0 := hR _
      have hBuniv := binary_isotropic_universal hc0 hc1 ⟨x 0, x 1, hxy, hB⟩ (-(R ⟨0, hm⟩))
      refine ⟨-(R ⟨0, hm⟩), by simpa using hR0, hBuniv, ?_⟩
      refine ⟨fun i => if i = ⟨0, hm⟩ then 1 else 0, ?_⟩
      rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ _) h
  · exact ⟨c0 * x 0 ^ 2 + c1 * x 1 ^ 2, hB, ⟨x 0, x 1, rfl⟩, ⟨xR, by linear_combination hsum⟩⟩

/-- A diagonal form's represented values are closed under multiplication by a square (`y ↦ s • y`). -/
theorem diag_represents_congr_sq {K : Type*} [Field K] {m : ℕ} (R : Fin m → K) {t s : K}
    (h : ∃ y : Fin m → K, ∑ i, R i * y i ^ 2 = t) :
    ∃ y : Fin m → K, ∑ i, R i * y i ^ 2 = t * s ^ 2 := by
  obtain ⟨y, hy⟩ := h
  refine ⟨fun i => s * y i, ?_⟩
  show ∑ i, R i * (s * y i) ^ 2 = t * s ^ 2
  have : ∑ i, R i * (s * y i) ^ 2 = s ^ 2 * ∑ i, R i * y i ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [this, hy]; ring

/-- If a diagonal form represents `c ≠ 0` and `r / c` is a square, it represents `r` (square-class
invariance of representability — the rank-`m` analog of `binary_represents_of_isSquare_ratio`). The
bad-prime descent transfers `R reps −w_p` to `R reps −a` once `a / w_p` is a `ℚ_p`-square. -/
theorem diag_represents_of_isSquare_ratio {K : Type*} [Field K] {m : ℕ} (R : Fin m → K) {c r : K}
    (hc : c ≠ 0) (hsq : IsSquare (r / c)) (h : ∃ y : Fin m → K, ∑ i, R i * y i ^ 2 = c) :
    ∃ y : Fin m → K, ∑ i, R i * y i ^ 2 = r := by
  obtain ⟨s, hs⟩ := hsq
  obtain ⟨y, hy⟩ := h
  refine ⟨fun i => s * y i, ?_⟩
  show ∑ i, R i * (s * y i) ^ 2 = r
  have hstep : ∑ i, R i * (s * y i) ^ 2 = s ^ 2 * ∑ i, R i * y i ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hstep, hy, show r = c * (s * s) by rw [← hs]; field_simp]; ring

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

/-- **`⟨a, R⟩` is isotropic when `R` represents `−a`.** Witness `(1, z)` where `R(z) = −a`. The descent
direction of the Meyer reduction: once the residual `R` represents `−a` (the descended value), the rank-`(m+1)`
form `⟨a, R⟩` has a nontrivial zero, feeding the inductive hypothesis. -/
theorem cons_isotropic_of_repr_neg {K : Type*} [Field K] {m : ℕ} {a : K} (R : Fin m → K)
    (h : ∃ z : Fin m → K, ∑ i, R i * z i ^ 2 = -a) :
    ∃ y : Fin (m + 1) → K, y ≠ 0 ∧ ∑ i, (Fin.cons a R : Fin (m + 1) → K) i * y i ^ 2 = 0 := by
  obtain ⟨z, hz⟩ := h
  refine ⟨Fin.cons 1 z, ?_, ?_⟩
  · intro hzero; have := congrFun hzero 0; simp at this
  · rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; rw [hz]; ring

/-- **A real-isotropic diagonal form is indefinite.** A nontrivial real zero of `∑ cᵢ xᵢ²` (all `cᵢ ≠ 0`)
forces both a positive and a negative coefficient. (If all had one sign the form would be definite.) Supplies
the hypotheses of `exists_peel_pair`. -/
theorem exists_pos_neg_of_real_isotropic {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ≠ 0)
    (h : ∃ x : Fin n → ℝ, x ≠ 0 ∧ ∑ i, c i * x i ^ 2 = 0) :
    (∃ i, 0 < c i) ∧ (∃ j, c j < 0) := by
  obtain ⟨x, hx0, he⟩ := h
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hx0
  simp only [Pi.zero_apply] at hk
  constructor
  · by_contra hpos
    simp only [not_exists, not_lt] at hpos
    have hlt : ∀ i, c i < 0 := fun i => lt_of_le_of_ne (hpos i) (hc i)
    have : ∑ i, c i * x i ^ 2 < 0 :=
      Finset.sum_neg' (fun i _ => mul_nonpos_of_nonpos_of_nonneg (hlt i).le (sq_nonneg _))
        ⟨k, Finset.mem_univ k, mul_neg_of_neg_of_pos (hlt k) (by positivity)⟩
    linarith
  · by_contra hneg
    simp only [not_exists, not_lt] at hneg
    have hgt : ∀ i, 0 < c i := fun i => lt_of_le_of_ne (hneg i) (Ne.symm (hc i))
    have : 0 < ∑ i, c i * x i ^ 2 :=
      Finset.sum_pos' (fun i _ => mul_nonneg (hgt i).le (sq_nonneg _))
        ⟨k, Finset.mem_univ k, mul_pos (hgt k) (by positivity)⟩
    linarith

/-- **Finite bad-prime list.** For nonzero integer coefficients `c`, there is a finite list `S` of primes
(containing `2`, nodup) outside which every coefficient is coprime to `p` — i.e. a `p`-adic unit. (Take the
prime factors of `∏ |cᵢ|`, plus `2`.) The good-prime set of the Meyer descent: outside `S` the residual unit
form is universal over `ℚ_[p]`. -/
theorem exists_bad_prime_list {n : ℕ} (c : Fin n → ℤ) (hc : ∀ i, c i ≠ 0) :
    ∃ S : List ℕ, (∀ p ∈ S, p.Prime) ∧ S.Nodup ∧ 2 ∈ S ∧
      ∀ p : ℕ, p.Prime → p ∉ S → ∀ i, ¬ (p : ℤ) ∣ c i := by
  classical
  set N : ℕ := ∏ i, (c i).natAbs with hN
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => Int.natAbs_ne_zero.mpr (hc i))
  set Sf : Finset ℕ := insert 2 N.primeFactors with hSf
  refine ⟨Sf.toList, ?_, Sf.nodup_toList, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_toList, hSf, Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · exact Nat.prime_two
    · exact (Nat.mem_primeFactors.mp hp).1
  · rw [Finset.mem_toList, hSf, Finset.mem_insert]; exact Or.inl rfl
  · intro p hp hpS i hdvd
    rw [Finset.mem_toList, hSf, Finset.mem_insert, not_or] at hpS
    have hpN : ¬ p ∣ N := fun h => hpS.2 (Nat.mem_primeFactors.mpr ⟨hp, h, hN0⟩)
    have hdvdAbs : p ∣ (c i).natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hdvd; simpa using this
    exact hpN (dvd_trans hdvdAbs (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))

/-! ### Bad-prime descent certificate -/

/-- **Bad-prime descent certificate (odd `p`).** If `⟨c₀, c₁, R⟩` (integer `c₀, c₁`; `R : Fin m → ℚ_[p]`,
`m ≥ 1`) is isotropic over `ℚ_[p]`, there are integer residue targets `n₀, n₁` and a modulus exponent `N`
such that for *every* integer pair `X₀ ≡ n₀, X₁ ≡ n₁ (mod p^N)`, the integer value `a = c₀X₀² + c₁X₁²` is
nonzero and `R` represents `−a` over `ℚ_[p]`. This is the per-bad-prime input of the Meyer descent: the global
value `a = B(X)` from integer CRT is automatically `B`-represented (free) and, at each bad prime, `R`-represents
`−a` so the descended `⟨a, R⟩` is locally isotropic. (Chain: `exists_common_value_split` → `exists_int_sq_ratio_odd`
→ `binary_represents_congr_sq` → `exists_padicInt_binary_rep` [integer target `T = mᵢ·p^{2M}`] →
`diag_represents_*` [`R` reps `−T`] → `appr_bridge` [`a ≡ T mod p^N`, integer] → `isSquare_padic_div_of_modEq`
[`a/T` square] → `R` reps `−a`. `N = padicValInt p T + 1` makes `p^N ∤ T`, forcing `a ≠ 0`.) -/
theorem bad_prime_R_certificate_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {m : ℕ} (hm : 0 < m)
    {c0 c1 : ℤ} (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0) (Rq : Fin m → ℚ_[p]) (hRq : ∀ i, Rq i ≠ 0)
    (hiso : ∃ x : Fin (m + 2) → ℚ_[p], x ≠ 0 ∧
      ∑ i, (Fin.cons (c0 : ℚ_[p]) (Fin.cons (c1 : ℚ_[p]) Rq : Fin (m + 1) → ℚ_[p]) :
        Fin (m + 2) → ℚ_[p]) i * x i ^ 2 = 0) :
    ∃ (n0 n1 : ℤ) (N : ℕ), ∀ X0 X1 : ℤ, (p : ℤ) ^ N ∣ X0 - n0 → (p : ℤ) ^ N ∣ X1 - n1 →
      c0 * X0 ^ 2 + c1 * X1 ^ 2 ≠ 0 ∧
      ∃ y : Fin m → ℚ_[p], ∑ i, Rq i * y i ^ 2 = -((c0 * X0 ^ 2 + c1 * X1 ^ 2 : ℤ) : ℚ_[p]) := by
  haveI : Invertible (2 : ℚ_[p]) := invertibleOfNonzero (by norm_num)
  have hc0Q : (c0 : ℚ_[p]) ≠ 0 := by exact_mod_cast hc0
  have hc1Q : (c1 : ℚ_[p]) ≠ 0 := by exact_mod_cast hc1
  obtain ⟨w, hw0, hBw, hRw⟩ := exists_common_value_split hm Rq hc0Q hc1Q hRq hiso
  obtain ⟨mi, hmi0, hsq⟩ := exists_int_sq_ratio_odd hp hw0
  obtain ⟨s, hs⟩ := hsq
  have hmiQ : (mi : ℚ_[p]) ≠ 0 := by exact_mod_cast hmi0
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [mul_zero, div_eq_zero_iff] at hs; exact hw0 (hs.resolve_right hmiQ)
  have hweq : w = (mi : ℚ_[p]) * s ^ 2 := by field_simp at hs; linear_combination hs
  have hBm : ∃ u0 u1 : ℚ_[p], (c0 : ℚ_[p]) * u0 ^ 2 + (c1 : ℚ_[p]) * u1 ^ 2 = (mi : ℚ_[p]) := by
    rw [binary_represents_congr_sq hs0]
    obtain ⟨u0, u1, h⟩ := hBw; exact ⟨u0, u1, by rw [h, hweq]⟩
  obtain ⟨M, v0, v1, hv⟩ := exists_padicInt_binary_rep hBm
  set T : ℤ := mi * (p : ℤ) ^ (2 * M) with hTdef
  have hpZ0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hT0 : T ≠ 0 := mul_ne_zero hmi0 (pow_ne_zero _ hpZ0)
  have hTQ0 : ((T : ℤ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hT0
  have hTQ : ((T : ℤ) : ℚ_[p]) = (c0 : ℚ_[p]) * (v0 : ℚ_[p]) ^ 2 + (c1 : ℚ_[p]) * (v1 : ℚ_[p]) ^ 2 := by
    rw [hv, hTdef]; push_cast; ring
  have hsqr : IsSquare ((-(mi : ℚ_[p])) / (-w)) := by
    rw [neg_div_neg_eq, hweq]; refine ⟨s⁻¹, ?_⟩; field_simp
  have hRm : ∃ y : Fin m → ℚ_[p], ∑ i, Rq i * y i ^ 2 = -(mi : ℚ_[p]) :=
    diag_represents_of_isSquare_ratio Rq (neg_ne_zero.mpr hw0) hsqr hRw
  have hRT : ∃ y : Fin m → ℚ_[p], ∑ i, Rq i * y i ^ 2 = -((T : ℤ) : ℚ_[p]) := by
    obtain ⟨y, hy⟩ := diag_represents_congr_sq Rq (s := (p : ℚ_[p]) ^ M) hRm
    exact ⟨y, by rw [hy, hTdef]; push_cast; ring⟩
  set N := padicValInt p T + 1 with hNdef
  refine ⟨(v0.appr N : ℤ), (v1.appr N : ℤ), N, fun X0 X1 hX0 hX1 => ?_⟩
  set a : ℤ := c0 * X0 ^ 2 + c1 * X1 ^ 2 with hadef
  have hcong : (p : ℤ) ^ N ∣ a - T := by
    have hbr := appr_bridge c0 c1 v0 v1 T N hTQ
    have hd0 : (p : ℤ) ^ N ∣ X0 ^ 2 - (v0.appr N : ℤ) ^ 2 := by
      rw [show X0 ^ 2 - (v0.appr N : ℤ) ^ 2 = (X0 - (v0.appr N : ℤ)) * (X0 + (v0.appr N : ℤ)) by ring]
      exact Dvd.dvd.mul_right hX0 _
    have hd1 : (p : ℤ) ^ N ∣ X1 ^ 2 - (v1.appr N : ℤ) ^ 2 := by
      rw [show X1 ^ 2 - (v1.appr N : ℤ) ^ 2 = (X1 - (v1.appr N : ℤ)) * (X1 + (v1.appr N : ℤ)) by ring]
      exact Dvd.dvd.mul_right hX1 _
    have heq : a - T = (c0 * (X0 ^ 2 - (v0.appr N : ℤ) ^ 2) + c1 * (X1 ^ 2 - (v1.appr N : ℤ) ^ 2))
        + ((c0 * (v0.appr N : ℤ) ^ 2 + c1 * (v1.appr N : ℤ) ^ 2) - T) := by rw [hadef]; ring
    rw [heq]
    exact dvd_add (dvd_add (Dvd.dvd.mul_left hd0 _) (Dvd.dvd.mul_left hd1 _)) hbr
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_sub, dvd_neg, hNdef, padicValInt_dvd_iff] at hcong
    rcases hcong with h' | h'
    · exact hT0 h'
    · omega
  refine ⟨ha0, ?_⟩
  have hsqaT : IsSquare ((a : ℚ_[p]) / (T : ℚ_[p])) := isSquare_padic_div_of_modEq hp ha0 hT0 hcong
  exact diag_represents_of_isSquare_ratio Rq (neg_ne_zero.mpr hTQ0)
    (by rw [neg_div_neg_eq]; exact hsqaT) hRT

/-- **Bad-prime descent certificate at `p = 2`.** The `p = 2` analogue of `bad_prime_R_certificate_odd`,
using `exists_int_sq_ratio_2` and `isSquare_2adic_div_of_modEq` (modulus exponent `N = padicValInt 2 T + 3`).
`2 ∈ S` always, so this is mandatory. -/
theorem bad_prime_R_certificate_2 {m : ℕ} (hm : 0 < m)
    {c0 c1 : ℤ} (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0) (Rq : Fin m → ℚ_[2]) (hRq : ∀ i, Rq i ≠ 0)
    (hiso : ∃ x : Fin (m + 2) → ℚ_[2], x ≠ 0 ∧
      ∑ i, (Fin.cons (c0 : ℚ_[2]) (Fin.cons (c1 : ℚ_[2]) Rq : Fin (m + 1) → ℚ_[2]) :
        Fin (m + 2) → ℚ_[2]) i * x i ^ 2 = 0) :
    ∃ (n0 n1 : ℤ) (N : ℕ), ∀ X0 X1 : ℤ, (2 : ℤ) ^ N ∣ X0 - n0 → (2 : ℤ) ^ N ∣ X1 - n1 →
      c0 * X0 ^ 2 + c1 * X1 ^ 2 ≠ 0 ∧
      ∃ y : Fin m → ℚ_[2], ∑ i, Rq i * y i ^ 2 = -((c0 * X0 ^ 2 + c1 * X1 ^ 2 : ℤ) : ℚ_[2]) := by
  haveI : Invertible (2 : ℚ_[2]) := invertibleOfNonzero (by norm_num)
  have hc0Q : (c0 : ℚ_[2]) ≠ 0 := by exact_mod_cast hc0
  have hc1Q : (c1 : ℚ_[2]) ≠ 0 := by exact_mod_cast hc1
  obtain ⟨w, hw0, hBw, hRw⟩ := exists_common_value_split hm Rq hc0Q hc1Q hRq hiso
  obtain ⟨mi, hmi0, hsq⟩ := exists_int_sq_ratio_2 hw0
  obtain ⟨s, hs⟩ := hsq
  have hmiQ : (mi : ℚ_[2]) ≠ 0 := by exact_mod_cast hmi0
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [mul_zero, div_eq_zero_iff] at hs; exact hw0 (hs.resolve_right hmiQ)
  have hweq : w = (mi : ℚ_[2]) * s ^ 2 := by field_simp at hs; linear_combination hs
  have hBm : ∃ u0 u1 : ℚ_[2], (c0 : ℚ_[2]) * u0 ^ 2 + (c1 : ℚ_[2]) * u1 ^ 2 = (mi : ℚ_[2]) := by
    rw [binary_represents_congr_sq hs0]
    obtain ⟨u0, u1, h⟩ := hBw; exact ⟨u0, u1, by rw [h, hweq]⟩
  obtain ⟨M, v0, v1, hv⟩ := exists_padicInt_binary_rep hBm
  set T : ℤ := mi * (2 : ℤ) ^ (2 * M) with hTdef
  have hT0 : T ≠ 0 := mul_ne_zero hmi0 (pow_ne_zero _ (by norm_num))
  have hTQ0 : ((T : ℤ) : ℚ_[2]) ≠ 0 := by exact_mod_cast hT0
  have hTQ : ((T : ℤ) : ℚ_[2]) = (c0 : ℚ_[2]) * (v0 : ℚ_[2]) ^ 2 + (c1 : ℚ_[2]) * (v1 : ℚ_[2]) ^ 2 := by
    rw [hv, hTdef]; push_cast; ring
  have hsqr : IsSquare ((-(mi : ℚ_[2])) / (-w)) := by
    rw [neg_div_neg_eq, hweq]; refine ⟨s⁻¹, ?_⟩; field_simp
  have hRm : ∃ y : Fin m → ℚ_[2], ∑ i, Rq i * y i ^ 2 = -(mi : ℚ_[2]) :=
    diag_represents_of_isSquare_ratio Rq (neg_ne_zero.mpr hw0) hsqr hRw
  have hRT : ∃ y : Fin m → ℚ_[2], ∑ i, Rq i * y i ^ 2 = -((T : ℤ) : ℚ_[2]) := by
    obtain ⟨y, hy⟩ := diag_represents_congr_sq Rq (s := (2 : ℚ_[2]) ^ M) hRm
    exact ⟨y, by rw [hy, hTdef]; push_cast; ring⟩
  set N := padicValInt 2 T + 3 with hNdef
  refine ⟨(v0.appr N : ℤ), (v1.appr N : ℤ), N, fun X0 X1 hX0 hX1 => ?_⟩
  set a : ℤ := c0 * X0 ^ 2 + c1 * X1 ^ 2 with hadef
  have hcong : (2 : ℤ) ^ N ∣ a - T := by
    have hbr := appr_bridge (p := 2) c0 c1 v0 v1 T N hTQ
    have hd0 : (2 : ℤ) ^ N ∣ X0 ^ 2 - (v0.appr N : ℤ) ^ 2 := by
      rw [show X0 ^ 2 - (v0.appr N : ℤ) ^ 2 = (X0 - (v0.appr N : ℤ)) * (X0 + (v0.appr N : ℤ)) by ring]
      exact Dvd.dvd.mul_right hX0 _
    have hd1 : (2 : ℤ) ^ N ∣ X1 ^ 2 - (v1.appr N : ℤ) ^ 2 := by
      rw [show X1 ^ 2 - (v1.appr N : ℤ) ^ 2 = (X1 - (v1.appr N : ℤ)) * (X1 + (v1.appr N : ℤ)) by ring]
      exact Dvd.dvd.mul_right hX1 _
    have heq : a - T = (c0 * (X0 ^ 2 - (v0.appr N : ℤ) ^ 2) + c1 * (X1 ^ 2 - (v1.appr N : ℤ) ^ 2))
        + ((c0 * (v0.appr N : ℤ) ^ 2 + c1 * (v1.appr N : ℤ) ^ 2) - T) := by rw [hadef]; ring
    rw [heq]
    exact dvd_add (dvd_add (Dvd.dvd.mul_left hd0 _) (Dvd.dvd.mul_left hd1 _)) hbr
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_sub, dvd_neg] at hcong
    have hcong2 : ((2 : ℕ) : ℤ) ^ (padicValInt 2 T + 3) ∣ T := by rw [hNdef] at hcong; exact_mod_cast hcong
    rw [padicValInt_dvd_iff] at hcong2
    rcases hcong2 with h' | h'
    · exact hT0 h'
    · omega
  refine ⟨ha0, ?_⟩
  have hsqaT : IsSquare ((a : ℚ_[2]) / (T : ℚ_[2])) := isSquare_2adic_div_of_modEq ha0 hT0 hcong
  exact diag_represents_of_isSquare_ratio Rq (neg_ne_zero.mpr hTQ0)
    (by rw [neg_div_neg_eq]; exact hsqaT) hRT

end SKEFTHawking
