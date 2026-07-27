/-
# Phase 5q.H (K8b interior) — the odd-form unit-vector brick

The K8b interior brick `EvenUnimodularIndefiniteSplit.StableNegRank16` (the one-hyperbolic
stabilization `H ⊕ D ≅ H ⊕ 2(−E₈)`) is the classical Eichler/Kneser statement that indefinite even
unimodular lattices are classified by rank and signature. The route adjudicated for it
(`docs/dev-loops/Phase5qH/KUMMER_K4K10_DESIGN.md`, K8b route (i)) goes through **Milnor–Husemoller
II.4.3** — the classification of INDEFINITE ODD unimodular forms as `⟨1⟩^p ⊕ ⟨−1⟩^q` — whose entry
point is: *an indefinite odd unimodular form represents `1`*.

This module discharges that entry point. The key enabling asset is already banked and kernel-pure:
`RokhlinHMDischarge.weakIsotropic_of_five_le` is a genuine **Meyer/Hasse–Minkowski** theorem — an
indefinite integer Gram form of rank `≥ 5` has a nonzero integer isotropic vector, with **no**
evenness or unimodularity hypothesis. Everything past that point here is elementary vector algebra:

* `gramPair_comm` and the `gramPair_{add,sub,smul}_{left,right}` expansion set — the bilinear toolkit
  for `x ⬝ᵥ M *ᵥ y`.
* `exists_unit_of_odd_partner` — if `v` is isotropic with partner `w` (`v·w = 1`) of ODD self-product
  `2k+1`, then `w − k·v` has self-product `1`.
* `isotropic_partner_of_even` — if the partner has EVEN self-product it is normalized to a genuine
  hyperbolic partner (`w₀·w₀ = 0`).
* `gramPair_hypProj` — orthogonalizing any `z` against a hyperbolic pair changes its self-product by
  `−2ab`, hence PRESERVES ITS PARITY. This is the crux: it is what lets an odd vector anywhere in the
  lattice be transported into the hyperbolic plane's complement.
* `exists_unit_of_orthogonal_odd` — for `z'` orthogonal to a hyperbolic pair with `z'·z' = 2k+1`,
  the vector `z' + (−k)·v + w` has self-product exactly `1`.
* `odd_indefinite_represents_one` — the headline: an indefinite symmetric unimodular form of rank
  `≥ 5` with an odd diagonal entry represents `1`, by a PRIMITIVE vector.

The odd-diagonal hypothesis is load-bearing, not decorative: an EVEN form takes only even values, so
it never represents `1` — the statement is false without it (`even_form_not_represents_one`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.RokhlinHMRankFour
import SKEFTHawking.LatticePrimitive
import SKEFTHawking.LatticeContent

namespace SKEFTHawking

open Matrix QuadraticForm

/-! ### The bilinear-pairing toolkit

`x ⬝ᵥ M *ᵥ y` is the Gram pairing of the lattice presented by `M`. The six expansion lemmas below
reduce any pairing of integer combinations to the pairings of the generators; `gramPair_comm` (for
symmetric `M`) then identifies the two orders. Together they let `simp only [...] ; ring` discharge
every Gram computation in this file. -/

/-- **Symmetry of the Gram pairing** for a symmetric Gram matrix. -/
theorem gramPair_comm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} (hsymm : Mᵀ = M) (x y : Fin n → ℤ) :
    x ⬝ᵥ M *ᵥ y = y ⬝ᵥ M *ᵥ x := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]

/-- Additivity of the Gram pairing in the right slot. -/
theorem gramPair_add_right {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x y z : Fin n → ℤ) :
    x ⬝ᵥ M *ᵥ (y + z) = x ⬝ᵥ M *ᵥ y + x ⬝ᵥ M *ᵥ z := by
  rw [Matrix.mulVec_add, dotProduct_add]

/-- Subtractivity of the Gram pairing in the right slot. -/
theorem gramPair_sub_right {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x y z : Fin n → ℤ) :
    x ⬝ᵥ M *ᵥ (y - z) = x ⬝ᵥ M *ᵥ y - x ⬝ᵥ M *ᵥ z := by
  rw [Matrix.mulVec_sub, dotProduct_sub]

/-- Homogeneity of the Gram pairing in the right slot. -/
theorem gramPair_smul_right {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) (x y : Fin n → ℤ) :
    x ⬝ᵥ M *ᵥ (c • y) = c * (x ⬝ᵥ M *ᵥ y) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/-- Additivity of the Gram pairing in the left slot. -/
theorem gramPair_add_left {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x y z : Fin n → ℤ) :
    (x + y) ⬝ᵥ M *ᵥ z = x ⬝ᵥ M *ᵥ z + y ⬝ᵥ M *ᵥ z := add_dotProduct x y (M *ᵥ z)

/-- Subtractivity of the Gram pairing in the left slot. -/
theorem gramPair_sub_left {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (x y z : Fin n → ℤ) :
    (x - y) ⬝ᵥ M *ᵥ z = x ⬝ᵥ M *ᵥ z - y ⬝ᵥ M *ᵥ z := sub_dotProduct x y (M *ᵥ z)

/-- Homogeneity of the Gram pairing in the left slot. -/
theorem gramPair_smul_left {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) (x y : Fin n → ℤ) :
    (c • x) ⬝ᵥ M *ᵥ y = c * (x ⬝ᵥ M *ᵥ y) := by
  rw [smul_dotProduct, smul_eq_mul]

/-- **The self-product of a standard basis vector is the diagonal entry.** Turns the "odd form"
hypothesis (some diagonal entry is odd) into a vector of odd self-product. -/
theorem gramPair_single_self {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    (Pi.single i (1 : ℤ)) ⬝ᵥ M *ᵥ (Pi.single i (1 : ℤ)) = M i i := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_ite_eq']

/-- **An even form never represents `1`** — the sharpness companion. Every value `x ⬝ᵥ M *ᵥ x` of an
even symmetric form is even (`EvenLattice.even_form_dvd`), so `x ⬝ᵥ M *ᵥ x = 1` is impossible. This is
what makes the odd-diagonal hypothesis of `odd_indefinite_represents_one` load-bearing rather than
decorative: with `heven` in place of `hodd` the conclusion is FALSE, not merely unproved. -/
theorem even_form_not_represents_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (heven : ∀ i, 2 ∣ M i i) (x : Fin n → ℤ) : x ⬝ᵥ M *ᵥ x ≠ 1 := by
  intro hx
  have h2 : (2 : ℤ) ∣ 1 := hx ▸ EvenLattice.even_form_dvd hsymm heven x
  norm_num at h2

/-! ### Producing a vector of self-product `1` -/

/-- **Odd partner ⟹ a unit vector.** If `v` is isotropic and `w` pairs to `1` with `v` but has ODD
self-product `2k+1`, then `w − k·v` has self-product `1` and still pairs to `1` with `v`. -/
theorem exists_unit_of_odd_partner {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (v w : Fin n → ℤ) (hv0 : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w = 1)
    (k : ℤ) (hk : w ⬝ᵥ M *ᵥ w = 2 * k + 1) :
    ∃ x : Fin n → ℤ, v ⬝ᵥ M *ᵥ x = 1 ∧ x ⬝ᵥ M *ᵥ x = 1 := by
  have hwv : w ⬝ᵥ M *ᵥ v = 1 := by rw [gramPair_comm hsymm]; exact hvw
  refine ⟨w - k • v, ?_, ?_⟩ <;>
    simp only [gramPair_sub_left, gramPair_sub_right, gramPair_smul_left, gramPair_smul_right,
      hv0, hvw, hwv, hk] <;> ring

/-- **Even partner ⟹ a genuine hyperbolic partner.** If `v` is isotropic and `w` pairs to `1` with `v`
with EVEN self-product `2c`, then `w − c·v` is isotropic and still pairs to `1` with `v`. -/
theorem isotropic_partner_of_even {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (v w : Fin n → ℤ) (hv0 : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w = 1)
    (c : ℤ) (hc : w ⬝ᵥ M *ᵥ w = 2 * c) :
    v ⬝ᵥ M *ᵥ (w - c • v) = 1 ∧ (w - c • v) ⬝ᵥ M *ᵥ (w - c • v) = 0 := by
  have hwv : w ⬝ᵥ M *ᵥ v = 1 := by rw [gramPair_comm hsymm]; exact hvw
  constructor <;>
    simp only [gramPair_sub_left, gramPair_sub_right, gramPair_smul_left, gramPair_smul_right,
      hv0, hvw, hwv, hc] <;> ring

/-- **Orthogonalization against a hyperbolic pair preserves the parity of the self-product.** For a
hyperbolic pair `(v, w)` (`v·v = w·w = 0`, `v·w = 1`) and any `z`, the projection
`z' = z − (z·w)·v − (z·v)·w` is orthogonal to both `v` and `w`, and `z'·z' = z·z − 2·(z·w)·(z·v)` —
so `z'` has the SAME parity as `z`. -/
theorem gramPair_hypProj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (v w : Fin n → ℤ) (hv0 : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w = 1) (hw0 : w ⬝ᵥ M *ᵥ w = 0)
    (z : Fin n → ℤ) (a b : ℤ) (ha : a = z ⬝ᵥ M *ᵥ w) (hb : b = z ⬝ᵥ M *ᵥ v) :
    v ⬝ᵥ M *ᵥ (z - a • v - b • w) = 0 ∧ w ⬝ᵥ M *ᵥ (z - a • v - b • w) = 0 ∧
    (z - a • v - b • w) ⬝ᵥ M *ᵥ (z - a • v - b • w) = z ⬝ᵥ M *ᵥ z - 2 * a * b := by
  have hwv : w ⬝ᵥ M *ᵥ v = 1 := by rw [gramPair_comm hsymm]; exact hvw
  have hvz : v ⬝ᵥ M *ᵥ z = b := by rw [gramPair_comm hsymm]; exact hb.symm
  have hwz : w ⬝ᵥ M *ᵥ z = a := by rw [gramPair_comm hsymm]; exact ha.symm
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [gramPair_sub_left, gramPair_sub_right, gramPair_smul_left, gramPair_smul_right,
      hv0, hvw, hwv, hw0, hvz, hwz, ← ha, ← hb] <;> ring

/-- **A hyperbolic pair plus an orthogonal odd vector yields a vector of self-product exactly `1`.**
For `z'` orthogonal to the hyperbolic pair `(v, w)` with `z'·z' = 2k+1`, the vector
`x = z' + (−k)·v + w` satisfies `x·x = z'·z' + 2·(−k) = 1`, and `v·x = 1`. -/
theorem exists_unit_of_orthogonal_odd {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (v w z' : Fin n → ℤ) (hv0 : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w = 1) (hw0 : w ⬝ᵥ M *ᵥ w = 0)
    (hvz' : v ⬝ᵥ M *ᵥ z' = 0) (hwz' : w ⬝ᵥ M *ᵥ z' = 0) (k : ℤ) (hk : z' ⬝ᵥ M *ᵥ z' = 2 * k + 1) :
    v ⬝ᵥ M *ᵥ (z' + (-k) • v + w) = 1 ∧
    (z' + (-k) • v + w) ⬝ᵥ M *ᵥ (z' + (-k) • v + w) = 1 := by
  have hwv : w ⬝ᵥ M *ᵥ v = 1 := by rw [gramPair_comm hsymm]; exact hvw
  have hz'v : z' ⬝ᵥ M *ᵥ v = 0 := by rw [gramPair_comm hsymm]; exact hvz'
  have hz'w : z' ⬝ᵥ M *ᵥ w = 0 := by rw [gramPair_comm hsymm]; exact hwz'
  constructor <;>
    simp only [gramPair_add_left, gramPair_add_right, gramPair_smul_left, gramPair_smul_right,
      hv0, hvw, hwv, hw0, hvz', hwz', hz'v, hz'w, hk] <;> ring

/-! ### The headline: an indefinite odd unimodular form represents `1` -/

/-- **An indefinite odd unimodular form of rank `≥ 5` represents `1`, primitively.**

`M` symmetric unimodular of rank `≥ 5`, indefinite (`0 < sigPos`, `0 < sigNeg`), with SOME odd
diagonal entry `M i₀ i₀`. Then some **primitive** `x` has `x ⬝ᵥ M *ᵥ x = 1`.

This is the entry point of the Milnor–Husemoller II.4.3 classification of indefinite odd unimodular
forms (`⟨1⟩^p ⊕ ⟨−1⟩^q`), which the K8b route (i) needs in order to reach
`EvenUnimodularIndefiniteSplit.StableNegRank16`. Chain: Meyer/Hasse–Minkowski
(`weakIsotropic_of_five_le` — no evenness needed at rank ≥ 5) gives a nonzero isotropic vector;
content extraction (`exists_primitive_isotropic_of_isotropic`) makes it primitive; unimodularity
(`exists_vecMul_dot_eq_one`) supplies a partner `w` pairing to `1`; the partner's self-product is
either odd (`exists_unit_of_odd_partner`) or even, in which case it is normalized to a hyperbolic
partner (`isotropic_partner_of_even`) and the odd DIAGONAL entry supplies the parity
(`gramPair_hypProj` + `exists_unit_of_orthogonal_odd`). Primitivity of the output is free: it pairs to
`1` against `v`, so `x ⬝ᵥ (M *ᵥ v) = 1`.

The odd-diagonal hypothesis is load-bearing: by `even_form_not_represents_one` an even form takes only
even values, so the conclusion is FALSE without it. -/
theorem odd_unimodular_represents_one_of_isotropic {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ)
    (hsymm : Mᵀ = M) (hunim : IsUnimodular M) (i₀ : Fin m) (hodd : ¬ (2 ∣ M i₀ i₀))
    (v₀ : Fin m → ℤ) (hv₀ne : v₀ ≠ 0) (hv₀iso : v₀ ⬝ᵥ M *ᵥ v₀ = 0) :
    ∃ x : Fin m → ℤ, IsPrimitiveVec x ∧ x ⬝ᵥ M *ᵥ x = 1 := by
  -- Content extraction makes the isotropic vector primitive.
  obtain ⟨v, hvprim, hviso⟩ := exists_primitive_isotropic_of_isotropic M v₀ hv₀ne hv₀iso
  -- Unimodularity gives a partner pairing to `1`.
  obtain ⟨w, hw⟩ := exists_vecMul_dot_eq_one v M hvprim hunim
  have hvw : v ⬝ᵥ M *ᵥ w = 1 := by rw [Matrix.dotProduct_mulVec]; exact hw
  -- Either the partner is already a unit vector, or it normalizes to a hyperbolic partner and the
  -- odd diagonal entry supplies the parity.
  have key : ∃ x : Fin m → ℤ, v ⬝ᵥ M *ᵥ x = 1 ∧ x ⬝ᵥ M *ᵥ x = 1 := by
    rcases Int.even_or_odd (w ⬝ᵥ M *ᵥ w) with hev | hod
    · obtain ⟨c, hc⟩ := hev
      obtain ⟨hvw₀, hw₀0⟩ := isotropic_partner_of_even M hsymm v w hviso hvw c (by rw [hc]; ring)
      set w₀ := w - c • v with hw₀def
      set z : Fin m → ℤ := Pi.single i₀ (1 : ℤ) with hzdef
      obtain ⟨hvz', hwz', hz'z'⟩ :=
        gramPair_hypProj M hsymm v w₀ hviso hvw₀ hw₀0 z (z ⬝ᵥ M *ᵥ w₀) (z ⬝ᵥ M *ᵥ v) rfl rfl
      obtain ⟨k, hk⟩ : ∃ k : ℤ,
          (z - (z ⬝ᵥ M *ᵥ w₀) • v - (z ⬝ᵥ M *ᵥ v) • w₀) ⬝ᵥ M *ᵥ
            (z - (z ⬝ᵥ M *ᵥ w₀) • v - (z ⬝ᵥ M *ᵥ v) • w₀) = 2 * k + 1 := by
        have hzz : ¬ (2 ∣ z ⬝ᵥ M *ᵥ z) := by rw [hzdef, gramPair_single_self]; exact hodd
        rcases Int.even_or_odd (z ⬝ᵥ M *ᵥ z) with hev' | hod'
        · exact absurd hev'.two_dvd hzz
        · obtain ⟨j, hj⟩ := hod'
          exact ⟨j - (z ⬝ᵥ M *ᵥ w₀) * (z ⬝ᵥ M *ᵥ v), by rw [hz'z', hj]; ring⟩
      obtain ⟨h1, h2⟩ :=
        exists_unit_of_orthogonal_odd M hsymm v w₀ _ hviso hvw₀ hw₀0 hvz' hwz' k hk
      exact ⟨_, h1, h2⟩
    · obtain ⟨k, hk⟩ := hod
      exact exists_unit_of_odd_partner M hsymm v w hviso hvw k (by omega)
  obtain ⟨x, hxv, hxx⟩ := key
  refine ⟨x, ?_, hxx⟩
  rw [isPrimitiveVec_iff_exists_dot]
  exact ⟨M *ᵥ v, by rw [gramPair_comm hsymm x v]; exact hxv⟩

/-- **An indefinite odd unimodular form of rank `≥ 5` represents `1`, primitively.** The rank-`≥ 5`
corollary of `odd_unimodular_represents_one_of_isotropic`: Meyer/Hasse–Minkowski
(`weakIsotropic_of_five_le`, which carries no evenness hypothesis) supplies the isotropic vector.
This is the entry point of the Milnor–Husemoller II.4.3 classification. -/
theorem odd_indefinite_represents_one {m : ℕ} (hm : 5 ≤ m) (M : Matrix (Fin m) (Fin m) ℤ)
    (hsymm : Mᵀ = M) (hunim : IsUnimodular M) (i₀ : Fin m) (hodd : ¬ (2 ∣ M i₀ i₀))
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    ∃ x : Fin m → ℤ, IsPrimitiveVec x ∧ x ⬝ᵥ M *ᵥ x = 1 := by
  obtain ⟨v₀, hv₀ne, hv₀iso⟩ := weakIsotropic_of_five_le hm M hsp hsn
  exact odd_unimodular_represents_one_of_isotropic M hsymm hunim i₀ hodd v₀ hv₀ne hv₀iso

/-! ### The `−1` companion (orientation reversal) -/

/-- Negating the Gram matrix negates the real quadratic form. -/
theorem toQuadraticMap'_neg_matrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    ((-M).map (Int.cast : ℤ → ℝ)).toQuadraticMap'
      = -((M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') := by
  have hmap : ((-M).map (Int.cast : ℤ → ℝ)) = -(M.map (Int.cast : ℤ → ℝ)) := by ext i j; simp
  rw [hmap]; simp [Matrix.toQuadraticMap']

/-- Negating the form swaps the positive inertia index into the negative one. -/
theorem sigPos_neg_matrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    sigPos (((-M).map (Int.cast : ℤ → ℝ)).toQuadraticMap')
      = sigNeg ((M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') := by
  rw [toQuadraticMap'_neg_matrix, sigNeg]

/-- Negating the form swaps the negative inertia index into the positive one. -/
theorem sigNeg_neg_matrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    sigNeg (((-M).map (Int.cast : ℤ → ℝ)).toQuadraticMap')
      = sigPos ((M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') := by
  rw [sigNeg, toQuadraticMap'_neg_matrix, neg_neg]

/-- **Unimodularity is preserved by negation** (`det (−M) = (−1)^n · det M`, still a unit). -/
theorem isUnimodular_neg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} (hunim : IsUnimodular M) :
    IsUnimodular (-M) := by
  have hdet : (-M).det = (-1) ^ n * M.det := by simpa using Matrix.det_neg M
  simp only [IsUnimodular] at hunim ⊢
  rcases Nat.even_or_odd n with hp | hp
  · rw [hdet, hp.neg_one_pow, one_mul]; exact hunim
  · rw [hdet, hp.neg_one_pow]
    rcases hunim with h | h
    · exact Or.inr (by rw [h]; ring)
    · exact Or.inl (by rw [h]; ring)

/-- **An indefinite odd unimodular form of rank `≥ 5` represents `−1`, primitively.** Orientation
reversal of `odd_indefinite_represents_one`: apply it to `−M`, whose inertia indices are those of `M`
swapped (`sigPos_neg_matrix` / `sigNeg_neg_matrix`), whose diagonal is still odd, and which is still
symmetric and unimodular. Together the two give the "represents `±1`" input that the
Milnor–Husemoller induction peels `⟨1⟩` and `⟨−1⟩` with. -/
theorem odd_indefinite_represents_neg_one {m : ℕ} (hm : 5 ≤ m) (M : Matrix (Fin m) (Fin m) ℤ)
    (hsymm : Mᵀ = M) (hunim : IsUnimodular M) (i₀ : Fin m) (hodd : ¬ (2 ∣ M i₀ i₀))
    (hsp : 0 < sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
    (hsn : 0 < sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') :
    ∃ x : Fin m → ℤ, IsPrimitiveVec x ∧ x ⬝ᵥ M *ᵥ x = -1 := by
  have hsymm' : (-M)ᵀ = -M := by rw [Matrix.transpose_neg, hsymm]
  have hunim' : IsUnimodular (-M) := isUnimodular_neg hunim
  have hodd' : ¬ (2 ∣ (-M) i₀ i₀) := by
    simpa [Matrix.neg_apply, Int.dvd_neg] using hodd
  obtain ⟨x, hxprim, hxx⟩ := odd_indefinite_represents_one hm (-M) hsymm' hunim' i₀ hodd'
    (by rw [sigPos_neg_matrix]; exact hsn) (by rw [sigNeg_neg_matrix]; exact hsp)
  refine ⟨x, hxprim, ?_⟩
  have : x ⬝ᵥ (-M) *ᵥ x = -(x ⬝ᵥ M *ᵥ x) := by
    rw [Matrix.neg_mulVec, dotProduct_neg]
  omega

end SKEFTHawking
