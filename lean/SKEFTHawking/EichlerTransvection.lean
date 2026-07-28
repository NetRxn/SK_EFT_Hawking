/-
# Eichler transvections — integral isometries attached to an isotropic vector

For a symmetric integer form `M`, an `M`-isotropic vector `u` and a vector `x ⟂ u` whose
self-product is EVEN (`x ⬝ᵥ M *ᵥ x = 2 * h`), the **Eichler transvection**

  `E(z) = z + (x·z) u − (u·z) x − h (u·z) u`

is an integral isometry of `M` fixing `u`. It is the standard elementary move of unimodular-lattice
theory (Eichler, Kneser, Wall) and the only non-reflection generator the `StableNegRank16` route
needs: unlike a reflection it never divides, so integrality costs only the parity condition on
`x ⬝ᵥ M *ᵥ x`, which is automatic on an EVEN sublattice.

Encoded as an explicit matrix `eichler M u x h = 1 + u(Mx)ᵀ − x(Mu)ᵀ − h·u(Mu)ᵀ` so that it plugs
straight into `IntCongr` (`∃ P, IsUnit P.det ∧ Pᵀ M P = N`). The isometry identity is pure
outer-product algebra: with `p = M *ᵥ u`, `r = M *ᵥ x` and the three scalar side conditions
`u ⬝ᵥ p = 0`, `u ⬝ᵥ r = 0`, `x ⬝ᵥ r = 2h`, every mixed term collapses.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.AlgebraicRokhlin
import SKEFTHawking.HyperbolicNormalForm

namespace SKEFTHawking

open Matrix

/-! ### Outer-product toolkit -/

/-- The transpose of an outer product swaps the factors. -/
theorem transpose_vecMulVec {n : ℕ} (a b : Fin n → ℤ) :
    (Matrix.vecMulVec a b)ᵀ = Matrix.vecMulVec b a := by
  ext i j
  simp [Matrix.vecMulVec_apply, mul_comm]

/-- The product of two outer products contracts through the inner dot product. -/
theorem vecMulVec_mul_vecMulVec {n : ℕ} (a b c d : Fin n → ℤ) :
    Matrix.vecMulVec a b * Matrix.vecMulVec c d = (b ⬝ᵥ c) • Matrix.vecMulVec a d := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, dotProduct,
    smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => by ring

/-- Right multiplication of an outer product by a SYMMETRIC matrix. -/
theorem vecMulVec_mul_symm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} (hsymm : Mᵀ = M)
    (a b : Fin n → ℤ) : Matrix.vecMulVec a b * M = Matrix.vecMulVec a (M *ᵥ b) := by
  rw [Matrix.vecMulVec_mul, ← Matrix.vecMul_transpose, hsymm]

/-- An outer product applied to a vector is a rescaling. -/
theorem vecMulVec_mulVec {n : ℕ} (a b z : Fin n → ℤ) :
    Matrix.vecMulVec a b *ᵥ z = (b ⬝ᵥ z) • a := by
  ext i
  simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum, mul_comm,
    mul_left_comm]

/-! ### The transvection -/

/-- **The Eichler transvection matrix.** `eichler M u x h = 1 + u(Mx)ᵀ − x(Mu)ᵀ − h·u(Mu)ᵀ`, i.e.
`z ↦ z + (x·z)u − (u·z)x − h(u·z)u`. The parameter `h` is *half* the self-product of `x`; passing it
explicitly (rather than dividing) is what keeps the matrix integral. -/
def eichler {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (u x : Fin n → ℤ) (h : ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  1 + Matrix.vecMulVec u (M *ᵥ x) - Matrix.vecMulVec x (M *ᵥ u) - h • Matrix.vecMulVec u (M *ᵥ u)

/-- The action of `eichler` on a vector. -/
theorem eichler_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (u x : Fin n → ℤ) (h : ℤ)
    (z : Fin n → ℤ) :
    eichler M u x h *ᵥ z
      = z + ((M *ᵥ x) ⬝ᵥ z) • u - ((M *ᵥ u) ⬝ᵥ z) • x - (h * ((M *ᵥ u) ⬝ᵥ z)) • u := by
  simp only [eichler, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, vecMulVec_mulVec, smul_smul]

/-- The action of `eichler` written with all pairings in `_ ⬝ᵥ M *ᵥ _` form (needs `M` symmetric). -/
theorem eichler_mulVec_symm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (u x : Fin n → ℤ) (h : ℤ) (z : Fin n → ℤ) :
    eichler M u x h *ᵥ z
      = z + (x ⬝ᵥ M *ᵥ z) • u - (u ⬝ᵥ M *ᵥ z) • x - (h * (u ⬝ᵥ M *ᵥ z)) • u := by
  have hmv : ∀ y : Fin n → ℤ, (M *ᵥ y) ⬝ᵥ z = y ⬝ᵥ M *ᵥ z := fun y => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hsymm]
  rw [eichler_mulVec, hmv, hmv]

/-- **The Eichler transvection is an isometry.** Requires `M` symmetric, `u` isotropic, `x ⟂ u`,
and `x ⬝ᵥ M *ᵥ x = 2h`. -/
theorem eichler_isometry {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (u x : Fin n → ℤ) (h : ℤ) (huu : u ⬝ᵥ M *ᵥ u = 0) (hux : u ⬝ᵥ M *ᵥ x = 0)
    (hxx : x ⬝ᵥ M *ᵥ x = 2 * h) :
    (eichler M u x h)ᵀ * M * (eichler M u x h) = M := by
  set p := M *ᵥ u with hp
  set r := M *ᵥ x with hr
  have hMsymm : ∀ y : Fin n → ℤ, y ᵥ* M = M *ᵥ y := fun y => by
    rw [← Matrix.vecMul_transpose, hsymm]
  have hup : u ⬝ᵥ p = 0 := huu
  have hur : u ⬝ᵥ r = 0 := hux
  have hxr : x ⬝ᵥ r = 2 * h := hxx
  have hxp : x ⬝ᵥ p = 0 := by
    have hcomm : x ⬝ᵥ M *ᵥ u = u ⬝ᵥ M *ᵥ x := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hsymm, dotProduct_comm]
    rw [hp, hcomm]; exact hux
  have hEt : (eichler M u x h)ᵀ
      = 1 + Matrix.vecMulVec r u - Matrix.vecMulVec p x - h • Matrix.vecMulVec p u := by
    simp only [eichler, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_smul, transpose_vecMulVec, ← hp, ← hr]
  have hME : M * eichler M u x h
      = M + Matrix.vecMulVec p r - Matrix.vecMulVec r p - h • Matrix.vecMulVec p p := by
    simp only [eichler, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_vecMulVec, ← hp, ← hr]
  rw [hEt, Matrix.mul_assoc, hME]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, one_mul, Matrix.mul_add,
    Matrix.mul_sub, Matrix.mul_smul, vecMulVec_mul_symm hsymm, vecMulVec_mul_vecMulVec,
    ← hp, ← hr, hup, hur, hxr, hxp]
  simp only [zero_smul, smul_zero, sub_zero, add_zero]
  module

/-- **The Eichler transvection is unimodular.** Its determinant is `±1` because it preserves a
nondegenerate form; concretely `(det E)² · det M = det M` and `det M = ±1`. -/
theorem eichler_isUnit_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (hunim : IsUnimodular M) (u x : Fin n → ℤ) (h : ℤ) (huu : u ⬝ᵥ M *ᵥ u = 0)
    (hux : u ⬝ᵥ M *ᵥ x = 0) (hxx : x ⬝ᵥ M *ᵥ x = 2 * h) :
    IsUnit (eichler M u x h).det := by
  have hiso := eichler_isometry M hsymm u x h huu hux hxx
  have hdet := congrArg Matrix.det hiso
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  have hMne : M.det ≠ 0 := by rcases hunim with h1 | h1 <;> rw [h1] <;> norm_num
  have hsq : (eichler M u x h).det * (eichler M u x h).det = 1 := by
    have hz : M.det * ((eichler M u x h).det * (eichler M u x h).det - 1) = 0 := by
      linear_combination hdet
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact absurd h1 hMne
    · linarith [h1]
  exact ⟨Units.mkOfMulEqOne _ _ hsq, rfl⟩

/-- **`IntCongr` witness form**: an Eichler transvection exhibits `M ≅ M` by a change of basis that
moves vectors. Packaged for the descent, which needs both the isometry and the unimodularity. -/
theorem eichler_intCongr_self {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (hunim : IsUnimodular M) (u x : Fin n → ℤ) (h : ℤ) (huu : u ⬝ᵥ M *ᵥ u = 0)
    (hux : u ⬝ᵥ M *ᵥ x = 0) (hxx : x ⬝ᵥ M *ᵥ x = 2 * h) :
    IsUnit (eichler M u x h).det ∧ (eichler M u x h)ᵀ * M * (eichler M u x h) = M :=
  ⟨eichler_isUnit_det M hsymm hunim u x h huu hux hxx,
    eichler_isometry M hsymm u x h huu hux hxx⟩

/-! ### Eichler's criterion, STEP 2: the three-transvection chain

This is the geometric heart of Eichler's criterion (Gritsenko–Hulek–Sankaran, *Abelianisation of
orthogonal groups and the fundamental group of modular varieties*, J. Algebra 322 (2009) 463–478,
Prop. 3.3(i); attributed to Eichler, *Quadratische Formen und orthogonale Gruppen*, Grundlehren 63,
1952, Satz 10.4), specialized to the two CHARACTERISTIC self-product-`1` vectors that the
`⟨1⟩`-cancellation needs, and with all the divisibility bookkeeping already discharged.

Setting: `G` symmetric, `⟨e, f⟩` a hyperbolic plane (`e² = f² = 0`, `e·f = 1`), and `w, w'` two vectors
of self-product `1` BOTH orthogonal to that plane, with `w − w' = 2k` and `k·k` EVEN. Then three
explicit Eichler transvections carry `w` to `w'`:

  `w  --t(e, 2w)-->  w + 2e  --t(f, k)-->  w' + 2e  --t(e, −2w')-->  w'`.

Each hypothesis is consumed exactly once: the hyperbolic plane makes `(f, w + 2e) = 2 ≠ 0` so the middle
transvection can move by `−2k = w' − w`; `w·w = w'·w'` is what makes the leftover `f`-coefficient of the
middle arrow VANISH (it equals `k·w − k·k`, and the two norms being equal forces `k·w = k·k`); and
`k·k` even is exactly the integrality of the middle transvection — in the `⟨1⟩`-cancellation it is the
statement `w·w' ≡ 1 (mod 4)`, arranged by replacing `w'` with `−w'` (which has the same orthogonal
complement).

**STEP 1 of the criterion is NOT here**: getting `w' ⟂ ⟨e, f⟩` in the first place requires the
`SO⁺(U ⊕ U₁) ≅ (SL₂ ℤ × SL₂ ℤ)/±` normalisation (a 2×2 Smith normal form over the two hyperbolic
planes), and hence a SECOND hyperbolic plane orthogonal to the first — which is why the interior brick
must be stated at rank 20 (inertia `(2, 18)`), not rank 18 (inertia `(1, 17)`, the Lorentzian
`II_{1,17}`, where `2U` cannot split and the classical proofs need the spinor genus). -/
theorem exists_isometry_map_of_perp_hyp {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hsymm : Gᵀ = G)
    (hunim : IsUnimodular G) (e f w w' k : Fin n → ℤ) (m : ℤ)
    (hee : e ⬝ᵥ G *ᵥ e = 0) (hff : f ⬝ᵥ G *ᵥ f = 0) (hef : e ⬝ᵥ G *ᵥ f = 1)
    (hww : w ⬝ᵥ G *ᵥ w = 1) (hw'w' : w' ⬝ᵥ G *ᵥ w' = 1)
    (hew : e ⬝ᵥ G *ᵥ w = 0) (hfw : f ⬝ᵥ G *ᵥ w = 0)
    (hew' : e ⬝ᵥ G *ᵥ w' = 0) (hfw' : f ⬝ᵥ G *ᵥ w' = 0)
    (hk : w - w' = (2 : ℤ) • k) (hkk : k ⬝ᵥ G *ᵥ k = 2 * m) :
    ∃ T : Matrix (Fin n) (Fin n) ℤ, IsUnit T.det ∧ Tᵀ * G * T = G ∧ T *ᵥ w = w' := by
  -- bilinearity toolkit for `x ⬝ᵥ G *ᵥ y`
  have hcomm : ∀ x y : Fin n → ℤ, x ⬝ᵥ G *ᵥ y = y ⬝ᵥ G *ᵥ x := fun x y => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hsymm, dotProduct_comm]
  have hsmr : ∀ (c : ℤ) (x y : Fin n → ℤ), x ⬝ᵥ G *ᵥ (c • y) = c * (x ⬝ᵥ G *ᵥ y) :=
    fun c x y => by rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hsml : ∀ (c : ℤ) (x y : Fin n → ℤ), (c • x) ⬝ᵥ G *ᵥ y = c * (x ⬝ᵥ G *ᵥ y) :=
    fun c x y => by rw [smul_dotProduct, smul_eq_mul]
  have hadr : ∀ x y z : Fin n → ℤ, x ⬝ᵥ G *ᵥ (y + z) = x ⬝ᵥ G *ᵥ y + x ⬝ᵥ G *ᵥ z :=
    fun x y z => by rw [Matrix.mulVec_add, dotProduct_add]
  have hsbl : ∀ x y z : Fin n → ℤ, (x - y) ⬝ᵥ G *ᵥ z = x ⬝ᵥ G *ᵥ z - y ⬝ᵥ G *ᵥ z :=
    fun x y z => by rw [sub_dotProduct]
  have hsbr : ∀ x y z : Fin n → ℤ, x ⬝ᵥ G *ᵥ (y - z) = x ⬝ᵥ G *ᵥ y - x ⬝ᵥ G *ᵥ z :=
    fun x y z => by rw [Matrix.mulVec_sub, dotProduct_sub]
  have hngl : ∀ x y : Fin n → ℤ, (-x) ⬝ᵥ G *ᵥ y = -(x ⬝ᵥ G *ᵥ y) :=
    fun x y => by rw [neg_dotProduct]
  -- `k` inherits orthogonality to the hyperbolic plane from `w` and `w'`
  have hek : e ⬝ᵥ G *ᵥ k = 0 := by
    have h1 : e ⬝ᵥ G *ᵥ (w - w') = e ⬝ᵥ G *ᵥ ((2 : ℤ) • k) := by rw [hk]
    rw [hsbr, hsmr, hew, hew'] at h1; linarith
  have hfk : f ⬝ᵥ G *ᵥ k = 0 := by
    have h1 : f ⬝ᵥ G *ᵥ (w - w') = f ⬝ᵥ G *ᵥ ((2 : ℤ) • k) := by rw [hk]
    rw [hsbr, hsmr, hfw, hfw'] at h1; linarith
  have hke : k ⬝ᵥ G *ᵥ e = 0 := by rw [hcomm]; exact hek
  have hwe : w' ⬝ᵥ G *ᵥ e = 0 := by rw [hcomm]; exact hew'
  have hfe : f ⬝ᵥ G *ᵥ e = 1 := by rw [hcomm]; exact hef
  -- the norm hypothesis `w·w = w'·w'` forces `k·w = k·k = 2m`
  have hkwk : k ⬝ᵥ G *ᵥ w = 2 * m := by
    have h1 : (w - w') ⬝ᵥ G *ᵥ w = ((2 : ℤ) • k) ⬝ᵥ G *ᵥ w := by rw [hk]
    have h2 : (w - w') ⬝ᵥ G *ᵥ (w - w') = ((2 : ℤ) • k) ⬝ᵥ G *ᵥ ((2 : ℤ) • k) := by rw [hk]
    have hsym2 : w' ⬝ᵥ G *ᵥ w = w ⬝ᵥ G *ᵥ w' := hcomm w' w
    rw [hsbl, hsml, hww] at h1
    rw [hsbl, hsbr, hsbr, hsml, hsmr, hkk, hww, hw'w', hcomm w' w] at h2
    linarith
  -- the three transvections
  set E₁ := eichler G e ((2 : ℤ) • w) 2 with hE₁
  set E₂ := eichler G f k m with hE₂
  set E₃ := eichler G e (-((2 : ℤ) • w')) 2 with hE₃
  have hx1 : ((2 : ℤ) • w) ⬝ᵥ G *ᵥ ((2 : ℤ) • w) = 2 * 2 := by
    rw [hsml, hsmr, hww]; ring
  have hu1 : e ⬝ᵥ G *ᵥ ((2 : ℤ) • w) = 0 := by rw [hsmr, hew]; ring
  have hx3 : (-((2 : ℤ) • w')) ⬝ᵥ G *ᵥ (-((2 : ℤ) • w')) = 2 * 2 := by
    rw [hngl, Matrix.mulVec_neg, dotProduct_neg, hsml, hsmr, hw'w']; ring
  have hu3 : e ⬝ᵥ G *ᵥ (-((2 : ℤ) • w')) = 0 := by
    rw [Matrix.mulVec_neg, dotProduct_neg, hsmr, hew']; ring
  -- arrow 1: `w ↦ w + 2e`
  have ha1 : E₁ *ᵥ w = w + (2 : ℤ) • e := by
    rw [hE₁, eichler_mulVec_symm G hsymm, hew, hsml, hww]
    simp only [mul_zero, zero_smul, sub_zero]
    module
  -- arrow 2: `w + 2e ↦ w' + 2e` (the `f`-coefficient cancels because `k·w = k·k`)
  have ha2 : E₂ *ᵥ (w + (2 : ℤ) • e) = w' + (2 : ℤ) • e := by
    have hfz : f ⬝ᵥ G *ᵥ (w + (2 : ℤ) • e) = 2 := by
      rw [hadr, hfw, hsmr, hfe]; ring
    have hkz : k ⬝ᵥ G *ᵥ (w + (2 : ℤ) • e) = 2 * m := by
      rw [hadr, hkwk, hsmr, hke]; ring
    rw [hE₂, eichler_mulVec_symm G hsymm, hfz, hkz]
    have hstep : w + (2 : ℤ) • e + (2 * m) • f - (2 : ℤ) • k - (m * 2) • f
        = w - (w - w') + (2 : ℤ) • e := by rw [← hk]; module
    rw [hstep]; module
  -- arrow 3: `w' + 2e ↦ w'`
  have ha3 : E₃ *ᵥ (w' + (2 : ℤ) • e) = w' := by
    have hez : e ⬝ᵥ G *ᵥ (w' + (2 : ℤ) • e) = 0 := by
      rw [hadr, hew', hsmr, hee]; ring
    have hxz : (-((2 : ℤ) • w')) ⬝ᵥ G *ᵥ (w' + (2 : ℤ) • e) = -2 := by
      rw [hngl, hadr, hsml, hsml, hw'w', hsmr, hwe]; ring
    rw [hE₃, eichler_mulVec_symm G hsymm, hez, hxz]
    simp only [mul_zero, zero_smul, sub_zero]
    module
  -- assemble
  refine ⟨E₃ * (E₂ * E₁), ?_, ?_, ?_⟩
  · have h1 := eichler_isUnit_det G hsymm hunim e ((2 : ℤ) • w) 2 hee hu1 hx1
    have h2 := eichler_isUnit_det G hsymm hunim f k m hff hfk hkk
    have h3 := eichler_isUnit_det G hsymm hunim e (-((2 : ℤ) • w')) 2 hee hu3 hx3
    rw [Matrix.det_mul, Matrix.det_mul]
    exact h3.mul (h2.mul h1)
  · have h1 := eichler_isometry G hsymm e ((2 : ℤ) • w) 2 hee hu1 hx1
    have h2 := eichler_isometry G hsymm f k m hff hfk hkk
    have h3 := eichler_isometry G hsymm e (-((2 : ℤ) • w')) 2 hee hu3 hx3
    rw [← hE₁] at h1; rw [← hE₂] at h2; rw [← hE₃] at h3
    calc (E₃ * (E₂ * E₁))ᵀ * G * (E₃ * (E₂ * E₁))
        = E₁ᵀ * (E₂ᵀ * (E₃ᵀ * G * E₃) * E₂) * E₁ := by
          simp only [Matrix.transpose_mul]; noncomm_ring
      _ = G := by rw [h3, h2, h1]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha1, ha2, ha3]

end SKEFTHawking
