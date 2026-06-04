/-
Phase 5q.B: primitive integer vectors and the dual-vector lemma — first brick of the classification
scaffolding ([E1] in `Phase5qB_LabNotebook.md`).

The classification of even unimodular lattices (the remaining input to van der Blij `8 ∣ σ`) proceeds by
*splitting off a hyperbolic plane* `H` from a primitive isotropic vector. That construction needs, as its
very first step, that a primitive vector pairs to `1` with some other vector: `∃ w, ⟨v, w⟩ = 1`. Mathlib has
no primitive-vector API, so we build it here.

We define `IsPrimitiveVec v` as `1 ∈ span_ℤ (range v)` (equivalently, the coordinates of `v` generate ℤ,
i.e. their gcd is `1`), and prove:
* `isPrimitiveVec_iff_exists_dot` — `IsPrimitiveVec v ↔ ∃ w, v ⬝ᵥ w = 1` (Bezout for tuples).
* `exists_vecMul_dot_eq_one` — for a unimodular `M`, the covector `v ᵥ* M` of a primitive `v` also pairs to
  `1`: `∃ w, (v ᵥ* M) ⬝ᵥ w = 1`. This is the form used in the H-splitting: with `M` the Gram matrix it gives
  `w` with `vᵀ M w = 1`, the partner of the isotropic vector spanning the hyperbolic plane.

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.AlgebraicRokhlin
import SKEFTHawking.EvenLatticeForm

namespace SKEFTHawking

open Matrix

/-- A vector `v : Fin n → ℤ` is **primitive** when `1` lies in the ℤ-span of its coordinate values
(equivalently, the gcd of its entries is `1`). -/
def IsPrimitiveVec {n : ℕ} (v : Fin n → ℤ) : Prop := (1 : ℤ) ∈ Submodule.span ℤ (Set.range v)

/-- **Bezout for tuples:** `v` is primitive iff some integer vector pairs with it to give `1`. -/
theorem isPrimitiveVec_iff_exists_dot {n : ℕ} (v : Fin n → ℤ) :
    IsPrimitiveVec v ↔ ∃ w, v ⬝ᵥ w = 1 := by
  constructor
  · intro h
    rw [IsPrimitiveVec, Finsupp.mem_span_range_iff_exists_finsupp] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨fun i => c i, by rw [dotProduct, ← hc, Finsupp.sum_fintype] <;> simp [mul_comm]⟩
  · rintro ⟨w, hw⟩
    rw [IsPrimitiveVec, Finsupp.mem_span_range_iff_exists_finsupp]
    exact ⟨(Finsupp.equivFunOnFinite.symm (fun i => w i)), by
      rw [Finsupp.sum_fintype] <;> simp [← hw, dotProduct, mul_comm]⟩

/-- **The covector of a primitive vector through a unimodular matrix is again primitive.** For unimodular
`M`, a primitive `v` gives `w` with `(v ᵥ* M) ⬝ᵥ w = 1` (take `w = M⁻¹ ·ᵥ u` where `v ⬝ᵥ u = 1`). With `M`
the Gram matrix this produces the hyperbolic partner of an isotropic vector. -/
theorem exists_vecMul_dot_eq_one {n : ℕ} (v : Fin n → ℤ) (M : Matrix (Fin n) (Fin n) ℤ)
    (hv : IsPrimitiveVec v) (hM : IsUnimodular M) : ∃ w, (v ᵥ* M) ⬝ᵥ w = 1 := by
  obtain ⟨u, hu⟩ := (isPrimitiveVec_iff_exists_dot v).mp hv
  have hunit : IsUnit M.det := Int.isUnit_iff.mpr hM
  refine ⟨M⁻¹ *ᵥ u, ?_⟩
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv M hunit,
    Matrix.vecMul_one]
  exact hu

/-- **The hyperbolic pair.** From a primitive isotropic vector `v` of an even unimodular form `M`, produce
`w'` so that `{v, w'}` has Gram matrix `H = [[0,1],[1,0]]`: both `v` and `w'` are isotropic
(`vᵀMv = w'ᵀMw' = 0`) and they pair to `1` (`vᵀMw' = 1`). Construct the partner `w` with `vᵀMw = 1`
(`exists_vecMul_dot_eq_one`), then correct it to `w' = w − (wᵀMw/2)·v` — integral since `wᵀMw` is even
(`even_form_dvd`) — which zeroes `w'ᵀMw'` while preserving `vᵀMw' = 1`. This is the heart of the
hyperbolic-plane splitting ([E2]); what remains is to extend `{v, w'}` to a ℤ-basis and read off the
orthogonal complement. -/
theorem exists_hyperbolic_pair {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : Mᵀ = M) (heven : ∀ i, 2 ∣ M i i) (v : Fin n → ℤ)
    (hv : IsPrimitiveVec v) (hiso : v ⬝ᵥ M *ᵥ v = 0) (hM : IsUnimodular M) :
    ∃ w', v ⬝ᵥ M *ᵥ v = 0 ∧ v ⬝ᵥ M *ᵥ w' = 1 ∧ w' ⬝ᵥ M *ᵥ w' = 0 := by
  obtain ⟨w, hw⟩ := exists_vecMul_dot_eq_one v M hv hM
  have hvw : v ⬝ᵥ M *ᵥ w = 1 := by rw [Matrix.dotProduct_mulVec]; exact hw
  have hwv : w ⬝ᵥ M *ᵥ v = 1 := by
    rw [show w ⬝ᵥ M *ᵥ v = v ⬝ᵥ M *ᵥ w from by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]]
    exact hvw
  obtain ⟨k, hk⟩ := EvenLattice.even_form_dvd hsymm heven w
  refine ⟨w - k • v, hiso, ?_, ?_⟩
  · rw [Matrix.mulVec_sub, dotProduct_sub, hvw, Matrix.mulVec_smul, dotProduct_smul, hiso]
    simp
  · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct, sub_dotProduct,
      smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_dotProduct, hiso, hvw, hwv, hk]
    ring

/-- **Orthogonal projection onto the hyperbolic complement `K^⊥`.** For a hyperbolic pair `{v, w'}`
(`vᵀMv = 0`, `vᵀMw' = 1`, `w'ᵀMw' = 0` — the output of `exists_hyperbolic_pair`), the map
`q(x) = x − (vᵀMx)·w' − (w'ᵀMx)·v` lands every `x` in the orthogonal complement
`K^⊥ = {y | vᵀMy = 0 ∧ w'ᵀMy = 0}`. This is the splitting `ℤⁿ = K ⊕ K^⊥` of the H-duality projection: `q`
is the projector onto `K^⊥`, leaving the residual form `M|_{K^⊥} = M'` such that `M ≅ H ⊕ M'`. Completing
[E2] requires only a ℤ-basis of `K^⊥` (free of rank `n−2`; Smith Normal Form) to assemble the concrete
unimodular change of basis. -/
theorem hyperbolic_proj_ortho {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (v w' : Fin n → ℤ) (hv0 : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w' = 1)
    (hw0 : w' ⬝ᵥ M *ᵥ w' = 0) (x : Fin n → ℤ) :
    v ⬝ᵥ M *ᵥ (x - (v ⬝ᵥ M *ᵥ x) • w' - (w' ⬝ᵥ M *ᵥ x) • v) = 0 ∧
    w' ⬝ᵥ M *ᵥ (x - (v ⬝ᵥ M *ᵥ x) • w' - (w' ⬝ᵥ M *ᵥ x) • v) = 0 := by
  have hwv : w' ⬝ᵥ M *ᵥ v = 1 := by
    rw [show w' ⬝ᵥ M *ᵥ v = v ⬝ᵥ M *ᵥ w' from by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]]
    exact hvw
  refine ⟨?_, ?_⟩
  · rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul, hvw, hv0]
    ring
  · rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul, hw0, hwv]
    ring

/-- **The projection onto `K = span{v,w'}` is idempotent.** With `p(x) = (w'ᵀMx)·v + (vᵀMx)·w'` (the
complement of `hyperbolic_proj_ortho`'s `q = id − p`), `p(p x) = p x`. So `p` is the projector onto the
hyperbolic plane `K` along `K^⊥`, and `q = id − p` is the projector onto `K^⊥`; together they realise the
direct-sum splitting `ℤⁿ = K ⊕ K^⊥` underlying `M ≅ H ⊕ M'`. -/
theorem hyperbolic_proj_idem {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (v w' : Fin n → ℤ) (hv0 : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w' = 1)
    (hw0 : w' ⬝ᵥ M *ᵥ w' = 0) (x : Fin n → ℤ) :
    (w' ⬝ᵥ M *ᵥ ((w' ⬝ᵥ M *ᵥ x) • v + (v ⬝ᵥ M *ᵥ x) • w')) • v
      + (v ⬝ᵥ M *ᵥ ((w' ⬝ᵥ M *ᵥ x) • v + (v ⬝ᵥ M *ᵥ x) • w')) • w'
    = (w' ⬝ᵥ M *ᵥ x) • v + (v ⬝ᵥ M *ᵥ x) • w' := by
  have hwv : w' ⬝ᵥ M *ᵥ v = 1 := by
    rw [show w' ⬝ᵥ M *ᵥ v = v ⬝ᵥ M *ᵥ w' from by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]]
    exact hvw
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_add, dotProduct_add,
    dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul, hv0, hvw, hw0, hwv]
  module

/-- The **orthogonal complement** `K^⊥ = {x | vᵀMx = 0 ∧ w'ᵀMx = 0}` of a hyperbolic pair, as a
submodule of `ℤⁿ`. -/
def hypPerp {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v w' : Fin n → ℤ) :
    Submodule ℤ (Fin n → ℤ) where
  carrier := {x | v ⬝ᵥ M *ᵥ x = 0 ∧ w' ⬝ᵥ M *ᵥ x = 0}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩ <;> rw [Matrix.mulVec_add, dotProduct_add] <;> simp_all
  zero_mem' := by simp
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩ <;> rw [Matrix.mulVec_smul, dotProduct_smul] <;> simp_all

/-- **The direct-sum splitting `ℤⁿ = K ⊕ K^⊥`.** For a hyperbolic pair `{v, w'}` (Gram `H`) of an even
unimodular form, the rank-2 hyperbolic sublattice `K = span{v, w'}` and its orthogonal complement
`K^⊥ = hypPerp` are complementary (`IsCompl`): disjointness because `x = a·v + b·w' ∈ K^⊥` forces
`a = b = 0` (pairing with `v, w'` and the `H` Gram), and codisjointness because every `x` splits as
`p(x) + q(x)` with `p(x) ∈ K` and `q(x) = x − p(x) ∈ K^⊥` (`hyperbolic_proj_ortho`). This is the lattice
decomposition underlying `M ≅ H ⊕ M'`; the residual `M' = M|_{K^⊥}` is read off once a ℤ-basis of `K^⊥`
(free of rank `n − 2`) is chosen. -/
theorem hyperbolic_isCompl {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v w' : Fin n → ℤ) (hsymm : Mᵀ = M)
    (hv0 : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w' = 1) (hw0 : w' ⬝ᵥ M *ᵥ w' = 0) :
    IsCompl (Submodule.span ℤ {v, w'}) (hypPerp M v w') := by
  have hwv : w' ⬝ᵥ M *ᵥ v = 1 := by
    rw [show w' ⬝ᵥ M *ᵥ v = v ⬝ᵥ M *ᵥ w' from by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]]
    exact hvw
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxK hxP
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hxK
    obtain ⟨h1, h2⟩ := hxP
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_add,
      dotProduct_smul, dotProduct_smul, hv0, hvw] at h1
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_add,
      dotProduct_smul, dotProduct_smul, hwv, hw0] at h2
    simp only [smul_eq_mul, mul_zero, mul_one, add_zero, zero_add] at h1 h2
    rw [h1, h2]; simp
  · rw [codisjoint_iff_le_sup]
    intro x _
    rw [Submodule.mem_sup]
    refine ⟨(w' ⬝ᵥ M *ᵥ x) • v + (v ⬝ᵥ M *ᵥ x) • w', ?_,
            x - ((w' ⬝ᵥ M *ᵥ x) • v + (v ⬝ᵥ M *ᵥ x) • w'), ?_, by abel⟩
    · exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · have hortho := hyperbolic_proj_ortho M hsymm v w' hv0 hvw hw0 x
      have hrw : x - ((w' ⬝ᵥ M *ᵥ x) • v + (v ⬝ᵥ M *ᵥ x) • w')
          = x - (v ⬝ᵥ M *ᵥ x) • w' - (w' ⬝ᵥ M *ᵥ x) • v := by abel
      exact ⟨by rw [hrw]; exact hortho.1, by rw [hrw]; exact hortho.2⟩

/-- A hyperbolic pair `{v, w'}` (Gram `H`) is **linearly independent** over ℤ: pairing `s·v + t·w' = 0`
with `v` and `w'` through `M` and using `vᵀMv = 0`, `vᵀMw' = 1`, `w'ᵀMw' = 0` forces `s = t = 0`. -/
theorem hyperbolic_linearIndependent {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (v w' : Fin n → ℤ) (hv0 : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w' = 1)
    (hw0 : w' ⬝ᵥ M *ᵥ w' = 0) : LinearIndependent ℤ ![v, w'] := by
  have hwv : w' ⬝ᵥ M *ᵥ v = 1 := by
    rw [show w' ⬝ᵥ M *ᵥ v = v ⬝ᵥ M *ᵥ w' from by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]]
    exact hvw
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (fun y => v ⬝ᵥ M *ᵥ y) hst
  have h2 := congrArg (fun y => w' ⬝ᵥ M *ᵥ y) hst
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
    Matrix.mulVec_zero, dotProduct_zero, smul_eq_mul, hv0, hvw, hw0, hwv] at h1 h2
  constructor <;> [skip; skip] <;> omega

/-- The hyperbolic complement `K^⊥ = hypPerp` is **free of rank `n − 2`**: it is a direct summand of the
free module `ℤⁿ` (by `hyperbolic_isCompl`), and `K = span{v, w'}` has rank 2
(`hyperbolic_linearIndependent`), so `finrank K^⊥ = n − 2`. This is the rank bookkeeping that lets the
residual form `M' = M|_{K^⊥}` be presented as an `(n−2) × (n−2)` integer Gram matrix. -/
theorem hypPerp_finrank {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v w' : Fin n → ℤ)
    (hindep : LinearIndependent ℤ ![v, w'])
    (hic : IsCompl (Submodule.span ℤ {v, w'}) (hypPerp M v w')) :
    Module.finrank ℤ (hypPerp M v w') = n - 2 := by
  have hspan : Submodule.span ℤ {v, w'} = Submodule.span ℤ (Set.range ![v, w']) := by
    congr 1; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range,
      Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; tauto
  have hK : Module.finrank ℤ (Submodule.span ℤ {v, w'}) = 2 := by
    rw [hspan, finrank_span_eq_card hindep]; simp
  have hprod := (Submodule.prodEquivOfIsCompl _ _ hic).finrank_eq
  rw [Module.finrank_prod, hK] at hprod
  have hn : Module.finrank ℤ (Fin n → ℤ) = n := by simp
  rw [hn] at hprod
  omega

/-- A concrete ℤ-basis of the hyperbolic complement `K^⊥`, indexed by `Fin (n−2)` (using that `K^⊥` is
free of rank `n−2`, `hypPerp_finrank`). The columns of this basis, together with `v` and `w'`, will form
the unimodular change of basis realising `M ≅ H ⊕ M'`. -/
noncomputable def hypPerpBasis {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v w' : Fin n → ℤ)
    (hfr : Module.finrank ℤ (hypPerp M v w') = n - 2) :
    Module.Basis (Fin (n - 2)) ℤ (hypPerp M v w') :=
  (Module.finBasis ℤ (hypPerp M v w')).reindex (finCongr hfr)

/-- Each `K^⊥`-basis vector is orthogonal (through `M`) to both `v` and `w'` — immediate from membership in
`hypPerp`. This is the orthogonality that makes the Gram matrix block-diagonal `H ⊕ M'` in the combined basis. -/
theorem hypPerpBasis_ortho {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v w' : Fin n → ℤ)
    (hfr : Module.finrank ℤ (hypPerp M v w') = n - 2) (i : Fin (n - 2)) :
    v ⬝ᵥ M *ᵥ ((hypPerpBasis M v w' hfr i : Fin n → ℤ)) = 0 ∧
    w' ⬝ᵥ M *ᵥ ((hypPerpBasis M v w' hfr i : Fin n → ℤ)) = 0 :=
  (hypPerpBasis M v w' hfr i).2

/-- The **combined basis of `ℤⁿ`** adapted to the splitting `ℤⁿ = K ⊕ K^⊥`: the hyperbolic pair `{v, w'}`
(basis of `K`) together with `hypPerpBasis` (basis of `K^⊥`), assembled via `Submodule.prodEquivOfIsCompl`
over `hyperbolic_isCompl`. Indexed by `Fin 2 ⊕ Fin (n−2)`. The change-of-basis matrix to this basis is
unimodular, and the Gram of `M` in it is block-diagonal `H ⊕ M'` (off-diagonal blocks vanish by
`hypPerpBasis_ortho`) — the realisation of `M ≅ H ⊕ M'`. -/
noncomputable def hypFullBasis {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v w' : Fin n → ℤ)
    (hsymm : Mᵀ = M) (hv0 : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w' = 1) (hw0 : w' ⬝ᵥ M *ᵥ w' = 0)
    (hfr : Module.finrank ℤ (hypPerp M v w') = n - 2) :
    Module.Basis (Fin 2 ⊕ Fin (n - 2)) ℤ (Fin n → ℤ) :=
  let hindep := hyperbolic_linearIndependent M hsymm v w' hv0 hvw hw0
  let hic := hyperbolic_isCompl M v w' hsymm hv0 hvw hw0
  have hspan : Submodule.span ℤ {v, w'} = Submodule.span ℤ (Set.range ![v, w']) := by
    congr 1; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range,
      Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]; tauto
  let bK : Module.Basis (Fin 2) ℤ ↥(Submodule.span ℤ {v, w'}) :=
    (Module.Basis.span hindep).map (LinearEquiv.ofEq _ _ hspan.symm)
  (bK.prod (hypPerpBasis M v w' hfr)).map (Submodule.prodEquivOfIsCompl _ _ hic)

/-- The `K`-part of `hypFullBasis` is the hyperbolic pair: `B (inl k) = ![v, w'] k`. -/
theorem hypFullBasis_inl {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v w' : Fin n → ℤ)
    (hsymm : Mᵀ = M) (hv0 : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w' = 1) (hw0 : w' ⬝ᵥ M *ᵥ w' = 0)
    (hfr : Module.finrank ℤ (hypPerp M v w') = n - 2) (k : Fin 2) :
    (hypFullBasis M v w' hsymm hv0 hvw hw0 hfr (Sum.inl k) : Fin n → ℤ) = ![v, w'] k := by
  simp only [hypFullBasis, Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inl,
    Function.comp_apply, LinearMap.inl_apply]
  rw [Submodule.prodEquivOfIsCompl]
  simp [LinearMap.coprod_apply, Module.Basis.span_apply]

/-- The `K^⊥`-part of `hypFullBasis` is the `hypPerpBasis`: `B (inr i) = hypPerpBasis i`. -/
theorem hypFullBasis_inr {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v w' : Fin n → ℤ)
    (hsymm : Mᵀ = M) (hv0 : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w' = 1) (hw0 : w' ⬝ᵥ M *ᵥ w' = 0)
    (hfr : Module.finrank ℤ (hypPerp M v w') = n - 2) (i : Fin (n - 2)) :
    (hypFullBasis M v w' hsymm hv0 hvw hw0 hfr (Sum.inr i) : Fin n → ℤ)
      = (hypPerpBasis M v w' hfr i : Fin n → ℤ) := by
  simp only [hypFullBasis, Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inr,
    Function.comp_apply, LinearMap.inr_apply]
  rw [Submodule.prodEquivOfIsCompl]
  simp [LinearMap.coprod_apply]

/-- The **residual Gram matrix** `M'` of `M` restricted to `K^⊥` in the `hypPerpBasis`:
`M' i j = (bᵢ)ᵀ M (bⱼ)` for the `K^⊥`-basis vectors `bᵢ`. This is the `(n−2) × (n−2)` block of the
block-diagonal form `H ⊕ M'` in the combined basis. -/
noncomputable def residGram {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v w' : Fin n → ℤ)
    (hfr : Module.finrank ℤ (hypPerp M v w') = n - 2) : Matrix (Fin (n - 2)) (Fin (n - 2)) ℤ :=
  fun i j => (hypPerpBasis M v w' hfr i : Fin n → ℤ) ⬝ᵥ M *ᵥ (hypPerpBasis M v w' hfr j : Fin n → ℤ)

/-- The residual form `M'` is **symmetric** (inherited from `M`). -/
theorem residGram_symm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M) (v w' : Fin n → ℤ)
    (hfr : Module.finrank ℤ (hypPerp M v w') = n - 2) :
    (residGram M v w' hfr)ᵀ = residGram M v w' hfr := by
  ext i j
  show (hypPerpBasis M v w' hfr j : Fin n → ℤ) ⬝ᵥ M *ᵥ _
      = (hypPerpBasis M v w' hfr i : Fin n → ℤ) ⬝ᵥ M *ᵥ _
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]

/-- The residual form `M'` is **even** (inherited from `M` via `even_form_dvd`). Together with
`residGram_symm` this maintains the even-symmetric invariant for the split-off-H induction (unimodularity
of `M'` follows from the unimodular change of basis, the remaining assembly step). -/
theorem residGram_even {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (heven : ∀ i, 2 ∣ M i i) (v w' : Fin n → ℤ)
    (hfr : Module.finrank ℤ (hypPerp M v w') = n - 2) (i : Fin (n - 2)) :
    2 ∣ residGram M v w' hfr i i :=
  EvenLattice.even_form_dvd hsymm heven _

end SKEFTHawking
