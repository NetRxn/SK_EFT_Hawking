import SKEFTHawking.LindbladSemigroup
import Mathlib.Analysis.Matrix.Normed

/-!
# GKSL CP-semigroup theorem (Phase 6BC Wave 5 / D10 Discharge W4) — discharge of `hreal`

`LindbladSemigroup.lean` proved trace-distance contractivity of the GKSL dynamical map
`Λ_t = e^{tℒ}` *conditionally* on a disclosed hypothesis `hreal`: that `Λ_t` is realized by a Kraus
channel (its complete positivity, the physical content of the GKSL theorem). This module discharges
`hreal` by **proving** that `Λ_t` is completely positive — hence (finite-dimensional Choi/Kraus
theorem) a Kraus channel — so the contraction becomes unconditional.

The route (Lie–Trotter): `ℒ = ℒ_jump + ℒ_drift` with `ℒ_jump` the dissipator (completely positive,
`lindblad_generator_CP`) and `ℒ_drift(ρ) = Gρ + ρG†` a conjugation generator (so `e^{sℒ_drift}` is
conjugation by `e^{sG}`, completely positive). Each Trotter factor `e^{(t/n)ℒ_drift} e^{(t/n)ℒ_jump}`
is CP; `e^{tℒ} = lim_n (e^{(t/n)ℒ_drift} e^{(t/n)ℒ_jump})^n` (matrix Lie–Trotter — built from scratch,
absent from Mathlib); CP is closed under limits (Choi matrix PSD, and the PSD cone is closed). Hence
`e^{tℒ}` is CP.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; zero `sorry`; no new axiom;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.OpenSystems

open scoped Matrix ComplexOrder Matrix.Norms.Operator
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- **The positive-semidefinite cone is closed.** A limit of positive-semidefinite matrices is
positive semidefinite — the topological input to "complete positivity is closed under limits". -/
lemma posSemidef_of_tendsto {A : ℕ → Matrix n n ℂ} {L : Matrix n n ℂ}
    (hA : Filter.Tendsto A Filter.atTop (nhds L)) (hpsd : ∀ k, (A k).PosSemidef) :
    L.PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · have hconj : Filter.Tendsto (fun k => (A k)ᴴ) Filter.atTop (nhds Lᴴ) :=
      (Continuous.tendsto (f := fun B : Matrix n n ℂ => Bᴴ) (by fun_prop) L).comp hA
    rw [show (fun k => (A k)ᴴ) = A from funext fun k => (hpsd k).1] at hconj
    exact tendsto_nhds_unique hconj hA
  · have hcont : Continuous (fun B : Matrix n n ℂ =>
        x.sum fun i xi => x.sum fun j xj => star xi * B i j * xj) := by
      simp only [Finsupp.sum]
      exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => by fun_prop
    exact ge_of_tendsto' ((hcont.tendsto L).comp hA) fun k => (hpsd k).2 x

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

omit [DecidableEq B] in
/-- **Complete positivity is closed under limits.** If the Choi matrices of a sequence of completely
positive maps converge to the Choi matrix of `N`, then `N` is completely positive — via Choi's theorem
(CP ⟺ Choi PSD) and the closed PSD cone (`posSemidef_of_tendsto`). -/
lemma isCompletelyPositive_of_tendsto_choi {M : ℕ → MatrixMap A B ℂ} {N : MatrixMap A B ℂ}
    (hchoi : Filter.Tendsto (fun k => (M k).choi_matrix) Filter.atTop (nhds N.choi_matrix))
    (hcp : ∀ k, (M k).IsCompletelyPositive) :
    N.IsCompletelyPositive :=
  (MatrixMap.choi_PSD_iff_CP_map N).mpr
    (posSemidef_of_tendsto hchoi fun k => (MatrixMap.choi_PSD_iff_CP_map (M k)).mp (hcp k))

/-- **Powers of a completely positive endomorphism are completely positive** (the terms of the
exponential series). -/
lemma isCompletelyPositive_pow {M : MatrixMap A A ℂ} (hM : M.IsCompletelyPositive) :
    ∀ k : ℕ, (M ^ k).IsCompletelyPositive
  | 0 => by rw [pow_zero]; exact MatrixMap.IsCompletelyPositive.id
  | k + 1 => by rw [pow_succ]; exact hM.comp (isCompletelyPositive_pow hM k)

section ExpCP
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- `Matrix.toLin` (same basis) carries matrix powers to endomorphism powers — it is the underlying
map of the algebra equivalence `Matrix.toLinAlgEquiv`. -/
lemma toLin_pow (b : Module.Basis (d × d) ℂ (Matrix d d ℂ)) (X : Matrix (d × d) (d × d) ℂ) (k : ℕ) :
    Matrix.toLin b b (X ^ k) = (Matrix.toLin b b X) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.toLin_one]; rfl
  | succ k ih => rw [pow_succ, Matrix.toLin_mul b b b, ih, pow_succ]; rfl

/-- **The superoperator `e^{sℒ}` is completely positive when `ℒ` is completely positive and `s ≥ 0`**
— the exponential `toLin(exp(s • toMatrix M))` is a limit of the completely-positive partial sums
`∑_{n<N} (sⁿ/n!) Mⁿ` (each `Mⁿ` CP). The dissipator factor of the Lie–Trotter product. -/
lemma isCompletelyPositive_toLin_exp {M : MatrixMap d d ℂ} (hM : M.IsCompletelyPositive) {s : ℝ}
    (hs : 0 ≤ s) :
    MatrixMap.IsCompletelyPositive (Matrix.toLin (Matrix.stdBasis ℂ d d) (Matrix.stdBasis ℂ d d)
      (NormedSpace.exp ((s : ℂ) • LinearMap.toMatrix (Matrix.stdBasis ℂ d d)
        (Matrix.stdBasis ℂ d d) M))) := by
  set b := Matrix.stdBasis ℂ d d
  set A : Matrix (d × d) (d × d) ℂ := (s : ℂ) • LinearMap.toMatrix b b M with hA_def
  have hterm : ∀ n : ℕ, Matrix.toLin b b (NormedSpace.expSeries ℂ (Matrix (d × d) (d × d) ℂ) n
      (fun _ => A)) = (((n.factorial : ℂ)⁻¹ * (s : ℂ) ^ n)) • M ^ n := by
    intro n
    rw [NormedSpace.expSeries_apply_eq, hA_def, smul_pow, map_smul, map_smul, toLin_pow,
      Matrix.toLin_toMatrix, smul_smul]
  refine isCompletelyPositive_of_tendsto_choi
    (M := fun N => Matrix.toLin b b
      (∑ n ∈ Finset.range N, NormedSpace.expSeries ℂ (Matrix (d × d) (d × d) ℂ) n (fun _ => A))) ?_ ?_
  · have hlin : (fun Y : Matrix (d × d) (d × d) ℂ => MatrixMap.choi_matrix (Matrix.toLin b b Y))
        = ⇑(MatrixMap.choi_equiv.toLinearMap ∘ₗ (Matrix.toLin b b).toLinearMap) := by
      ext Y; rfl
    have hcont : Continuous fun Y : Matrix (d × d) (d × d) ℂ =>
        MatrixMap.choi_matrix (Matrix.toLin b b Y) := by
      rw [hlin]; exact LinearMap.continuous_of_finiteDimensional _
    exact (hcont.tendsto _).comp (NormedSpace.expSeries_hasSum_exp A).tendsto_sum_nat
  · intro N
    dsimp only
    rw [map_sum]
    refine Finset.sum_induction _ _ (fun _ _ => MatrixMap.IsCompletelyPositive.add)
      (MatrixMap.IsCompletelyPositive.zero d d) (fun n _ => ?_)
    rw [hterm n]
    refine (isCompletelyPositive_pow hM n).smul ?_
    have : ((n.factorial : ℂ)⁻¹ * (s : ℂ) ^ n) = (((n.factorial : ℝ)⁻¹ * s ^ n : ℝ) : ℂ) := by
      push_cast; ring
    rw [this]
    exact_mod_cast (by positivity : (0 : ℝ) ≤ (n.factorial : ℝ)⁻¹ * s ^ n)

end ExpCP

section Drift
variable {d : Type*} [Fintype d] [DecidableEq d] {κ : Type*} [Fintype κ]

/-- The **drift generator** `A := −iH − ½∑ₖ Lₖ†Lₖ`. Its conjugation `ρ ↦ e^{sA} ρ e^{sA†}` is the
no-jump part of the GKSL dynamics. -/
noncomputable def driftMatrix (H : Matrix d d ℂ) (L : κ → Matrix d d ℂ) : Matrix d d ℂ :=
  -Complex.I • H - (2⁻¹ : ℂ) • ∑ k, (L k)ᴴ * L k

/-- The drift part `−i[H,·] − ½{∑Lₖ†Lₖ, ·}` of the GKSL generator equals `ρ ↦ Aρ + ρA†` for `A` the
drift generator, when `H` is Hermitian — a left-plus-right multiplication (the conjugation generator). -/
lemma lindbladDrift_eq (H : Matrix d d ℂ) (hH : H.IsHermitian) (L : κ → Matrix d d ℂ) :
    lindbladHamPart H + lindbladAnticommPart L
      = LinearMap.mulLeft ℂ (driftMatrix H L) + LinearMap.mulRight ℂ (driftMatrix H L)ᴴ := by
  have hAdj : (driftMatrix H L)ᴴ = Complex.I • H - (2⁻¹ : ℂ) • ∑ k, (L k)ᴴ * L k := by
    simp only [driftMatrix, conjTranspose_sub, conjTranspose_smul,
      conjTranspose_sum, conjTranspose_mul, conjTranspose_conjTranspose, hH.eq, star_inv₀,
      Complex.star_def, map_neg, Complex.conj_I, neg_neg, star_ofNat]
  refine LinearMap.ext fun ρ => ?_
  rw [LinearMap.add_apply, lindbladHamPart_apply, lindbladAnticommPart_apply,
    LinearMap.add_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, hAdj, driftMatrix]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]; module

end Drift

end SKEFTHawking.OpenSystems
