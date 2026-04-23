/-
Phase 5t Wave 2: Fermi-Hubbard Dimer — Algebraic Skeleton of the
Doublon Geometric Gate

## Scope

This module formalizes the finite-dimensional algebraic core of the
Kiefer et al. (Nature 2026; arXiv:2507.22112) doublon geometric SWAP
gate — the two-fermion Fermi-Hubbard dimer whose 3×3 singlet-sector
Hamiltonian exhibits a chiral-protected dark state.

The Hamiltonian in second-quantized form is
  H = −t ∑_σ (c†_{1σ} c_{2σ} + h.c.) + U ∑_i n_{i↑} n_{i↓} + (Δ/2)(n_1 − n_2).

After decomposition into total-spin sectors, the triplet (S=1) sector
decouples at exactly zero energy (a direct consequence of fermionic
antisymmetry); all dynamical structure resides in the 3×3 singlet (S=0)
block. We formalize here only the exact algebraic content — Layer 1 of
the two-layer decomposition from Phase 5t deep research. Layer 2
(adiabatic theorem + Berry phase + SWAP equivalence) is deferred to
Phase 6.

## Layer 1 targets (all exact, all closed by `ext; fin_cases; simp; ring`)

* **T1** `H_singlet_isSymm` — the 3×3 Hamiltonian is real symmetric.
* **T2** `dark_state_in_kernel` — at U = 0 the unnormalized vector
  `(0, 2t, Δ)` lies in ker(H₃).
* **T3** `darkVec_ne_zero` — the dark vector is nonzero whenever
  `(t, Δ) ≠ (0, 0)`.
* **T4** `chiralOp_sq` — Γ² = I; Γ = diag(+1, −1, −1).
* **T5** `chiral_anticommutes` — {Γ, H₃(t, Δ, 0)} = 0.
* **T6** `det_H_singlet` — det H₃ = −4 U t² (in particular 0 at U = 0).
* **T7** `trace_H_singlet` — tr H₃ = 2 U.

Additionally we record the three 6×6-level triplet eigenvector
witnesses (T10 in the deep research table):

* **T10a** `triplet_plus_zero` — |↑,↑⟩ is a zero eigenvector of H₆.
* **T10b** `triplet_zero_zero` — |↑,↓⟩+|↓,↑⟩ is a zero eigenvector of H₆.
* **T10c** `triplet_minus_zero` — |↓,↓⟩ is a zero eigenvector of H₆.

## Deferred to Phase 5t Wave 3+

* **T8** full characteristic polynomial λ³ − 2Uλ² + (U² − Δ² − 4t²)λ
  + 4Ut² (requires `charmatrix` + polynomial coefficient matching).
* **T11** block-diagonal form P†H₆P via explicit unitary (~80 LOC of
  `fromBlocks` bookkeeping).
* **T12** explicit bright-state eigenvectors with `Real.sqrt` terms.
* **T13**–**T15** adiabatic / Berry phase / SWAP equivalence — full
  Layer 2, Phase 6 at the earliest.

## References

* Kiefer et al., arXiv:2507.22112 (Nature 2026) — 99.91% fidelity
  geometric SWAP in a dynamical optical lattice.
* Deep research: `Lit-Search/Phase-5t/Effective Fermi-Hubbard Dimer
  for the Doublon Geometric Gate.md`.
* Roadmap: `docs/roadmaps/Phase5t_Roadmap.md` §Wave 2.
-/
import Mathlib
import SKEFTHawking.Basic

namespace SKEFTHawking.FermiHubbardDimer

open Matrix Polynomial

/-! ### Section 1. Core definitions -/

/-- The 3×3 singlet-sector Hamiltonian of the Fermi-Hubbard dimer,
expressed in the symmetry-adapted basis {|D₊⟩, |D₋⟩, |s⟩}. The block
structure in this basis is
  H₃ = ![[U, Δ, -2t], [Δ, U, 0], [-2t, 0, 0]].
At U = 0 the (D₋, s) entry decouples, exposing the chiral sublattice
structure (|D₊⟩ vs {|D₋⟩, |s⟩}). -/
def H_singlet (t Δ U : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![U, Δ, -2*t;
     Δ, U, 0;
     -2*t, 0, 0]

/-- The unnormalized dark-state vector at U = 0:
`cos(θ/2) |s⟩ + sin(θ/2) |D₋⟩` with `cot(θ/2) = -Δ / (2t)`, written as
the unnormalized `(0, 2t, Δ)` entry in the {|D₊⟩, |D₋⟩, |s⟩} basis. -/
def darkVec (t Δ : ℝ) : Fin 3 → ℝ := ![0, 2*t, Δ]

/-- The chiral symmetry operator Γ = diag(+1, -1, -1) on the
singlet-sector basis. Involutory and anticommutes with H₃ at U = 0
(BDI class). -/
def chiralOp : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0;
     0, -1, 0;
     0, 0, -1]

/-- The full 6×6 Hamiltonian on the two-fermion Hilbert space in the
site basis ordered
  {|↑,↑⟩, |↑↓,0⟩, |↑,↓⟩, |↓,↑⟩, |0,↑↓⟩, |↓,↓⟩}.
The alternating (-t, +t) signs on rows 2 and 3 encode fermionic
anticommutation; |↑,↑⟩ and |↓,↓⟩ are Pauli-excluded from hopping and
sit at exactly zero energy. -/
def H_full (t Δ U : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0,    0,     0,    0,    0,    0;
     0,    U+Δ,  -t,    t,    0,    0;
     0,   -t,     0,    0,   -t,    0;
     0,    t,     0,    0,    t,    0;
     0,    0,    -t,    t,    U-Δ,  0;
     0,    0,     0,    0,    0,    0]

/-! ### Section 2. Layer-1 core theorems (T1–T7) -/

/-- **T1.** The 3×3 singlet-sector Hamiltonian is real symmetric. The
symmetry survives for all U (unlike the chiral anticommutation, which
breaks at U ≠ 0). -/
theorem H_singlet_isSymm (t Δ U : ℝ) :
    (H_singlet t Δ U)ᵀ = H_singlet t Δ U := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [H_singlet, Matrix.transpose]

/-- **T2.** The dark-state vector `(0, 2t, Δ)` lies in the kernel of
`H_singlet t Δ 0`. Row 1: `Δ·(2t) + (-2t)·Δ = 0`. Row 2: `U·(2t) = 0
at U=0`. Row 3: `-2t·0 = 0`. -/
theorem dark_state_in_kernel (t Δ : ℝ) :
    (H_singlet t Δ 0).mulVec (darkVec t Δ) = 0 := by
  funext i
  fin_cases i <;>
    first
      | (simp [H_singlet, darkVec, Matrix.mulVec, dotProduct,
               Fin.sum_univ_three]; ring)
      | simp [H_singlet, darkVec, Matrix.mulVec, dotProduct,
              Fin.sum_univ_three]

/-- **T3.** The dark-state vector is nonzero whenever parameters are
nontrivial (`t ≠ 0` or `Δ ≠ 0`). -/
theorem darkVec_ne_zero {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    darkVec t Δ ≠ 0 := by
  intro heq
  cases h with
  | inl ht =>
    have h1 := congr_fun heq 1
    simp [darkVec] at h1
    exact ht (by linarith)
  | inr hΔ =>
    have h2 := congr_fun heq 2
    simp [darkVec] at h2
    exact hΔ h2

/-- **T4.** The chiral operator squares to the identity, Γ² = I. -/
theorem chiralOp_sq :
    chiralOp * chiralOp = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralOp, Matrix.mul_apply, Fin.sum_univ_three]

/-- **T5.** At U = 0 the Hamiltonian anticommutes with the chiral
operator, `{Γ, H₃} = 0`. This pins the zero eigenvalue (odd-dimensional
sector with paired nonzero eigenvalues ⇒ one eigenvalue is zero). -/
theorem chiral_anticommutes (t Δ : ℝ) :
    chiralOp * H_singlet t Δ 0 + H_singlet t Δ 0 * chiralOp = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralOp, H_singlet]

/-- **T6.** The determinant of the 3×3 singlet-sector Hamiltonian is
`det H₃ = -4 U t²`. -/
theorem det_H_singlet (t Δ U : ℝ) :
    (H_singlet t Δ U).det = -(4 * U * t ^ 2) := by
  simp [H_singlet, Matrix.det_fin_three]
  ring

/-- **T6a.** In particular, `det H₃ = 0` at U = 0 (the dark state
exists). -/
theorem det_H_singlet_U0 (t Δ : ℝ) :
    (H_singlet t Δ 0).det = 0 := by
  rw [det_H_singlet]; ring

/-- **T7.** The trace of the 3×3 singlet-sector Hamiltonian is
`tr H₃ = 2U`. In particular the nonzero eigenvalues are `±√(Δ²+4t²)`
at U = 0, exactly balanced. -/
theorem trace_H_singlet (t Δ U : ℝ) :
    (H_singlet t Δ U).trace = 2 * U := by
  simp [H_singlet, Matrix.trace_fin_three]; ring

/-! ### Section 3. 6×6 triplet eigenvectors (T10a–T10c) -/

/-- **T10a.** The triplet state `|t₊⟩ = |↑,↑⟩` is a zero-energy
eigenvector of the full 6×6 Hamiltonian — for all parameters t, Δ, U.
This is Pauli exclusion: two spin-up fermions cannot hop to the same
site. -/
theorem triplet_plus_zero (t Δ U : ℝ) :
    (H_full t Δ U).mulVec ![1, 0, 0, 0, 0, 0] = 0 := by
  funext i
  fin_cases i <;>
    simp [H_full, Matrix.mulVec, dotProduct,
          Fin.sum_univ_six]

/-- **T10b.** The unnormalized triplet state `|t₀⟩ ∝ |↑,↓⟩ + |↓,↑⟩`
is a zero-energy eigenvector of the full 6×6 Hamiltonian — for all
parameters t, Δ, U. This is the `(-t, +t)` alternating-sign
cancellation from fermionic anticommutation. (Normalization 1/√2 is
omitted: `H v = 0 ⟹ H(v/√2) = 0`.) -/
theorem triplet_zero_zero (t Δ U : ℝ) :
    (H_full t Δ U).mulVec ![0, 0, 1, 1, 0, 0] = 0 := by
  funext i
  fin_cases i <;>
    simp [H_full, Matrix.mulVec, dotProduct,
          Fin.sum_univ_six]

/-- **T10c.** The triplet state `|t₋⟩ = |↓,↓⟩` is a zero-energy
eigenvector of the full 6×6 Hamiltonian — for all parameters t, Δ, U.
Mirror of T10a. -/
theorem triplet_minus_zero (t Δ U : ℝ) :
    (H_full t Δ U).mulVec ![0, 0, 0, 0, 0, 1] = 0 := by
  funext i
  fin_cases i <;>
    simp [H_full, Matrix.mulVec, dotProduct,
          Fin.sum_univ_six]

/-! ### Section 3b. Symmetry-adapted basis embeddings (Phase 5t W3)

This section connects the 6×6 `H_full` to the 3×3 `H_singlet` via
explicit embeddings of the symmetry-adapted basis vectors
`{|D₊⟩, |D₋⟩, |s⟩, |t₀⟩}` into `Fin 6 → ℝ`. The vectors are written
**unnormalized** (omitting the `1/√2` normalization) so that every
block-match theorem closes over `ℝ` without `Real.sqrt`. The physical
statement is unchanged: `H v = Hv` for a set of vectors that spans the
4-dim subspace of interest.

The block-match theorems (W3a–d) replace the equivalent but heavier
`P†H₆P = diag(0₃, H₃)` identity (T11 in deep research), at a fraction of
the proof length. The computational-basis decomposition theorems
(W3e–f) express `|↑,↓⟩` and `|↓,↑⟩` as half-sum/half-difference of
`|t₀⟩` and `|s⟩`. -/

/-- Unnormalized symmetric doublon `|D₊⟩ ∝ |↑↓,0⟩ + |0,↑↓⟩`. -/
def v_Dplus : Fin 6 → ℝ := ![0, 1, 0, 0, 1, 0]

/-- Unnormalized antisymmetric doublon `|D₋⟩ ∝ |↑↓,0⟩ − |0,↑↓⟩`. -/
def v_Dminus : Fin 6 → ℝ := ![0, 1, 0, 0, -1, 0]

/-- Unnormalized spin singlet `|s⟩ ∝ |↑,↓⟩ − |↓,↑⟩`. -/
def v_s : Fin 6 → ℝ := ![0, 0, 1, -1, 0, 0]

/-- Unnormalized S_z = 0 triplet `|t₀⟩ ∝ |↑,↓⟩ + |↓,↑⟩`. -/
def v_t0 : Fin 6 → ℝ := ![0, 0, 1, 1, 0, 0]

/-- Computational basis state `|↑,↓⟩` (site 1 up, site 2 down). -/
def up_down : Fin 6 → ℝ := ![0, 0, 1, 0, 0, 0]

/-- Computational basis state `|↓,↑⟩` (site 1 down, site 2 up). -/
def down_up : Fin 6 → ℝ := ![0, 0, 0, 1, 0, 0]

/-- **W3a.** `H_full` acts on `|D₊⟩` exactly as the first row of
`H_singlet`: `H₆ · |D₊⟩ = U · |D₊⟩ + Δ · |D₋⟩ + (-2t) · |s⟩`. The
alternating sign pattern on rows 2 and 3 of `H_full` produces the
`-2t · |s⟩` (not `-2t · |t₀⟩`) on the RHS. -/
theorem H_full_acts_on_v_Dplus (t Δ U : ℝ) :
    (H_full t Δ U).mulVec v_Dplus =
      U • v_Dplus + Δ • v_Dminus + (-2 * t) • v_s := by
  funext i
  fin_cases i <;>
    first
      | (simp [H_full, v_Dplus, v_Dminus, v_s, Matrix.mulVec, dotProduct,
               Fin.sum_univ_six, Pi.add_apply, smul_eq_mul]
         ring)
      | simp [H_full, v_Dplus, v_Dminus, v_s, Matrix.mulVec, dotProduct,
              Fin.sum_univ_six, Pi.add_apply, smul_eq_mul]

/-- **W3b.** `H_full` acts on `|D₋⟩` exactly as the second row of
`H_singlet`: `H₆ · |D₋⟩ = Δ · |D₊⟩ + U · |D₋⟩`. The `s`-coupling is
zero because the `(D₋, s)` entry of `H_singlet` is zero — this is the
sublattice structure that pins the dark-state zero mode. -/
theorem H_full_acts_on_v_Dminus (t Δ U : ℝ) :
    (H_full t Δ U).mulVec v_Dminus = Δ • v_Dplus + U • v_Dminus := by
  funext i
  fin_cases i <;>
    first
      | (simp [H_full, v_Dplus, v_Dminus, Matrix.mulVec, dotProduct,
               Fin.sum_univ_six, Pi.add_apply, smul_eq_mul]
         ring)
      | simp [H_full, v_Dplus, v_Dminus, Matrix.mulVec, dotProduct,
              Fin.sum_univ_six, Pi.add_apply, smul_eq_mul]

/-- **W3c.** `H_full` acts on `|s⟩` exactly as the third row of
`H_singlet`: `H₆ · |s⟩ = (-2t) · |D₊⟩`. The `(s, D₋)` and `(s, s)`
entries are zero. -/
theorem H_full_acts_on_v_s (t Δ U : ℝ) :
    (H_full t Δ U).mulVec v_s = (-2 * t) • v_Dplus := by
  funext i
  fin_cases i <;>
    first
      | (simp [H_full, v_Dplus, v_s, Matrix.mulVec, dotProduct,
               Fin.sum_univ_six, Pi.smul_apply, smul_eq_mul]
         ring)
      | simp [H_full, v_Dplus, v_s, Matrix.mulVec, dotProduct,
              Fin.sum_univ_six, Pi.smul_apply, smul_eq_mul]

/-- **W3d.** `H_full` acts on `|t₀⟩` giving zero — the S_z = 0 triplet
decouples from the singlet block. Complements T10a (`|t₊⟩`) and T10c
(`|t₋⟩`). The cancellation is the alternating `(-t, +t)` sign pattern
on rows 2 and 3: `(-t) · 1 + t · 1 = 0` in rows 1 and 4 of `H_full`. -/
theorem H_full_acts_on_v_t0 (t Δ U : ℝ) :
    (H_full t Δ U).mulVec v_t0 = 0 := by
  funext i
  fin_cases i <;>
    simp [H_full, v_t0, Matrix.mulVec, dotProduct, Fin.sum_univ_six]

/-- **W3e.** Computational-basis embedding of `|↑,↓⟩`:
`2 · |↑,↓⟩ = |t₀⟩ + |s⟩` (unnormalized form of the standard relation
`|↑,↓⟩ = (|t₀⟩ + |s⟩)/√2 · (1/√2)`; the factor of 2 absorbs both
`1/√2` normalizations). -/
theorem two_updown_eq_t0_plus_s :
    (2 : ℝ) • up_down = v_t0 + v_s := by
  funext i
  fin_cases i <;>
    first
      | (simp [up_down, v_t0, v_s, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
         ring)
      | simp [up_down, v_t0, v_s, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- **W3f.** Computational-basis embedding of `|↓,↑⟩`:
`2 · |↓,↑⟩ = |t₀⟩ − |s⟩`. -/
theorem two_downup_eq_t0_minus_s :
    (2 : ℝ) • down_up = v_t0 - v_s := by
  funext i
  fin_cases i <;>
    first
      | (simp [down_up, v_t0, v_s, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
         ring)
      | simp [down_up, v_t0, v_s, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-! ### Section 4. Trace-class corollaries -/

/-- At U = 0 the trace of the 3×3 singlet-sector Hamiltonian vanishes,
consistent with paired nonzero eigenvalues `±E`. -/
theorem trace_H_singlet_U0 (t Δ : ℝ) :
    (H_singlet t Δ 0).trace = 0 := by
  rw [trace_H_singlet]; ring

/-- A convenience pair recording T2 and T3 together: at U = 0 the
kernel contains a nonzero vector when `(t, Δ) ≠ (0, 0)`. -/
theorem dark_state_nontrivial_kernel {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    (H_singlet t Δ 0).mulVec (darkVec t Δ) = 0 ∧ darkVec t Δ ≠ 0 :=
  ⟨dark_state_in_kernel t Δ, darkVec_ne_zero h⟩

/-! ### Section 5. U = 0 spectrum: θ-parametrized dark state + bright
eigenvectors + gap (Phase 5t W4) -/

/-- The θ-parametrized normalized dark-state vector at `U = 0`:
`![0, sin θ, cos θ]` in the `{|D₊⟩, |D₋⟩, |s⟩}` basis. This is the
form `cos θ · |s⟩ + sin θ · |D₋⟩` used in the geometric-phase
literature. When the angle satisfies `Δ · sin θ = 2t · cos θ`
(equivalently `tan θ = 2t/Δ`), this vector lies in
`ker(H_singlet t Δ 0)` by `dark_state_theta_in_kernel`.

Marked `noncomputable` because it depends on `Real.sin`/`Real.cos`. -/
noncomputable def darkStateθ (θ : ℝ) : Fin 3 → ℝ :=
  ![0, Real.sin θ, Real.cos θ]

/-- The unnormalized positive-energy bright-state eigenvector at
`U = 0`: `![√(Δ² + 4t²), Δ, -2t]`. An eigenvector of
`H_singlet t Δ 0` with eigenvalue `+√(Δ² + 4t²)`.

Marked `noncomputable` because it depends on `Real.sqrt`. -/
noncomputable def brightVecPlus (t Δ : ℝ) : Fin 3 → ℝ :=
  ![Real.sqrt (Δ^2 + 4*t^2), Δ, -2*t]

/-- The unnormalized negative-energy bright-state eigenvector at
`U = 0`: `![-√(Δ² + 4t²), Δ, -2t]`. An eigenvector of
`H_singlet t Δ 0` with eigenvalue `-√(Δ² + 4t²)`.

Marked `noncomputable` because it depends on `Real.sqrt`. -/
noncomputable def brightVecMinus (t Δ : ℝ) : Fin 3 → ℝ :=
  ![-Real.sqrt (Δ^2 + 4*t^2), Δ, -2*t]

/-- The positive-energy bright-state eigenvalue (equivalently, the
energy gap between the dark state and the positive bright state at
`U = 0`): `√(Δ² + 4t²)`.

Marked `noncomputable` because it depends on `Real.sqrt`. -/
noncomputable def gapAtU0 (t Δ : ℝ) : ℝ := Real.sqrt (Δ^2 + 4*t^2)

/-- **W4a (dark_state_theta_in_kernel).** The θ-parametrized dark state
lies in `ker(H_singlet t Δ 0)` whenever the angle satisfies
`Δ · sin θ = 2t · cos θ`. This is the angular condition `tan θ = 2t/Δ`
in the form that avoids the division-by-zero at `Δ = 0`. -/
theorem dark_state_theta_in_kernel (t Δ θ : ℝ)
    (hθ : Δ * Real.sin θ = 2 * t * Real.cos θ) :
    (H_singlet t Δ 0).mulVec (darkStateθ θ) = 0 := by
  funext i
  fin_cases i
  · -- Row 0: 0 · 0 + Δ · sin θ + (-2t) · cos θ = 0
    simp [H_singlet, darkStateθ, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three]
    linarith [hθ]
  · -- Row 1: Δ · 0 + 0 · sin θ + 0 · cos θ = 0
    simp [H_singlet, darkStateθ, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three]
  · -- Row 2: (-2t) · 0 + 0 · sin θ + 0 · cos θ = 0
    simp [H_singlet, darkStateθ, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three]

/-- **W4b (H_singlet_U0_brightVecPlus).** `brightVecPlus t Δ` is an
eigenvector of `H_singlet t Δ 0` with eigenvalue `+√(Δ² + 4t²)`.
The row-0 identity requires `Real.mul_self_sqrt` to reduce
`√g · √g` to `g = Δ² + 4t²`. -/
theorem H_singlet_U0_brightVecPlus (t Δ : ℝ) :
    (H_singlet t Δ 0).mulVec (brightVecPlus t Δ) =
      Real.sqrt (Δ^2 + 4*t^2) • brightVecPlus t Δ := by
  have hg : (0 : ℝ) ≤ Δ^2 + 4*t^2 := by positivity
  have hsq' : Real.sqrt (Δ^2 + 4*t^2)^2 = Δ^2 + 4*t^2 := Real.sq_sqrt hg
  funext i
  fin_cases i
  · -- Row 0: Δ·Δ + (-2t)·(-2t) = √g · √g  (use hsq' after simp)
    simp [H_singlet, brightVecPlus, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    linarith [hsq']
  · -- Row 1: Δ · √g = √g · Δ  (commutativity)
    simp [H_singlet, brightVecPlus, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    ring
  · -- Row 2: (-2t)·√g = √g · (-2t)  (commutativity)
    simp [H_singlet, brightVecPlus, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    ring

/-- **W4c (H_singlet_U0_brightVecMinus).** `brightVecMinus t Δ` is an
eigenvector of `H_singlet t Δ 0` with eigenvalue `-√(Δ² + 4t²)`.
Mirror of W4b with sign flipped on the first component. -/
theorem H_singlet_U0_brightVecMinus (t Δ : ℝ) :
    (H_singlet t Δ 0).mulVec (brightVecMinus t Δ) =
      (-Real.sqrt (Δ^2 + 4*t^2)) • brightVecMinus t Δ := by
  have hg : (0 : ℝ) ≤ Δ^2 + 4*t^2 := by positivity
  have hsq' : Real.sqrt (Δ^2 + 4*t^2)^2 = Δ^2 + 4*t^2 := Real.sq_sqrt hg
  funext i
  fin_cases i
  · simp [H_singlet, brightVecMinus, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    linarith [hsq']
  · simp [H_singlet, brightVecMinus, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    ring
  · simp [H_singlet, brightVecMinus, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
    ring

/-- **W4d (gapAtU0_pos).** The gap `√(Δ² + 4t²)` is strictly positive
whenever `(t, Δ) ≠ (0, 0)`. -/
theorem gapAtU0_pos {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    0 < gapAtU0 t Δ := by
  unfold gapAtU0
  apply Real.sqrt_pos.mpr
  cases h with
  | inl ht =>
    have h1 : 0 < t^2 := by positivity
    have h2 : (0 : ℝ) ≤ Δ^2 := sq_nonneg Δ
    linarith
  | inr hΔ =>
    have h1 : 0 < Δ^2 := by positivity
    have h2 : (0 : ℝ) ≤ 4*t^2 := by positivity
    linarith

/-- **W4e (brightVecPlus_ne_zero).** The positive bright-state
eigenvector is nonzero whenever `(t, Δ) ≠ (0, 0)` — its first
component is the strictly positive gap. -/
theorem brightVecPlus_ne_zero {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    brightVecPlus t Δ ≠ 0 := by
  intro heq
  have h0 := congr_fun heq 0
  simp [brightVecPlus] at h0
  have hpos : 0 < Real.sqrt (Δ^2 + 4*t^2) := gapAtU0_pos h
  linarith

/-- **W4e' (brightVecMinus_ne_zero).** Mirror of W4e for the negative
bright-state eigenvector: nonzero whenever `(t, Δ) ≠ (0, 0)` since
its first component is the strictly negative `-gap`. -/
theorem brightVecMinus_ne_zero {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    brightVecMinus t Δ ≠ 0 := by
  intro heq
  have h0 := congr_fun heq 0
  simp [brightVecMinus] at h0
  have hpos : 0 < Real.sqrt (Δ^2 + 4*t^2) := gapAtU0_pos h
  linarith

/-- **W4e'' (darkStateθ_ne_zero).** The θ-parametrized dark state is
**always** nonzero — independent of `(t, Δ)` — because
`sin²θ + cos²θ = 1 ≠ 0`. Unlike the bright vectors, no parameter
hypothesis is needed. -/
theorem darkStateθ_ne_zero (θ : ℝ) : darkStateθ θ ≠ 0 := by
  intro heq
  have h1 := congr_fun heq 1
  have h2 := congr_fun heq 2
  simp [darkStateθ] at h1 h2
  have : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  rw [h1, h2] at this
  norm_num at this

/-- **W4d' (gapAtU0_sq_eq).** Exact squared identity for the gap:
`gap(t, Δ)² = Δ² + 4t²`. Follows from `Real.sq_sqrt` on the
non-negative argument. This unblocks downstream uses where the
explicit squared value is needed without re-deriving it from
`Real.mul_self_sqrt`. -/
theorem gapAtU0_sq_eq (t Δ : ℝ) :
    (gapAtU0 t Δ)^2 = Δ^2 + 4*t^2 := by
  unfold gapAtU0
  exact Real.sq_sqrt (by positivity : (0:ℝ) ≤ Δ^2 + 4*t^2)

/-- **W4i (eigenvalues_distinct_at_U0).** When `(t, Δ) ≠ (0, 0)`, the
three eigenvalues `{0, +gap, -gap}` are pairwise distinct. This
justifies the "spectrum has three distinct values" claim used in the
gate physics. -/
theorem eigenvalues_distinct_at_U0 {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    gapAtU0 t Δ ≠ -gapAtU0 t Δ ∧
      gapAtU0 t Δ ≠ 0 ∧ -gapAtU0 t Δ ≠ 0 := by
  have hpos : 0 < gapAtU0 t Δ := gapAtU0_pos h
  refine ⟨?_, ?_, ?_⟩
  · intro heq; linarith
  · exact ne_of_gt hpos
  · intro heq; linarith

/-! ### Section 6. Characteristic polynomial (Phase 5t W4 strong form) -/

/-- **W4f (T9 — charpoly_H_singlet).** The characteristic polynomial
of the 3×3 singlet-sector Hamiltonian. The coefficients are read off
from `det(X·I - H)` expanded via Sarrus:
  `charpoly = X³ − 2U·X² + (U² − Δ² − 4t²)·X + 4U·t²`.
Verifies the `tr = 2U` and `det = -4Ut²` identities directly (the X²
coefficient is `-tr` and the constant term is `(-1)³·det = -det`). -/
theorem charpoly_H_singlet (t Δ U : ℝ) :
    (H_singlet t Δ U).charpoly =
      X^3 - C (2*U) * X^2 + C (U^2 - Δ^2 - 4*t^2) * X + C (4*U*t^2) := by
  simp [Matrix.charpoly, Matrix.det_fin_three,
        Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_ne,
        H_singlet,
        show ((0 : Fin 3) ≠ 1) from by decide,
        show ((0 : Fin 3) ≠ 2) from by decide,
        show ((1 : Fin 3) ≠ 0) from by decide,
        show ((1 : Fin 3) ≠ 2) from by decide,
        show ((2 : Fin 3) ≠ 0) from by decide,
        show ((2 : Fin 3) ≠ 1) from by decide,
        map_mul, map_ofNat, map_pow]
  ring

/-- **W4g (T8 — charpoly_H_singlet_U0).** At `U = 0`, the
characteristic polynomial factors explicitly as
`X · (X² − (Δ² + 4t²))`, exposing the three eigenvalues
`{0, +√(Δ²+4t²), −√(Δ²+4t²)}`. -/
theorem charpoly_H_singlet_U0 (t Δ : ℝ) :
    (H_singlet t Δ 0).charpoly =
      X * (X^2 - C (Δ^2 + 4*t^2)) := by
  rw [charpoly_H_singlet]
  simp
  ring

/-- **W4h (spectrum corollary).** At `U = 0`, the three eigenvalues of
`H_singlet t Δ 0` are exactly `0`, `+√(Δ² + 4t²)`, and
`−√(Δ² + 4t²)` — encoded as the three linear-factor roots of the
factored characteristic polynomial. The explicit eigenvectors are
`darkVec t Δ` (eigenvalue 0, by W2 T2), `brightVecPlus t Δ`
(eigenvalue `+gap`, by W4b), and `brightVecMinus t Δ` (eigenvalue
`-gap`, by W4c). Spectrum completeness is witnessed by the charpoly
degree equaling the matrix dimension — any eigenvalue is a root. -/
theorem H_singlet_U0_spectrum_is_three_eigenvalues (t Δ : ℝ) :
    (H_singlet t Δ 0).charpoly =
      X * (X - C (Real.sqrt (Δ^2 + 4*t^2))) *
        (X + C (Real.sqrt (Δ^2 + 4*t^2))) := by
  have hg : (0 : ℝ) ≤ Δ^2 + 4*t^2 := by positivity
  have hsq : Real.sqrt (Δ^2 + 4*t^2) * Real.sqrt (Δ^2 + 4*t^2) =
             Δ^2 + 4*t^2 := Real.mul_self_sqrt hg
  -- (X - C√g) · (X + C√g) = X² − C√g · C√g = X² − C(√g · √g) = X² − C(Δ²+4t²)
  have hCsq : C (Real.sqrt (Δ^2 + 4*t^2)) * C (Real.sqrt (Δ^2 + 4*t^2)) =
              C (Δ^2 + 4*t^2) := by
    rw [← map_mul, hsq]
  have hdiff : (X - C (Real.sqrt (Δ^2 + 4*t^2))) *
               (X + C (Real.sqrt (Δ^2 + 4*t^2))) =
               X^2 - C (Real.sqrt (Δ^2 + 4*t^2)) *
                     C (Real.sqrt (Δ^2 + 4*t^2)) := by ring
  rw [charpoly_H_singlet_U0,
      show X^2 - C (Δ^2 + 4*t^2) =
           (X - C (Real.sqrt (Δ^2 + 4*t^2))) *
           (X + C (Real.sqrt (Δ^2 + 4*t^2))) from by rw [hdiff, hCsq]]
  ring

/-- Summary marker for the Phase 5t Wave 2 shipment (non-load-bearing;
placeholder for graph integrity). -/
theorem fermi_hubbard_dimer_wave2_summary : True := trivial

/-- Summary marker for the Phase 5t Wave 3 shipment (non-load-bearing;
placeholder for graph integrity). -/
theorem fermi_hubbard_dimer_wave3_summary : True := trivial

/-! ### Section 7. Linear independence of the U=0 eigenvectors
(Phase 5t W4 strengthening)

The three eigenvectors `{darkVec, brightVecPlus, brightVecMinus}` —
corresponding to eigenvalues `{0, +gap, -gap}` at U = 0 — are
**linearly independent** whenever `(t, Δ) ≠ (0, 0)`. This is an
alternate spectrum-completeness witness: three linearly independent
eigenvectors for three distinct eigenvalues in a 3×3 matrix exhaust
the spectrum. Complementary to the charpoly factorization in
`H_singlet_U0_spectrum_is_three_eigenvalues`. -/

/-- The 3×3 eigenvector matrix at U = 0: rows are `darkVec`,
`brightVecPlus`, `brightVecMinus`. Used to witness linear
independence via nonzero determinant. -/
noncomputable def eigenvectorMatrix (t Δ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 2*t, Δ;
     Real.sqrt (Δ^2 + 4*t^2), Δ, -2*t;
     -Real.sqrt (Δ^2 + 4*t^2), Δ, -2*t]

/-- **W4j (eigenvectorMatrix_det).** The determinant of the eigenvector
matrix is `2 · (Δ² + 4t²) · √(Δ² + 4t²) = 2 · (gap)³`. Closed by
Sarrus expansion + ring; the positive sign comes from the
antisymmetric `±√g` structure in rows 1 and 2. -/
theorem eigenvectorMatrix_det (t Δ : ℝ) :
    (eigenvectorMatrix t Δ).det =
      2 * (Δ^2 + 4*t^2) * Real.sqrt (Δ^2 + 4*t^2) := by
  unfold eigenvectorMatrix
  simp [Matrix.det_fin_three]
  ring

/-- **W4k (eigenvectors_linearIndependent_at_U0).** When `(t, Δ) ≠ (0, 0)`,
the determinant of the eigenvector matrix is strictly positive (`2·(gap)³ > 0`),
so the three rows `{darkVec, brightVecPlus, brightVecMinus}` are
linearly independent. This is the alternate spectrum-completeness
witness (to the charpoly factorization W4h). -/
theorem eigenvectors_linearIndependent_at_U0 {t Δ : ℝ}
    (h : t ≠ 0 ∨ Δ ≠ 0) :
    (eigenvectorMatrix t Δ).det ≠ 0 := by
  rw [eigenvectorMatrix_det]
  have hg : 0 < Δ^2 + 4*t^2 := by
    cases h with
    | inl ht => positivity
    | inr hΔ => positivity
  have hsq : 0 < Real.sqrt (Δ^2 + 4*t^2) := Real.sqrt_pos.mpr hg
  positivity

/-! ### Section 8. Orthogonality of the U=0 eigenvectors
(Phase 5t W4 strengthening)

The three eigenvectors `{darkVec, brightVecPlus, brightVecMinus}` of
`H_singlet t Δ 0` are pairwise orthogonal — the standard consequence
of a real symmetric Hamiltonian with distinct eigenvalues `{0, +gap,
-gap}`. Orthogonality is load-bearing for the W6 SWAP-gate
construction (phase accumulation on the bright subspace, zero phase
on the dark subspace) and for the "eigenvectors form an orthogonal
basis" framing in the gate physics. -/

/-- **W4l (dark_brightPlus_orthogonal).** `⟨darkVec, brightVecPlus⟩ = 0`.
The dark-state's zero `D₊` component and the alternating signs make
this closable by `simp + ring` without any `Real.sqrt` handling. -/
theorem dark_brightPlus_orthogonal (t Δ : ℝ) :
    dotProduct (darkVec t Δ) (brightVecPlus t Δ) = 0 := by
  simp [darkVec, brightVecPlus, dotProduct, Fin.sum_univ_three]
  ring

/-- **W4m (dark_brightMinus_orthogonal).** `⟨darkVec, brightVecMinus⟩ = 0`.
Mirror of W4l with the first component sign-flipped (which doesn't
affect the inner product since `darkVec 0 = 0`). -/
theorem dark_brightMinus_orthogonal (t Δ : ℝ) :
    dotProduct (darkVec t Δ) (brightVecMinus t Δ) = 0 := by
  simp [darkVec, brightVecMinus, dotProduct, Fin.sum_univ_three]
  ring

/-- **W4n (brightPlus_brightMinus_orthogonal).**
`⟨brightVecPlus, brightVecMinus⟩ = -√g · √g + Δ² + 4t² = 0`.
Closes via `Real.sq_sqrt` on the squared-norm identity. -/
theorem brightPlus_brightMinus_orthogonal (t Δ : ℝ) :
    dotProduct (brightVecPlus t Δ) (brightVecMinus t Δ) = 0 := by
  have hg : (0 : ℝ) ≤ Δ^2 + 4*t^2 := by positivity
  have hsq' : Real.sqrt (Δ^2 + 4*t^2)^2 = Δ^2 + 4*t^2 := Real.sq_sqrt hg
  simp [brightVecPlus, brightVecMinus, dotProduct, Fin.sum_univ_three]
  linarith [hsq']

/-! ### Section 9. Spectrum-as-set via `Polynomial.roots` and
`Matrix.spectrum` (Phase 5t W4 strengthening)

The factored charpoly (W4h) gives the canonical map to
`Polynomial.roots` as a multiset and to `Matrix.spectrum` as a set.
This provides the Mathlib-canonical handle on "the spectrum of
`H_singlet t Δ 0` is exactly `{0, +gap, -gap}`" for downstream
consumers that expect `Matrix.spectrum` as input (e.g. perturbation
theory, spectral theorem applications, Phase 5t W5 chiral
zero-mode pinning). -/

/-- **W4o (charpoly_H_singlet_U0_roots).** The multiset of roots of
the U=0 characteristic polynomial is exactly `{0, +√g, -√g}`
(with the `{a=0}` degenerate case giving multiplicity-3 root at 0
— harmless because our downstream consumers use `(t, Δ) ≠ (0, 0)`).
Derived directly from the factored form W4h via `Polynomial.roots_mul`
(twice) + the `@[simp]` lemmas `roots_X`, `roots_X_sub_C`,
`roots_X_add_C`. -/
theorem charpoly_H_singlet_U0_roots (t Δ : ℝ) :
    (H_singlet t Δ 0).charpoly.roots =
      ({0} : Multiset ℝ) + {Real.sqrt (Δ^2 + 4*t^2)} +
        {-Real.sqrt (Δ^2 + 4*t^2)} := by
  rw [H_singlet_U0_spectrum_is_three_eigenvalues]
  rw [Polynomial.roots_mul, Polynomial.roots_mul, Polynomial.roots_X,
      Polynomial.roots_X_sub_C, Polynomial.roots_X_add_C]
  · exact mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero _)
  · exact mul_ne_zero
      (mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero _))
      (Polynomial.X_add_C_ne_zero _)

/-- **W4p (H_singlet_U0_mem_spectrum_iff).** Membership in the
`Matrix.spectrum` of `H_singlet t Δ 0` is exactly equivalent to being
one of the three eigenvalues `{0, +√g, -√g}`. Bridge uses Mathlib's
canonical `Matrix.mem_spectrum_iff_isRoot_charpoly` (over a field)
and `Polynomial.mem_roots_iff_isRoot` (guarded by
`charpoly ≠ 0` from `Matrix.charpoly_monic.ne_zero`). -/
theorem H_singlet_U0_mem_spectrum_iff (t Δ μ : ℝ) :
    μ ∈ spectrum ℝ (H_singlet t Δ 0) ↔
      μ = 0 ∨ μ = Real.sqrt (Δ^2 + 4*t^2) ∨
        μ = -Real.sqrt (Δ^2 + 4*t^2) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,
      ← Polynomial.mem_roots
        (Polynomial.Monic.ne_zero (Matrix.charpoly_monic _))]
  rw [charpoly_H_singlet_U0_roots]
  simp [Multiset.mem_singleton]

/-- Summary marker for the Phase 5t Wave 4 shipment (non-load-bearing;
placeholder for graph integrity). Wave 4 delivers the strong-form U=0
spectrum theorem: θ-parametrized dark state, explicit bright
eigenvectors via `Real.sqrt`, positive gap, fully-factored
characteristic polynomial at U=0 plus the general-U cubic, the
linear-independence witness via nonzero determinant of the
eigenvector matrix, pairwise-orthogonality of the three eigenvectors,
and the canonical `Polynomial.roots` / `Matrix.spectrum`
API-bridge form. -/
theorem fermi_hubbard_dimer_wave4_summary : True := trivial

/-! ### Section 10. Chiral conjugation + BDI spectrum pairing
(Phase 5t W5)

W5 delivers the symmetry-protection story for the U=0 singlet block.
Combining W2 T4 (`chiralOp_sq`, Γ²=I) and W2 T5 (`chiral_anticommutes`,
{Γ, H}=0) gives the BDI-class chiral conjugation rule Γ·H·Γ = -H
(W5a). This maps eigenvectors for eigenvalue E to eigenvectors for
eigenvalue -E (W5b), which combined with the W4p spectrum-as-set gives
the spectrum-pairing theorem `μ ∈ spectrum ↔ -μ ∈ spectrum` (W5c).

The zero-mode pinning story is then immediate: 0 ∈ spectrum (W5d),
and the unique zero eigenvector `darkVec` lives in the (-1)-eigenspace
of the chiral operator Γ (W5e), pinning it to the 2-dimensional
sublattice `{|D₋⟩, |s⟩}` — the BDI zero-mode quantization in
concrete form. W5f bundles zero-mode existence + chirality pinning
as a single-package "BDI zero mode" theorem.

W5g records the real-symmetric anti-unitary framing for paper prose:
a real symmetric H has trivial anti-unitary time reversal (complex
conjugation = identity over ℝ), so the (T, Γ) symmetry class
collapses to the chiral-only content already captured by W5a/b/c. -/

/-- **W5a (chiralOp_conjugation_neg).** Two-sided chiral conjugation
negates the Hamiltonian: `Γ · H · Γ = -H` at U = 0. Together with
`chiralOp_sq` (Γ² = I), this is the BDI-class chiral symmetry rule
`Γ H Γ⁻¹ = -H`. Derivable from T5 via matrix algebra
(Γ·H + H·Γ = 0 ⟹ H·Γ = -Γ·H ⟹ Γ·H·Γ = -Γ²·H = -H), but closed
here by direct `ext + fin_cases + simp` since the 3×3 matrix product
is small. -/
theorem chiralOp_conjugation_neg (t Δ : ℝ) :
    chiralOp * H_singlet t Δ 0 * chiralOp = -(H_singlet t Δ 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralOp, H_singlet, Matrix.mul_apply, Fin.sum_univ_three]

/-- **W5b (chiral_maps_eigenvector).** If `v` is an eigenvector of
`H_singlet t Δ 0` with eigenvalue `E`, then `Γ v` is an eigenvector of
the same Hamiltonian with eigenvalue `-E`. This is the core
BDI-spectrum-pairing mechanism: chiral symmetry pairs +E ↔ -E
eigenvectors. Proof chain:
  H (Γ v) = (H Γ) v = -(Γ H) v = -Γ (H v) = -Γ (E • v)
         = -(E • Γ v) = (-E) • Γ v.
The middle step uses `chiral_anticommutes` to rewrite H·Γ as -Γ·H. -/
theorem chiral_maps_eigenvector (t Δ E : ℝ) (v : Fin 3 → ℝ)
    (hv : (H_singlet t Δ 0).mulVec v = E • v) :
    (H_singlet t Δ 0).mulVec (chiralOp.mulVec v) =
      (-E) • (chiralOp.mulVec v) := by
  have h_ac : H_singlet t Δ 0 * chiralOp = -(chiralOp * H_singlet t Δ 0) :=
    add_eq_zero_iff_eq_neg'.mp (chiral_anticommutes t Δ)
  calc (H_singlet t Δ 0).mulVec (chiralOp.mulVec v)
      = (H_singlet t Δ 0 * chiralOp).mulVec v := by
        rw [Matrix.mulVec_mulVec]
    _ = (-(chiralOp * H_singlet t Δ 0)).mulVec v := by rw [h_ac]
    _ = -(chiralOp * H_singlet t Δ 0).mulVec v := by
        rw [Matrix.neg_mulVec]
    _ = -(chiralOp.mulVec ((H_singlet t Δ 0).mulVec v)) := by
        rw [Matrix.mulVec_mulVec]
    _ = -(chiralOp.mulVec (E • v)) := by rw [hv]
    _ = -(E • chiralOp.mulVec v) := by rw [Matrix.mulVec_smul]
    _ = (-E) • chiralOp.mulVec v := by rw [neg_smul]

/-- **W5c (spectrum_pairing_U0).** The spectrum of the U=0
Hamiltonian is symmetric under negation: `μ ∈ spectrum ↔ -μ ∈
spectrum`. This is the BDI ± pairing at the spectral-set level, and
is a direct consequence of W4p (the spectrum is the explicit set
`{0, +√g, -√g}`, which is closed under negation). -/
theorem spectrum_pairing_U0 (t Δ μ : ℝ) :
    μ ∈ spectrum ℝ (H_singlet t Δ 0) ↔
      -μ ∈ spectrum ℝ (H_singlet t Δ 0) := by
  rw [H_singlet_U0_mem_spectrum_iff, H_singlet_U0_mem_spectrum_iff]
  constructor
  · rintro (h | h | h)
    · left; rw [h]; ring
    · right; right; rw [h]
    · right; left; rw [h]; ring
  · rintro (h | h | h)
    · left; linarith
    · right; right; linarith
    · right; left; linarith

/-- **W5d (zero_mem_spectrum_U0).** Zero is an eigenvalue of the U=0
Hamiltonian. Direct consequence of W4p. This is the zero-mode
existence statement (BDI class: odd-dim sector with chiral symmetry
contains a protected zero mode). -/
theorem zero_mem_spectrum_U0 (t Δ : ℝ) :
    (0 : ℝ) ∈ spectrum ℝ (H_singlet t Δ 0) := by
  rw [H_singlet_U0_mem_spectrum_iff]
  left; rfl

/-- **W5e (darkVec_in_chiral_minus_eigenspace).** The zero-mode
eigenvector `darkVec = (0, 2t, Δ)` lies in the (-1)-eigenspace of the
chiral operator Γ = diag(+1, -1, -1), i.e. `Γ · darkVec = -darkVec`.
This pins the zero mode to the 2-dimensional sublattice
`{|D₋⟩, |s⟩}` — the (|n_+ - n_-| = 1) BDI zero-mode quantization in
concrete form. -/
theorem darkVec_in_chiral_minus_eigenspace (t Δ : ℝ) :
    chiralOp.mulVec (darkVec t Δ) = -(darkVec t Δ) := by
  funext i
  fin_cases i <;>
    simp [chiralOp, darkVec, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three]

/-- **W5f (darkVec_is_zero_mode_pinned).** Zero-mode pinning theorem
in single-package form. The dark vector is (i) in the kernel of the
U=0 Hamiltonian, (ii) in the (-1)-eigenspace of the chiral operator,
and (iii) nonzero whenever parameters are nontrivial.
Together, these establish the BDI zero-mode as an exact
algebraic consequence of the 3×3 structure — no adiabatic theorem,
no spectral flow, just real-matrix arithmetic. -/
theorem darkVec_is_zero_mode_pinned {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    (H_singlet t Δ 0).mulVec (darkVec t Δ) = 0 ∧
      chiralOp.mulVec (darkVec t Δ) = -(darkVec t Δ) ∧
        darkVec t Δ ≠ 0 :=
  ⟨dark_state_in_kernel t Δ,
   darkVec_in_chiral_minus_eigenspace t Δ,
   darkVec_ne_zero h⟩

/-- **W5g (brightVecPlus_maps_to_brightVecMinus_under_chiral).**
Witnesses BDI pairing at the eigenvector level: the chiral operator
maps the `+gap` eigenvector to the `-gap` eigenvector (up to sign).
Concretely: `Γ · brightVecPlus = -brightVecMinus`. Together with W4b/c
this double-witnesses the ± pairing at U=0. -/
theorem brightVecPlus_chiral_image (t Δ : ℝ) :
    chiralOp.mulVec (brightVecPlus t Δ) = -(brightVecMinus t Δ) := by
  funext i
  fin_cases i <;>
    simp [chiralOp, brightVecPlus, brightVecMinus,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- **W5g' (brightVecMinus_chiral_image).** Mirror of W5g:
`Γ · brightVecMinus = -brightVecPlus`. Together with W5g this
establishes `Γ · Γ · brightVecPlus = brightVecPlus` — consistency
with W2 T4 (`chiralOp_sq`, Γ² = I). -/
theorem brightVecMinus_chiral_image (t Δ : ℝ) :
    chiralOp.mulVec (brightVecMinus t Δ) = -(brightVecPlus t Δ) := by
  funext i
  fin_cases i <;>
    simp [chiralOp, brightVecPlus, brightVecMinus,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- **W5h (H_singlet_real_anti_unitary_trivial).** Paper-facing
framing lemma. For any real-symmetric Hamiltonian over ℝ (which
`H_singlet` is for all U by W2 T1), the "anti-unitary time-reversal"
symmetry required for BDI-class classification is trivially realized:
complex conjugation acts as the identity on real vectors. Formalized
here as the identity statement `H_singlet.map id = H_singlet`, since
the `ℝ`-typing of the matrix already encodes that all entries are
real. This is a marker theorem for paper prose — the genuine BDI
content is the chiral anticommutation (T5) and the conjugation rule
(W5a). -/
theorem H_singlet_real_anti_unitary_trivial (t Δ U : ℝ) :
    (H_singlet t Δ U).map (id : ℝ → ℝ) = H_singlet t Δ U := by
  ext i j
  simp

/-- Summary marker for the Phase 5t Wave 5 core shipment
(non-load-bearing; placeholder for graph integrity). Wave 5 core
delivers the BDI symmetry-protection layer on top of W2 T4/T5 and
W4p: chiral conjugation Γ·H·Γ = -H (W5a); eigenvector pairing
H(Γv) = -E·(Γv) (W5b); spectrum pairing μ ∈ spec ↔ -μ ∈ spec (W5c);
zero-mode existence (W5d) and sublattice pinning `Γ·darkVec =
-darkVec` (W5e); bundled zero-mode pinning theorem (W5f); bright
eigenvector chiral image pairing W5g/g'; and the paper-facing
real-symmetric-anti-unitary framing marker (W5h). Together these
encode the full "real meridian path + chiral-protected zero mode"
story from the Phase 5t roadmap W5 spec, without touching the
adiabatic theorem or Berry-phase holonomy machinery. -/
theorem fermi_hubbard_dimer_wave5_summary : True := trivial

/-! ### Section 11. W5 strengthening (chiral-invariance + projectors +
zero-mode uniqueness) — Phase 5t W5 round 2

Deepens the W5 core with four additional pieces:

1. **Chiral invariance of ker(H)** (W5i). Direct corollary of W5b with
   E = 0: any zero-mode vector remains a zero-mode under the action
   of Γ. Establishes that Γ restricts to an involution on the kernel.

2. **Γ preserves nonzero-ness** (W5j). Via Γ² = I, the chiral map is
   an involution, hence injective. This makes the W5b/g/g' "pairing"
   genuine — it rules out the pathological case `Γ v = 0` when v ≠ 0.

3. **Multiset-level spectrum pairing** (W5k). Strengthens W5c from the
   `spectrum ℝ`-set level to the `charpoly.roots`-multiset level. The
   explicit multiset `{0} + {√g} + {-√g}` is invariant under the
   `Multiset.map Neg.neg` action.

4. **Chiral sublattice projectors** (W5l–W5o2). Define
   `P_+ := (1 + Γ)/2` and `P_- := (1 - Γ)/2`. Prove the projector
   algebra:
   - `P_±² = P_±` (W5l, W5m: idempotent)
   - `P_+ · P_- = 0` (W5n: orthogonal)
   - `P_+ + P_- = 1` (W5o: complete)
   - `Γ · P_+ = P_+` and `Γ · P_- = -P_-` (W5o1, W5o2: Γ acts as ±1
     on the ±1 eigenspaces)
   These are load-bearing for the W6 SWAP-gate construction
   — the SWAP acts as a phase on the `{|t₀⟩, |s⟩}` subspace, and the
   chiral projectors make the `V_+ ⊕ V_-` decomposition first-class.

5. **Zero-mode uniqueness up to scalar** (W5p). The kernel of
   `H_singlet t Δ 0` is 1-dimensional (when `(t, Δ) ≠ (0, 0)`):
   every zero-mode vector is a scalar multiple of `darkVec`. This is
   the strongest "pinning" statement — not just "a zero mode exists
   and lives in the (-1)-eigenspace of Γ" (W5f), but "the zero-mode
   space *is* ℝ · darkVec". Proof is by direct componentwise expansion
   of the mulVec equation + case split on Δ = 0 vs Δ ≠ 0, with
   explicit scalar witnesses in each branch. -/

/-- **W5i (zero_mode_space_is_chiral_invariant).** If `v` is a
zero-mode of `H_singlet t Δ 0`, then so is `Γ v`. Direct corollary
of W5b (eigenvector pairing) with E = 0: `(-0) • Γv = 0`. -/
theorem zero_mode_space_is_chiral_invariant (t Δ : ℝ) (v : Fin 3 → ℝ)
    (hv : (H_singlet t Δ 0).mulVec v = 0) :
    (H_singlet t Δ 0).mulVec (chiralOp.mulVec v) = 0 := by
  have h : (H_singlet t Δ 0).mulVec v = (0 : ℝ) • v := by
    rw [hv]; simp
  have := chiral_maps_eigenvector t Δ 0 v h
  simpa using this

/-- **W5j (chiral_preserves_nonzero).** The chiral operator is
injective (via Γ² = I), so it preserves nonzero-ness:
`v ≠ 0 ⟹ Γ v ≠ 0`. Makes the W5b/g/g' ± pairing genuine
(rules out the pathological `Γ v = 0` case). -/
theorem chiral_preserves_nonzero (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    chiralOp.mulVec v ≠ 0 := by
  intro hΓv
  apply hv
  -- From Γv = 0 and Γ² = I: v = (Γ·Γ)v = Γ(Γv) = Γ·0 = 0.
  have : chiralOp.mulVec (chiralOp.mulVec v) = 0 := by
    rw [hΓv]; simp
  rw [Matrix.mulVec_mulVec, chiralOp_sq, Matrix.one_mulVec] at this
  exact this

/-- **W5k (charpoly_roots_U0_symmetric_under_neg).** The multiset of
roots of the U=0 charpoly is invariant under negation:
`roots.map Neg.neg = roots`. Strengthens W5c (set-level `μ ∈ spec ↔
-μ ∈ spec`) to the multiset level (with multiplicities). Direct
consequence of the explicit factorization W4o:
`roots = {0} + {√g} + {-√g}`, and negation maps this multiset
`{0} + {-√g} + {√g}` which is the same multiset (addition on Multiset
is commutative). -/
theorem charpoly_roots_U0_symmetric_under_neg (t Δ : ℝ) :
    (H_singlet t Δ 0).charpoly.roots.map Neg.neg =
      (H_singlet t Δ 0).charpoly.roots := by
  rw [charpoly_H_singlet_U0_roots]
  simp only [Multiset.map_add, Multiset.map_singleton, neg_zero, neg_neg]
  -- Goal: {0} + {-√g} + {√g} = {0} + {√g} + {-√g}.
  -- Multiset addition is commutative; reassociate + commute the last two
  -- singleton summands.
  rw [add_right_comm]

/-! #### Section 11b. Chiral sublattice projectors (W5l–W5o2) -/

/-- The `(+1)`-eigenspace projector of the chiral operator:
`P_+ := (1 + Γ)/2`. For `Γ = diag(+1, -1, -1)` this projects onto
span{(1, 0, 0)} = `ℝ·|D₊⟩` (the 1-dim sublattice). -/
noncomputable def chiralProjPlus : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / 2 : ℝ) • ((1 : Matrix (Fin 3) (Fin 3) ℝ) + chiralOp)

/-- The `(-1)`-eigenspace projector of the chiral operator:
`P_- := (1 - Γ)/2`. For `Γ = diag(+1, -1, -1)` this projects onto
span{(0, 1, 0), (0, 0, 1)} = `ℝ·|D₋⟩ ⊕ ℝ·|s⟩` (the 2-dim sublattice,
where the zero mode `darkVec` lives by W5e). -/
noncomputable def chiralProjMinus : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / 2 : ℝ) • ((1 : Matrix (Fin 3) (Fin 3) ℝ) - chiralOp)

/-- **W5l (chiralProjPlus_sq).** `P_+` is idempotent: `P_+² = P_+`. -/
theorem chiralProjPlus_sq :
    chiralProjPlus * chiralProjPlus = chiralProjPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralProjPlus, chiralOp, Matrix.mul_apply,
          Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
          Fin.sum_univ_three] <;> ring

/-- **W5m (chiralProjMinus_sq).** `P_-` is idempotent: `P_-² = P_-`. -/
theorem chiralProjMinus_sq :
    chiralProjMinus * chiralProjMinus = chiralProjMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralProjMinus, chiralOp, Matrix.mul_apply,
          Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
          Fin.sum_univ_three] <;> ring

/-- **W5n (chiralProj_orthogonal).** The two sublattice projectors
are orthogonal: `P_+ · P_- = 0` (and symmetrically `P_- · P_+ = 0`).
The `+1` and `-1` eigenspaces of Γ intersect trivially. -/
theorem chiralProjPlus_chiralProjMinus :
    chiralProjPlus * chiralProjMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralProjPlus, chiralProjMinus, chiralOp, Matrix.mul_apply,
          Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
          Matrix.one_apply, Fin.sum_univ_three]

/-- **W5n' (chiralProjMinus_chiralProjPlus).** Mirror of W5n. -/
theorem chiralProjMinus_chiralProjPlus :
    chiralProjMinus * chiralProjPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralProjPlus, chiralProjMinus, chiralOp, Matrix.mul_apply,
          Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
          Matrix.one_apply, Fin.sum_univ_three]

/-- **W5o (chiralProj_complete).** The two sublattice projectors are
complete: `P_+ + P_- = 1`. Together with W5l/m/n this is the full
projector algebra on the `V_+ ⊕ V_-` sublattice decomposition of
ℝ³. -/
theorem chiralProj_complete :
    chiralProjPlus + chiralProjMinus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralProjPlus, chiralProjMinus, chiralOp,
          Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
          Matrix.one_apply] <;> ring

/-- **W5o1 (chiralOp_mul_chiralProjPlus).** Γ acts as `+1` on the
`(+1)`-eigenspace: `Γ · P_+ = P_+`. Algebraically:
`Γ (1 + Γ)/2 = (Γ + Γ²)/2 = (Γ + 1)/2 = P_+`. -/
theorem chiralOp_mul_chiralProjPlus :
    chiralOp * chiralProjPlus = chiralProjPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralProjPlus, chiralOp, Matrix.mul_apply,
          Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
          Fin.sum_univ_three] <;> ring

/-- **W5o2 (chiralOp_mul_chiralProjMinus).** Γ acts as `-1` on the
`(-1)`-eigenspace: `Γ · P_- = -P_-`. Algebraically:
`Γ (1 - Γ)/2 = (Γ - Γ²)/2 = (Γ - 1)/2 = -P_-`. -/
theorem chiralOp_mul_chiralProjMinus :
    chiralOp * chiralProjMinus = -chiralProjMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralProjMinus, chiralOp, Matrix.mul_apply,
          Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
          Fin.sum_univ_three, Matrix.neg_apply]

/-! #### Section 11c. Zero-mode uniqueness up to scalar (W5p) -/

/-- **W5p (zero_mode_unique_up_to_scalar).** The kernel of
`H_singlet t Δ 0` is 1-dimensional whenever `(t, Δ) ≠ (0, 0)`: every
zero-mode vector is a scalar multiple of `darkVec t Δ`. This is the
strongest "pinning" statement — not just "a zero mode exists and lives
in the (-1)-eigenspace of Γ" (W5e/f), but "the zero-mode space is
exactly `ℝ · darkVec`".

Proof is by direct componentwise expansion of the mulVec equation:
  Row 0: `Δ · v₁ - 2t · v₂ = 0`
  Row 1: `Δ · v₀ = 0`
  Row 2: `-2t · v₀ = 0`
Combined with `(t, Δ) ≠ (0, 0)` this forces `v₀ = 0` and yields a
linear relation between `v₁` and `v₂` compatible with `darkVec =
(0, 2t, Δ)`. The explicit scalar is `c = v₂ / Δ` when Δ ≠ 0, and
`c = v₁ / (2t)` when Δ = 0 (hence `t ≠ 0`). -/
theorem zero_mode_unique_up_to_scalar {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0)
    (v : Fin 3 → ℝ) (hv : (H_singlet t Δ 0).mulVec v = 0) :
    ∃ c : ℝ, v = c • darkVec t Δ := by
  have h0 : Δ * v 1 + -(2 * t) * v 2 = 0 := by
    have := congr_fun hv 0
    simpa [H_singlet, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      using this
  have h1 : Δ * v 0 = 0 := by
    have := congr_fun hv 1
    simpa [H_singlet, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      using this
  have h2 : -(2 * t) * v 0 = 0 := by
    have := congr_fun hv 2
    simpa [H_singlet, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      using this
  -- Force v 0 = 0 from (t, Δ) ≠ (0, 0).
  have hv0 : v 0 = 0 := by
    cases h with
    | inl ht =>
      have h2' : t * v 0 = 0 := by linarith
      rcases mul_eq_zero.mp h2' with ht' | hv0'
      · exact absurd ht' ht
      · exact hv0'
    | inr hΔ =>
      rcases mul_eq_zero.mp h1 with hΔ' | hv0'
      · exact absurd hΔ' hΔ
      · exact hv0'
  -- Case on whether Δ = 0 or not.
  by_cases hΔ : Δ = 0
  · -- Δ = 0 forces t ≠ 0 (from h).
    have ht : t ≠ 0 := by
      cases h with
      | inl ht => exact ht
      | inr hΔ' => exact absurd hΔ hΔ'
    -- With Δ = 0, h0 becomes `-2t · v 2 = 0`, so v 2 = 0.
    have hv2 : v 2 = 0 := by
      have : -(2 * t) * v 2 = 0 := by rw [hΔ] at h0; linarith
      have ht' : t * v 2 = 0 := by linarith
      rcases mul_eq_zero.mp ht' with h' | h'
      · exact absurd h' ht
      · exact h'
    -- darkVec at Δ=0 is (0, 2t, 0); pick c = v 1 / (2t).
    refine ⟨v 1 / (2 * t), ?_⟩
    funext i
    fin_cases i
    · simp [darkVec, hv0]
    · simp [darkVec]; field_simp
    · simp [darkVec, hv2, hΔ]
  · -- Δ ≠ 0: pick c = v 2 / Δ.
    refine ⟨v 2 / Δ, ?_⟩
    funext i
    fin_cases i
    · simp [darkVec, hv0]
    · -- Goal: v 1 = (v 2 / Δ) • (2 * t) = 2t · v 2 / Δ.
      -- From h0: Δ · v 1 = 2t · v 2. Divide by Δ.
      simp [darkVec]
      field_simp
      linarith
    · -- Goal: v 2 = (v 2 / Δ) • Δ.
      simp [darkVec]
      field_simp

/-- Summary marker for the Phase 5t Wave 5 round-2 strengthening
(non-load-bearing; placeholder for graph integrity). Round-2
delivers chiral invariance of ker(H) (W5i); Γ preserves nonzero (W5j);
multiset-level spectrum pairing (W5k); the chiral sublattice
projector algebra (W5l–W5o2: idempotent, orthogonal, complete, with
Γ acting as ±1 on the ±1 eigenspaces); and zero-mode uniqueness up to
scalar (W5p — the kernel of `H_singlet t Δ 0` is exactly
`ℝ · darkVec`). -/
theorem fermi_hubbard_dimer_wave5_round2_summary : True := trivial

/-! ### Section 12. Phase 5t W6A: EuclideanSpace infrastructure +
normalized eigenvectors + orthonormality

Path A migration (per 2026-04-25 session-8 explore-agent decision:
see `temporary/working-docs/W6_normalization_decision.md`). The
existing W4 eigenvectors `darkVec`, `brightVecPlus`, `brightVecMinus`
typed as `Fin 3 → ℝ` have the sup-norm (L∞) as their default Mathlib
norm, which is NOT the Euclidean norm. For W6's SWAP-gate unitarity
proof we need L2-normalized eigenvectors, which means either retyping
to `EuclideanSpace ℝ (Fin 3)` (Path A) or building a local
`dotProduct v v = 1` predicate (Path B).

Path A is preferred because:
1. Mathlib's `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`
   gives one-line unitarity from an orthonormal basis, whereas
   Path B requires manual `Matrix.mem_unitaryGroup_iff` unrolling.
2. Full `InnerProductSpace` API becomes available for downstream
   spectral-theorem / adjoint / orthogonal-projection work.

This section builds the EuclideanSpace-typed infrastructure
additively — we do not retype the existing W4 defs, we simply add
new defs typed as `EuclideanSpace ℝ (Fin 3)` plus bridge lemmas
connecting them to the W4 versions via component equality. -/

/-- The EuclideanSpace version of `darkVec`: the same data as the
`Fin 3 → ℝ` version, but typed with the L2 (Euclidean) norm. -/
noncomputable def darkVecE (t Δ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (darkVec t Δ)

/-- The EuclideanSpace version of `brightVecPlus`. -/
noncomputable def brightVecPlusE (t Δ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (brightVecPlus t Δ)

/-- The EuclideanSpace version of `brightVecMinus`. -/
noncomputable def brightVecMinusE (t Δ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (brightVecMinus t Δ)

/-- Componentwise: `darkVecE` agrees with `darkVec` on each index. -/
@[simp]
theorem darkVecE_apply (t Δ : ℝ) (i : Fin 3) :
    darkVecE t Δ i = darkVec t Δ i := rfl

/-- Componentwise: `brightVecPlusE` agrees with `brightVecPlus`. -/
@[simp]
theorem brightVecPlusE_apply (t Δ : ℝ) (i : Fin 3) :
    brightVecPlusE t Δ i = brightVecPlus t Δ i := rfl

/-- Componentwise: `brightVecMinusE` agrees with `brightVecMinus`. -/
@[simp]
theorem brightVecMinusE_apply (t Δ : ℝ) (i : Fin 3) :
    brightVecMinusE t Δ i = brightVecMinus t Δ i := rfl

/-- **W6A-N1 (darkVecE_norm_sq).** The L2 norm-squared of `darkVecE`
is `Δ² + 4t² = gap²`. Closes via `EuclideanSpace.real_norm_sq_eq`
unfolding the L2 norm as `∑ i, (x i)²`, then componentwise
evaluation on `![0, 2t, Δ]`. -/
theorem darkVecE_norm_sq (t Δ : ℝ) :
    ‖darkVecE t Δ‖ ^ 2 = Δ^2 + 4*t^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [darkVecE_apply, darkVec, Fin.sum_univ_three]
  ring

/-- **W6A-N2 (brightVecPlusE_norm_sq).** The L2 norm-squared of
`brightVecPlusE` is `2·(Δ² + 4t²) = 2·gap²`. The `√g` component
contributes `g`, plus `Δ²` plus `4t²`. -/
theorem brightVecPlusE_norm_sq (t Δ : ℝ) :
    ‖brightVecPlusE t Δ‖ ^ 2 = 2 * (Δ^2 + 4*t^2) := by
  have hg : (0 : ℝ) ≤ Δ^2 + 4*t^2 := by positivity
  have hsq : Real.sqrt (Δ^2 + 4*t^2) ^ 2 = Δ^2 + 4*t^2 := Real.sq_sqrt hg
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [brightVecPlusE_apply, brightVecPlus, Fin.sum_univ_three]
  linarith [hsq]

/-- **W6A-N3 (brightVecMinusE_norm_sq).** Same as W6A-N2 mirror. -/
theorem brightVecMinusE_norm_sq (t Δ : ℝ) :
    ‖brightVecMinusE t Δ‖ ^ 2 = 2 * (Δ^2 + 4*t^2) := by
  have hg : (0 : ℝ) ≤ Δ^2 + 4*t^2 := by positivity
  have hsq : Real.sqrt (Δ^2 + 4*t^2) ^ 2 = Δ^2 + 4*t^2 := Real.sq_sqrt hg
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [brightVecMinusE_apply, brightVecMinus, Fin.sum_univ_three]
  linarith [hsq]

/-- **W6A-N4 (darkVecE_norm_eq_gap).** The L2 norm of `darkVecE` is
`gap = √(Δ² + 4t²)`. -/
theorem darkVecE_norm_eq_gap (t Δ : ℝ) :
    ‖darkVecE t Δ‖ = Real.sqrt (Δ^2 + 4*t^2) := by
  have h := darkVecE_norm_sq t Δ
  have hg : (0 : ℝ) ≤ Δ^2 + 4*t^2 := by positivity
  have hn : (0 : ℝ) ≤ ‖darkVecE t Δ‖ := norm_nonneg _
  nlinarith [Real.sq_sqrt hg, Real.sqrt_nonneg (Δ^2 + 4*t^2), h]

/-- **W6A-N5 (brightVecPlusE_norm_eq).** The L2 norm of
`brightVecPlusE` is `√2 · gap`. -/
theorem brightVecPlusE_norm_eq (t Δ : ℝ) :
    ‖brightVecPlusE t Δ‖ = Real.sqrt 2 * Real.sqrt (Δ^2 + 4*t^2) := by
  have h := brightVecPlusE_norm_sq t Δ
  have hg : (0 : ℝ) ≤ Δ^2 + 4*t^2 := by positivity
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hsqrtg : Real.sqrt (Δ^2 + 4*t^2) ^ 2 = Δ^2 + 4*t^2 := Real.sq_sqrt hg
  have hn : (0 : ℝ) ≤ ‖brightVecPlusE t Δ‖ := norm_nonneg _
  have hrhs : (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt (Δ^2 + 4*t^2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [hsqrt2, hsqrtg, h]

/-- **W6A-N6 (brightVecMinusE_norm_eq).** Mirror of N5. -/
theorem brightVecMinusE_norm_eq (t Δ : ℝ) :
    ‖brightVecMinusE t Δ‖ = Real.sqrt 2 * Real.sqrt (Δ^2 + 4*t^2) := by
  have h := brightVecMinusE_norm_sq t Δ
  have hg : (0 : ℝ) ≤ Δ^2 + 4*t^2 := by positivity
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hsqrtg : Real.sqrt (Δ^2 + 4*t^2) ^ 2 = Δ^2 + 4*t^2 := Real.sq_sqrt hg
  have hn : (0 : ℝ) ≤ ‖brightVecMinusE t Δ‖ := norm_nonneg _
  have hrhs : (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt (Δ^2 + 4*t^2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [hsqrt2, hsqrtg, h]

/-! #### Section 12b. Normalized eigenvectors (W6A unit vectors) -/

/-- The L2-normalized dark-state eigenvector:
`darkVecNorm := gap⁻¹ • darkVecE`. Unit-norm when `(t, Δ) ≠ (0, 0)`.
Matches the physics convention of a normalized dark state. -/
noncomputable def darkVecNorm (t Δ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (Real.sqrt (Δ^2 + 4*t^2))⁻¹ • darkVecE t Δ

/-- The L2-normalized positive-energy bright eigenvector:
`brightVecPlusNorm := (√2 · gap)⁻¹ • brightVecPlusE`. -/
noncomputable def brightVecPlusNorm (t Δ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (Real.sqrt 2 * Real.sqrt (Δ^2 + 4*t^2))⁻¹ • brightVecPlusE t Δ

/-- The L2-normalized negative-energy bright eigenvector. -/
noncomputable def brightVecMinusNorm (t Δ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (Real.sqrt 2 * Real.sqrt (Δ^2 + 4*t^2))⁻¹ • brightVecMinusE t Δ

/-- **W6A-U1 (darkVecNorm_norm).** `‖darkVecNorm t Δ‖ = 1` when
`(t, Δ) ≠ (0, 0)` (so `gap > 0` and the inverse is well-defined). -/
theorem darkVecNorm_norm {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    ‖darkVecNorm t Δ‖ = 1 := by
  have hg : 0 < Δ^2 + 4*t^2 := by
    cases h with
    | inl ht => positivity
    | inr hΔ => positivity
  have hsqrt : 0 < Real.sqrt (Δ^2 + 4*t^2) := Real.sqrt_pos.mpr hg
  unfold darkVecNorm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt),
      darkVecE_norm_eq_gap, inv_mul_cancel₀ hsqrt.ne']

/-- **W6A-U2 (brightVecPlusNorm_norm).** `‖brightVecPlusNorm‖ = 1`
when `(t, Δ) ≠ (0, 0)`. -/
theorem brightVecPlusNorm_norm {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    ‖brightVecPlusNorm t Δ‖ = 1 := by
  have hg : 0 < Δ^2 + 4*t^2 := by
    cases h with
    | inl ht => positivity
    | inr hΔ => positivity
  have hsqrt : 0 < Real.sqrt (Δ^2 + 4*t^2) := Real.sqrt_pos.mpr hg
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have hprod : 0 < Real.sqrt 2 * Real.sqrt (Δ^2 + 4*t^2) :=
    mul_pos hsqrt2 hsqrt
  unfold brightVecPlusNorm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hprod),
      brightVecPlusE_norm_eq, inv_mul_cancel₀ hprod.ne']

/-- **W6A-U3 (brightVecMinusNorm_norm).** Mirror of U2. -/
theorem brightVecMinusNorm_norm {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    ‖brightVecMinusNorm t Δ‖ = 1 := by
  have hg : 0 < Δ^2 + 4*t^2 := by
    cases h with
    | inl ht => positivity
    | inr hΔ => positivity
  have hsqrt : 0 < Real.sqrt (Δ^2 + 4*t^2) := Real.sqrt_pos.mpr hg
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have hprod : 0 < Real.sqrt 2 * Real.sqrt (Δ^2 + 4*t^2) :=
    mul_pos hsqrt2 hsqrt
  unfold brightVecMinusNorm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hprod),
      brightVecMinusE_norm_eq, inv_mul_cancel₀ hprod.ne']

/-! #### Section 12c. Inner-product bridge + orthonormality (W6A-3) -/

/-- **W6A-I1 (darkVecE_brightVecPlusE_inner).** The EuclideanSpace
inner product `⟪darkVecE, brightVecPlusE⟫ = 0` — bridges W4l to the
inner-product form. Over ℝ, `@inner ℝ _ _ x y` on `EuclideanSpace ℝ ι`
is definitionally `dotProduct y.ofLp (star x.ofLp)`, and `star v = v`
for `v : Fin n → ℝ` (trivial star on ℝ-valued functions), so the
inner product equals `dotProduct (brightVecPlus) (darkVec)` which is
the commuted form of W4l. -/
theorem darkVecE_brightVecPlusE_inner (t Δ : ℝ) :
    @inner ℝ _ _ (darkVecE t Δ) (brightVecPlusE t Δ) = 0 := by
  show dotProduct (brightVecPlus t Δ) (darkVec t Δ) = 0
  rw [dotProduct_comm]
  exact dark_brightPlus_orthogonal t Δ

/-- **W6A-I2 (darkVecE_brightVecMinusE_inner).** Mirror of I1. -/
theorem darkVecE_brightVecMinusE_inner (t Δ : ℝ) :
    @inner ℝ _ _ (darkVecE t Δ) (brightVecMinusE t Δ) = 0 := by
  show dotProduct (brightVecMinus t Δ) (darkVec t Δ) = 0
  rw [dotProduct_comm]
  exact dark_brightMinus_orthogonal t Δ

/-- **W6A-I3 (brightVecPlusE_brightVecMinusE_inner).** -/
theorem brightVecPlusE_brightVecMinusE_inner (t Δ : ℝ) :
    @inner ℝ _ _ (brightVecPlusE t Δ) (brightVecMinusE t Δ) = 0 := by
  show dotProduct (brightVecMinus t Δ) (brightVecPlus t Δ) = 0
  rw [dotProduct_comm]
  exact brightPlus_brightMinus_orthogonal t Δ

/-- **W6A-I1' (darkVecNorm_brightVecPlusNorm_inner).** The normalized
versions inherit orthogonality from the unnormalized W6A-I1 via
bilinearity of the inner product. -/
theorem darkVecNorm_brightVecPlusNorm_inner (t Δ : ℝ) :
    @inner ℝ _ _ (darkVecNorm t Δ) (brightVecPlusNorm t Δ) = 0 := by
  unfold darkVecNorm brightVecPlusNorm
  rw [real_inner_smul_left, real_inner_smul_right,
      darkVecE_brightVecPlusE_inner]
  ring

/-- **W6A-I2' (darkVecNorm_brightVecMinusNorm_inner).** -/
theorem darkVecNorm_brightVecMinusNorm_inner (t Δ : ℝ) :
    @inner ℝ _ _ (darkVecNorm t Δ) (brightVecMinusNorm t Δ) = 0 := by
  unfold darkVecNorm brightVecMinusNorm
  rw [real_inner_smul_left, real_inner_smul_right,
      darkVecE_brightVecMinusE_inner]
  ring

/-- **W6A-I3' (brightVecPlusNorm_brightVecMinusNorm_inner).** -/
theorem brightVecPlusNorm_brightVecMinusNorm_inner (t Δ : ℝ) :
    @inner ℝ _ _ (brightVecPlusNorm t Δ) (brightVecMinusNorm t Δ) = 0 := by
  unfold brightVecPlusNorm brightVecMinusNorm
  rw [real_inner_smul_left, real_inner_smul_right,
      brightVecPlusE_brightVecMinusE_inner]
  ring

/-- **W6A-O1 (eigenvector_triple_orthonormal).** The three L2-normalized
eigenvectors `![darkVecNorm, brightVecPlusNorm, brightVecMinusNorm]`
form an orthonormal family in `EuclideanSpace ℝ (Fin 3)` when
`(t, Δ) ≠ (0, 0)`. Combines the three norm-equals-one lemmas
(W6A-U1/U2/U3) with the three inner-product-zero bridge lemmas
(W6A-I1'/I2'/I3') via `orthonormal_vecCons_iff` recursion. -/
theorem eigenvector_triple_orthonormal {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    Orthonormal ℝ
      (![darkVecNorm t Δ, brightVecPlusNorm t Δ,
         brightVecMinusNorm t Δ] :
         Fin 3 → EuclideanSpace ℝ (Fin 3)) := by
  rw [orthonormal_vecCons_iff]
  refine ⟨darkVecNorm_norm h, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact darkVecNorm_brightVecPlusNorm_inner t Δ
    · exact darkVecNorm_brightVecMinusNorm_inner t Δ
  · rw [orthonormal_vecCons_iff]
    refine ⟨brightVecPlusNorm_norm h, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact brightVecPlusNorm_brightVecMinusNorm_inner t Δ
    · rw [show (Matrix.vecCons (brightVecMinusNorm t Δ) ![] :
             Fin 1 → EuclideanSpace ℝ (Fin 3)) = fun _ => brightVecMinusNorm t Δ from by
            funext i; fin_cases i; rfl]
      refine ⟨fun _ => brightVecMinusNorm_norm h, ?_⟩
      intros i j hij
      fin_cases i
      fin_cases j
      exact absurd rfl hij

/-- Summary marker for Phase 5t W6A infrastructure shipment
(non-load-bearing). W6A delivers: `darkVecE`/`brightVecPlusE`/
`brightVecMinusE` as `EuclideanSpace ℝ (Fin 3)` versions of the W4
eigenvectors; componentwise bridge lemmas; explicit L2 norm formulas
(`‖darkVecE‖ = gap`, `‖brightVec±E‖ = √2 · gap`); L2-normalized
versions `darkVecNorm`/`brightVecPlusNorm`/`brightVecMinusNorm`;
`‖·Norm‖ = 1` witnesses; EuclideanSpace inner-product bridge lemmas
(W6A-I1/I2/I3 + I1'/I2'/I3'); and the `Orthonormal` predicate on the
normalized triple. Foundation for W6B (OrthonormalBasis construction
+ unitarity via `toMatrix_orthonormalBasis_mem_unitary`) and W6C
(SWAP gate action on computational basis). -/
theorem fermi_hubbard_dimer_wave6A_summary : True := trivial

/-! ### Section 13. Phase 5t W6B: OrthonormalBasis construction +
unitarity of change-of-basis

Building on the W6A orthonormality predicate, we construct the
eigenbasis as a `Module.Basis` (via `basisOfOrthonormalOfCardEqFinrank`
since the 3 orthonormal vectors fill `finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3`)
and then lift it to an `OrthonormalBasis` via `Basis.toOrthonormalBasis`.
The change-of-basis matrix from the standard basis `EuclideanSpace.basisFun`
to this eigenbasis is automatically unitary via Mathlib's
`OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`. -/

/-- The eigenvector Module.Basis: 3 orthonormal vectors in a 3-dim
space form a basis. -/
noncomputable def eigenBasisModule {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    Module.Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  basisOfOrthonormalOfCardEqFinrank
    (eigenvector_triple_orthonormal h)
    (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])

/-- The eigenbasis as an `OrthonormalBasis`. Lifted from
`eigenBasisModule` via `Basis.toOrthonormalBasis`. -/
noncomputable def eigenBasis {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  (eigenBasisModule h).toOrthonormalBasis (by
    unfold eigenBasisModule
    rw [coe_basisOfOrthonormalOfCardEqFinrank]
    exact eigenvector_triple_orthonormal h)

/-- **W6B-B1 (eigenBasis_apply).** Componentwise: `eigenBasis i` is
the `i`-th normalized eigenvector. -/
theorem eigenBasis_apply {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) (i : Fin 3) :
    eigenBasis h i =
      ![darkVecNorm t Δ, brightVecPlusNorm t Δ,
        brightVecMinusNorm t Δ] i := by
  unfold eigenBasis eigenBasisModule
  rw [Module.Basis.coe_toOrthonormalBasis,
      coe_basisOfOrthonormalOfCardEqFinrank]

/-- **W6B-B2 (eigenBasis_zero).** The zeroth basis vector is
`darkVecNorm`. -/
@[simp]
theorem eigenBasis_zero {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    eigenBasis h 0 = darkVecNorm t Δ := by
  rw [eigenBasis_apply]; rfl

/-- **W6B-B3 (eigenBasis_one).** The first basis vector is
`brightVecPlusNorm`. -/
@[simp]
theorem eigenBasis_one {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    eigenBasis h 1 = brightVecPlusNorm t Δ := by
  rw [eigenBasis_apply]; rfl

/-- **W6B-B4 (eigenBasis_two).** The second basis vector is
`brightVecMinusNorm`. -/
@[simp]
theorem eigenBasis_two {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    eigenBasis h 2 = brightVecMinusNorm t Δ := by
  rw [eigenBasis_apply]; rfl

/-- **W6B-U1 (eigenBasis_change_of_basis_unitary).** The change-of-basis
matrix from the standard `EuclideanSpace.basisFun` orthonormal basis
to the eigenbasis is in the unitary group. This is the main
unitarity witness — one-line application of Mathlib's
`OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`.

For the SWAP gate construction (W6C), this means any operator
diagonal in the eigenbasis will be unitary in the standard basis
iff its eigenvalues all have modulus 1 — which is satisfied by the
`diag(-1, +1, +1)` geometric SWAP action on the singlet sector. -/
theorem eigenBasis_change_of_basis_unitary {t Δ : ℝ}
    (h : t ≠ 0 ∨ Δ ≠ 0) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix (eigenBasis h) ∈
      Matrix.unitaryGroup (Fin 3) ℝ :=
  OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _

/-- **W6B-U2 (eigenBasis_change_of_basis_orthogonal).** Over ℝ the
unitary group is the orthogonal group: `M · Mᵀ = 1`. Direct
consequence of W6B-U1 via `OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose`
(which for a real matrix gives `M · Mᵀ = 1`). -/
theorem eigenBasis_change_of_basis_transpose_mul_self {t Δ : ℝ}
    (h : t ≠ 0 ∨ Δ ≠ 0) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix (eigenBasis h) *
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix
        (eigenBasis h)).conjTranspose = 1 :=
  OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose _ _

/-- Summary marker for Phase 5t W6B shipment (non-load-bearing).
W6B delivers: `eigenBasisModule` as a `Module.Basis` from the W6A
orthonormal triple; `eigenBasis` as the promoted `OrthonormalBasis`;
componentwise apply lemmas (W6B-B2/B3/B4: `eigenBasis 0 = darkVecNorm`,
`eigenBasis 1 = brightVecPlusNorm`, `eigenBasis 2 = brightVecMinusNorm`);
and the change-of-basis matrix unitarity (W6B-U1) and its
`M · Mᵀ = 1` form (W6B-U2) via Mathlib's
`OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`. Foundation
for W6C (SWAP operator + action on computational basis). -/
theorem fermi_hubbard_dimer_wave6B_summary : True := trivial

/-! ### Section 14. Phase 5t W6C: Geometric SWAP operator + action
on the singlet sector

The idealized geometric SWAP operator on the singlet subspace is the
Householder-type reflection that acts as `-1` on the dark-state
subspace and `+1` on the bright subspace:
  `U_SWAP := I - 2 · |darkVecNorm⟩⟨darkVecNorm|`
In the `{|D₊⟩, |D₋⟩, |s⟩}` basis, this has the explicit rank-1
correction form
  `U_SWAP(i, j) = δ_{ij} - (2 / gap²) · darkVec(i) · darkVec(j)`
(The `gap² = Δ² + 4t²` denominator comes from normalizing the
unnormalized `darkVec = (0, 2t, Δ)`.)

Key properties proved in this section:
- Sign flip on the dark state: `U_SWAP · darkVec = -darkVec` (W6C-A1)
- Identity on bright states: `U_SWAP · brightVec± = brightVec±` (W6C-A2/A3)
- Symmetric: `U_SWAPᵀ = U_SWAP` (W6C-S1)
- Involution: `U_SWAP · U_SWAP = I` (W6C-S2)
- Orthogonal/Unitary: `U_SWAP · U_SWAPᵀ = I` (W6C-S3 — the core
  unitarity claim, a one-liner from S1 + S2) -/

/-- The geometric SWAP operator on the singlet subspace
`{|D₊⟩, |D₋⟩, |s⟩}`. In explicit rank-1-correction form:
  `U_SWAP(i, j) = δ_{ij} - (2 / (Δ²+4t²)) · darkVec(i) · darkVec(j)`
Implements the dark-state sign flip after a 2π cycle (the Berry phase
that makes the geometric SWAP gate work). -/
noncomputable def U_SWAP_singlet (t Δ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  1 - (2 / (Δ^2 + 4*t^2)) •
    Matrix.of (fun i j => darkVec t Δ i * darkVec t Δ j)

/-- **W6C-A1 (U_SWAP_singlet_darkVec).** The SWAP operator flips the
sign of the dark-state vector: `U_SWAP · darkVec = -darkVec` when
`(t, Δ) ≠ (0, 0)`. This is the core BDI gate action — the Berry
phase acquired on the closed parameter-loop cycle shows up as the
`-1` eigenvalue on the kernel direction. -/
theorem U_SWAP_singlet_darkVec {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    (U_SWAP_singlet t Δ).mulVec (darkVec t Δ) = -(darkVec t Δ) := by
  have hg : 0 < Δ^2 + 4*t^2 := by
    cases h with
    | inl ht => positivity
    | inr hΔ => positivity
  funext i
  fin_cases i <;>
    simp [U_SWAP_singlet, darkVec, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three, Matrix.sub_apply, Matrix.smul_apply,
          Matrix.one_apply, Matrix.of_apply] <;>
    field_simp <;> ring

/-- **W6C-A2 (U_SWAP_singlet_brightVecPlus).** The SWAP operator is
the identity on the positive-energy bright state:
`U_SWAP · brightVecPlus = brightVecPlus`. The bright state is
orthogonal to the dark-state kernel direction, so the rank-1
correction vanishes. -/
theorem U_SWAP_singlet_brightVecPlus {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    (U_SWAP_singlet t Δ).mulVec (brightVecPlus t Δ) =
      brightVecPlus t Δ := by
  have hg : 0 < Δ^2 + 4*t^2 := by
    cases h with
    | inl ht => positivity
    | inr hΔ => positivity
  funext i
  fin_cases i <;>
    simp [U_SWAP_singlet, darkVec, brightVecPlus, Matrix.mulVec,
          dotProduct, Fin.sum_univ_three, Matrix.sub_apply,
          Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply] <;>
    field_simp <;> ring

/-- **W6C-A3 (U_SWAP_singlet_brightVecMinus).** Mirror of A2. -/
theorem U_SWAP_singlet_brightVecMinus {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    (U_SWAP_singlet t Δ).mulVec (brightVecMinus t Δ) =
      brightVecMinus t Δ := by
  have hg : 0 < Δ^2 + 4*t^2 := by
    cases h with
    | inl ht => positivity
    | inr hΔ => positivity
  funext i
  fin_cases i <;>
    simp [U_SWAP_singlet, darkVec, brightVecMinus, Matrix.mulVec,
          dotProduct, Fin.sum_univ_three, Matrix.sub_apply,
          Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply] <;>
    field_simp <;> ring

/-- **W6C-S1 (U_SWAP_singlet_isSymm).** The SWAP operator is real
symmetric: `U_SWAPᵀ = U_SWAP`. Inherits symmetry from the identity
matrix and the symmetric outer product `darkVec ⊗ darkVec`. -/
theorem U_SWAP_singlet_isSymm (t Δ : ℝ) :
    (U_SWAP_singlet t Δ)ᵀ = U_SWAP_singlet t Δ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U_SWAP_singlet, darkVec, Matrix.transpose, Matrix.sub_apply,
          Matrix.one_apply, Matrix.of_apply, mul_comm]

/-- **W6C-S2 (U_SWAP_singlet_sq).** The SWAP operator squares to the
identity: `U_SWAP · U_SWAP = I`. A Householder reflection property:
`(I - 2P)² = I - 4P + 4P² = I` when `P² = P` (P is an idempotent
projector). Here `P = |darkVecNorm⟩⟨darkVecNorm|` is the rank-1
projector onto the dark-state subspace. -/
theorem U_SWAP_singlet_sq {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    U_SWAP_singlet t Δ * U_SWAP_singlet t Δ = 1 := by
  have hg : 0 < Δ^2 + 4*t^2 := by
    cases h with
    | inl ht => positivity
    | inr hΔ => positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U_SWAP_singlet, darkVec, Matrix.mul_apply, Fin.sum_univ_three,
          Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
          Matrix.of_apply] <;>
    field_simp <;> ring

/-- **W6C-S3 (U_SWAP_singlet_orthogonal).** The SWAP operator is
orthogonal: `U_SWAP · U_SWAPᵀ = I`. Immediate consequence of S1
(symmetric) + S2 (squares to I): `U · Uᵀ = U · U = I`. This is the
unitarity witness in the real case — the singlet-sector SWAP is a
bona fide unitary operator. -/
theorem U_SWAP_singlet_orthogonal {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    U_SWAP_singlet t Δ * (U_SWAP_singlet t Δ)ᵀ = 1 := by
  rw [U_SWAP_singlet_isSymm, U_SWAP_singlet_sq h]

/-- **W6C-S3' (U_SWAP_singlet_transpose_mul).** Mirror form:
`U_SWAPᵀ · U_SWAP = I`. -/
theorem U_SWAP_singlet_transpose_mul {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    (U_SWAP_singlet t Δ)ᵀ * U_SWAP_singlet t Δ = 1 := by
  rw [U_SWAP_singlet_isSymm, U_SWAP_singlet_sq h]

/-- **W6C-E1 (U_SWAP_singlet_eigenvalues).** The SWAP operator has
eigenvalues `{-1, +1, +1}` in the canonical order
`{darkVec, brightVecPlus, brightVecMinus}`. Bundled version of
W6C-A1/A2/A3 for downstream consumers. -/
theorem U_SWAP_singlet_eigenvalues {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    (U_SWAP_singlet t Δ).mulVec (darkVec t Δ) = (-1 : ℝ) • darkVec t Δ ∧
      (U_SWAP_singlet t Δ).mulVec (brightVecPlus t Δ) =
        (1 : ℝ) • brightVecPlus t Δ ∧
      (U_SWAP_singlet t Δ).mulVec (brightVecMinus t Δ) =
        (1 : ℝ) • brightVecMinus t Δ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [U_SWAP_singlet_darkVec h, neg_one_smul]
  · rw [U_SWAP_singlet_brightVecPlus h, one_smul]
  · rw [U_SWAP_singlet_brightVecMinus h, one_smul]

/-- **W6C-D1 (U_SWAP_singlet_det).** The SWAP operator has
determinant `-1` (orientation-reversing): `det U_SWAP = (-1)·1·1 =
-1`. Consistent with W6C-E1 eigenvalue `{-1, +1, +1}` (product of
eigenvalues). -/
theorem U_SWAP_singlet_det {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    (U_SWAP_singlet t Δ).det = -1 := by
  have hg : 0 < Δ^2 + 4*t^2 := by
    cases h with
    | inl ht => positivity
    | inr hΔ => positivity
  simp [U_SWAP_singlet, darkVec, Matrix.det_fin_three,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.of_apply]
  field_simp
  ring

/-- **W6C-T1 (U_SWAP_singlet_trace).** The SWAP operator has trace
`+1` (sum of eigenvalues `-1 + 1 + 1 = 1`). -/
theorem U_SWAP_singlet_trace {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    (U_SWAP_singlet t Δ).trace = 1 := by
  have hg : 0 < Δ^2 + 4*t^2 := by
    cases h with
    | inl ht => positivity
    | inr hΔ => positivity
  simp [U_SWAP_singlet, darkVec, Matrix.trace_fin_three,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.of_apply]
  field_simp
  ring

/-- Summary marker for Phase 5t W6C shipment (non-load-bearing).
W6C delivers: the geometric SWAP operator `U_SWAP_singlet` as a
Householder reflection `I - (2/gap²) · darkVec ⊗ darkVec`;
eigenvalue actions W6C-A1/A2/A3 (sign-flip on dark, identity on
brights); symmetry W6C-S1; involution W6C-S2 `U² = I`; orthogonality
W6C-S3 `U · Uᵀ = I` (the unitarity witness); eigenvalue bundle
W6C-E1; determinant W6C-D1 (`-1`) and trace W6C-T1 (`+1`)
consistency. Together with W6A/B, this completes the
finite-dimensional algebraic core of the Kiefer et al. doublon
geometric SWAP gate — as a "pure matrix computation" in the spirit
of the Phase 5t roadmap, without touching the adiabatic theorem
or Berry-phase holonomy machinery. -/
theorem fermi_hubbard_dimer_wave6C_summary : True := trivial

/-! ### Section 15. Wave 6 round-2 strengthening (2026-04-26 session 9)

This section adds three strengthening theorems on top of W6A/B/C:

- **Scalar-multiple SWAP action (W6C-A1s/A2s/A3s):** generalizes
  W6C-A1/A2/A3 from the explicit eigenvectors to any scalar multiple.
  Covers the normalized form `U · darkVecNorm = -darkVecNorm` as a
  special case (`c = gap⁻¹`) without needing a separate normalized
  statement in the `Fin 3 → ℝ` basis.
- **Unitary-group membership (W6C-U1):** packages `U · Uᵀ = 1` /
  `Uᵀ · U = 1` as membership in `Matrix.unitaryGroup (Fin 3) ℝ`. Over
  ℝ, `TrivialStar ℝ` gives `conjTranspose = transpose`, so unitary
  membership reduces to the orthogonality identity. Mathlib's
  unitary-submonoid API becomes the canonical form consumers can use.
- **Kernel action (W6C-K1):** for any `v ∈ ker(H_singlet t Δ 0)` with
  `(t, Δ) ≠ (0, 0)`, `U_SWAP v = -v`. Combines W5p (zero-mode
  uniqueness) with W6C-A1s (scalar-multiple sign flip) to give the
  strongest "SWAP acts as −1 on the full pinned zero-mode subspace"
  statement in the module. -/

/-- **W6C-A1s (U_SWAP_singlet_smul_darkVec).** The SWAP operator flips
the sign of any scalar multiple of the dark-state vector:
`U · (c • darkVec) = -(c • darkVec)`. Covers the normalized form
as the special case `c = gap⁻¹`. -/
theorem U_SWAP_singlet_smul_darkVec (c : ℝ) {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    (U_SWAP_singlet t Δ).mulVec (c • darkVec t Δ) = -(c • darkVec t Δ) := by
  rw [Matrix.mulVec_smul, U_SWAP_singlet_darkVec h, smul_neg]

/-- **W6C-A2s (U_SWAP_singlet_smul_brightVecPlus).** Identity on any
scalar multiple of the positive-energy bright state. -/
theorem U_SWAP_singlet_smul_brightVecPlus (c : ℝ) {t Δ : ℝ}
    (h : t ≠ 0 ∨ Δ ≠ 0) :
    (U_SWAP_singlet t Δ).mulVec (c • brightVecPlus t Δ) =
      c • brightVecPlus t Δ := by
  rw [Matrix.mulVec_smul, U_SWAP_singlet_brightVecPlus h]

/-- **W6C-A3s (U_SWAP_singlet_smul_brightVecMinus).** Mirror of A2s. -/
theorem U_SWAP_singlet_smul_brightVecMinus (c : ℝ) {t Δ : ℝ}
    (h : t ≠ 0 ∨ Δ ≠ 0) :
    (U_SWAP_singlet t Δ).mulVec (c • brightVecMinus t Δ) =
      c • brightVecMinus t Δ := by
  rw [Matrix.mulVec_smul, U_SWAP_singlet_brightVecMinus h]

/-- **W6C-U1 (U_SWAP_singlet_mem_unitaryGroup).** The SWAP operator is
a member of the Mathlib unitary submonoid `Matrix.unitaryGroup (Fin 3) ℝ`.
Over ℝ, `TrivialStar ℝ` gives `conjTranspose = transpose`, so unitary
membership reduces to `Uᵀ · U = 1` (W6C-S3'). This packages the
unitarity witness in the canonical Mathlib API form for downstream
consumers that expect `Matrix.unitaryGroup` membership (e.g., the
`OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary` path used in
W6B). -/
theorem U_SWAP_singlet_mem_unitaryGroup {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    U_SWAP_singlet t Δ ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff',
      Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  exact U_SWAP_singlet_transpose_mul h

/-- **W6C-K1 (U_SWAP_singlet_on_kernel).** The SWAP operator acts as
`-1` on the full kernel of `H_singlet t Δ 0`: for any `v` with
`H · v = 0` and `(t, Δ) ≠ (0, 0)`, `U_SWAP v = -v`. Combines W5p
(zero-mode uniqueness: every such `v` is a scalar multiple of
`darkVec`) with W6C-A1s (sign flip on any scalar multiple of
`darkVec`). This is the strongest "SWAP acts as −1 on the pinned
zero-mode subspace" statement in the module. -/
theorem U_SWAP_singlet_on_kernel {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0)
    (v : Fin 3 → ℝ) (hv : (H_singlet t Δ 0).mulVec v = 0) :
    (U_SWAP_singlet t Δ).mulVec v = -v := by
  obtain ⟨c, hc⟩ := zero_mode_unique_up_to_scalar h v hv
  rw [hc, U_SWAP_singlet_smul_darkVec c h]

/-- Summary marker for W6 round-2 strengthening (non-load-bearing).
Adds: W6C-A1s/A2s/A3s scalar-multiple eigenvector actions, W6C-U1
unitary-group membership in canonical Mathlib form, W6C-K1 kernel-action
theorem combining W5p uniqueness with W6C-A1s. -/
theorem fermi_hubbard_dimer_wave6_round2_summary : True := trivial

/-! ### Section 16. Wave 7 — Direct Exchange vs Superexchange Scaling
(2026-04-26 session 9)

This section formalizes the qualitative scaling distinction between
the direct-exchange regime (`U = 0`, gap set by hopping `t`) and the
superexchange regime (`U → ∞`, gap inherits `t²/U` dependence),
following the deep research *"Direct exchange vs superexchange in
doublon gates: what is safely formalizable"*
(`Lit-Search/Phase-5t/`).

**Algebraic foundation.** At `Δ = 0`, the characteristic polynomial
of `H_singlet t 0 U` factors as `(λ − U)·(λ² − U·λ − 4·t²)`, giving
three eigenvalues:
- `U` (antisymmetric doublon — the `|D₋⟩` direction),
- `E_plus(t, U) := (U + √(U² + 16·t²)) / 2`,
- `E_minus(t, U) := (U − √(U² + 16·t²)) / 2`.

The scaling story is about `E_plus` (upper symmetric-sector
eigenvalue) and the superexchange gap `J(t, U) := E_plus − U`. The
key claims are pure real-analysis facts about these explicit
functions, independent of the matrix interpretation.

**Theorems in this section:**
- **W7a:** `E_plus(t, 0) = 2·|t|` — direct-exchange gap value at
  `U = 0`.
- **W7b:** `E_plus(t, U) + E_minus(t, U) = U` — Vieta trace identity
  for the 2×2 sector quadratic.
- **W7c:** `E_plus(t, U) · E_minus(t, U) = −4·t²` — Vieta product
  identity (the negative constant term of the quadratic).
- **W7d:** `HasDerivAt (fun U ↦ E_plus t U) (1/2) 0` for `t ≠ 0` —
  the direct-exchange linear-in-`U` scaling (Taylor coefficient at
  `U = 0` is exactly `1/2`).
- **W7e:** `√(U² + 16·t²) ≥ 4·|t|` — foundational sqrt lower bound.
- **W7f:** Monotonicity: for any `t`, `U₁ ≤ U₂ ⟹ E_plus t U₁ ≤
  E_plus t U₂`.
- **W7g:** `J_superexchange(t, 0) = 2·|t|` — at `U = 0` the
  superexchange gap coincides with the direct exchange value
  (matching regimes).
- **W7h:** `√(1 + x) ≤ 1 + x/2` for `x ≥ 0` — sqrt upper bound (used
  in W7i).
- **W7i:** Superexchange approximation bound. For `0 < 4·|t| ≤ U`,
  `|J(t, U) − 4·t²/U| ≤ 16·t⁴/U³`.

W7i is the main Tier-2 quantitative-scaling theorem; W7a/W7d are the
Tier-1 direct-exchange statements; the rest are algebraic consistency
and foundations. -/

/-- The upper eigenvalue of the 2×2 symmetric sector of the
Fermi-Hubbard dimer at zero detuning:
`E_plus(t, U) := (U + √(U² + 16·t²)) / 2`. Root of the quadratic
`λ² − U·λ − 4·t² = 0`. -/
noncomputable def E_plus (t U : ℝ) : ℝ :=
  (U + Real.sqrt (U^2 + 16*t^2)) / 2

/-- The lower eigenvalue of the same 2×2 sector:
`E_minus(t, U) := (U − √(U² + 16·t²)) / 2`. -/
noncomputable def E_minus (t U : ℝ) : ℝ :=
  (U - Real.sqrt (U^2 + 16*t^2)) / 2

/-- The superexchange gap:
`J(t, U) := E_plus(t, U) − U = (√(U² + 16·t²) − U) / 2`. At large
`U` this approaches `4·t²/U` (textbook superexchange). -/
noncomputable def J_superexchange (t U : ℝ) : ℝ := E_plus t U - U

/-- **W7a (E_plus_value_at_zero).** The direct-exchange value: at
`U = 0` the upper eigenvalue is `E_plus(t, 0) = 2·|t|`. Computed via
`√(16·t²) = 4·|t|`. -/
theorem E_plus_value_at_zero (t : ℝ) :
    E_plus t 0 = 2 * |t| := by
  unfold E_plus
  have h : (0:ℝ)^2 + 16*t^2 = (4*|t|)^2 := by
    rw [mul_pow, sq_abs]; ring
  rw [h, Real.sqrt_sq (by positivity : (0:ℝ) ≤ 4*|t|)]
  ring

/-- **W7b (E_plus_plus_E_minus).** Vieta trace identity:
`E_plus(t, U) + E_minus(t, U) = U`. This matches the trace
`tr([[U, −2t], [−2t, 0]]) = U` of the 2×2 symmetric-sector block
(from the deep research). -/
theorem E_plus_plus_E_minus (t U : ℝ) :
    E_plus t U + E_minus t U = U := by
  unfold E_plus E_minus; ring

/-- **W7c (E_plus_times_E_minus).** Vieta product identity:
`E_plus(t, U) · E_minus(t, U) = −4·t²`. This matches the determinant
`det([[U, −2t], [−2t, 0]]) = −4·t²` of the 2×2 symmetric-sector
block. -/
theorem E_plus_times_E_minus (t U : ℝ) :
    E_plus t U * E_minus t U = -(4 * t^2) := by
  unfold E_plus E_minus
  have hnn : (0:ℝ) ≤ U^2 + 16*t^2 := by positivity
  have hsq : Real.sqrt (U^2 + 16*t^2) * Real.sqrt (U^2 + 16*t^2) =
      U^2 + 16*t^2 :=
    Real.mul_self_sqrt hnn
  nlinarith [hsq]

/-- **W7d (E_plus_hasDerivAt_at_zero).** The upper eigenvalue
`E_plus(t, ·)` has derivative exactly `1/2` at `U = 0` (for any
`t ≠ 0`). This is the direct-exchange linear-in-`U` scaling
theorem: the Taylor coefficient of `E_plus` at `U = 0` is `1/2`.
Equivalent statement: the leading `U`-dependent correction to the
direct-exchange gap is first-order in `U` with coefficient `1/2`. -/
theorem E_plus_hasDerivAt_at_zero (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun U => E_plus t U) (1/2) 0 := by
  have hpoly : HasDerivAt (fun U : ℝ => U^2 + 16*t^2) 0 0 := by
    have h1 : HasDerivAt (fun U : ℝ => U^2) (2 * 0 ^ (2 - 1) * 1) 0 :=
      (hasDerivAt_id 0).pow 2
    have h2 : HasDerivAt (fun U : ℝ => U^2) 0 0 := by simpa using h1
    simpa using h2.add_const (16*t^2)
  have ht2 : t^2 ≠ 0 := pow_ne_zero 2 ht
  have hval_ne : ((fun U : ℝ => U^2 + 16*t^2) 0) ≠ 0 := by
    simp only [ne_eq]
    intro h
    apply ht2
    nlinarith [h]
  have hsqrt : HasDerivAt (fun U : ℝ => Real.sqrt (U^2 + 16*t^2)) 0 0 := by
    have h := hpoly.sqrt hval_ne
    simpa [zero_div] using h
  have hsum : HasDerivAt
      (fun U : ℝ => U + Real.sqrt (U^2 + 16*t^2)) 1 0 := by
    have := (hasDerivAt_id 0).add hsqrt
    simpa using this
  have hdiv : HasDerivAt
      (fun U : ℝ => (U + Real.sqrt (U^2 + 16*t^2)) / 2) (1/2) 0 :=
    hsum.div_const 2
  exact hdiv

/-- **W7e (sqrt_lower_bound_abs_t).** Foundational inequality:
`√(U² + 16·t²) ≥ 4·|t|`. Follows from `U² + 16·t² ≥ (4·|t|)²` by
monotonicity of sqrt. -/
theorem sqrt_lower_bound_abs_t (t U : ℝ) :
    4 * |t| ≤ Real.sqrt (U^2 + 16*t^2) := by
  have hnn : (0:ℝ) ≤ 4 * |t| := by positivity
  have hsq : (4 * |t|)^2 ≤ U^2 + 16*t^2 := by
    have : (4 * |t|)^2 = 16 * t^2 := by rw [mul_pow, sq_abs]; ring
    nlinarith [sq_nonneg U, this]
  calc 4 * |t|
      = Real.sqrt ((4 * |t|)^2) := by rw [Real.sqrt_sq hnn]
    _ ≤ Real.sqrt (U^2 + 16*t^2) := Real.sqrt_le_sqrt hsq

/-- **W7f (E_plus_monotone_nonneg).** Monotonicity of `E_plus` in `U`
on the nonneg ray: for any fixed `t` and `0 ≤ U₁ ≤ U₂`,
`E_plus t U₁ ≤ E_plus t U₂`. Both the identity term and the
`√(U² + 16·t²)` term are monotone non-decreasing on `[0, ∞)`. -/
theorem E_plus_monotone_nonneg (t : ℝ) :
    MonotoneOn (fun U => E_plus t U) (Set.Ici 0) := by
  intro U₁ hU₁ U₂ hU₂ h
  simp only [Set.mem_Ici] at hU₁ hU₂
  unfold E_plus
  have hsq : U₁^2 ≤ U₂^2 := by nlinarith
  have hss : Real.sqrt (U₁^2 + 16*t^2) ≤ Real.sqrt (U₂^2 + 16*t^2) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

/-- **W7g (J_superexchange_at_zero).** At `U = 0`, the superexchange
gap coincides with the direct-exchange value:
`J_superexchange(t, 0) = 2·|t|`. Regimes meet at `U = 0`. -/
theorem J_superexchange_at_zero (t : ℝ) :
    J_superexchange t 0 = 2 * |t| := by
  unfold J_superexchange
  rw [E_plus_value_at_zero]; ring

/-- **W7h (sqrt_one_add_le).** For `x ≥ 0`, `√(1 + x) ≤ 1 + x/2`.
AM-GM–style inequality: `(1 + x/2)² = 1 + x + x²/4 ≥ 1 + x`. Used as
a step in the superexchange approximation bound W7i. -/
theorem sqrt_one_add_le (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (1 + x) ≤ 1 + x/2 := by
  have h1 : (0:ℝ) ≤ 1 + x/2 := by linarith
  have h2 : (1 + x) ≤ (1 + x/2)^2 := by nlinarith [sq_nonneg x]
  calc Real.sqrt (1 + x)
      ≤ Real.sqrt ((1 + x/2)^2) := Real.sqrt_le_sqrt h2
    _ = 1 + x/2 := Real.sqrt_sq h1

/-- **W7i (J_superexchange_bound).** The superexchange approximation
bound with explicit remainder: for `0 < 4·|t| ≤ U`,
`|J(t, U) − 4·t²/U| ≤ 16·t⁴/U³`. The leading superexchange coupling
`4·t²/U` approximates `J` with fourth-order-in-`t` error controlled
by `U³`. Matches the deep-research Tier-2 target.

**Proof architecture.** The key algebraic identity is
  `J − 4·t²/U = -(s − U)² / (4·U)`
where `s := √(U² + 16·t²)`. This follows from `s² = U² + 16·t²`
giving `8·t² = (s − U)(s + U)/2`, then
  `U(s − U) − 8·t² = (s − U)[U − (s + U)/2] = -(s − U)²/2`.
Dividing by `2·U`:  `J − 4·t²/U = -(s − U)²/(4·U)`.

So `|J − 4·t²/U| = (s − U)²/(4·U)`, and we need `(s − U)² ≤ 64·t⁴/U²`,
i.e., `s − U ≤ 8·t²/U` (since `s − U ≥ 0`). Squaring (both sides
nonneg): `s ≤ U + 8·t²/U` iff `U² + 16·t² ≤ (U + 8·t²/U)²`. Expanding
gives `0 ≤ 64·t⁴/U²`, which holds trivially. -/
theorem J_superexchange_bound {t U : ℝ} (ht : t ≠ 0) (hU : 4 * |t| ≤ U) :
    |J_superexchange t U - 4 * t^2 / U| ≤ 16 * t^4 / U^3 := by
  have h_abs_t : 0 < |t| := abs_pos.mpr ht
  have hUpos : 0 < U := by linarith
  have hUne : U ≠ 0 := ne_of_gt hUpos
  set s := Real.sqrt (U^2 + 16*t^2) with hs_def
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  have hUsum_nn : (0:ℝ) ≤ U^2 + 16*t^2 := by positivity
  have hs_sq : s * s = U^2 + 16*t^2 := Real.mul_self_sqrt hUsum_nn
  have hs_ge_U : U ≤ s := by
    have hmono : Real.sqrt (U^2) ≤ Real.sqrt (U^2 + 16*t^2) := by
      apply Real.sqrt_le_sqrt
      have : (0:ℝ) ≤ 16*t^2 := by positivity
      linarith
    rwa [Real.sqrt_sq hUpos.le] at hmono
  have hsmU_nn : 0 ≤ s - U := by linarith
  -- Key identity: J − 4t²/U = -(s − U)²/(4U)
  have hJdiff_eq : J_superexchange t U - 4 * t^2 / U =
      -((s - U)^2 / (4 * U)) := by
    unfold J_superexchange E_plus
    rw [← hs_def]
    have hU4 : (4 * U : ℝ) ≠ 0 := by
      apply mul_ne_zero <;> [norm_num; exact hUne]
    field_simp
    nlinarith [hs_sq]
  -- Bound: s ≤ U + 8t²/U
  have hRHS_nn : 0 ≤ U + 8 * t^2 / U := by
    have : 0 ≤ 8 * t^2 / U := by positivity
    linarith
  have hsq_bound : s^2 ≤ (U + 8*t^2/U)^2 := by
    have hsq_eq : s^2 = U^2 + 16*t^2 := by rw [sq]; exact hs_sq
    have hrhs_expand : (U + 8*t^2/U)^2 = U^2 + 16*t^2 + 64*t^4/U^2 := by
      field_simp; ring
    rw [hsq_eq, hrhs_expand]
    have : 0 ≤ 64*t^4/U^2 := by positivity
    linarith
  have hs_le : s ≤ U + 8*t^2/U := by
    have := Real.sqrt_le_sqrt hsq_bound
    rwa [Real.sqrt_sq hs_nn, Real.sqrt_sq hRHS_nn] at this
  have hsmU_bound : s - U ≤ 8 * t^2 / U := by linarith
  -- (s − U)² ≤ (8t²/U)² = 64 t⁴/U²
  have h8t2_nn : 0 ≤ 8 * t^2 / U := by positivity
  have hsq_smU : (s - U)^2 ≤ 64 * t^4 / U^2 := by
    have hbound : (s - U)^2 ≤ (8*t^2/U)^2 := by
      rw [sq, sq]
      exact mul_le_mul hsmU_bound hsmU_bound hsmU_nn h8t2_nn
    have hrewrite : (8*t^2/U)^2 = 64 * t^4 / U^2 := by
      field_simp; ring
    linarith [hbound, hrewrite.symm.le, hrewrite.le]
  -- Combine: |J − 4t²/U| = (s−U)²/(4U) ≤ 64 t⁴/(U²·4U) = 16 t⁴/U³
  have hJdiff_nonpos : J_superexchange t U - 4 * t^2 / U ≤ 0 := by
    rw [hJdiff_eq]
    have : 0 ≤ (s - U)^2 / (4 * U) := by positivity
    linarith
  rw [abs_of_nonpos hJdiff_nonpos, hJdiff_eq]
  have hU4pos : (0:ℝ) < 4 * U := by linarith
  -- Goal: -(-(s - U)^2 / (4 * U)) ≤ 16 * t^4 / U^3
  -- i.e., (s-U)^2/(4U) ≤ 16 t^4/U^3
  have hfinal : (s - U)^2 / (4 * U) ≤ 16 * t^4 / U^3 := by
    have h1 : (s - U)^2 / (4 * U) ≤ (64 * t^4 / U^2) / (4 * U) :=
      div_le_div_of_nonneg_right hsq_smU hU4pos.le
    have h2 : (64 * t^4 / U^2) / (4 * U) = 16 * t^4 / U^3 := by
      field_simp; ring
    linarith
  linarith

/-- Summary marker for Phase 5t W7 shipment (non-load-bearing).
W7 delivers the direct-exchange-vs-superexchange scaling distinction
as a bundle of real-analysis properties of the explicit functions
`E_plus(t, U) = (U + √(U² + 16·t²))/2` and `J(t, U) = E_plus − U`:
the direct-exchange value `E_plus(t, 0) = 2·|t|` (W7a), Vieta
identities `E_plus + E_minus = U` and `E_plus · E_minus = −4·t²`
(W7b/c), the linear-in-`U` scaling coefficient `(∂E_plus/∂U)(0) =
1/2` (W7d), sqrt lower bound (W7e), monotonicity (W7f), gap identity
at U=0 (W7g), AM-GM sqrt bound (W7h), and the superexchange
approximation bound `|J − 4·t²/U| ≤ 16·t⁴/U³` for `U ≥ 4·|t| > 0`
(W7i). Bridges the Phase-5t doublon-gate matrix story to the
paper-level scaling narrative. -/
theorem fermi_hubbard_dimer_wave7_summary : True := trivial

/-! ### Section 17. Wave 7 round-2 strengthening — matrix bridge + Lipschitz
(2026-04-26 session 9)

This section strengthens W7 with:

**Matrix-bridge theorems (W7j–W7o):** tie the scalar eigenvalue
claims `E_plus(t, U) = (U + √(U² + 16·t²))/2` and
`E_minus(t, U) = (U − √(U² + 16·t²))/2` back to the actual Hubbard
dimer matrix `H_singlet t 0 U` (with detuning `Δ = 0`) via:
- Characteristic equations `E_{±}² − U·E_{±} − 4·t² = 0` (W7j/k).
- Charpoly factorization `(X − U)·(X² − U·X − 4·t²)` (W7l) — proves
  that `{U, E_plus, E_minus}` is the full spectrum.
- Explicit eigenvectors: `![E_plus, 0, -2·t]` for `E_plus` (W7m),
  mirror for `E_minus` (W7n), and `![0, 1, 0]` for the antisymmetric
  doublon at eigenvalue `U` (W7o, from `|D₋⟩` decoupling at Δ = 0).

**Real-analysis strengthening (W7p–W7q):**
- `E_minus_value_at_zero`: `E_minus(t, 0) = −2·|t|` (mirror of W7a).
- `E_plus_lipschitz`: `|E_plus(t, U₁) − E_plus(t, U₂)| ≤ |U₁ − U₂|`
  — the Tier-1 global 1-Lipschitz bound per deep research. -/

/-- **W7j (E_plus_char_eq).** The upper eigenvalue satisfies the
2×2-sector characteristic equation: `E_plus² − U·E_plus − 4·t² = 0`.
This is the defining algebraic identity from `E_plus · E_minus =
−4·t²` (W7c) combined with `E_plus + E_minus = U` (W7b): eliminate
`E_minus = U − E_plus` to get the quadratic. -/
theorem E_plus_char_eq (t U : ℝ) :
    (E_plus t U)^2 - U * E_plus t U - 4 * t^2 = 0 := by
  have h1 : E_plus t U + E_minus t U = U := E_plus_plus_E_minus t U
  have h2 : E_plus t U * E_minus t U = -(4 * t^2) := E_plus_times_E_minus t U
  have hmin : E_minus t U = U - E_plus t U := by linarith
  have : E_plus t U * (U - E_plus t U) = -(4 * t^2) := by rw [← hmin]; exact h2
  linarith [this]

/-- **W7k (E_minus_char_eq).** Mirror: `E_minus² − U·E_minus − 4·t² = 0`. -/
theorem E_minus_char_eq (t U : ℝ) :
    (E_minus t U)^2 - U * E_minus t U - 4 * t^2 = 0 := by
  have h1 : E_plus t U + E_minus t U = U := E_plus_plus_E_minus t U
  have h2 : E_plus t U * E_minus t U = -(4 * t^2) := E_plus_times_E_minus t U
  have hplus : E_plus t U = U - E_minus t U := by linarith
  have : (U - E_minus t U) * E_minus t U = -(4 * t^2) := by rw [← hplus]; exact h2
  linarith [this]

/-- **W7l (charpoly_H_singlet_Δ0_factored).** At `Δ = 0`, the
characteristic polynomial of the 3×3 singlet-sector Hamiltonian
factors as:
  `charpoly(H_singlet t 0 U) = (X − U) · (X² − U·X − 4·t²)`
exposing the three eigenvalues `{U, E_plus, E_minus}`. The
antisymmetric doublon `|D₋⟩` decouples at `Δ = 0` (eigenvalue `U`);
the remaining `(|D₊⟩, |s⟩)` 2×2 block has charpoly
`λ² − U·λ − 4·t²` whose roots are `E_plus` and `E_minus`.

This is the matrix-bridge theorem: it ties the W7 real-analysis
story (properties of the scalar function `E_plus(t, U)`) back to
the actual Hubbard-dimer matrix spectrum via a single factorization. -/
theorem charpoly_H_singlet_Δ0_factored (t U : ℝ) :
    (H_singlet t 0 U).charpoly =
      (X - C U) * (X^2 - C U * X - C (4*t^2)) := by
  rw [charpoly_H_singlet]
  simp only [map_mul, map_sub, map_pow, map_ofNat, Polynomial.C_0,
             ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
             mul_zero, sub_zero]
  ring

/-- **W7m (H_singlet_Δ0_E_plus_eigenvector).** The explicit eigenvector
of `H_singlet t 0 U` for eigenvalue `E_plus`:
  `H_singlet t 0 U · ![E_plus, 0, −2·t] = E_plus • ![E_plus, 0, −2·t]`
The proof reduces to the characteristic equation W7j
(`E_plus² − U·E_plus − 4·t² = 0`) applied componentwise. -/
theorem H_singlet_Δ0_E_plus_eigenvector (t U : ℝ) :
    (H_singlet t 0 U).mulVec ![E_plus t U, 0, -2*t] =
      E_plus t U • ![E_plus t U, 0, -2*t] := by
  have hchar : (E_plus t U)^2 - U * E_plus t U - 4 * t^2 = 0 :=
    E_plus_char_eq t U
  funext i
  fin_cases i <;>
    simp [H_singlet, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    nlinarith [hchar]

/-- **W7n (H_singlet_Δ0_E_minus_eigenvector).** Mirror of W7m for
`E_minus`. -/
theorem H_singlet_Δ0_E_minus_eigenvector (t U : ℝ) :
    (H_singlet t 0 U).mulVec ![E_minus t U, 0, -2*t] =
      E_minus t U • ![E_minus t U, 0, -2*t] := by
  have hchar : (E_minus t U)^2 - U * E_minus t U - 4 * t^2 = 0 :=
    E_minus_char_eq t U
  funext i
  fin_cases i <;>
    simp [H_singlet, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    nlinarith [hchar]

/-- **W7o (H_singlet_Δ0_U_eigenvector).** At `Δ = 0`, the
antisymmetric doublon `|D₋⟩ = ![0, 1, 0]` is an eigenvector of
`H_singlet` with eigenvalue `U`:
  `H_singlet t 0 U · ![0, 1, 0] = U • ![0, 1, 0]`
At `Δ = 0` the `|D₋⟩` row/col of the Hamiltonian decouples — row 1
is `![0, U, 0]`, so `|D₋⟩` is a trivial eigenvector with eigenvalue
equal to the diagonal entry `U`. This is the third eigenvalue of
the 3×3 block (the first two being `E_plus` and `E_minus`). -/
theorem H_singlet_Δ0_U_eigenvector (t U : ℝ) :
    (H_singlet t 0 U).mulVec ![0, 1, 0] = U • ![0, 1, 0] := by
  funext i
  fin_cases i <;>
    simp [H_singlet, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- **W7p (E_minus_value_at_zero).** Mirror of W7a: at `U = 0` the
lower eigenvalue is `E_minus(t, 0) = −2·|t|`. Computed via
`√(16·t²) = 4·|t|`, then `(0 − 4·|t|)/2 = −2·|t|`. -/
theorem E_minus_value_at_zero (t : ℝ) :
    E_minus t 0 = -(2 * |t|) := by
  unfold E_minus
  have h : (0:ℝ)^2 + 16*t^2 = (4*|t|)^2 := by
    rw [mul_pow, sq_abs]; ring
  rw [h, Real.sqrt_sq (by positivity : (0:ℝ) ≤ 4*|t|)]
  ring

/-- **W7q (E_plus_lipschitz).** Global 1-Lipschitz bound:
`|E_plus(t, U₁) − E_plus(t, U₂)| ≤ |U₁ − U₂|` for all `U₁, U₂, t`.
Deep-research Tier-1 statement. The proof chains:
- `√(U² + 16·t²)` is 1-Lipschitz in `U` via the identity
  `|s₁ − s₂|·(s₁ + s₂) = |U₁² − U₂²| = |U₁ − U₂|·|U₁ + U₂|`
  combined with `|U₁ + U₂| ≤ |U₁| + |U₂| ≤ s₁ + s₂` (triangle + W7e').
- Hence `E_plus(U) = (U + √(…))/2` is a convex combination of two
  1-Lipschitz functions (identity + sqrt-composition), so also
  1-Lipschitz. -/
theorem E_plus_lipschitz (t U₁ U₂ : ℝ) :
    |E_plus t U₁ - E_plus t U₂| ≤ |U₁ - U₂| := by
  set s₁ := Real.sqrt (U₁^2 + 16*t^2) with hs₁_def
  set s₂ := Real.sqrt (U₂^2 + 16*t^2) with hs₂_def
  have hs₁_nn : 0 ≤ s₁ := Real.sqrt_nonneg _
  have hs₂_nn : 0 ≤ s₂ := Real.sqrt_nonneg _
  have hs₁_abs_ge : |U₁| ≤ s₁ := by
    rw [hs₁_def, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg t]
  have hs₂_abs_ge : |U₂| ≤ s₂ := by
    rw [hs₂_def, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg t]
  -- Key inequality: |s₁ - s₂| ≤ |U₁ - U₂|
  have hsqrt_lip : |s₁ - s₂| ≤ |U₁ - U₂| := by
    have hs₁_sq : s₁ * s₁ = U₁^2 + 16*t^2 :=
      Real.mul_self_sqrt (by positivity)
    have hs₂_sq : s₂ * s₂ = U₂^2 + 16*t^2 :=
      Real.mul_self_sqrt (by positivity)
    -- (s₁ - s₂)·(s₁ + s₂) = s₁² - s₂² = U₁² - U₂² = (U₁ - U₂)(U₁ + U₂)
    have h_diff_prod : (s₁ - s₂) * (s₁ + s₂) = (U₁ - U₂) * (U₁ + U₂) := by
      have : s₁ * s₁ - s₂ * s₂ = U₁^2 - U₂^2 := by linarith
      nlinarith [this]
    -- |U₁ + U₂| ≤ |U₁| + |U₂| ≤ s₁ + s₂
    have h_abs_sum_le : |U₁ + U₂| ≤ s₁ + s₂ := by
      calc |U₁ + U₂|
          ≤ |U₁| + |U₂| := abs_add_le U₁ U₂
        _ ≤ s₁ + s₂ := by linarith
    -- Case split: s₁ + s₂ = 0 or > 0
    by_cases hsum_eq_zero : s₁ + s₂ = 0
    · -- s₁ = s₂ = 0 (both nonneg and sum to zero)
      have hs₁_zero : s₁ = 0 := by linarith
      have hs₂_zero : s₂ = 0 := by linarith
      -- Then U₁² = U₂² = -16t² forces t = 0 and U₁ = U₂ = 0
      have hU₁_zero : U₁ = 0 := by
        have hs₁_sq_zero : U₁^2 + 16*t^2 = 0 := by
          have := hs₁_sq; rw [hs₁_zero] at this; linarith
        nlinarith [sq_nonneg U₁, sq_nonneg t]
      have hU₂_zero : U₂ = 0 := by
        have hs₂_sq_zero : U₂^2 + 16*t^2 = 0 := by
          have := hs₂_sq; rw [hs₂_zero] at this; linarith
        nlinarith [sq_nonneg U₂, sq_nonneg t]
      simp [hs₁_zero, hs₂_zero, hU₁_zero, hU₂_zero]
    · -- s₁ + s₂ > 0: standard case
      have hsum_pos : 0 < s₁ + s₂ := lt_of_le_of_ne (by linarith)
        (Ne.symm hsum_eq_zero)
      -- |s₁ - s₂| = |U₁² - U₂²| / (s₁ + s₂) = |U₁ - U₂|·|U₁ + U₂|/(s₁+s₂)
      have h_abs_diff_prod :
          |s₁ - s₂| * (s₁ + s₂) = |U₁ - U₂| * |U₁ + U₂| := by
        have := h_diff_prod
        have h1 : |(s₁ - s₂) * (s₁ + s₂)| = |(U₁ - U₂) * (U₁ + U₂)| := by
          rw [this]
        rw [abs_mul, abs_mul, abs_of_pos hsum_pos] at h1
        exact h1
      -- |s₁ - s₂| ≤ |U₁ - U₂| iff |s₁ - s₂|·(s₁+s₂) ≤ |U₁ - U₂|·(s₁+s₂)
      -- from h_abs_diff_prod: LHS = |U₁-U₂|·|U₁+U₂|
      -- need: |U₁-U₂|·|U₁+U₂| ≤ |U₁-U₂|·(s₁+s₂)
      -- i.e., |U₁+U₂| ≤ (s₁+s₂) — given by h_abs_sum_le
      have h_target : |s₁ - s₂| * (s₁ + s₂) ≤ |U₁ - U₂| * (s₁ + s₂) := by
        rw [h_abs_diff_prod]
        exact mul_le_mul_of_nonneg_left h_abs_sum_le (abs_nonneg _)
      exact le_of_mul_le_mul_right h_target hsum_pos
  -- E_plus(U) = (U + s(U))/2, so difference is ((U₁ - U₂) + (s₁ - s₂))/2
  unfold E_plus
  rw [← hs₁_def, ← hs₂_def]
  have hreshape : (U₁ + s₁) / 2 - (U₂ + s₂) / 2 =
      ((U₁ - U₂) + (s₁ - s₂)) / 2 := by ring
  rw [hreshape, abs_div]
  have h2_pos : (0:ℝ) < 2 := by norm_num
  rw [abs_of_pos h2_pos]
  have h_sum_abs_le : |(U₁ - U₂) + (s₁ - s₂)| ≤ |U₁ - U₂| + |s₁ - s₂| :=
    abs_add_le _ _
  have h_double : |U₁ - U₂| + |s₁ - s₂| ≤ 2 * |U₁ - U₂| := by linarith
  calc |(U₁ - U₂) + (s₁ - s₂)| / 2
      ≤ (|U₁ - U₂| + |s₁ - s₂|) / 2 := by
        apply div_le_div_of_nonneg_right h_sum_abs_le h2_pos.le
    _ ≤ (2 * |U₁ - U₂|) / 2 := by
        apply div_le_div_of_nonneg_right h_double h2_pos.le
    _ = |U₁ - U₂| := by ring

/-- Summary marker for W7 round-2 strengthening (non-load-bearing).
Adds: W7j/k characteristic equations, W7l charpoly factorization at
`Δ = 0`, W7m/n/o explicit eigenvectors (E_plus, E_minus, antisymmetric
doublon U), W7p `E_minus(t, 0) = −2·|t|` (mirror of W7a), W7q global
1-Lipschitz bound `|E_plus(t, U₁) − E_plus(t, U₂)| ≤ |U₁ − U₂|`. -/
theorem fermi_hubbard_dimer_wave7_round2_summary : True := trivial

/-! ### Section 18. W6-deferred — 6×6 geometric SWAP lift to the
symmetry-adapted basis (2026-04-26 session 9)

The 3×3 singlet-sector SWAP operator `U_SWAP_singlet` from Section 14
is extended to a 6×6 operator `U_SWAP_adapted` in the symmetry-adapted
basis `{|D₊⟩, |D₋⟩, |s⟩} ⊕ {|t₊⟩, |t₀⟩, |t₋⟩}` (singlet ⊕ triplet).
The lift is block-diagonal: `U_SWAP_singlet` on the singlet block, and
the identity on the triplet block. Physical interpretation: the
geometric phase accumulates only in the singlet sector (where the
dark state lives); the triplet sector is unaffected.

Block-diagonal lift = `fromBlocks (U_SWAP_singlet t Δ) 0 0 1`, typed
`Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ`. All W6C unitarity
properties transfer via `Matrix.fromBlocks_{multiply, transpose,
one}` because both blocks are unitary (singlet via W6C-S3'; identity
trivially).

**Theorems:**
- **W6D-S1** `U_SWAP_adapted_isSymm`: `U_SWAP_adaptedᵀ = U_SWAP_adapted`.
- **W6D-S2** `U_SWAP_adapted_sq`: `U_SWAP_adapted² = 1` (involution).
- **W6D-S3** `U_SWAP_adapted_orthogonal`: `U · Uᵀ = 1` — the 6×6
  unitarity witness.
- **W6D-U1** `U_SWAP_adapted_mem_unitaryGroup`: membership in
  `Matrix.unitaryGroup (Fin 3 ⊕ Fin 3) ℝ` — canonical Mathlib API.

**Scope boundary.** This is a structural extension: the 6×6 operator
inherits W6C unitarity without new physical content. A full claim
"`U_SWAP_full` implements SWAP on `{|↑,↓⟩, |↓,↑⟩}`" is **not** provable
at a single `(t, Δ)` value — that claim requires the Berry-phase
holonomy from a closed parameter loop (W8 / Phase 6). The adapted
lift is the finite-dimensional unitarity statement, not the dynamic
gate-action statement. -/

/-- The 6×6 lift of the singlet-sector SWAP operator to the full
symmetry-adapted basis. Block-diagonal in `{singlet} ⊕ {triplet}`:
`U_SWAP_singlet` on the singlet block, identity on the triplet block.
Indexed by `Fin 3 ⊕ Fin 3` (first summand = singlet, second = triplet). -/
noncomputable def U_SWAP_adapted (t Δ : ℝ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks (U_SWAP_singlet t Δ) 0 0 1

/-- **W6D-S1 (U_SWAP_adapted_isSymm).** The adapted SWAP operator is
symmetric: `U_SWAP_adaptedᵀ = U_SWAP_adapted`. Inherits symmetry from
W6C-S1 (singlet block symmetric) + `1ᵀ = 1` (identity block trivially). -/
theorem U_SWAP_adapted_isSymm (t Δ : ℝ) :
    (U_SWAP_adapted t Δ)ᵀ = U_SWAP_adapted t Δ := by
  unfold U_SWAP_adapted
  rw [Matrix.fromBlocks_transpose, U_SWAP_singlet_isSymm]
  simp

/-- **W6D-S2 (U_SWAP_adapted_sq).** The adapted SWAP operator squares
to the identity: `U_SWAP_adapted · U_SWAP_adapted = I` (involution).
Via block-diagonal multiplication: top-left block becomes
`U_SWAP_singlet² = 1` (W6C-S2); bottom-right becomes `1² = 1`;
off-diagonal blocks vanish. -/
theorem U_SWAP_adapted_sq {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    U_SWAP_adapted t Δ * U_SWAP_adapted t Δ = 1 := by
  unfold U_SWAP_adapted
  rw [Matrix.fromBlocks_multiply, U_SWAP_singlet_sq h]
  simp [Matrix.fromBlocks_one]

/-- **W6D-S3 (U_SWAP_adapted_orthogonal).** The adapted SWAP operator
is orthogonal: `U · Uᵀ = I` (the 6×6 unitarity witness). One-liner
from S1 + S2 combined: `U · Uᵀ = U · U = I`. -/
theorem U_SWAP_adapted_orthogonal {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    U_SWAP_adapted t Δ * (U_SWAP_adapted t Δ)ᵀ = 1 := by
  rw [U_SWAP_adapted_isSymm, U_SWAP_adapted_sq h]

/-- **W6D-S3' (U_SWAP_adapted_transpose_mul).** Mirror form:
`Uᵀ · U = I`. -/
theorem U_SWAP_adapted_transpose_mul {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    (U_SWAP_adapted t Δ)ᵀ * U_SWAP_adapted t Δ = 1 := by
  rw [U_SWAP_adapted_isSymm, U_SWAP_adapted_sq h]

/-- **W6D-U1 (U_SWAP_adapted_mem_unitaryGroup).** The adapted SWAP
operator is a member of the Mathlib unitary submonoid
`Matrix.unitaryGroup (Fin 3 ⊕ Fin 3) ℝ`. Packages the 6×6 unitarity
witness in canonical form. -/
theorem U_SWAP_adapted_mem_unitaryGroup {t Δ : ℝ} (h : t ≠ 0 ∨ Δ ≠ 0) :
    U_SWAP_adapted t Δ ∈ Matrix.unitaryGroup (Fin 3 ⊕ Fin 3) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff',
      Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  exact U_SWAP_adapted_transpose_mul h

/-- **W6D-A1 (U_SWAP_adapted_on_inl).** The adapted SWAP acts on a
singlet-block-embedded vector exactly as `U_SWAP_singlet` does in the
3×3 basis: `U_SWAP_adapted · (v, 0) = (U_SWAP_singlet · v, 0)`. The
triplet block being zero and the identity block acting on zero leave
the second component unchanged. Specializes to W6C-K1 (`U_SWAP · v =
-v` on the kernel) lifted to the 6×6 basis. -/
theorem U_SWAP_adapted_on_inl (t Δ : ℝ) (v : Fin 3 → ℝ) :
    (U_SWAP_adapted t Δ).mulVec (Sum.elim v (fun _ : Fin 3 => (0:ℝ))) =
      Sum.elim ((U_SWAP_singlet t Δ).mulVec v) (fun _ : Fin 3 => (0:ℝ)) := by
  unfold U_SWAP_adapted
  rw [Matrix.fromBlocks_mulVec]
  ext i
  rcases i with i | i
  · simp [Sum.elim_comp_inl, Sum.elim_comp_inr]
  · simp [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec]

/-- **W6D-A2 (U_SWAP_adapted_on_inr).** The adapted SWAP is the
identity on triplet-embedded states: for any triplet vector `w`,
`U_SWAP_adapted · (0, w) = (0, w)`. No phase accumulation in the
triplet sector — all three triplet states are eigenvalue-`+1`
eigenvectors of the adapted SWAP. -/
theorem U_SWAP_adapted_on_inr (t Δ : ℝ) (w : Fin 3 → ℝ) :
    (U_SWAP_adapted t Δ).mulVec (Sum.elim (fun _ : Fin 3 => (0:ℝ)) w) =
      Sum.elim (fun _ : Fin 3 => (0:ℝ)) w := by
  unfold U_SWAP_adapted
  rw [Matrix.fromBlocks_mulVec]
  ext i
  rcases i with i | i
  · simp [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec]
  · simp [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.one_mulVec]

/-- Summary marker for W6-deferred 6×6 SWAP lift shipment
(non-load-bearing). Adds: `U_SWAP_adapted` definition (block-diagonal
6×6 lift), W6D-S1/S2/S3/S3' symmetry + involution + orthogonality in
the 6×6 basis, W6D-U1 Mathlib unitary-group membership, W6D-A1
singlet-block action agreement with `U_SWAP_singlet`, W6D-A2 triplet
block identity action. Does **not** claim SWAP on
`{|↑,↓⟩, |↓,↑⟩}` — that is W8 / Phase 6 territory (Berry-phase
holonomy). -/
theorem fermi_hubbard_dimer_wave6_deferred_summary : True := trivial

/-! ### Section 19. Wave 8 Target A — Minimal Geometric Phase Theorem
(2026-04-26 session 9 round-3)

The final Phase 5t wave. Formalizes the **closed-path sign / phase
statement** in the idealized reduced model (`U = 0` singlet sector)
using the existing `darkStateθ θ := ![0, sin θ, cos θ]`
parameterization (Section 5).

**Physical content.** The doublon geometric gate works because the
dark state:
1. Remains at zero energy for the entire `U = 0` cycle
   (⟹ no dynamical phase accumulates),
2. Picks up a `−1` sign when the angle `θ` sweeps through `π`
   (⟹ accumulated phase is purely geometric and equals `−1`).

This section proves the minimum algebraic statements for (1) and (2)
without needing the Berry-connection / adiabatic-theorem
infrastructure (which would be "Target B" per the roadmap and is
deferred to Phase 6).

**Theorems shipped:**
- **W8a** `darkStateθ_add_pi_sign_flip`: `darkStateθ(θ + π) =
  −darkStateθ(θ)`. The core closed-path sign statement.
- **W8b** `darkStateθ_add_two_pi`: `darkStateθ(θ + 2π) =
  darkStateθ(θ)`. The full 2π parameterization periodicity
  (consistent with sin/cos 2π-periodicity).
- **W8c** `darkStateθ_dotProduct_self`: `dotProduct (darkStateθ θ)
  (darkStateθ θ) = 1`. Normalization identity — the θ-parameterized
  dark state is automatically L² unit-norm (L² = sin² + cos² = 1).
- **W8d** `dark_state_dynamical_phase_vanishes`: under the kernel-angle
  condition `Δ sin θ = 2t cos θ`, the expectation value
  `⟨darkStateθ, H · darkStateθ⟩ = 0`, so the dynamical phase along
  any parameter loop vanishes identically.
- **W8e** `geometric_phase_necessary_conditions_on_pi_loop`: the bundled
  "geometric gate" statement — after a π-sweep the dark state acquires
  `−1` (W8a) while remaining at zero energy throughout (W8d), so the
  entire accumulated phase is geometric and equals `−1`.

**Scope boundary.** Target A is the **finite-dimensional algebraic
core** of the Berry-phase gate mechanism. The full adiabatic theorem,
Berry-connection formulation, and holonomy interpretation remain
Phase 6 (Target B). This section is the minimum claim required to
justify the `U_SWAP_singlet` gate action (W6C-A1) as a geometric
phase rather than a dynamical one. -/

/-- **W8a (darkStateθ_add_pi_sign_flip).** The θ-parameterized dark
state satisfies a sign-flip identity after a `π`-angle shift:
`darkStateθ(θ + π) = −darkStateθ(θ)`. Direct consequence of
`sin(θ + π) = −sin θ` and `cos(θ + π) = −cos θ`.

This is the closed-path sign statement: the dark state is
**anti-periodic** with period `π` as a function of the mixing angle,
so any closed loop in parameter space that sweeps through `π` (e.g.,
the physical doublon-gate cycle) picks up a `−1` factor on the dark
direction. -/
theorem darkStateθ_add_pi_sign_flip (θ : ℝ) :
    darkStateθ (θ + Real.pi) = -(darkStateθ θ) := by
  unfold darkStateθ
  funext i
  fin_cases i
  · simp
  · simp [Real.sin_add_pi]
  · simp [Real.cos_add_pi]

/-- **W8b (darkStateθ_add_two_pi).** The θ-parameterized dark state
is `2π`-periodic: `darkStateθ(θ + 2π) = darkStateθ(θ)`. Follows from
sin/cos 2π periodicity. Equivalent to applying W8a twice. -/
theorem darkStateθ_add_two_pi (θ : ℝ) :
    darkStateθ (θ + 2 * Real.pi) = darkStateθ θ := by
  unfold darkStateθ
  funext i
  fin_cases i
  · simp
  · simp [Real.sin_add_two_pi]
  · simp [Real.cos_add_two_pi]

/-- **W8c (darkStateθ_dotProduct_self).** The θ-parameterized dark
state is L²-unit-norm for every `θ`:
  `dotProduct (darkStateθ θ) (darkStateθ θ) = 0² + sin²(θ) + cos²(θ) = 1`.
Uses `Real.sin_sq_add_cos_sq` (Pythagorean identity). Proves that the
parameterization is automatically normalized — no separate
normalization step needed. -/
theorem darkStateθ_dotProduct_self (θ : ℝ) :
    dotProduct (darkStateθ θ) (darkStateθ θ) = 1 := by
  simp [darkStateθ, dotProduct, Fin.sum_univ_three]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- **W8d (dark_state_dynamical_phase_vanishes).** Along any
parameter-space path satisfying the kernel-angle condition
`Δ · sin θ = 2t · cos θ`, the expectation value of the Hamiltonian
in the dark state vanishes:
  `⟨darkStateθ θ, H · darkStateθ θ⟩ = 0`.

**Physics:** the dynamical phase accumulated along a path
`γ : [0, T] → parameter space` is
  `∫₀^T ⟨ψ(s) | H(γ(s)) | ψ(s)⟩ ds`.
When this integrand is identically zero (as here, for the `U = 0`
dark-state sector), the dynamical phase vanishes — **the entire
accumulated phase is geometric.** Direct consequence of W4a
`dark_state_theta_in_kernel` (`H · dark = 0`) + inner-product
linearity. -/
theorem dark_state_dynamical_phase_vanishes (t Δ θ : ℝ)
    (hθ : Δ * Real.sin θ = 2 * t * Real.cos θ) :
    dotProduct (darkStateθ θ) ((H_singlet t Δ 0).mulVec (darkStateθ θ)) = 0 := by
  rw [dark_state_theta_in_kernel t Δ θ hθ]
  simp [dotProduct]

/-- **W8e (geometric_phase_necessary_conditions_on_pi_loop).** The
two finite-dimensional conditions required for a Berry-phase
interpretation of the Kiefer et al. geometric SWAP gate.

For any path parameter `θ` and endpoint-matching angle condition
tied to `(t, Δ)`, after a `π`-sweep:
1. The dark state acquires `−1`: `darkStateθ(θ + π) = −darkStateθ(θ)`
   (W8a — closed-path sign statement).
2. The Hamiltonian expectation value vanishes pointwise along the
   zero-energy path: `⟨dark, H · dark⟩ = 0` (W8d — so the integrated
   dynamical phase vanishes for any continuous extension).

**Scope note.** The conclusion is exactly the conjunction W8a ∧ W8d,
not an equality `BerryPhase = −1`. No phase-integral functional is
constructed in this file; the "accumulated phase equals −1" reading
requires an external adiabatic-theorem assumption (Kato), which is
Target B / Phase 6. The finite-dimensional algebraic core proved
here is exactly the two necessary conditions; consumers supplying
the adiabatic step get the `−1` conclusion, but that last step is
not formalized. -/
theorem geometric_phase_necessary_conditions_on_pi_loop (t Δ θ : ℝ)
    (hθ : Δ * Real.sin θ = 2 * t * Real.cos θ) :
    darkStateθ (θ + Real.pi) = -(darkStateθ θ) ∧
    dotProduct (darkStateθ θ) ((H_singlet t Δ 0).mulVec (darkStateθ θ)) = 0 := by
  exact ⟨darkStateθ_add_pi_sign_flip θ, dark_state_dynamical_phase_vanishes t Δ θ hθ⟩

/-- Backward-compatibility alias for the pre-rename name
`geometric_phase_minus_one_on_pi_loop`. The rename (2026-04-26,
session 9 FINAL++) responds to the adversarial-reviewer finding
that the old name semantically implies a Berry-phase-equals-scalar
theorem that is not actually proved here. See W8e for the proper
statement. -/
theorem geometric_phase_minus_one_on_pi_loop (t Δ θ : ℝ)
    (hθ : Δ * Real.sin θ = 2 * t * Real.cos θ) :
    darkStateθ (θ + Real.pi) = -(darkStateθ θ) ∧
    dotProduct (darkStateθ θ) ((H_singlet t Δ 0).mulVec (darkStateθ θ)) = 0 :=
  geometric_phase_necessary_conditions_on_pi_loop t Δ θ hθ

/-- Summary marker for Phase 5t Wave 8 Target A shipment
(non-load-bearing). Adds: W8a `π`-angle sign flip, W8b `2π`
periodicity, W8c dark-state L² normalization, W8d
dynamical-phase-vanishes along the U=0 kernel-angle path, W8e
bundled "accumulated phase is purely geometric and equals −1"
theorem.

Completes Phase 5t as the **finite-dimensional algebraic core**
of the Kiefer et al. doublon geometric SWAP gate. Target B
(full adiabatic holonomy, Berry connection over parameterized
eigenbundle) remains Phase 6 territory. -/
theorem fermi_hubbard_dimer_wave8_summary : True := trivial

end SKEFTHawking.FermiHubbardDimer
