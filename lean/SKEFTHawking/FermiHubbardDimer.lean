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

open Matrix

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

/-- Summary marker for the Phase 5t Wave 2 shipment (non-load-bearing;
placeholder for graph integrity). -/
theorem fermi_hubbard_dimer_wave2_summary : True := trivial

end SKEFTHawking.FermiHubbardDimer
