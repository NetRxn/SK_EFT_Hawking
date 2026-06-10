/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 10) — the column-synthesis backbone (state preparation, dim 4)

The remaining headline brick is circuit `C`: an `O(k)` Clifford+T word preparing the KMM ancilla state
`|v⟩` (inc 7–9). Faithfully (KMM §2.2 invokes the Giles–Selinger/KMM-1206.5236 exact-synthesis Column
Lemma — there is no guessable explicit circuit), this is the **dim-4 column lemma**: any unit column over
`ℤ[ω][1/√2]` is the first column of a `Gate2` Clifford+T word, with length `O(denominator exponent)`.

This file ships the **structural backbone** of that synthesis, before the (hard) residue-reduction core:

  * `IsColRealizableWithin v L` — `v` is the first column (`M·e₀`) of a `Gate2` word of length `≤ L`.
  * `IsColRealizableWithin.smul_left` — **the induction backbone**: if `G` is realizable within `L'`
    and `v` is column-realizable within `L`, then `G·v` (matrix–vector) is column-realizable within
    `L' + L`. Each reduction step left-multiplies by a generator, so the column-lemma induction is
    exactly iterated `smul_left`; budgets add (`IsRealizableWithin.mul`), giving the `O(k)` length.
  * `isColRealizableWithin_e0` — the base anchor: the computational basis state `e₀ = |00⟩` is
    column-realizable within `0` (the empty word; `M = 1`).

Once the residue-reduction step (`denExp = k+1 ⟹ ∃ O(1)-word g, denExp (g·v) ≤ k`) and the inverse-
closure of the realizable class are in place, `smul_left` + `isColRealizableWithin_e0` assemble the
full `O(k)` column lemma by induction on the denominator exponent.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.CliffordTGate2

set_option autoImplicit false

open scoped Matrix Kronecker

namespace SKEFTHawking.RossSelinger
namespace Gate2

/-- **Column (state-preparation) realizability within a length budget.** A column
`v : Fin 2 × Fin 2 → ZOmegaSqrt2` is **column-realizable within `L`** if it is the first column
(`M · e₀`, i.e. `fun i => M i (0,0)`) of some `Gate2` word of length `≤ L`. This is the target of the
dim-4 exact synthesis: preparing `|v⟩` from `|00⟩`. -/
def IsColRealizableWithin (v : Fin 2 × Fin 2 → ZOmegaSqrt2) (L : ℕ) : Prop :=
  ∃ M : Mat4, IsRealizableWithin M L ∧ (fun i => M i (0, 0)) = v

/-- Weaken the length budget. -/
theorem IsColRealizableWithin.mono {v : Fin 2 × Fin 2 → ZOmegaSqrt2} {L L' : ℕ}
    (h : IsColRealizableWithin v L) (hL : L ≤ L') : IsColRealizableWithin v L' :=
  let ⟨M, hM, hcol⟩ := h; ⟨M, hM.mono hL, hcol⟩

/-- **The induction backbone.** If `G` is realizable within `L'` and `v` is column-realizable within
`L`, then `G · v` (the matrix–vector product) is column-realizable within `L' + L`. The witness is
`G * M` (where `M` prepares `v`): its first column is `G · (M·e₀) = G · v`, and budgets add. The
column lemma is iterated `smul_left` — each residue-reduction step left-multiplies by a generator. -/
theorem IsColRealizableWithin.smul_left {v : Fin 2 × Fin 2 → ZOmegaSqrt2} {G : Mat4} {L L' : ℕ}
    (hG : IsRealizableWithin G L') (hv : IsColRealizableWithin v L) :
    IsColRealizableWithin (G.mulVec v) (L' + L) := by
  obtain ⟨M, hM, hMcol⟩ := hv
  refine ⟨G * M, hG.mul hM, ?_⟩
  funext i
  show (G * M) i (0, 0) = G.mulVec v i
  rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => by rw [← congrFun hMcol j]

/-- **Base anchor**: the computational basis state `e₀ = |00⟩` (`fun i => if i = (0,0) then 1 else 0`)
is column-realizable within `0` — it is the first column of the identity (the empty word). -/
theorem isColRealizableWithin_e0 :
    IsColRealizableWithin (fun i => if i = ((0 : Fin 2), (0 : Fin 2)) then 1 else 0) 0 := by
  refine ⟨1, ⟨[], interp2_nil, le_refl 0⟩, ?_⟩
  funext i
  rw [Matrix.one_apply]

/-- **Every computational basis state is column-realizable within `2`.** The basis state `|a,b⟩`
(`fun i => if i = (a,b) then 1 else 0`) is prepared from `|00⟩` by `X^a ⊗ X^b` — a Clifford word of
`≤ 2` `Gate2` gates (an `onFst X` iff `a = 1`, an `onSnd X` iff `b = 1`). The base-case permutation
piece of the dim-4 column lemma. -/
theorem isColRealizableWithin_basis (a b : Fin 2) :
    IsColRealizableWithin (fun i => if i = (a, b) then 1 else 0) 2 := by
  refine ⟨interp2 ((if a = 1 then [Gate2.onFst .X] else []) ++ (if b = 1 then [Gate2.onSnd .X] else [])),
    ⟨_, rfl, ?_⟩, ?_⟩
  · fin_cases a <;> fin_cases b <;> decide
  · fin_cases a <;> fin_cases b <;> decide

/-! ### Global `ω`-phase (the base case's `ωᵏ` factor)

The denExp-0 unit column is `ωᵏ·eᵢ` (base-case number theory, `ColumnBaseCase`). The basis state `eᵢ`
is realizable (`isColRealizableWithin_basis`); these lemmas supply the global `ωᵏ` phase, realized by
`k` copies of the `onFst ω` gate (each scales the whole register by `ωS`). -/

/-- `gateMatrix2 (onFst ω) = ωS • 1` (the global-phase generator: `ω·I ⊗ I = ωS·I`). -/
theorem gateMatrix2_onFst_omega :
    gateMatrix2 (Gate2.onFst CliffordTGate.omega) = CliffordTGate.ωS • (1 : Mat4) := by
  show (CliffordTGate.gateMatrix CliffordTGate.omega) ⊗ₖ (1 : Mat2') = CliffordTGate.ωS • (1 : Mat4)
  rw [show CliffordTGate.gateMatrix CliffordTGate.omega = CliffordTGate.ωS • (1 : Mat2') from rfl,
    Matrix.smul_kronecker, Matrix.one_kronecker_one]

/-- Prepending one `onFst ω` scales a realizable matrix by `ωS` (length `+1`). -/
theorem IsRealizableWithin.smul_omega {M : Mat4} {L : ℕ} (h : IsRealizableWithin M L) :
    IsRealizableWithin (CliffordTGate.ωS • M) (L + 1) := by
  obtain ⟨w, hw, hl⟩ := h
  refine ⟨Gate2.onFst CliffordTGate.omega :: w, ?_, by simpa using hl⟩
  rw [interp2_cons, gateMatrix2_onFst_omega, hw, Matrix.smul_mul]
  congr 1
  exact one_mul M

/-- Scaling a column-realizable vector by `ωS` (length `+1`). -/
theorem IsColRealizableWithin.smul_omega {v : Fin 2 × Fin 2 → ZOmegaSqrt2} {L : ℕ}
    (h : IsColRealizableWithin v L) : IsColRealizableWithin (CliffordTGate.ωS • v) (L + 1) := by
  obtain ⟨M, hM, hcol⟩ := h
  refine ⟨CliffordTGate.ωS • M, hM.smul_omega, ?_⟩
  funext i
  rw [Matrix.smul_apply, Pi.smul_apply, ← congrFun hcol i]

/-- Scaling by `ωᵏ` (length `+k`): iterate `smul_omega`. -/
theorem IsColRealizableWithin.smul_omega_pow {v : Fin 2 × Fin 2 → ZOmegaSqrt2} {L : ℕ}
    (h : IsColRealizableWithin v L) (k : ℕ) :
    IsColRealizableWithin (CliffordTGate.ωS ^ k • v) (L + k) := by
  induction k with
  | zero => rw [pow_zero, one_smul]; exact h
  | succ n ih => rw [pow_succ', mul_smul]; exact ih.smul_omega

/-- **`ωᵏ·eᵢ` is column-realizable within `k + 2`** (the dim-4 column-lemma base case's realizable
form): the basis state `e_{(a,b)}` (`isColRealizableWithin_basis`, `≤ 2` gates) phased by `ωᵏ`
(`k` copies of `onFst ω`). -/
theorem isColRealizableWithin_omega_pow_basis (k : ℕ) (a b : Fin 2) :
    IsColRealizableWithin (fun i => if i = (a, b) then CliffordTGate.ωS ^ k else 0) (k + 2) := by
  have h := (isColRealizableWithin_basis a b).smul_omega_pow k
  rw [show CliffordTGate.ωS ^ k • (fun i => if i = (a, b) then (1 : ZOmegaSqrt2) else 0)
        = (fun i => if i = (a, b) then CliffordTGate.ωS ^ k else 0) from by
      funext i; rw [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]] at h
  exact h.mono (by omega)

/-! ### Block-wise action of embedded single-qubit operations on a 4-column

The dim-4 reduction's 2-level operations are embedded single-qubit gates (`embedFst`/`embedSnd`); these
lemmas compute their `mulVec` action on a column block-wise — `embedSnd A` applies `A` within each
first-qubit block (combining the second-qubit pair), `embedFst A` applies `A` across blocks at fixed
second qubit. The raw matrix-algebra the reduction (and `smul_left`) consume. -/

/-- **`embedSnd A` acts within each first-qubit block**: `(embedSnd A · v)(i,j) = ∑_{j'} A j j' · v(i,j')`
(combines the second-qubit pair `{(i,0),(i,1)}` by `A`, for each `i`). -/
theorem embedSnd_mulVec_apply (A : Mat2') (v : Fin 2 × Fin 2 → ZOmegaSqrt2) (i j : Fin 2) :
    (embedSnd A).mulVec v (i, j) = ∑ j' : Fin 2, A j j' * v (i, j') := by
  rw [embedSnd, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      (fun i' _ hi' => Finset.sum_eq_zero fun j' _ => by
        rw [Matrix.kroneckerMap_apply]
        show (1 : Mat2') i i' * A j j' * v (i', j') = 0
        rw [Matrix.one_apply_ne (Ne.symm hi'), zero_mul, zero_mul])]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Matrix.kroneckerMap_apply]
  show (1 : Mat2') i i * A j j' * v (i, j') = A j j' * v (i, j')
  rw [Matrix.one_apply_eq, one_mul]

/-- **`embedFst A` acts across blocks at fixed second qubit**: `(embedFst A · v)(i,j) =
∑_{i'} A i i' · v(i',j)` (combines the first-qubit pair `{(0,j),(1,j)}` by `A`, for each `j`). -/
theorem embedFst_mulVec_apply (A : Mat2') (v : Fin 2 × Fin 2 → ZOmegaSqrt2) (i j : Fin 2) :
    (embedFst A).mulVec v (i, j) = ∑ i' : Fin 2, A i i' * v (i', j) := by
  rw [embedFst, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
    (fun j' _ hj' => by
      rw [Matrix.kroneckerMap_apply]
      show A i i' * (1 : Mat2') j j' * v (i', j') = 0
      rw [Matrix.one_apply_ne (Ne.symm hj'), mul_zero, zero_mul])]
  rw [Matrix.kroneckerMap_apply]
  show A i i' * (1 : Mat2') j j * v (i', j) = A i i' * v (i', j)
  rw [Matrix.one_apply_eq, mul_one]

/-! ### Circuit-layer foundations (inc 28): embedded single-qubit words are realizable

The dim-4 column reduction realizes each row operation as a two-qubit `Gate2` word. The simplest such
words embed a single-qubit Clifford+T word onto one line (`embedFst`/`embedSnd`); these are realizable
within the word's length (`embedFst_interp`/`embedSnd_interp` are length-preserving). `wHTm` is the
single-qubit `H·Tᵐ` word (the row-operation generator). NB an *embedded* `H·Tᵐ` acts on BOTH qubit
blocks at once — the single-pair (controlled) operation the reduction ultimately needs is a follow-on;
these lemmas are the shared realizability substrate. -/

/-- `embedSnd` of a realizable single-qubit word is realizable within the word's length. -/
theorem embedSnd_realizableWithin (gs : List CliffordTGate) :
    IsRealizableWithin (embedSnd (CliffordTGate.interp gs)) gs.length :=
  ⟨gs.map Gate2.onSnd, (embedSnd_interp gs).symm, by simp⟩

/-- `embedFst` of a realizable single-qubit word is realizable within the word's length. -/
theorem embedFst_realizableWithin (gs : List CliffordTGate) :
    IsRealizableWithin (embedFst (CliffordTGate.interp gs)) gs.length :=
  ⟨gs.map Gate2.onFst, (embedFst_interp gs).symm, by simp⟩

/-- A replicated single-qubit word interprets to a power: `interp (replicate m g) = gateMatrix g ^ m`. -/
theorem interp_replicate (g : CliffordTGate) (m : ℕ) :
    CliffordTGate.interp (List.replicate m g) = (CliffordTGate.gateMatrix g) ^ m := by
  induction m with
  | zero => simp [CliffordTGate.interp_nil]
  | succ n ih => rw [List.replicate_succ, CliffordTGate.interp_cons, ih]; exact (pow_succ' _ _).symm

/-- The single-qubit `H·Tᵐ` word (the Giles–Selinger row-operation generator): one `H` then `m` `T`s. -/
def wHTm (m : ℕ) : List CliffordTGate := CliffordTGate.H :: List.replicate m CliffordTGate.T

@[simp] theorem wHTm_length (m : ℕ) : (wHTm m).length = m + 1 := by simp [wHTm]

/-- `wHTm m` interprets to `H · Tᵐ`. -/
theorem wHTm_interp (m : ℕ) :
    CliffordTGate.interp (wHTm m) = CliffordTGate.gateMatrix CliffordTGate.H *
      CliffordTGate.gateMatrix CliffordTGate.T ^ m := by
  rw [wHTm, CliffordTGate.interp_cons, interp_replicate]

end Gate2
end SKEFTHawking.RossSelinger
