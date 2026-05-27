/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — KMM exact synthesis substrate + algorithm spec

Ships the **typed-API substrate** for the Kliuchnikov-Maslov-Mosca
(KMM) exact synthesis algorithm (arXiv:1206.5236) plus the
`KMMReduction` algorithm-spec structure that downstream consumers
(Item G's KMM base finder, Item I's Ross-Selinger full compose)
construct concrete instances of.

## Substrate vs full algorithm ship

The full M4 KMM ship per Pre-Implementation DR §3.3 (the ~800 LoC
target) requires:
  1. A concrete 192-element single-qubit Clifford lookup table (the
     `cliffordLookup` for `sde ≤ 3` cases).
  2. A computable `sde` (least denominator exponent) function over
     a **runtime** `ZOmegaSqrt2` (z, k) representation — DR §1.7
     option (B). Item E shipped only the theory-layer `Localization.Away`
     representation; the runtime pair-rep is documented as deferred.
  3. A concrete `chooseReduction` implementing KMM Lemma 3 (residue
     check in `ZOmega / √2·ZOmega`).
  4. The full inductive sde-decreasing termination proof of `kmmReduce`.
  5. The correctness + length-bound proofs (Giles-Selinger 2013
     Theorem 7.10: T-count = sde, giving `length ≤ N₃ + 4·sde`).

Items 1, 2, 4 are substantial multi-session work each. This ship lands
the **substrate**: the algorithm specification as a structure bundling
the algorithm's data + properties. Downstream consumers depend on the
substrate spec; future ships construct concrete instances satisfying it.

## Headline definitions

  * `Mat2` — convenience alias for `Matrix (Fin 2) (Fin 2) ZOmegaSqrt2`.

  * `sde_le` — the relation `√2^k · M ∈ image of ZOmega-valued matrix`.
    Defines what it means for `M` to have least-denominator-exponent
    `≤ k`.

  * `IsCliffordTRealizable` — the proposition that `M` is in the image
    of some Clifford+T gate sequence under `interp`.

  * `KMMReduction` — the algorithm-spec structure with `reduce`, `correct`,
    and `length_bound` fields. A concrete instance is the KMM algorithm.

  * `KMMReductionExists` — the substrate Prop asserting existence of a
    KMM algorithm (= `Nonempty KMMReduction`).

## Deferred deliverables (KMM concrete-ship session)

  * The 192-element `cliffordLookup` table populated.
  * A concrete `KMMReduction` instance constructed (uses runtime
    ZOmegaSqrt2 from a deferred Item E extension).
  * `sde_decreases_on_reduction` substantive proof.
  * `kmmReduce_correct` + `kmmReduce_length_bound` substantive proofs.

## References

  * Pre-Implementation Research Dossier §3.3, §4.
  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) — Algorithm 1,
    Theorem 1, Corollary 1.
  * Giles-Selinger 2013 (arXiv:1312.6584) — Theorem 7.10 (T-count = sde
    for Matsumoto-Amano normal form).
  * Selinger 2012 (arXiv:1212.6253) — deterministic-branch T-count
    bound `K + 4·log₂(1/ε)`, `K ≈ 11`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected. The substrate
  ships as a Nonempty Prop pattern (tracked-Prop style), NOT as a
  project-local axiom.

-/

import SKEFTHawking.FKLW.RossSelinger.CliffordTGate

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-- **Convenience alias** for `2×2` matrices over `ZOmegaSqrt2`. -/
abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ZOmegaSqrt2

namespace KMM

open ZOmegaSqrt2

/-- **Lift of a `ZOmega` matrix to a `Mat2`** via the canonical algebra
map on each entry. -/
noncomputable def liftZOmegaMatrix (A : Matrix (Fin 2) (Fin 2) ZOmega) : Mat2 :=
  A.map (algebraMap ZOmega ZOmegaSqrt2)

/-- **Least-denominator-exponent relation**: `sde_le M k` holds iff
multiplying `M` by `sqrt2^k` lands in the image of `liftZOmegaMatrix`
(i.e., `M = (√2^k)⁻¹ · A` for some `A` over `ZOmega`).

Equivalent characterization: `M` is representable as `A / √2^k` for
some `A : Matrix (Fin 2) (Fin 2) ZOmega`.

This is the KMM "smallest denominator exponent" structure (KMM 2013
arXiv:1206.5236 §3). -/
def sde_le (M : Mat2) (k : ℕ) : Prop :=
  ∃ A : Matrix (Fin 2) (Fin 2) ZOmega,
    (sqrt2 ^ k) • M = liftZOmegaMatrix A

/-- **Has finite sde**: every `M` representable as `A / √2^k` for some
`(A, k)` has finite sde. By KMM Theorem 1, every Clifford+T-realizable
matrix has this property. -/
def hasFiniteSde (M : Mat2) : Prop := ∃ k, sde_le M k

/-- **`sde_le` is monotone in `k`**: if `M` is representable at exponent
`k`, then also at any larger exponent (by tucking in extra factors of
`√2`). Entry-wise proof via `congrFun` decomposition. -/
theorem sde_le_succ {M : Mat2} {k : ℕ} (h : sde_le M k) :
    sde_le M (k + 1) := by
  obtain ⟨A, hA⟩ := h
  refine ⟨ZOmega.sqrt2 • A, ?_⟩
  have hA' : ∀ i j, (sqrt2 ^ k • M) i j = (liftZOmegaMatrix A) i j :=
    fun i j => congrFun (congrFun hA i) j
  ext i j
  have hentry : (sqrt2 ^ k) * M i j
              = algebraMap ZOmega ZOmegaSqrt2 (A i j) := by
    have := hA' i j
    simpa [Matrix.smul_apply, liftZOmegaMatrix, Matrix.map_apply,
           smul_eq_mul] using this
  show (sqrt2 ^ (k + 1) • M) i j = (liftZOmegaMatrix (ZOmega.sqrt2 • A)) i j
  simp only [Matrix.smul_apply, liftZOmegaMatrix, Matrix.map_apply,
             Matrix.smul_apply, smul_eq_mul]
  -- Goal: sqrt2^(k+1) * M i j = algebraMap (ZOmega.sqrt2 * A i j)
  -- Rearrange LHS to expose sqrt2^k * M i j for hentry rewrite
  rw [show sqrt2 ^ (k + 1) * M i j = sqrt2 * (sqrt2 ^ k * M i j) by ring,
      hentry]
  show sqrt2 * (algebraMap ZOmega ZOmegaSqrt2) (A i j)
        = (algebraMap ZOmega ZOmegaSqrt2) (ZOmega.sqrt2 * A i j)
  rw [show (sqrt2 : ZOmegaSqrt2) = algebraMap ZOmega ZOmegaSqrt2 ZOmega.sqrt2 from rfl,
      ← map_mul]

/-- **Identity matrix has `sde_le 0`**: trivially representable as
itself with no denominators. -/
theorem sde_le_one_zero : sde_le (1 : Mat2) 0 := by
  refine ⟨(1 : Matrix (Fin 2) (Fin 2) ZOmega), ?_⟩
  ext i j
  show (sqrt2 ^ 0 • (1 : Mat2)) i j = (liftZOmegaMatrix 1) i j
  simp [liftZOmegaMatrix, Matrix.one_apply, Matrix.map_apply,
        apply_ite (algebraMap ZOmega ZOmegaSqrt2)]

/-- **Clifford+T realizability**: `M` is in the image of `interp` from
some gate sequence. KMM Theorem 1 characterizes this set as exactly the
`2×2` unitaries over `ZOmegaSqrt2` with determinant `ω^k` for some `k`. -/
def IsCliffordTRealizable (M : Mat2) : Prop :=
  ∃ gs : List CliffordTGate, CliffordTGate.interp gs = M

/-- **Every Clifford+T gate's matrix is Clifford+T-realizable**
(trivially, by the singleton sequence). -/
theorem gateMatrix_isCliffordTRealizable (g : CliffordTGate) :
    IsCliffordTRealizable (CliffordTGate.gateMatrix g) :=
  ⟨[g], by simp⟩

/-- **Realizability is closed under product** (left-multiplication by
another realizable matrix). -/
theorem IsCliffordTRealizable.mul {M N : Mat2}
    (hM : IsCliffordTRealizable M) (hN : IsCliffordTRealizable N) :
    IsCliffordTRealizable (M * N) := by
  obtain ⟨gs, hgs⟩ := hM
  obtain ⟨hs, hhs⟩ := hN
  exact ⟨gs ++ hs, by rw [CliffordTGate.interp_append, hgs, hhs]⟩

/-- **Identity is Clifford+T-realizable** (the empty sequence). -/
theorem IsCliffordTRealizable.one : IsCliffordTRealizable (1 : Mat2) :=
  ⟨[], by simp⟩

/-! ## KMM algorithm specification -/

/-- **The KMM algorithm specification**: data + properties bundling the
exact synthesis of `2×2` Clifford+T-realizable matrices into gate
sequences.

A concrete instance carries:
  * `reduce : Mat2 → List CliffordTGate` — the synthesis function.
  * `correct` — left-inverse property: for any matrix `M` that is the
    interpretation of some gate sequence, `interp (reduce M) = M`.
  * `length_bound` — KMM Corollary 1 length bound:
    `(reduce M).length ≤ N₃ + 4·k` whenever `sde_le M k`, for a
    universal constant `N₃` (computable by exhaustive BFS over the
    `sde ≤ 3` Clifford+T orbit, bounded above by a few hundred per
    KMM arXiv:1206.5236 §3).

Construction of a concrete `KMMReduction` instance is the deferred
substantive ship (multi-session work; requires the 192-Clifford lookup
+ runtime `ZOmegaSqrt2` representation per DR §1.7 option (B)). -/
structure KMMReduction where
  /-- The reduction function: Clifford+T-realizable matrix → gate sequence. -/
  reduce : Mat2 → List CliffordTGate
  /-- **Correctness**: `reduce` is a left-inverse of `interp` on the
  image of `interp`. -/
  correct : ∀ M : Mat2, IsCliffordTRealizable M →
              CliffordTGate.interp (reduce M) = M
  /-- **The KMM constant `N₃`** (max gate count among `sde ≤ 3` orbit). -/
  N₃ : ℕ
  /-- **Length bound (KMM Corollary 1)**: `n_g ≤ N₃ + 4·sde`. -/
  length_bound : ∀ M : Mat2, ∀ k : ℕ, IsCliffordTRealizable M →
                   sde_le M k → (reduce M).length ≤ N₃ + 4 * k

/-- **The substrate Prop**: a `KMMReduction` instance exists.

By KMM Theorem 1 + Algorithm 1 (arXiv:1206.5236), this is a true
mathematical statement. A concrete witness is the substantive ship
deferred to a follow-on session (requires the 192-Clifford lookup
+ runtime `ZOmegaSqrt2` per DR §1.7).

Tracked-Prop pattern (Phase 6q/6r-style); NOT a project-local axiom. -/
def KMMReductionExists : Prop := Nonempty KMMReduction

end KMM
end SKEFTHawking.RossSelinger
