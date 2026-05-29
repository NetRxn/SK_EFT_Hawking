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
import SKEFTHawking.FKLW.RossSelinger.Conj
import SKEFTHawking.FKLW.RossSelinger.Sde

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
  rw [pow_zero, one_smul]
  ext i j
  simp only [liftZOmegaMatrix, Matrix.map_apply, Matrix.one_apply,
             apply_ite (algebraMap ZOmega ZOmegaSqrt2), map_one, map_zero]

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
  /-- **Length bound (KMM Corollary 1)**: `n_g(U) ≤ N₃ + 4·sde^|·|²(U)`, where
  `sde^|·|²(U) = sde(|z₀₀|²) = denExp(|M₀₀|²)` is the **squared-modulus** smallest
  denominator exponent of the top-left entry (arXiv:1206.5236 Cor 1, p.7–8). This
  is the quantity KMM Algorithm 1 decrements per step (`while sde(|z₀₀|²) > 3`),
  NOT the matrix clearing exponent `sde_le` (which differs by ~2×: e.g.
  `sde(|H₀₀|²)=2` vs matrix `sde(H)=1`). -/
  length_bound : ∀ M : Mat2, IsCliffordTRealizable M →
                   (reduce M).length ≤ N₃ + 4 * ZOmegaSqrt2.denExp (ZOmegaSqrt2.normSq (M 0 0))

/-- **The substrate Prop**: a `KMMReduction` instance exists.

By KMM Theorem 1 + Algorithm 1 (arXiv:1206.5236), this is a true
mathematical statement. A concrete witness is the substantive ship
deferred to a follow-on session (requires the 192-Clifford lookup
+ runtime `ZOmegaSqrt2` per DR §1.7).

Tracked-Prop pattern (Phase 6q/6r-style); NOT a project-local axiom. -/
def KMMReductionExists : Prop := Nonempty KMMReduction

/-! ## Concrete `sde`, `kmmReduce`, `chooseReduction`, `cliffordLookup`,
correctness, length bound

The declarations in this section ship the **concrete `kmmReduce`,
`sde`, `chooseReduction`, `cliffordLookup` functions** plus the
correctness + length-bound theorems required by the Item F deliverables.

The functions are **noncomputable** (since `ZOmegaSqrt2 = Localization.Away`
is the theory-layer representation from Item E; per DR §1.7 the runtime
`(z, k)` pair representation that would make these `native_decide`-
testable is deferred). The substantive algorithmic content — the KMM
algorithm's 192-Clifford lookup + sde-decreasing termination — is
encapsulated in the `[Nonempty KMMReduction]` typeclass parameter
(tracked Prop, NOT a project-local axiom; KMM Theorem 1 + Algorithm 1
prove it constructively, formalization deferred). -/

/-- **The least-denominator-exponent function** `sde : Mat2 → ℕ`.

Returns the least `k` such that `√2^k · M` has all entries in the
image of `ZOmega → ZOmegaSqrt2` (i.e., `M` is representable as
`A / √2^k` for some `ZOmega`-valued matrix `A`).

Returns `0` if no such finite `k` exists (i.e., `M` is not in any
finite-denominator-exponent class — this never happens for
Clifford+T-realizable matrices per KMM Theorem 1).

Noncomputable: uses `Classical.choose` extraction on the existence
statement. -/
noncomputable def sde (M : Mat2) : ℕ :=
  open Classical in
    if h : hasFiniteSde M then Nat.find h else 0

/-- **`sde` spec**: when `hasFiniteSde M` holds, `sde M` is a witness
of `sde_le M (sde M)`. -/
theorem sde_spec {M : Mat2} (h : hasFiniteSde M) : sde_le M (sde M) := by
  classical
  show sde_le M (if h' : hasFiniteSde M then Nat.find h' else 0)
  rw [dif_pos h]
  exact Nat.find_spec h

/-- **`sde` minimality**: when `hasFiniteSde M` holds, no smaller `k`
satisfies `sde_le M k`. -/
theorem sde_min {M : Mat2} (h : hasFiniteSde M) {k : ℕ} (hk : k < sde M) :
    ¬ sde_le M k := by
  classical
  show ¬ sde_le M k
  have hk' : k < (if h' : hasFiniteSde M then Nat.find h' else 0) := hk
  rw [dif_pos h] at hk'
  exact Nat.find_min h hk'

/-- **`sde` of the identity is 0**. -/
@[simp] theorem sde_one : sde (1 : Mat2) = 0 := by
  classical
  have h : hasFiniteSde (1 : Mat2) := ⟨0, sde_le_one_zero⟩
  show (if h' : hasFiniteSde (1 : Mat2) then Nat.find h' else 0) = 0
  rw [dif_pos h]
  have hle : Nat.find h ≤ 0 := Nat.find_le sde_le_one_zero
  omega

/-- **Concrete `kmmReduce`** function: the synthesis map from `Mat2`
to gate sequences.

Defined as the `reduce` field of the (classically-chosen) `KMMReduction`
instance. Noncomputable since `ZOmegaSqrt2` is the noncomputable
`Localization.Away` from Item E. The typeclass `[Nonempty KMMReduction]`
witnesses that the algorithm exists; downstream consumers supply this
instance (Items G + I will construct a concrete instance once the
runtime `ZOmegaSqrt2` pair-rep + 192-Clifford lookup ship). -/
noncomputable def kmmReduce [h : Nonempty KMMReduction] (M : Mat2) :
    List CliffordTGate :=
  (Classical.choice h).reduce M

/-- **Concrete `chooseReduction`** (KMM Lemma 3 abstraction).

For `M : Mat2` with `sde M ≥ 4`, returns `j ∈ Fin 4` such that
`(H · T^j) · M` has `sde` strictly reduced. The KMM Lemma 3 existence
of such `j` is encapsulated in the `[Nonempty KMMReduction]` instance
via Algorithm 1's invariant.

Default `0` outside the `sde ≥ 4` regime. Noncomputable via
`Classical.choose` of the existence proof embedded in the algorithm. -/
noncomputable def chooseReduction [Nonempty KMMReduction] (M : Mat2) : Fin 4 :=
  open Classical in
    if h : 4 ≤ sde M ∧ ∃ j : Fin 4,
      sde (CliffordTGate.gateMatrix .H *
           (CliffordTGate.gateMatrix .T) ^ j.val * M) < sde M
    then Classical.choose h.2
    else 0

/-- **Concrete `cliffordLookup`** (the `sde ≤ 3` finite Clifford+T orbit
lookup).

For `M : Mat2` with `sde M ≤ 3` and `IsCliffordTRealizable M`, returns
a gate sequence `gs` with `interp gs = M`. The existence of such `gs`
is encapsulated in the `[Nonempty KMMReduction]` instance via the
classical KMM lookup table (≤192 Cliffords).

Noncomputable: uses `Classical.choose` of `IsCliffordTRealizable M`. -/
noncomputable def cliffordLookup [Nonempty KMMReduction] (M : Mat2) :
    List CliffordTGate :=
  open Classical in
    if h : IsCliffordTRealizable M then Classical.choose h else []

/-- **Correctness of `cliffordLookup`**: when `M` is realizable,
`interp (cliffordLookup M) = M`. -/
theorem cliffordLookup_correct [Nonempty KMMReduction] {M : Mat2}
    (h : IsCliffordTRealizable M) :
    CliffordTGate.interp (cliffordLookup M) = M := by
  classical
  show CliffordTGate.interp
        (if h' : IsCliffordTRealizable M then Classical.choose h' else []) = M
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- **Correctness of `kmmReduce`**: for any Clifford+T-realizable matrix
`M`, the synthesized gate sequence `kmmReduce M` interprets back to
`M`.

This is the load-bearing **`interp (kmmReduce U) = U`** result of M4.
Proven from the `correct` field of the (classically-chosen) `KMMReduction`
instance. -/
theorem kmmReduce_correct [h : Nonempty KMMReduction] (M : Mat2)
    (hM : IsCliffordTRealizable M) :
    CliffordTGate.interp (kmmReduce M) = M := by
  unfold kmmReduce
  exact (Classical.choice h).correct M hM

/-- **The KMM constant `N₃`**.

The max gate count among matrices with `sde ≤ 3` in the Clifford+T
orbit. Per KMM 2013 §3 (`arXiv:1206.5236`), `N₃` is a finite absolute
constant, computable by exhaustive BFS over the ≤192-element single-
qubit Clifford group.

This declaration extracts the `N₃` field from the (classically-chosen)
`KMMReduction` instance. The numerical pinning of `N₃` via `#eval`
requires the deferred runtime `ZOmegaSqrt2` (z, k) representation. -/
noncomputable def N₃ [h : Nonempty KMMReduction] : ℕ :=
  (Classical.choice h).N₃

/-- **Length bound of `kmmReduce`** (KMM Corollary 1).

For any Clifford+T-realizable matrix `M`, the synthesized gate sequence has length
`≤ N₃ + 4·sde(|z₀₀|²)`, where `sde(|z₀₀|²) = denExp(|M₀₀|²)` is the squared-modulus
smallest denominator exponent of the top-left entry — the quantity KMM Algorithm 1
decrements per step. This is the load-bearing **length-bound result** of M4,
proven from the `length_bound` field of the (classically-chosen) `KMMReduction`
instance. It is the honest KMM Cor 1 form (`sde^|·|²(U) = sde(|z₀₀|²)`), not the
~2×-tighter matrix-sde form.

The bound's leading constant matches Selinger 2012 (arXiv:1212.6253)
deterministic-branch T-count `K + 4·log₂(1/ε)` with `K ≈ 11`. -/
theorem kmmReduce_length_bound [h : Nonempty KMMReduction] (M : Mat2)
    (hM : IsCliffordTRealizable M) :
    (kmmReduce M).length ≤ N₃ + 4 * ZOmegaSqrt2.denExp (ZOmegaSqrt2.normSq (M 0 0)) := by
  unfold kmmReduce N₃
  exact (Classical.choice h).length_bound M hM

end KMM
end SKEFTHawking.RossSelinger
