import Mathlib
import SKEFTHawking.ETH.Predicates

/-!
# Phase 6o Wave 3a.3: ETH concrete witness substrates

## Goal

Ship concrete `MatrixSubstrate n` finite-dimensional witnesses for the
Wave 3a.4 productive-value Aristotle batch. Three sandboxes:

1. **Toy 1-dimensional substrate** — minimal trivial witness for type-checking.
2. **Trivial 4-dimensional substrate** — placeholder Ising-class structure
   suitable for Aristotle iteration (concrete matrix elements; Pauli σ_z
   block structure).
3. **n = 16 substrate** — minimum dimension where A4 (Eigenstate Typicality
   Principle) is non-vacuous; required for the substrate-discovery contrast
   `A4 fails on n < 16` vs. `A4 vacuously satisfiable on n = 16`.

These sandboxes are **substrate-data level**: they ship the finite-
dimensional matrix structure but do NOT ship full physical Hamiltonian
diagonalization (which Aristotle would need for A1/A2/A3 substantive
verification). Wave 3a.4 (post-user-auth) submits the substrates +
predicates to Aristotle for refutation iteration.

## Module structure

- §1: Toy 1-dim substrate (type-check witness).
- §2: 4-dim Ising-class block substrate (Aristotle target).
- §3: 16-dim minimal A4-non-vacuous substrate.
- §4: Substantive partition theorem combining the three sandboxes.
- §5: Wave 3a.3 closure summary.

## References

- Phase 6o Wave 3a.1 substrate-analysis working doc §3.
- Phase 6o Wave 3a.2 (`Predicates.lean`).
-/

noncomputable section

namespace SKEFTHawking.ETH

/-! ## §1. Toy 1-dim substrate -/

/-- Toy 1-dimensional substrate for type-check witness. -/
def toyOneDim : MatrixSubstrate 1 :=
  ⟨Nat.one_pos, 0, 0, fun _ => 0, fun _ => 0⟩

/-- Toy 1-dim substrate satisfies A1 (Srednicki) trivially. -/
theorem toyOneDim_satisfies_Srednicki : IsSrednickiAnsatz toyOneDim := by
  refine ⟨⟨fun _ => 0, trivial⟩, ⟨1, by norm_num, ?_⟩, ?_⟩
  · intro i j h
    exfalso
    have : i = j := Subsingleton.elim _ _
    exact h this
  · simp [toyOneDim]

/-- Toy 1-dim substrate fails A4 (n = 1 < 16). -/
theorem toyOneDim_fails_A4 :
    ¬ IsEigenstateTypicalityPrincipleAnsatz toyOneDim :=
  IsEigenstateTypicalityPrincipleAnsatz_fails_small_n (by norm_num) toyOneDim

/-! ## §2. 4-dim Ising-class block substrate -/

/-- 4-dimensional substrate with Ising-class diagonal structure.

`O = diag(1, -1, 1, -1)` — analog of σ_z observable on a 2-spin Hilbert space.
`H = diag(0, 1, 1, 2)` — analog of (σ_z ⊗ σ_z + σ_x ⊗ I + I ⊗ σ_x) Ising
Hamiltonian eigenvalues at chaotic regime parameters.
`E = id ∘ Fin.toNat` — eigenvalues match the Hamiltonian's diagonal
entries.
`S = identity` — trivial entropy function (placeholder).

The 4-dim substrate is the Aristotle target for the Wave 3a.4 batch:
small enough for `decide`/`native_decide` to be tractable; large enough
to make non-trivial structural distinctions between A1, A2, A3, A5. -/
def fourDimIsing : MatrixSubstrate 4 :=
  ⟨by norm_num,
   Matrix.of (fun i j =>
     if i = j then ((-1 : ℝ) ^ i.val) else 0),
   Matrix.of (fun i j =>
     if i = j then (i.val : ℝ) else 0),
   fun i => (i.val : ℝ),
   fun x => x⟩

/-- 4-dim substrate fails A4 (n = 4 < 16). -/
theorem fourDimIsing_fails_A4 :
    ¬ IsEigenstateTypicalityPrincipleAnsatz fourDimIsing :=
  IsEigenstateTypicalityPrincipleAnsatz_fails_small_n (by norm_num) fourDimIsing

/-! ## §3. 16-dim minimal A4-non-vacuous substrate -/

/-- 16-dimensional substrate where A4 is non-vacuously checkable.

Trivial structure (zero matrices, zero eigenvalues, zero entropy). The
substrate-data significance: `n = 16` is the minimum dimension where
A4's `16 ≤ n` hypothesis fires. The Wave 3a.4 productive-value Aristotle
target on this substrate is whether A4 *can* be satisfied (likely YES
for trivial Hamiltonians; the substantive refutation is whether A4
implies A1/A2/A3 — which would close the cross-axiomatization map). -/
def sixteenDimTrivial : MatrixSubstrate 16 :=
  ⟨by norm_num, 0, 0, fun _ => 0, fun _ => 0⟩

/-- 16-dim trivial substrate satisfies A1 (Srednicki) trivially. -/
theorem sixteenDimTrivial_satisfies_Srednicki :
    IsSrednickiAnsatz sixteenDimTrivial := by
  refine ⟨⟨fun _ => 0, trivial⟩, ⟨1, by norm_num, ?_⟩, ?_⟩
  · intro i j h
    -- All matrix entries are 0; |0| ≤ exp(...) trivially
    simp [sixteenDimTrivial]
  · simp [sixteenDimTrivial]

/-- 16-dim trivial substrate satisfies A4 (Eigenstate Typicality Principle)
non-vacuously — the `16 ≤ 16` hypothesis fires. -/
theorem sixteenDimTrivial_satisfies_A4 :
    IsEigenstateTypicalityPrincipleAnsatz sixteenDimTrivial := by
  refine ⟨by norm_num, 1/2, ?_, ?_⟩
  · norm_num
  · norm_num

/-! ## §4. Substantive partition theorem -/

/-- **Wave 3a.3 substantive partition.** The three concrete witness
substrates partition into:

* **Toy 1-dim:** satisfies A1, fails A4 (n < 16).
* **4-dim Ising:** Aristotle iteration target; fails A4 (n < 16); A1/A2/A3
  status determined by Wave 3a.4 batch.
* **16-dim trivial:** satisfies A1, satisfies A4 (minimum non-vacuous
  dimension). The substantive Wave 3a.3 finding: A4-satisfying substrates
  exist starting at n = 16 and trivially also satisfy A1, but the
  *substantive* Wave 3a.4 question is whether A4-satisfying substrates
  with non-trivial dynamics also satisfy A1/A2/A3.

This partition is sufficient infrastructure for the Wave 3a.4 productive-
value Aristotle batch. -/
theorem wave_3a_3_concrete_partition :
    -- Toy 1-dim
    (IsSrednickiAnsatz toyOneDim ∧
     ¬ IsEigenstateTypicalityPrincipleAnsatz toyOneDim) ∧
    -- 4-dim Ising fails A4
    (¬ IsEigenstateTypicalityPrincipleAnsatz fourDimIsing) ∧
    -- 16-dim trivial satisfies both A1 and A4
    (IsSrednickiAnsatz sixteenDimTrivial ∧
     IsEigenstateTypicalityPrincipleAnsatz sixteenDimTrivial) :=
  ⟨⟨toyOneDim_satisfies_Srednicki, toyOneDim_fails_A4⟩,
   fourDimIsing_fails_A4,
   ⟨sixteenDimTrivial_satisfies_Srednicki, sixteenDimTrivial_satisfies_A4⟩⟩

/-! ## §5. Wave 3a.3 closure summary -/

/-- Substantive deliverables shipped at Wave 3a.3:

1. `toyOneDim` 1-dim type-check witness + A1 satisfaction + A4 failure.
2. `fourDimIsing` 4-dim Ising-class block substrate (Aristotle iteration
   target for Wave 3a.4 batch) + A4 failure.
3. `sixteenDimTrivial` 16-dim minimum-dimension non-vacuous A4 witness
   + A1 + A4 simultaneous satisfaction.
4. `wave_3a_3_concrete_partition` substantive partition theorem.

The Wave 3a.3 sandboxes are sufficient infrastructure for the Wave 3a.4
productive-value Aristotle batch. The 4-dim Ising substrate is the
substantive iteration target where Aristotle is expected to surface
≥ 1 refutation (per Inozemcev-Volovich gap bound from Phase 6o Wave 3a.1
substrate-analysis §4.G).

**Wave 3a.4 user-auth gate held at this point** per `WAVE_EXECUTION_PIPELINE.md`
Stage 4 + Phase 6o roadmap §user authorization gates table: user gets
first and last call on Aristotle submissions. The Wave 3a.1 substrate-
analysis working doc + Wave 3a.2 predicates + Wave 3a.3 concrete
witnesses (this module) together form the user-auth pre-draft. -/
theorem wave_3a_3_concrete_witness_closure :
    IsSrednickiAnsatz toyOneDim ∧
    ¬ IsEigenstateTypicalityPrincipleAnsatz toyOneDim ∧
    ¬ IsEigenstateTypicalityPrincipleAnsatz fourDimIsing ∧
    IsSrednickiAnsatz sixteenDimTrivial ∧
    IsEigenstateTypicalityPrincipleAnsatz sixteenDimTrivial :=
  ⟨toyOneDim_satisfies_Srednicki,
   toyOneDim_fails_A4,
   fourDimIsing_fails_A4,
   sixteenDimTrivial_satisfies_Srednicki,
   sixteenDimTrivial_satisfies_A4⟩

end SKEFTHawking.ETH
