/-
Copyright (c) 2026 SK_EFT_Hawking contributors.
Released under Apache 2.0 license as described in the LEAN license.
Authors: John Roehm, Claude (Anthropic).
-/
import Mathlib
import SKEFTHawking.QCyc5
import SKEFTHawking.QCyc5Ext
import SKEFTHawking.Mat13K5Ext

set_option autoImplicit false

/-!
# True 6-strand Fibonacci R-matrix substrate: `FibonacciSextetTrueRep`

Phase 1.3 deliverable for Wave 1.D.4 (f) 6-strand Fibonacci CNOT
Lean-verified gate. This module ships the explicit 5 σ generators
(plus their 5 inverses) for the braid action on the 13-dimensional
fusion space of 6 Fibonacci anyons (2 logical qubits × 3 anyons per
qudit), encoded as `Mat13K_5Ext` literals.

## Scope

For 6 Fibonacci anyons grouped as a pair of 3-anyon qudits, the
fusion Hilbert space is 13-dimensional (per DR §Q2.1; matches
TQSim v0.0.2 `AnyonicCircuit(2, 3).dim`). The braid group B_6 acts
via 5 generators σ_1 .. σ_5 (the elementary swaps of adjacent strands
1↔2, 2↔3, 3↔4, 4↔5, 5↔6 respectively). Each σ_n is a unitary
13×13 matrix over K = Q(ζ₅, √φ) = `QCyc5Ext`.

## Provenance

Numerical values extracted from TQSim v0.0.2
(`AnyonicCircuit(nb_qudits=2, nb_anyons_per_qudit=3).braiding_operators`)
which implements Tounsi 2023 (arXiv:2307.01892 §3). Symbolic
conversion to closed-form Q(ζ₅, √φ) elements verified at 10⁻¹⁶
residual via `scripts/extract_sigma_symbolic.py` (Wave 1.D.4 (f)
Phase 1.3a). Cross-validated against DR §Q2.4/Q2.5/Q2.6/Q2.7/Q2.8
(Phase 6p Wave 3a.2.3b deep research).

## Basis ordering (TQSim canonical)

The 13-dim basis used here is the TQSim ordering — verified to match
DR Table 2 at indices 0..7, 11, 12 but with a 3-cycle permutation
at {8, 9, 10}: TQSim has (|00⟩₁, |10⟩₁, |21⟩₁) where DR Table 2 has
(|21⟩₁, |00⟩₁, |10⟩₁). **The Lean substrate adopts TQSim ordering**
as canonical (the extracted form). Downstream sub-block extraction
(Phase 1.3g) must therefore use the TQSim indices:
* Sector 0 computational sub-block: indices {1, 2, 3, 4}
* Sector 1 computational sub-block: indices **{8, 9, 11, 12}**
  (NOT DR's {9, 10, 11, 12}; the basis-permutation discovery is
  documented in `scripts/extract_sigma_symbolic.py` docstring and
  Wave_1D4f_Execution_Plan.md §6 addendum).

## Pipeline-Invariant compliance

* No `axiom` declarations (Pipeline Invariant #15).
* No `set_option maxHeartbeats N` in proof bodies (Pipeline
  Invariant #10). Inverse-identity theorems σ_n * σ_n⁻¹ = 1
  discharge via `native_decide` on the 169-entry equality after
  unfolding the hand-rolled `Mat13K_5Ext.mul` to the explicit
  13-term sum-of-products per output entry. Each call exercises a
  1-mul `Mat13K_5Ext` operation (within the ≤ 4-mul budget per
  `Mat13K5Ext.lean` docstring).

## References

* `SK_EFT_Hawking/lean/SKEFTHawking/Mat13K5Ext.lean` — substrate
  (Phase 1.2).
* `scripts/extract_sigma_symbolic.py` — closed-form extraction
  (Phase 1.3a; numerical cross-validation).
* Tounsi, A. (2023), "A Constructive Approach to Fibonacci Anyons,"
  arXiv:2307.01892 §3.
* DR Phase 6p Wave 3a.2.3b — substrate spec (private).
-/

namespace SKEFTHawking

open SKEFTHawking.QCyc5Ext

/-! ## 1. The 5 forward σ generators (TQSim ordering) -/

/-- σ_1: braid of strands 1↔2. Pure phase diagonal (no F-symbol
mixing — strands 1 and 2 are leaves of the same outermost fusion).
13 nonzero diagonal entries, each R_τ or R_1 depending on the
fusion outcome at the (1,2) edge of the basis state. -/
def sigma1_sextet : Mat13K_5Ext := fun i j =>
  match (i.val, j.val) with
  | (0, 0) => Rtau_ext
  | (1, 1) => R1_ext
  | (2, 2) => Rtau_ext
  | (3, 3) => R1_ext
  | (4, 4) => Rtau_ext
  | (5, 5) => R1_ext
  | (6, 6) => Rtau_ext
  | (7, 7) => Rtau_ext
  | (8, 8) => R1_ext
  | (9, 9) => Rtau_ext
  | (10, 10) => Rtau_ext
  | (11, 11) => R1_ext
  | (12, 12) => Rtau_ext
  | _ => 0

/-- σ_2: braid of strands 2↔3. Acts as the K-matrix
(F · diag(R_1, R_τ) · F) on 2-dim sub-blocks where the (2,3) fusion
edge has fusion outcome τ (admitting both R_1 and R_τ via F-symbol
recoupling), and as a pure phase on configurations with unique
fusion outcome. 23 nonzero entries; block-2×2 structure on
{(1,2), (3,4), (5,6), (8,9), (11,12)} + diagonal phases at
{0, 7, 10}. -/
def sigma2_sextet : Mat13K_5Ext := fun i j =>
  match (i.val, j.val) with
  | (0, 0) => Rtau_ext
  | (1, 1) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (1, 2) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (2, 1) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (2, 2) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (3, 3) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (3, 4) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (4, 3) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (4, 4) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (5, 5) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (5, 6) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (6, 5) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (6, 6) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (7, 7) => Rtau_ext
  | (8, 8) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (8, 9) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (9, 8) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (9, 9) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (10, 10) => Rtau_ext
  | (11, 11) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (11, 12) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (12, 11) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (12, 12) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | _ => 0

/-- σ_3: braid of strands 3↔4. The "inter-qubit" braid — the most
structurally complex of the 5 generators (43 nonzero entries across
four sparsity sub-blocks). Acts as the full F-symbol-conjugated K
on 2-dim sub-blocks within sector 0 + K embedded across the 3-block
top-left sector + the 5-block sector-1 structure. See DR §Q2.8 +
session-14 derivation log for closed-form entry-by-entry
identification. -/
def sigma3_sextet : Mat13K_5Ext := fun i j =>
  match (i.val, j.val) with
  | (0, 0) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (0, 2) => ofQCyc5 ⟨-1, 0, -1, 0⟩
  | (0, 4) => ⟨0, ⟨-1, 1, -1, 0⟩⟩
  | (1, 1) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (1, 3) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (2, 0) => ofQCyc5 ⟨-1, 0, -1, 0⟩
  | (2, 2) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (2, 4) => ⟨0, ⟨-1, 1, -1, 0⟩⟩
  | (3, 1) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (3, 3) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (4, 0) => ⟨0, ⟨-1, 1, -1, 0⟩⟩
  | (4, 2) => ⟨0, ⟨-1, 1, -1, 0⟩⟩
  | (4, 4) => ofQCyc5 ⟨2, 0, 2, 1⟩
  | (5, 5) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (5, 8) => ofQCyc5 ⟨-1, 0, -1, 0⟩
  | (5, 11) => ⟨0, ⟨-1, 1, -1, 0⟩⟩
  | (6, 6) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (6, 7) => ⟨0, ⟨1, -1, 1, 0⟩⟩
  | (6, 9) => ofQCyc5 ⟨-1, 1, -1, 0⟩
  | (6, 10) => ofQCyc5 ⟨-1, 1, -1, 0⟩
  | (6, 12) => ⟨0, ⟨-2, 1, -2, 0⟩⟩
  | (7, 6) => ⟨0, ⟨1, -1, 1, 0⟩⟩
  | (7, 7) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (7, 12) => ofQCyc5 ⟨-1, 0, -1, 0⟩
  | (8, 5) => ofQCyc5 ⟨-1, 0, -1, 0⟩
  | (8, 8) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (8, 11) => ⟨0, ⟨-1, 1, -1, 0⟩⟩
  | (9, 6) => ofQCyc5 ⟨-1, 1, -1, 0⟩
  | (9, 9) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (9, 10) => ofQCyc5 ⟨-1, 0, -1, 0⟩
  | (9, 12) => ⟨0, ⟨-2, 1, -2, 0⟩⟩
  | (10, 6) => ofQCyc5 ⟨-1, 1, -1, 0⟩
  | (10, 9) => ofQCyc5 ⟨-1, 0, -1, 0⟩
  | (10, 10) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (10, 12) => ⟨0, ⟨-2, 1, -2, 0⟩⟩
  | (11, 5) => ⟨0, ⟨-1, 1, -1, 0⟩⟩
  | (11, 8) => ⟨0, ⟨-1, 1, -1, 0⟩⟩
  | (11, 11) => ofQCyc5 ⟨2, 0, 2, 1⟩
  | (12, 6) => ⟨0, ⟨-2, 1, -2, 0⟩⟩
  | (12, 7) => ofQCyc5 ⟨-1, 0, -1, 0⟩
  | (12, 9) => ⟨0, ⟨-2, 1, -2, 0⟩⟩
  | (12, 10) => ⟨0, ⟨-2, 1, -2, 0⟩⟩
  | (12, 12) => ofQCyc5 ⟨3, -1, 3, 1⟩
  | _ => 0

/-- σ_4: braid of strands 4↔5. Pure phase diagonal (analogue of σ_1
on the second qubit). 13 nonzero diagonal entries — same R_τ / R_1
alphabet as σ_1, with different position assignments determined by
the (4,5) fusion edge across the 13 basis states. -/
def sigma4_sextet : Mat13K_5Ext := fun i j =>
  match (i.val, j.val) with
  | (0, 0) => Rtau_ext
  | (1, 1) => R1_ext
  | (2, 2) => R1_ext
  | (3, 3) => Rtau_ext
  | (4, 4) => Rtau_ext
  | (5, 5) => Rtau_ext
  | (6, 6) => Rtau_ext
  | (7, 7) => R1_ext
  | (8, 8) => R1_ext
  | (9, 9) => R1_ext
  | (10, 10) => Rtau_ext
  | (11, 11) => Rtau_ext
  | (12, 12) => Rtau_ext
  | _ => 0

/-- σ_5: braid of strands 5↔6. Acts as the K-matrix on 2-dim
sub-blocks where the (5,6) fusion edge has fusion outcome τ (the
second-qubit analogue of σ_2). 23 nonzero entries; block-2×2
structure on {(1,3), (2,4), (7,10), (8,11), (9,12)} + diagonal
phases at {0, 5, 6}. -/
def sigma5_sextet : Mat13K_5Ext := fun i j =>
  match (i.val, j.val) with
  | (0, 0) => Rtau_ext
  | (1, 1) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (1, 3) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (2, 2) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (2, 4) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (3, 1) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (3, 3) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (4, 2) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (4, 4) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (5, 5) => Rtau_ext
  | (6, 6) => Rtau_ext
  | (7, 7) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (7, 10) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (8, 8) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (8, 11) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (9, 9) => ofQCyc5 ⟨0, 1, 0, 1⟩
  | (9, 12) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (10, 7) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (10, 10) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (11, 8) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (11, 11) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (12, 9) => ⟨0, ⟨-1, 0, -1, 0⟩⟩
  | (12, 12) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | _ => 0

/-! ## 2. The 5 inverse σ generators (TQSim ordering)

Each σ_n_inv is the matrix inverse of σ_n, equivalently the
conjugate-transpose (σ_n is unitary). Entry alphabet is the complex
conjugate of the forward alphabet, computed via ζ̄ = ζ⁴ =
-1-ζ-ζ²-ζ³ within Q(ζ₅). -/

def sigma1_sextet_inv : Mat13K_5Ext := fun i j =>
  match (i.val, j.val) with
  | (0, 0) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (1, 1) => ofQCyc5 ⟨0, 0, 1, 0⟩
  | (2, 2) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (3, 3) => ofQCyc5 ⟨0, 0, 1, 0⟩
  | (4, 4) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (5, 5) => ofQCyc5 ⟨0, 0, 1, 0⟩
  | (6, 6) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (7, 7) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (8, 8) => ofQCyc5 ⟨0, 0, 1, 0⟩
  | (9, 9) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (10, 10) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (11, 11) => ofQCyc5 ⟨0, 0, 1, 0⟩
  | (12, 12) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | _ => 0

def sigma2_sextet_inv : Mat13K_5Ext := fun i j =>
  match (i.val, j.val) with
  | (0, 0) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (1, 1) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (1, 2) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (2, 1) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (2, 2) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (3, 3) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (3, 4) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (4, 3) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (4, 4) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (5, 5) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (5, 6) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (6, 5) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (6, 6) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (7, 7) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (8, 8) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (8, 9) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (9, 8) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (9, 9) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (10, 10) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (11, 11) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (11, 12) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (12, 11) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (12, 12) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | _ => 0

def sigma3_sextet_inv : Mat13K_5Ext := fun i j =>
  match (i.val, j.val) with
  | (0, 0) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (0, 2) => ofQCyc5 ⟨-1, 0, 0, -1⟩
  | (0, 4) => ⟨0, ⟨-2, -1, -1, -2⟩⟩
  | (1, 1) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (1, 3) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (2, 0) => ofQCyc5 ⟨-1, 0, 0, -1⟩
  | (2, 2) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (2, 4) => ⟨0, ⟨-2, -1, -1, -2⟩⟩
  | (3, 1) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (3, 3) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (4, 0) => ⟨0, ⟨-2, -1, -1, -2⟩⟩
  | (4, 2) => ⟨0, ⟨-2, -1, -1, -2⟩⟩
  | (4, 4) => ofQCyc5 ⟨2, 0, 1, 2⟩
  | (5, 5) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (5, 8) => ofQCyc5 ⟨-1, 0, 0, -1⟩
  | (5, 11) => ⟨0, ⟨-2, -1, -1, -2⟩⟩
  | (6, 6) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (6, 7) => ⟨0, ⟨2, 1, 1, 2⟩⟩
  | (6, 9) => ofQCyc5 ⟨-2, -1, -1, -2⟩
  | (6, 10) => ofQCyc5 ⟨-2, -1, -1, -2⟩
  | (6, 12) => ⟨0, ⟨-3, -1, -1, -3⟩⟩
  | (7, 6) => ⟨0, ⟨2, 1, 1, 2⟩⟩
  | (7, 7) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (7, 12) => ofQCyc5 ⟨-1, 0, 0, -1⟩
  | (8, 5) => ofQCyc5 ⟨-1, 0, 0, -1⟩
  | (8, 8) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (8, 11) => ⟨0, ⟨-2, -1, -1, -2⟩⟩
  | (9, 6) => ofQCyc5 ⟨-2, -1, -1, -2⟩
  | (9, 9) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (9, 10) => ofQCyc5 ⟨-1, 0, 0, -1⟩
  | (9, 12) => ⟨0, ⟨-3, -1, -1, -3⟩⟩
  | (10, 6) => ofQCyc5 ⟨-2, -1, -1, -2⟩
  | (10, 9) => ofQCyc5 ⟨-1, 0, 0, -1⟩
  | (10, 10) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (10, 12) => ⟨0, ⟨-3, -1, -1, -3⟩⟩
  | (11, 5) => ⟨0, ⟨-2, -1, -1, -2⟩⟩
  | (11, 8) => ⟨0, ⟨-2, -1, -1, -2⟩⟩
  | (11, 11) => ofQCyc5 ⟨2, 0, 1, 2⟩
  | (12, 6) => ⟨0, ⟨-3, -1, -1, -3⟩⟩
  | (12, 7) => ofQCyc5 ⟨-1, 0, 0, -1⟩
  | (12, 9) => ⟨0, ⟨-3, -1, -1, -3⟩⟩
  | (12, 10) => ⟨0, ⟨-3, -1, -1, -3⟩⟩
  | (12, 12) => ofQCyc5 ⟨4, 1, 2, 4⟩
  | _ => 0

def sigma4_sextet_inv : Mat13K_5Ext := fun i j =>
  match (i.val, j.val) with
  | (0, 0) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (1, 1) => ofQCyc5 ⟨0, 0, 1, 0⟩
  | (2, 2) => ofQCyc5 ⟨0, 0, 1, 0⟩
  | (3, 3) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (4, 4) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (5, 5) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (6, 6) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (7, 7) => ofQCyc5 ⟨0, 0, 1, 0⟩
  | (8, 8) => ofQCyc5 ⟨0, 0, 1, 0⟩
  | (9, 9) => ofQCyc5 ⟨0, 0, 1, 0⟩
  | (10, 10) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (11, 11) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (12, 12) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | _ => 0

def sigma5_sextet_inv : Mat13K_5Ext := fun i j =>
  match (i.val, j.val) with
  | (0, 0) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (1, 1) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (1, 3) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (2, 2) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (2, 4) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (3, 1) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (3, 3) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (4, 2) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (4, 4) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (5, 5) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (6, 6) => ofQCyc5 ⟨0, -1, 0, 0⟩
  | (7, 7) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (7, 10) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (8, 8) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (8, 11) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (9, 9) => ofQCyc5 ⟨-1, -1, 0, -1⟩
  | (9, 12) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (10, 7) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (10, 10) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (11, 8) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (11, 11) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | (12, 9) => ⟨0, ⟨-1, 0, 0, -1⟩⟩
  | (12, 12) => ofQCyc5 ⟨1, 0, 1, 1⟩
  | _ => 0

/-! ## 3. Inverse-identity theorems

Each `σ_n * σ_n_inv = 1` and `σ_n_inv * σ_n = 1` discharges via
`native_decide` on the 169-entry equality after unfolding the
hand-rolled `Mat13K_5Ext.mul` to its explicit 13-term sum-of-products
per output entry. Each theorem exercises a 1-mul Mat13K_5Ext
operation (within the ≤ 4-mul budget per `Mat13K5Ext.lean`). -/

theorem sigma1_inv_right : sigma1_sextet * sigma1_sextet_inv = 1 := by native_decide
theorem sigma1_inv_left  : sigma1_sextet_inv * sigma1_sextet = 1 := by native_decide
theorem sigma2_inv_right : sigma2_sextet * sigma2_sextet_inv = 1 := by native_decide
theorem sigma2_inv_left  : sigma2_sextet_inv * sigma2_sextet = 1 := by native_decide
theorem sigma3_inv_right : sigma3_sextet * sigma3_sextet_inv = 1 := by native_decide
theorem sigma3_inv_left  : sigma3_sextet_inv * sigma3_sextet = 1 := by native_decide
theorem sigma4_inv_right : sigma4_sextet * sigma4_sextet_inv = 1 := by native_decide
theorem sigma4_inv_left  : sigma4_sextet_inv * sigma4_sextet = 1 := by native_decide
theorem sigma5_inv_right : sigma5_sextet * sigma5_sextet_inv = 1 := by native_decide
theorem sigma5_inv_left  : sigma5_sextet_inv * sigma5_sextet = 1 := by native_decide

end SKEFTHawking
