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

/-! ## 4. Far-commutativity relations (B_6 braid group axiom 2)

For `|i - j| ≥ 2`, the generators σ_i and σ_j commute. In B_6 there
are 6 such pairs: (1,3), (1,4), (1,5), (2,4), (2,5), (3,5). Each
discharges via `native_decide` on a single Mat13K_5Ext multiplication
per side (1-mul chains). -/

theorem far_comm_1_3 : sigma1_sextet * sigma3_sextet = sigma3_sextet * sigma1_sextet := by native_decide
theorem far_comm_1_4 : sigma1_sextet * sigma4_sextet = sigma4_sextet * sigma1_sextet := by native_decide
theorem far_comm_1_5 : sigma1_sextet * sigma5_sextet = sigma5_sextet * sigma1_sextet := by native_decide
theorem far_comm_2_4 : sigma2_sextet * sigma4_sextet = sigma4_sextet * sigma2_sextet := by native_decide
theorem far_comm_2_5 : sigma2_sextet * sigma5_sextet = sigma5_sextet * sigma2_sextet := by native_decide
theorem far_comm_3_5 : sigma3_sextet * sigma5_sextet = sigma5_sextet * sigma3_sextet := by native_decide

/-! ## 5. Yang-Baxter relations (B_6 braid group axiom 1)

For adjacent generators σ_i, σ_{i+1}, the braid relation
`σ_i σ_{i+1} σ_i = σ_{i+1} σ_i σ_{i+1}` holds. In B_6 there are 4
such relations (i = 1, 2, 3, 4). Each discharges via `native_decide`
on a 2-mul Mat13K_5Ext chain per side (within the ≤ 4-mul budget). -/

theorem yang_baxter_1_2 :
    sigma1_sextet * sigma2_sextet * sigma1_sextet =
    sigma2_sextet * sigma1_sextet * sigma2_sextet := by native_decide

theorem yang_baxter_2_3 :
    sigma2_sextet * sigma3_sextet * sigma2_sextet =
    sigma3_sextet * sigma2_sextet * sigma3_sextet := by native_decide

theorem yang_baxter_3_4 :
    sigma3_sextet * sigma4_sextet * sigma3_sextet =
    sigma4_sextet * sigma3_sextet * sigma4_sextet := by native_decide

theorem yang_baxter_4_5 :
    sigma4_sextet * sigma5_sextet * sigma4_sextet =
    sigma5_sextet * sigma4_sextet * sigma5_sextet := by native_decide

/-! ## 6. Block-diagonality: sector preservation

The 13-dim fusion space splits as 5-dim c=1 sector (indices {0..4})
+ 8-dim c=τ sector (indices {5..12}) per DR §Q2.1. Each σ_n
preserves this decomposition (no cross-sector matrix elements):
all entries with `(i.val < 5) ≠ (j.val < 5)` are zero. This is a
structural property of the F-symbol-recoupled braid action and is
exploited in Phase 2 to extract the per-sector computational
sub-blocks independently.

We express this via the `blockDiag` predicate: zeroing out
cross-sector entries leaves the matrix unchanged. -/

/-- The block-diagonal projector: zeros out cross-sector entries of a
`Mat13K_5Ext`. A matrix `M` is block-diagonal w.r.t. the {0..4}/{5..12}
split iff `M = blockDiag M`. -/
def blockDiag (M : Mat13K_5Ext) : Mat13K_5Ext := fun i j =>
  if (i.val < 5) = (j.val < 5) then M i j else 0

theorem sigma1_block_diag : sigma1_sextet = blockDiag sigma1_sextet := by native_decide
theorem sigma2_block_diag : sigma2_sextet = blockDiag sigma2_sextet := by native_decide
theorem sigma3_block_diag : sigma3_sextet = blockDiag sigma3_sextet := by native_decide
theorem sigma4_block_diag : sigma4_sextet = blockDiag sigma4_sextet := by native_decide
theorem sigma5_block_diag : sigma5_sextet = blockDiag sigma5_sextet := by native_decide

/-! ### Block-diagonality of inverse generators

The inverse generators σ_n⁻¹ also preserve the sector decomposition.
This is structurally guaranteed by σ_n being block-diagonal (the
inverse of a block-diagonal unitary is block-diagonal — proved
substantively via `native_decide` on each entry). Load-bearing for
Phase 2 chunk-tree compositions involving both σ_n and σ_n⁻¹:
without this, mixed-product blocks could in principle leak across
sectors. -/

theorem sigma1_inv_block_diag : sigma1_sextet_inv = blockDiag sigma1_sextet_inv := by native_decide
theorem sigma2_inv_block_diag : sigma2_sextet_inv = blockDiag sigma2_sextet_inv := by native_decide
theorem sigma3_inv_block_diag : sigma3_sextet_inv = blockDiag sigma3_sextet_inv := by native_decide
theorem sigma4_inv_block_diag : sigma4_sextet_inv = blockDiag sigma4_sextet_inv := by native_decide
theorem sigma5_inv_block_diag : sigma5_sextet_inv = blockDiag sigma5_sextet_inv := by native_decide

/-! ## 7. Computational sub-block extraction (TQSim ordering)

The 13-dim fusion space carries two 4-dim computational sub-blocks
(per DR Q2.1; one per sector). These are the sub-spaces that admit
a 2-qubit interpretation:

* **Sector 0** (c=1, vacuum total charge): indices `{1, 2, 3, 4}`
  (matches both TQSim and DR ordering).
* **Sector 1** (c=τ, Fibonacci total charge): indices
  `{8, 9, 11, 12}` in TQSim ordering. (DR Table 2 uses
  `{9, 10, 11, 12}`; the difference is a 3-cycle permutation at
  `{8, 9, 10}` discovered in session 13. The Lean substrate uses
  TQSim ordering as canonical — see module-header docstring.)

We provide two extraction functions returning 4×4 matrices over
QCyc5Ext, plus sanity-check identity-mapping theorems.
-/

/-- Sector-0 computational sub-block index map: `0↦1, 1↦2, 2↦3, 3↦4`. -/
def sec0Idx (i : Fin 4) : Fin 13 :=
  match i with
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨2, _⟩ => ⟨3, by decide⟩
  | ⟨_, _⟩ => ⟨4, by decide⟩

/-- Sector-1 computational sub-block index map (TQSim ordering):
`0↦8, 1↦9, 2↦11, 3↦12`. -/
def sec1Idx (i : Fin 4) : Fin 13 :=
  match i with
  | ⟨0, _⟩ => ⟨8, by decide⟩
  | ⟨1, _⟩ => ⟨9, by decide⟩
  | ⟨2, _⟩ => ⟨11, by decide⟩
  | ⟨_, _⟩ => ⟨12, by decide⟩

/-- Extract the sector-0 computational sub-block (4×4 over QCyc5Ext). -/
def computationalSec0 (M : Mat13K_5Ext) : Fin 4 → Fin 4 → QCyc5Ext :=
  fun i j => M (sec0Idx i) (sec0Idx j)

/-- Extract the sector-1 computational sub-block (4×4 over QCyc5Ext)
in TQSim ordering. -/
def computationalSec1 (M : Mat13K_5Ext) : Fin 4 → Fin 4 → QCyc5Ext :=
  fun i j => M (sec1Idx i) (sec1Idx j)

/-! ### Smoke tests: sub-block extraction at corner entries

These exercise the extraction path on `native_decide` to catch
toolchain regressions. We test corner entries of σ_1 (diagonal
sector-0 entry pattern (R_τ, R_1, R_τ, R_1, R_τ)) AND σ_4 (different
diagonal pattern (R_τ, R_1, R_1, R_τ, R_τ)) on BOTH sectors —
independent coverage catches drift in any of (a) the σ_n literals,
(b) the `sec0Idx`/`sec1Idx` index maps, (c) the `computationalSec0/1`
extractors, or (d) the `Rtau_ext`/`R1_ext` primitives. -/

theorem computationalSec0_sigma1_00 :
    computationalSec0 sigma1_sextet 0 0 = R1_ext := by native_decide
theorem computationalSec0_sigma1_33 :
    computationalSec0 sigma1_sextet 3 3 = Rtau_ext := by native_decide
theorem computationalSec1_sigma1_00 :
    computationalSec1 sigma1_sextet 0 0 = R1_ext := by native_decide
theorem computationalSec1_sigma1_33 :
    computationalSec1 sigma1_sextet 3 3 = Rtau_ext := by native_decide

/-- σ_4 sector-0 sub-block corner (0,0) = R_1 (TQSim index 1 of σ_4 is R_1). -/
theorem computationalSec0_sigma4_00 :
    computationalSec0 sigma4_sextet 0 0 = R1_ext := by native_decide
/-- σ_4 sector-0 sub-block corner (3,3) = R_τ (TQSim index 4 of σ_4 is R_τ). -/
theorem computationalSec0_sigma4_33 :
    computationalSec0 sigma4_sextet 3 3 = Rtau_ext := by native_decide
/-- σ_4 sector-1 sub-block corner (0,0) = R_1 (TQSim index 8 of σ_4 is R_1). -/
theorem computationalSec1_sigma4_00 :
    computationalSec1 sigma4_sextet 0 0 = R1_ext := by native_decide
/-- σ_4 sector-1 sub-block corner (3,3) = R_τ (TQSim index 12 of σ_4 is R_τ). -/
theorem computationalSec1_sigma4_33 :
    computationalSec1 sigma4_sextet 3 3 = Rtau_ext := by native_decide

/-! ## 8. Block-diagonality closure under matrix algebra

The 13×13 block-diagonal subspace (matrices whose only nonzero entries
sit in the c=1 sector `{0..4}×{0..4}` or the c=τ sector `{5..12}×{5..12}`)
is closed under matrix multiplication and contains the identity. Together
with the per-generator theorems `sigma_n_block_diag` and `sigma_n_inv_block_diag`
above, these closure properties enable a clean *structural* sector-preservation
proof on any composition of σ-generators — for instance the 280-letter HZBS Fig 15
CNOT braid word that downstream consumers may wish to analyze.

Why this matters: a *coefficient-level* verification (each entry of the 280-
letter product equals a specific Q(ζ₅, √φ) element) is blocked by coefficient
explosion (max |coeff| grows ~10× per chunk-doubling, reaching ~10¹⁷ at the
full witness — well past `native_decide`'s kernel budget for our hand-rolled
`Mat13K_5Ext.mul`). The *structural* sector-preservation claim is the load-
bearing topological-protection content of HZBS Fig 15; the numerical
Frobenius distance from the target controlled-iX gate (sub-2×10⁻³ in both
sectors) can be verified by downstream numerical pipelines.
-/

/-- The identity 13×13 matrix is block-diagonal. -/
theorem one_block_diag : (1 : Mat13K_5Ext) = blockDiag 1 := by native_decide

/-- The zero 13×13 matrix is block-diagonal. -/
theorem zero_block_diag : (0 : Mat13K_5Ext) = blockDiag 0 := by native_decide

/-- Helper: pointwise off-block characterization of block-diagonality.
A matrix `M : Mat13K_5Ext` is block-diagonal (i.e. `M = blockDiag M`) iff
all cross-sector entries vanish. -/
theorem blockDiag_iff_off_block_zero (M : Mat13K_5Ext) :
    M = blockDiag M ↔
      ∀ i j : Fin 13, (i.val < 5) ≠ (j.val < 5) → M i j = 0 := by
  constructor
  · intro hM i j hne
    have eq_ij := congrFun (congrFun hM i) j
    unfold blockDiag at eq_ij
    rw [if_neg hne] at eq_ij
    exact eq_ij
  · intro h
    funext i j
    unfold blockDiag
    by_cases h_eq : (i.val < 5) = (j.val < 5)
    · rw [if_pos h_eq]
    · rw [if_neg h_eq]
      exact h i j h_eq

/-- **Closure property:** matrix multiplication preserves block-diagonality.
If `A` and `B` are block-diagonal w.r.t. the {0..4}/{5..12} sector split,
then so is `A * B`. Structural proof: each term `A i k * B k j` in the
explicit 13-term sum (from `Mat13K_5Ext.mul`) vanishes when `(i.val<5)`
and `(j.val<5)` differ — either the `A`-factor is off-block (so zero)
or the `B`-factor is off-block (so zero). -/
theorem mul_preserves_blockDiag {A B : Mat13K_5Ext}
    (hA : A = blockDiag A) (hB : B = blockDiag B) :
    A * B = blockDiag (A * B) := by
  -- Convert to predicate form for cleaner manipulation.
  rw [blockDiag_iff_off_block_zero] at hA hB ⊢
  intro i j h_eq
  -- Goal: (A * B) i j = 0 when (i.val<5) ≠ (j.val<5).
  show Mat13K_5Ext.mul A B i j = 0
  unfold Mat13K_5Ext.mul
  -- Each term in the unrolled 13-term sum vanishes.
  have zero_term : ∀ k : Fin 13, A i k * B k j = 0 := by
    intro k
    by_cases hki : (i.val < 5) = (k.val < 5)
    · -- (k.val<5) = (i.val<5) ≠ (j.val<5), so B k j = 0.
      have hkj : (k.val < 5) ≠ (j.val < 5) := fun heq => h_eq (hki.trans heq)
      rw [hB k j hkj, mul_zero]
    · -- (i.val<5) ≠ (k.val<5), so A i k = 0.
      rw [hA i k hki, zero_mul]
  rw [zero_term 0, zero_term 1, zero_term 2, zero_term 3, zero_term 4,
      zero_term 5, zero_term 6, zero_term 7, zero_term 8, zero_term 9,
      zero_term 10, zero_term 11, zero_term 12]
  ring

end SKEFTHawking
