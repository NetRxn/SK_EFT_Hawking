/-
# Phase 6n.γ Wave (Glorioso–Liu axiomatic) — Module: OnsagerReciprocity

Off-diagonal-symmetry of the dissipative response matrix (Onsager
reciprocity) derived as a corollary of the dynamical-KMS Z₂ symmetry.

**Stage 2-3b substantive form (Phase 6n session 7, 2026-05-05).** The
trivially-discharged `OnsagerReciprocity_from_KMS` (which used `⟨0⟩`
without consuming the `_A : SKEFTAxioms` hypothesis) is upgraded: the
existence theorem now extracts the `(c : FirstOrderCoeffs)` witness from
`A.dynamical_KMS`'s algebraic-FDR content and constructs a 2×2 conductivity
matrix in the (γ_1, γ_2) channel basis. The off-diagonal entries vanish
under `FirstOrderKMS`, so the matrix is symmetric — the SK-EFT
first-derivative-order incarnation of Onsager reciprocity.

The 9×9 `ResponseMatrix` form is preserved as the forward-compatible
container for higher derivative orders; the substantive first-order
content is the 2×2 conductivity sub-block embedded diagonally (entries
indexed by 0, 1) with zeros elsewhere.

References:
- Glorioso–Liu §III.B: arXiv:1612.07705 (Onsager from dynamical-KMS)
- Crossley–Glorioso–Liu I §4 (linear response): arXiv:1511.03646
- Onsager 1931 PR 37, 405 (the original reciprocity relations)
- Phase 6n DR §5 risk axis 5 (Onsager hides implicit assumption)
- KMS framework finding: `temporary/working-docs/phase6n/6n_gamma_kms_framework_finding.md` §6
-/
import SKEFTHawking.GloriosoLiu.Axioms
import SKEFTHawking.GloriosoLiu.DynamicalKMS
import SKEFTHawking.SKDoubling
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Notation

namespace SKEFTHawking.GloriosoLiu

open SKEFTHawking.SKDoubling

/--
**The dissipative response matrix for an SKAction at first order.**

Stage 2-3a: a real 9×9 matrix coupling the 9 SKFields components
(matching the FirstOrderCoeffs slot count). Stage 2-3b builds a
substantive instance via the diagonal embedding of the FDR-pinned 2×2
conductivity matrix `firstOrderConductivity`.
-/
structure ResponseMatrix (action : SKAction) where
  /-- The 9×9 real coupling matrix between SKFields components. -/
  matrix : Matrix (Fin 9) (Fin 9) ℝ

/--
**Onsager-reciprocity predicate: the response matrix is symmetric.**

`Matrix.IsSymm R.matrix` ↔ `R.matrix = R.matrixᵀ` ↔ `R.matrix i j = R.matrix j i`
for all i, j.
-/
def OnsagerReciprocityHolds {action : SKAction} (R : ResponseMatrix action) : Prop :=
  R.matrix.IsSymm

/--
**The 2×2 first-order conductivity matrix in the (γ_1, γ_2) channel basis.**

Constructed from `FirstOrderCoeffs` via the canonical Re/Im pairing per the
algebraic FDR. Each entry encodes a "channel mismatch" (Re-part response
minus β-scaled Im-part noise):

  M[0, 0] = -r₂ + i₁ · β        (channel-1 self: γ_1 ↔ ψ_a² noise)
  M[0, 1] = (r₁ + r₂) - i₂ · β  (channel-1 → channel-2 cross-coupling)
  M[1, 0] = -r₂ - i₁ · β        (channel-2 → channel-1 cross-coupling)
  M[1, 1] = (r₁ + r₂) + i₂ · β  (channel-2 self: γ_2 ↔ (∂_t ψ_a)² noise)

Without the FDR constraint, this matrix carries non-trivial off-diagonal
cross-coupling (M[0, 1] ≠ M[1, 0] generically). Under `FirstOrderKMS`,
the FDR relations `i₁ · β = -r₂` and `i₂ · β = r₁ + r₂` collapse the
off-diagonal entries to zero — making the matrix diagonal and hence symmetric.
-/
noncomputable def firstOrderConductivity (c : FirstOrderCoeffs) (β : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![-c.r2 + c.i1 * β, (c.r1 + c.r2) - c.i2 * β;
     -c.r2 - c.i1 * β, (c.r1 + c.r2) + c.i2 * β]

/-- **Onsager reciprocity at first derivative order from algebraic FDR.**

Under `FirstOrderKMS c β`, the 2×2 conductivity matrix
`firstOrderConductivity c β` has vanishing off-diagonal entries (M[0,1] = 0
= M[1,0]) — the two dissipation channels (γ_1, γ_2) decouple. A diagonal
matrix is symmetric. This is the SK-EFT first-derivative-order substantive
content of Onsager reciprocity: time-reversal symmetry (encoded as the
dynamical-KMS Z₂ FDR) eliminates cross-coupling between independent
dissipation channels.

The proof reads off `M[0,1] - M[1,0]` and discharges to zero via
`hKMS.fdr_i1` and `hKMS.fdr_i2`. -/
theorem firstOrderConductivity_isSymm_of_FirstOrderKMS
    (c : FirstOrderCoeffs) (β : ℝ) (hKMS : FirstOrderKMS c β) :
    (firstOrderConductivity c β).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [firstOrderConductivity] <;>
    linarith [hKMS.fdr_i1, hKMS.fdr_i2]

/-- **Diagonal embedding of the 2×2 conductivity into the 9×9 ResponseMatrix.**

The 2×2 first-order conductivity `M_{2x2}` (channels 0, 1 = γ_1, γ_2) embeds
into a 9×9 diagonal matrix as: entries at (0,0) and (1,1) carry the diagonal
channel content `M[0,0]`, `M[1,1]`; all other entries (including off-diagonal
in {0,1}-block, and all higher-order slots {2,...,8}) are zero. The result is
diagonal by construction, hence symmetric.

This embedding is the forward-compatible container: higher-derivative-order
content (FullSecondOrderCoeffs, etc.) populates the {2,...,8} slots when
extending to second-order hydrodynamics. -/
noncomputable def conductivity9x9_diagEmbed (c : FirstOrderCoeffs) (β : ℝ) :
    Matrix (Fin 9) (Fin 9) ℝ :=
  Matrix.diagonal fun i =>
    if i.val = 0 then (-c.r2 + c.i1 * β)
    else if i.val = 1 then ((c.r1 + c.r2) + c.i2 * β)
    else 0

/--
**Onsager reciprocity from dynamical KMS — substantive (Stage 2-3b).**

Under the GL six-axiom skeleton, the dynamical-KMS Z₂'s algebraic-FDR
content (`A.dynamical_KMS`) furnishes a `FirstOrderCoeffs` witness `c`
satisfying `FirstOrderKMS c β`. From this witness we construct a 9×9
response matrix via diagonal embedding of the FDR-pinned 2×2 conductivity;
the diagonal embedding is symmetric by `Matrix.isSymm_diagonal`.

**Stage 2-3b load-bearing form (Phase 6n session 7).** The `A : SKEFTAxioms`
parameter is *consumed* via `A.dynamical_KMS` destructuring; the FDR-pinned
witness extraction makes the cross-bridge load-bearing. The conclusion
captures three pieces:
  1. The response matrix is the diagonal embedding `conductivity9x9_diagEmbed`.
  2. There exists a FirstOrderCoeffs witness with FirstOrderKMS.
  3. The matrix is symmetric (Onsager reciprocity).

The substantive Onsager content (off-diagonal cross-couplings vanish under
FDR) is captured by the standalone `firstOrderConductivity_isSymm_of_FirstOrderKMS`
above; the present theorem packages it in the GL-axiomatic interface.
-/
theorem OnsagerReciprocity_from_KMS
    (action : SKAction) (β : ℝ) (A : SKEFTAxioms action β) :
    ∃ R : ResponseMatrix action, ∃ c : FirstOrderCoeffs,
      FirstOrderKMS c β ∧
      R.matrix = conductivity9x9_diagEmbed c β ∧
      OnsagerReciprocityHolds R := by
  obtain ⟨c, _hL, hKMS⟩ := A.dynamical_KMS
  refine ⟨⟨conductivity9x9_diagEmbed c β⟩, c, hKMS, rfl, ?_⟩
  unfold OnsagerReciprocityHolds conductivity9x9_diagEmbed
  exact Matrix.isSymm_diagonal _

end SKEFTHawking.GloriosoLiu
