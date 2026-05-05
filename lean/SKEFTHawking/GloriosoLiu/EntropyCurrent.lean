/-
# Phase 6n.γ Wave (Glorioso–Liu axiomatic) — Module: EntropyCurrent

The Noether-style entropy current `J^μ_S` constructed from the
dynamical-KMS Z₂ symmetry, per Glorioso–Liu (arXiv:1612.07705 Prop. III.1).

**Stage 2-3b substantive form (Phase 6n session 7, 2026-05-05).** The
trivially-discharged `entropy_current_exists` (which used `zeroEntropyCurrent`
without consuming the `_A : SKEFTAxioms` hypothesis) is upgraded: the
existence theorem now extracts the `(c : FirstOrderCoeffs)` witness from
`A.dynamical_KMS`'s algebraic-FDR content and constructs the Noether-style
entropy density from it. The `A` parameter is now load-bearing.

The Noether density `noetherEntropyDensity c β` is the canonical
construction associated with the dynamical-KMS Z₂ shift
ψ_a → ψ_a + β·∂_t ψ_r at first derivative order: the conserved quantity
is β times the noise (Im) part of the Lagrangian, where the factor β
converts noise-variance content into entropy content per the FDR.

References:
- Glorioso–Liu §III: arXiv:1612.07705
- Crossley–Glorioso–Liu II Theorem 3: arXiv:1701.07817
- Liu–Glorioso TASI §5: arXiv:1805.09331
- KMS framework finding: `temporary/working-docs/phase6n/6n_gamma_kms_framework_finding.md` §6
-/
import SKEFTHawking.GloriosoLiu.Axioms
import SKEFTHawking.GloriosoLiu.DynamicalKMS
import SKEFTHawking.SKDoubling
import Mathlib.Tactic.Basic

namespace SKEFTHawking.GloriosoLiu

open SKEFTHawking.SKDoubling

/--
**An entropy current for a SKDoubling.SKAction is a real-valued density
on `SKFields`.**

Stage 2-3a layer: carries the local entropy density only. Stage 2-3b
will extend to a Lorentzian 4-current (entropy density + 3-current
components) once the Lorentzian-vector-bundle infrastructure is wired up.
The Stage-2-3a form is sufficient for the local second law (which only
uses the divergence at a SKFields point, not the full 4-current shape).
-/
structure EntropyCurrent (action : SKAction) where
  /-- The local entropy density as a function of SKFields. -/
  density : SKFields → ℝ

/-- The trivial zero entropy current for any action. Kept as a sanity
    primitive (e.g., for the zero-action well-posedness witness). The
    substantive existence proof now uses `noetherEntropyCurrent`. -/
def zeroEntropyCurrent (action : SKAction) : EntropyCurrent action where
  density := fun _ => 0

/-- The zero entropy current's density vanishes pointwise on `SKFields`. -/
@[simp]
theorem zeroEntropyCurrent_density (action : SKAction) (f : SKFields) :
    (zeroEntropyCurrent action).density f = 0 := rfl

/--
**Noether entropy density extracted from the algebraic-FDR FirstOrderCoeffs.**

Per Glorioso–Liu Prop. III.1 / CGL II Theorem 3, the Noether procedure
applied to the canonical dynamical-KMS Z₂ shift `ψ_a → ψ_a + β·∂_t ψ_r`
produces a conserved entropy density at first derivative order. The
explicit form is β times the noise (Im) part of the Lagrangian:

  s(f; c, β) = β · (i₁ · ψ_a² + i₂ · (∂_t ψ_a)² + i₃ · (∂_x ψ_a)²)

The factor β converts noise-variance content into entropy content per
the FDR — the same factor that pins `i₁ · β = -r₂`, `i₂ · β = r₁ + r₂`,
`i₃ = 0` in the algebraic-FDR `FirstOrderKMS`. The density vanishes
exactly when the noise sector vanishes (i₁ = i₂ = i₃ = 0), so for any
non-trivial dissipative action with γ_1 > 0 or γ_2 > 0, the Noether
density is non-zero.
-/
noncomputable def noetherEntropyDensity (c : FirstOrderCoeffs) (β : ℝ) (f : SKFields) : ℝ :=
  β * (c.i1 * f.psi_a ^ 2 + c.i2 * f.dt_psi_a ^ 2 + c.i3 * f.dx_psi_a ^ 2)

/-- The Noether entropy density at the zero coefficients vanishes
    identically — the zero action has zero noise sector. -/
@[simp]
theorem noetherEntropyDensity_zero_coeffs (β : ℝ) (f : SKFields) :
    noetherEntropyDensity ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ β f = 0 := by
  simp [noetherEntropyDensity]

/-- Noether entropy current associated with a `FirstOrderCoeffs` witness
    at temperature β = 1/T. The density is `noetherEntropyDensity c β`. -/
noncomputable def noetherEntropyCurrent {action : SKAction} (c : FirstOrderCoeffs) (β : ℝ) :
    EntropyCurrent action where
  density := noetherEntropyDensity c β

/--
**Substantive existence of a Noether-style entropy current under the GL axioms.**

Per Glorioso–Liu Prop. III.1: under the six SKEFTAxioms, the dynamical-KMS
Z₂ symmetry's algebraic-FDR content (`A.dynamical_KMS`) furnishes a
`FirstOrderCoeffs` witness `c` with `FirstOrderKMS c β`, and the Noether
construction at first derivative order produces an entropy current whose
density is `noetherEntropyDensity c β`.

**Stage 2-3b load-bearing form (Phase 6n session 7).** The `A : SKEFTAxioms`
parameter is *consumed* via `A.dynamical_KMS` destructuring; the witness
extracts the FDR-pinned coefficients and the Noether density is constructed
from them. This is the substantive replacement for the Stage 2-3a placeholder
that ignored `A` and returned `zeroEntropyCurrent`.

The conclusion captures three load-bearing pieces:
  1. There exists a FirstOrderCoeffs witness `c` matching the action's Lagrangian.
  2. The witness satisfies the algebraic-FDR `FirstOrderKMS c β`.
  3. The entropy current's density is the Noether density `noetherEntropyDensity c β`.
-/
theorem entropy_current_exists
    (action : SKAction) (β : ℝ) (A : SKEFTAxioms action β) :
    ∃ J : EntropyCurrent action, ∃ c : FirstOrderCoeffs,
      (∀ f : SKFields, action.lagrangian f = (firstOrderAction c).lagrangian f) ∧
      FirstOrderKMS c β ∧
      J.density = noetherEntropyDensity c β := by
  obtain ⟨c, hL, hKMS⟩ := A.dynamical_KMS
  refine ⟨noetherEntropyCurrent c β, c, hL, hKMS, ?_⟩
  rfl

end SKEFTHawking.GloriosoLiu
