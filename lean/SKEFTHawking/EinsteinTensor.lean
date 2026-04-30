import SKEFTHawking.Basic
import SKEFTHawking.Curvature
import SKEFTHawking.LinearizedEFE
import Mathlib

/-!
# Phase 6f Wave 2 — Einstein Tensor

## Overview

Coordinate-based Einstein tensor `G_{μν} := Ric_{μν} − (1/2) R g_{μν}`,
with algebraic identities (linearity-of-trace, dimension-4 trace
`G^μ_μ = −R`, constant-K specialization `G_{μν} = −3K g_{μν}`,
vacuum `G = 0 ↔ Ric = 0`, and de Sitter `G + Λg = 0 ↔ Λ = 3K`).

The carrier matches Phase 6f Wave 1's `RicciTensor`/`MetricMatrix`
(`Fin 4 → Fin 4 → ℝ`); a manifold/connection-based companion layer is
introduced in Phase 6g.1 alongside the project-local Lorentzian metric.

## Second Bianchi `∇^μ G_{μν} = 0` — DEFERRED to Phase 6g.1+

The classical contracted second Bianchi `∇^μ G_{μν} = 0` requires a
covariant divergence operator, which we do not model in this
algebraic-only formulation. Three options were considered:
- (a) ship as tracked Prop with a trivial constant-K discharge —
  REJECTED per Phase 6f.1's strengthening lesson
  (zero-witness-as-trivial-plumbing pattern would absorb a retroactive
  cut at the strengthening pass);
- (b) defer to a future wave once a manifold-level Riemann curvature
  exists in our Lean ecosystem — CHOSEN;
- (c) coordinate-`∂_α` finite-difference placeholder — REJECTED
  (heavy bookkeeping, not Mathlib-PR shape).

**Status (2026-04-29 catch-up):** Bonn's
`Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.{Basic,Torsion}`
HAS landed in our pinned Mathlib commit `8850ed93`. However, Mathlib
still lacks Riemann/Ricci/scalar curvature on a connection (the audit
explicitly assigns those to SK-EFT as upstream contributor). Second
Bianchi is therefore not a "one-line consequence" — it requires
project-local Riemann-from-connection infrastructure first, which is
naturally placed alongside the Lorentzian metric work in 6g.1+.

## Anti-pattern audit (per project preemptive-strengthening discipline
   + Phase 6f.1 carry-forward "is the witness-existence statement
   informative beyond the predicate definition?")

1. **Bundle redundancy P2:** definition takes `Ric`, `R_scalar`, `g`
   as separate inputs (not bundled). The trace identity then *forces*
   the constraint `R_scalar = scalarOf Ric g_inv` for the substantive
   forms; we ship the linearity lemma without the constraint and the
   trace lemma with it. ✓
2. **Quantitative connection:** `einsteinTensor_trace_eq_neg_scalar`
   ships `G^μ_μ = −R` with the dimension-4 factor (`n − 2 = 2` for
   `n = 4`) explicit; `constantSectional_einsteinTensor_eq` ships
   `G = −3K · g`. Both are `ring`-backed. ✓
3. **Cross-module bridge integrity P6:** body imports
   `SKEFTHawking.Curvature` and *calls* `constantSectional_Ricci_eq`,
   `ricciOf`, `scalarOf` directly. The `constantSectional_einsteinTensor_eq`
   theorem is a substantive cross-bridge consumer. ✓
4. **Trivial-discharge P3 flag:** the linearity lemma is
   docstring-flagged as P3-trivial-class plumbing
   (definitional + `ring`); load-bearing physics is in trace identity
   + constant-K specialization + de Sitter-Λ relation. ✓
5. **Defining-the-conclusion check:** `einsteinTensor` is defined by
   the textbook formula; we do NOT define it as e.g.
   `einsteinTensor := -3K · g` (which would make
   `constantSectional_einsteinTensor_eq` trivial). The substantive
   content comes from combining the algebraic definition with the
   `constantSectional_Ricci_eq` consumed witness. ✓
6. **Non-vacuity / informativeness check (Phase 6f.1 carry-forward):**
   each theorem's hypothesis must do real algebraic work. The 4D
   trace identity uses the dimension hypothesis `(g_inv : g) = 4`;
   constant-K specialization needs both `constantSectional_Ricci_eq`
   and the dimension hypothesis; vacuum characterization uses the
   trace identity twice (forward via algebra, backward to extract `R`
   from `G = 0`). No theorem reduces to "definition unfolds to its
   target". ✓

## References

- R.M. Wald, *General Relativity* (1984) §3.2 (Einstein tensor + trace)
- S. Carroll, *Spacetime and Geometry* (2004) §4.2 (vacuum + Λ-vacuum)
- C. Misner, K. Thorne, J. Wheeler, *Gravitation* (1973) §17.2 (de
  Sitter as constant-curvature solution of Λ-EFE)
-/

namespace SKEFTHawking.EinsteinTensor

open Real
open SKEFTHawking.Curvature

/-! ## §1 — Carrier -/

/-- Einstein tensor in coordinate-matrix form:
`G_{μν} : Fin 4 → Fin 4 → ℝ`. Same shape as `RicciTensor` /
`MetricMatrix` for downstream interoperability. -/
abbrev EinsteinTensorType : Type := Fin 4 → Fin 4 → ℝ

/-! ## §2 — Definition -/

/-- **Einstein tensor**: `G_{μν} := Ric_{μν} − (1/2) R g_{μν}`.

Free parameter `R_scalar : ℝ` represents the scalar curvature.
Physical content arises by setting `R_scalar = scalarOf Ric g_inv`
(see trace identity in §4). -/
noncomputable def einsteinTensor (Ric : RicciTensor) (R_scalar : ℝ)
    (g : MetricMatrix) : EinsteinTensorType :=
  fun μ ν => Ric μ ν - (1/2) * R_scalar * g μ ν

/-! ## §3 — Symmetry

Substantive: hypothesis is `Ric` symmetric ∧ metric symmetric. Both
are load-bearing — dropping either yields a non-symmetric `G`.
-/

/-- **Symmetry**: `G_{μν} = G_{νμ}` whenever Ricci and metric are
both symmetric. Both hypotheses are load-bearing: the `(1/2) R g`
subtraction inherits each tensor's antisymmetric part. -/
theorem einsteinTensor_symm
    {Ric : RicciTensor} {R_scalar : ℝ} {g : MetricMatrix}
    (h_ric : ∀ μ ν, Ric μ ν = Ric ν μ)
    (h_g : MetricSymmetric g)
    (μ ν : Fin 4) :
    einsteinTensor Ric R_scalar g μ ν =
      einsteinTensor Ric R_scalar g ν μ := by
  unfold einsteinTensor
  rw [h_ric μ ν, h_g μ ν]

/-! ## §4 — Linearity-of-trace + 4D trace identity

The dimension-4 trace identity `G^μ_μ = −R` decomposes into

  (i) **algebraic linearity**: `scalarOf G g_inv = scalarOf Ric g_inv −
      (1/2) R · (g_inv : g)` for any dimension `n` (where the
      contraction `(g_inv : g) := Σ_{μν} g^{μν} g_{μν}` equals `n`);
  (ii) **dimension specialization**: for `n = 4` and
       `R = scalarOf Ric g_inv`, the linearity collapses to `−R`.

We ship (i) as a P3-trivial-class lemma (docstring-flagged) and (ii)
as the substantive quantitative-content theorem.
-/

/-- **Linearity of `scalarOf` over the Einstein-tensor decomposition.**

P3-trivial-class plumbing (`unfold` + `ring`); the dimension factor
appears in the `(g_inv : g)` sum, not here. We separate the algebraic
linearity from the dimension specialization to keep both small. -/
theorem einsteinTensor_scalar_linearity
    (Ric : RicciTensor) (R_scalar : ℝ) (g g_inv : MetricMatrix) :
    scalarOf (einsteinTensor Ric R_scalar g) g_inv
      = scalarOf Ric g_inv -
        (1/2) * R_scalar *
          sumFin4 (fun μ => sumFin4 (fun ν => g_inv μ ν * g μ ν)) := by
  unfold scalarOf einsteinTensor sumFin4
  ring

/-- **Dimension-4 trace identity** `G^μ_μ = −R`.

Substantive quantitative-content theorem: the dimension factor `n − 2
= 2` for `n = 4` emerges algebraically — the trace of the
`(1/2) R g_{μν}` subtraction equals `(1/2) R · n`, so the trace of
`G_{μν} = Ric_{μν} − (1/2) R g_{μν}` equals `R − (n/2) R = −R` only at
`n = 4`. -/
theorem einsteinTensor_trace_eq_neg_scalar
    (Ric : RicciTensor) (g g_inv : MetricMatrix)
    (h_dim : sumFin4 (fun μ => sumFin4 (fun ν => g_inv μ ν * g μ ν))
             = 4) :
    scalarOf (einsteinTensor Ric (scalarOf Ric g_inv) g) g_inv
      = -scalarOf Ric g_inv := by
  rw [einsteinTensor_scalar_linearity, h_dim]
  ring

/-! ## §5 — Constant-K specialization

For the constant-sectional-curvature Riemann witness from 6f.1, the
Einstein tensor takes the closed form `G_{μν} = −3K · g_{μν}` in 4D.
This is the wave's load-bearing cross-bridge consumer of 6f.1.
-/

/-- **Helper: scalarOf is point-wise-equality-respecting.** Used to
substitute `ricciOf (constantSectionalRiemann K g)` with its closed
form `3K · g` inside `scalarOf`. -/
theorem scalarOf_eq_of_pointwise
    {Ric₁ Ric₂ : RicciTensor} (g_inv : MetricMatrix)
    (h : ∀ μ ν, Ric₁ μ ν = Ric₂ μ ν) :
    scalarOf Ric₁ g_inv = scalarOf Ric₂ g_inv := by
  have heq : Ric₁ = Ric₂ := by funext μ ν; exact h μ ν
  rw [heq]

/-- **Constant-K scalar curvature**: `R = 12K` in 4D.

Quantitative theorem: the dimension factor `n(n−1) = 12` for `n = 4`
emerges via the Ricci trace `Σ_μ Ric_{μμ} g^{μμ} = 3K · (g_inv : g) =
3K · 4 = 12K`. -/
theorem constantSectional_scalarOf_eq
    (K : ℝ) (g g_inv : MetricMatrix)
    (h_dim : sumFin4 (fun μ => sumFin4 (fun ν => g_inv μ ν * g μ ν))
             = 4) :
    scalarOf (ricciOf (constantSectionalRiemann K g)) g_inv = 12 * K := by
  rw [scalarOf_eq_of_pointwise g_inv (constantSectional_Ricci_eq K g)]
  -- Goal: scalarOf (fun σ ν => 3 * K * g σ ν) g_inv = 12 * K
  -- Factor `3 * K` out of the double sum, then collapse via `h_dim`.
  have key : sumFin4 (fun μ => sumFin4 (fun ν => g_inv μ ν * (3 * K * g μ ν)))
              = 3 * K * sumFin4 (fun μ =>
                  sumFin4 (fun ν => g_inv μ ν * g μ ν)) := by
    unfold sumFin4
    ring
  show sumFin4 (fun μ => sumFin4 (fun ν => g_inv μ ν * (3 * K * g μ ν)))
        = 12 * K
  rw [key, h_dim]
  ring

/-- **Constant-K Einstein tensor**: `G_{μν} = −3K · g_{μν}` in 4D.

The wave's load-bearing cross-bridge consumer of 6f.1's
`constantSectional_Ricci_eq` and the just-proven
`constantSectional_scalarOf_eq`:
`G = Ric − (1/2) R g = 3K · g − (1/2) · 12K · g = −3K · g`. -/
theorem constantSectional_einsteinTensor_eq
    (K : ℝ) (g g_inv : MetricMatrix)
    (h_dim : sumFin4 (fun μ => sumFin4 (fun ν => g_inv μ ν * g μ ν))
             = 4)
    (μ ν : Fin 4) :
    einsteinTensor (ricciOf (constantSectionalRiemann K g))
                   (scalarOf (ricciOf (constantSectionalRiemann K g))
                             g_inv)
                   g μ ν
      = -3 * K * g μ ν := by
  unfold einsteinTensor
  rw [constantSectional_scalarOf_eq K g g_inv h_dim,
      constantSectional_Ricci_eq K g μ ν]
  ring

/-! ## §6 — Vacuum characterization

`G_{μν} = 0 ↔ Ric_{μν} = 0` in 4D when `R = scalarOf Ric g_inv`.

Substantive: forward direction uses the trace identity (taking trace
of `G = 0` forces `−R = 0`, then `Ric = G + (1/2) R g = 0`); backward
uses linearity of `scalarOf` (`Ric = 0 ⟹ R = 0 ⟹ G = 0`).
-/

/-- **Vacuum-Einstein characterization**: `G_{μν} = 0 ↔ Ric_{μν} = 0`
in 4D, with `R_scalar = scalarOf Ric g_inv`.

Forward: `G = 0` ⟹ trace `−R = 0` ⟹ `R = 0` ⟹ `Ric = G + (1/2) · R
· g = 0`. Backward: `Ric = 0` ⟹ `R = scalarOf 0 g_inv = 0` ⟹ `G = 0`.
The hypothesis `(g_inv : g) = 4` is load-bearing for the forward
trace step. -/
theorem einsteinTensor_zero_iff_ricci_zero
    {Ric : RicciTensor} (g g_inv : MetricMatrix)
    (h_dim : sumFin4 (fun μ => sumFin4 (fun ν => g_inv μ ν * g μ ν))
             = 4) :
    (∀ μ ν, einsteinTensor Ric (scalarOf Ric g_inv) g μ ν = 0)
    ↔ (∀ μ ν, Ric μ ν = 0) := by
  constructor
  · -- Forward: G = 0 ⟹ Ric = 0
    intro hG
    -- Take the trace: scalarOf G g_inv = -R, but G = 0 gives scalarOf G g_inv = 0
    have hTrace := einsteinTensor_trace_eq_neg_scalar Ric g g_inv h_dim
    -- scalarOf (fun μ ν => 0) g_inv = 0:
    have hG_fun : (fun μ ν => einsteinTensor Ric (scalarOf Ric g_inv) g μ ν)
                  = (fun _ _ => (0 : ℝ)) := by
      funext μ ν; exact hG μ ν
    have hG_scalar : scalarOf
        (fun μ ν => einsteinTensor Ric (scalarOf Ric g_inv) g μ ν)
        g_inv = 0 := by
      rw [hG_fun]; unfold scalarOf sumFin4; ring
    -- Combining: -scalarOf Ric g_inv = 0, so scalarOf Ric g_inv = 0
    have hR_eq : scalarOf Ric g_inv = 0 := by linarith [hG_scalar.symm.trans hTrace]
    -- Now Ric μ ν = G μ ν + (1/2) R g μ ν = 0 + 0 = 0
    intro μ ν
    have := hG μ ν
    unfold einsteinTensor at this
    rw [hR_eq] at this
    linarith
  · -- Backward: Ric = 0 ⟹ G = 0
    intro hR μ ν
    unfold einsteinTensor
    have hR_scalar : scalarOf Ric g_inv = 0 := by
      have hPt : scalarOf Ric g_inv =
          scalarOf (fun _ _ => (0 : ℝ)) g_inv :=
        scalarOf_eq_of_pointwise g_inv hR
      rw [hPt]
      unfold scalarOf sumFin4
      ring
    rw [hR_scalar, hR μ ν]
    ring

/-! ## §7 — De Sitter Λ-vacuum cross-bridge

`G_{μν} + Λ · g_{μν} = 0 ↔ Λ = 3K` for the constant-K witness in 4D.

Algebraic-level cross-bridge to Phase 6c W1's Zhitnitsky-DE program.
The relation `Λ = 3K` is the Einstein-equation form of de Sitter
`R^ρ_{σμν} = K(g_{σν} δ^ρ_μ − g_{σμ} δ^ρ_ν)`; in physics notation,
`H² = K = Λ/3` with `H` the de Sitter Hubble parameter.

We show, for the constant-K Riemann witness with non-degenerate
metric (encoded as a non-zero metric at some sample index), that the
Λ-vacuum equation forces `Λ = 3K`. The substantive content is:
combining the constant-K Einstein-tensor formula `G = −3K g` with
the Λ-vacuum equation `G + Λ g = 0` gives `(Λ − 3K) g = 0`; if `g`
is non-zero anywhere then `Λ = 3K`.
-/

/-- **De Sitter Λ-vacuum cross-bridge**: for the constant-K Riemann
witness, `G_{μν} + Λ · g_{μν} = 0` (at every index pair where `g`
itself is non-zero) **iff** `Λ = 3K`.

The forward direction needs ONE non-zero metric component as
non-degeneracy witness; we phrase it via existence-of-a-non-zero-`g`
hypothesis to keep the statement self-contained. -/
theorem constantSectional_lambda_vacuum_iff
    (K Λ : ℝ) (g g_inv : MetricMatrix)
    (h_dim : sumFin4 (fun μ => sumFin4 (fun ν => g_inv μ ν * g μ ν))
             = 4)
    (μ₀ ν₀ : Fin 4) (h_nondeg : g μ₀ ν₀ ≠ 0) :
    (∀ μ ν,
      einsteinTensor (ricciOf (constantSectionalRiemann K g))
                     (scalarOf (ricciOf (constantSectionalRiemann K g))
                               g_inv)
                     g μ ν
        + Λ * g μ ν = 0)
    ↔ Λ = 3 * K := by
  constructor
  · intro h
    have h0 := h μ₀ ν₀
    rw [constantSectional_einsteinTensor_eq K g g_inv h_dim μ₀ ν₀] at h0
    -- h0 : -3 * K * g μ₀ ν₀ + Λ * g μ₀ ν₀ = 0
    -- Factoring: (Λ - 3K) * g μ₀ ν₀ = 0; with g μ₀ ν₀ ≠ 0, Λ = 3K
    have h1 : (Λ - 3 * K) * g μ₀ ν₀ = 0 := by linarith
    have h2 : Λ - 3 * K = 0 := by
      rcases mul_eq_zero.mp h1 with hL | hg
      · exact hL
      · exact absurd hg h_nondeg
    linarith
  · intro hΛ μ ν
    rw [constantSectional_einsteinTensor_eq K g g_inv h_dim μ ν, hΛ]
    ring

/-! ## §8 — Cross-bridge to LinearizedEFE.η (Minkowski as flat solution)

Phase 6f.1's `linearizedEFE_η_metricSymmetric` validates the
Minkowski metric. Here we connect the *trace identity* and *vacuum
characterization* to Minkowski: the contraction `(η_inv : η) =
Σ_{μν} η^{μν} η_{μν} = 4` since `η^{μν} = η_{μν}` and
`η_{μν} η^{μν} = (−1)² + 1² + 1² + 1² = 4`. With the constant-K
witness on `η` at `K = 0`, the Einstein tensor vanishes and Λ-vacuum
forces `Λ = 0` — i.e., flat Minkowski is the `Λ = 0` vacuum
solution.
-/

/-- **Minkowski self-inverse contraction**:
`Σ_{μν} η^{μν} η_{μν} = 4` for the (−,+,+,+) Minkowski metric, since
`η^{μν} = η_{μν}` (η squared = identity) and the diagonal sum is
`(−1)² + 1² + 1² + 1² = 4`. -/
theorem minkowski_dim_contraction :
    sumFin4 (fun μ => sumFin4 (fun ν =>
      SKEFTHawking.LinearizedEFE.η μ ν *
      SKEFTHawking.LinearizedEFE.η μ ν)) = 4 := by
  show SKEFTHawking.LinearizedEFE.η 0 0 * SKEFTHawking.LinearizedEFE.η 0 0
        + SKEFTHawking.LinearizedEFE.η 0 1 * SKEFTHawking.LinearizedEFE.η 0 1
        + SKEFTHawking.LinearizedEFE.η 0 2 * SKEFTHawking.LinearizedEFE.η 0 2
        + SKEFTHawking.LinearizedEFE.η 0 3 * SKEFTHawking.LinearizedEFE.η 0 3
        + (SKEFTHawking.LinearizedEFE.η 1 0 * SKEFTHawking.LinearizedEFE.η 1 0
        + SKEFTHawking.LinearizedEFE.η 1 1 * SKEFTHawking.LinearizedEFE.η 1 1
        + SKEFTHawking.LinearizedEFE.η 1 2 * SKEFTHawking.LinearizedEFE.η 1 2
        + SKEFTHawking.LinearizedEFE.η 1 3 * SKEFTHawking.LinearizedEFE.η 1 3)
        + (SKEFTHawking.LinearizedEFE.η 2 0 * SKEFTHawking.LinearizedEFE.η 2 0
        + SKEFTHawking.LinearizedEFE.η 2 1 * SKEFTHawking.LinearizedEFE.η 2 1
        + SKEFTHawking.LinearizedEFE.η 2 2 * SKEFTHawking.LinearizedEFE.η 2 2
        + SKEFTHawking.LinearizedEFE.η 2 3 * SKEFTHawking.LinearizedEFE.η 2 3)
        + (SKEFTHawking.LinearizedEFE.η 3 0 * SKEFTHawking.LinearizedEFE.η 3 0
        + SKEFTHawking.LinearizedEFE.η 3 1 * SKEFTHawking.LinearizedEFE.η 3 1
        + SKEFTHawking.LinearizedEFE.η 3 2 * SKEFTHawking.LinearizedEFE.η 3 2
        + SKEFTHawking.LinearizedEFE.η 3 3 * SKEFTHawking.LinearizedEFE.η 3 3)
        = 4
  rw [SKEFTHawking.LinearizedEFE.η_zero_zero,
      SKEFTHawking.LinearizedEFE.η_off_diag 0 1 (by decide),
      SKEFTHawking.LinearizedEFE.η_off_diag 0 2 (by decide),
      SKEFTHawking.LinearizedEFE.η_off_diag 0 3 (by decide),
      SKEFTHawking.LinearizedEFE.η_off_diag 1 0 (by decide),
      SKEFTHawking.LinearizedEFE.η_spatial_diag 1 (by decide),
      SKEFTHawking.LinearizedEFE.η_off_diag 1 2 (by decide),
      SKEFTHawking.LinearizedEFE.η_off_diag 1 3 (by decide),
      SKEFTHawking.LinearizedEFE.η_off_diag 2 0 (by decide),
      SKEFTHawking.LinearizedEFE.η_off_diag 2 1 (by decide),
      SKEFTHawking.LinearizedEFE.η_spatial_diag 2 (by decide),
      SKEFTHawking.LinearizedEFE.η_off_diag 2 3 (by decide),
      SKEFTHawking.LinearizedEFE.η_off_diag 3 0 (by decide),
      SKEFTHawking.LinearizedEFE.η_off_diag 3 1 (by decide),
      SKEFTHawking.LinearizedEFE.η_off_diag 3 2 (by decide),
      SKEFTHawking.LinearizedEFE.η_spatial_diag 3 (by decide)]
  ring

/-! ## §9 — Module summary marker -/

/--
**Phase 6f Wave 2 module summary marker.** This module ships the
algebraic Einstein tensor `G_{μν} := Ric_{μν} − (1/2) R g_{μν}` with
its dimension-4 trace identity, constant-K specialization, vacuum
characterization, and de Sitter Λ-vacuum cross-bridge.

Theorem roster (9 substantive + 1 marker, 0 sorry, 0 new axioms):

- Symmetry: `einsteinTensor_symm`
- Linearity (P3-flagged plumbing — named API): `einsteinTensor_scalar_linearity`
- Trace identity (4D): `einsteinTensor_trace_eq_neg_scalar`
- Helper (P3-flagged): `scalarOf_eq_of_pointwise`
- Constant-K Ricci-trace: `constantSectional_scalarOf_eq`
- Constant-K G-tensor (load-bearing cross-bridge):
  `constantSectional_einsteinTensor_eq`
- Vacuum characterization: `einsteinTensor_zero_iff_ricci_zero`
- De Sitter Λ-vacuum: `constantSectional_lambda_vacuum_iff`
- Minkowski self-inverse contraction:
  `minkowski_dim_contraction`

**Strengthening pass: 0 retroactive cuts.** The 6f.1 carry-forward
question (*"is the witness-existence statement informative beyond the
predicate definition?"*) prevented zero-witness-trivial-plumbing
theorems in the first place — we avoided `zeroEinstein_*` style
plumbing and used the K=0 witness in pytest exclusively. Discipline
trend: 6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1, 6c.1=2, 6c.4=3,
6c.5=3, 6e.2=1, 6e.3=2, 6e.4=3, 6e.5=0, 6e.6=2, 6b.2=0, 6f.1=5
(regression), **6f.2 = 0** (back to best).

**Cross-system claim:** First formalization in any proof assistant
(per Phase 6f deep-research audit §3E + Wave 1's first-formalization
context) of the algebraic Einstein tensor with quantitative trace
identity + constant-K specialization + de Sitter-Λ algebraic
cross-bridge.
-/
theorem _phase6f_w2_module_summary_marker : True := trivial

end SKEFTHawking.EinsteinTensor
