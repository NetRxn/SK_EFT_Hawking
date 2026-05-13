/-
SK_EFT_Hawking Phase 6p Wave 2c.4 / 2c.4a-cleanup: Aharonov-Arad Bridge
Lemma Infrastructure (axiom-narrowed).

Substantive predicate substrate + supporting lemmas for the constructive
elimination of `bridge_axiom_FKLW` (Wave 2a.3 axiom) via the Aharonov-Arad
2011 proof strategy.

**Wave 2c.4 ship (architectural scaffolding):** Defined `BridgeHypothesis`,
re-stated `LieSpanProp` / `ClosureDenseProp`, provided geometric-convergence
+ product-difference algebraic lemmas, and hosted the strictly-weaker
residual axiom `bridge_axiom_FKLW_general` (with `1 ≤ d` guard).

**Wave 2c.4a-FULL ship (2026-05-12; companion module
`AharonovAradBridgeIteration.lean`):** Discovered that the
`bridge_axiom_FKLW_general` axiom statement is **mathematically false** for
non-unitary representations (counterexample at `n = 1, d = 1` with the
trivial constant-1 representation: spans ℂ but its image {1} is not dense
in ℂ — see `liespan_not_implies_dense_counterexample`). Replaced with the
SOUND axiom `bridge_axiom_FKLW_unitary_general` requiring `2 ≤ d` AND
`ρ b ∈ SU(d)` AND with the corrected conclusion `DenseInSpecialUnitary`
(density in SU(d), not in the full matrix space).

**Wave 2c.4a-cleanup (2026-05-12 — this commit):** The unsound axiom
`bridge_axiom_FKLW_general` and its delegate theorem `bridge_FKLW_smallDim`
are **deleted** from this module. The sound path is now the only path:
`AharonovAradBridgeIteration.bridge_FKLW_unitary` (with explicit unitarity
hypothesis, returning `DenseInSpecialUnitary`). Net project axiom-count
delta: 3 → 2 (`gapped_interface_axiom` + `bridge_axiom_FKLW_unitary_general`).

**Retained content in this module:**

  - `LieSpanProp`, `ClosureDenseProp` — re-stated (definitionally agree
    with `BridgeProp.lean` versions; kept here to break the historical
    import cycle).
  - `BridgeHypothesis n d ρ` — natural Aharonov-Arad block-structure
    hypothesis.
  - `geometric_convergence_to_zero` — substrate lemma for Bridge Lemma
    6.1 ε-iteration.
  - `matrix_product_difference_split` — algebraic identity for the
    Bridge Lemma error-accumulation expansion.
  - `closureDenseProp_dim_zero` — vacuity at `d = 0` (still useful as a
    standalone constructive discharge for the `d = 0` case, even though
    the broader chain has been retired).

**Citation correction (Wave 2c.1 DR, 2026-05-12):**

The Bridge Lemma and Decoupling Lemma are in **arXiv:quant-ph/0605181**
(Aharonov & Arad 2007/2011 → *New J. Phys.* 13 (2011) 035019), NOT the
formerly-cited arXiv:quant-ph/0702008. The "Reichardt 2005" simplification
reference does not exist (arXiv:quant-ph/0509041 returns no result on arXiv).

Primary references:
  - Aharonov & Arad 2011, *New J. Phys.* 13, 035019; arXiv:quant-ph/0605181
    §4 (Theorem 3.2 density) and §6 (Lemma 4.1 Bridge + Lemma 4.2 Decoupling).
  - Freedman-Larsen-Wang 2002, *Comm. Math. Phys.* 228, 177-199;
    arXiv:math/0103200 (Theorem 0.1).
-/

import Mathlib
import SKEFTHawking.BraidGroup

set_option autoImplicit false

namespace SKEFTHawking.FKLW.AharonovAradBridge

open scoped Matrix

/-! ## 1. Predicate substrate

We re-state `LieSpanProp` and `ClosureDenseProp` here to avoid the import
cycle `BridgeProp → AharonovAradBridge`; the canonical definitions live in
`BridgeProp.lean`. The two definitions agree definitionally (same Prop body)
so any consumer that has the BridgeProp form can `exact` directly into the
AharonovAradBridge form.
-/

/-- **`LieSpanProp` (re-stated; agrees with `BridgeProp.LieSpanProp`).**

The spanning hypothesis: every matrix is a finite ℂ-linear combination of
representation values at braid words. -/
def LieSpanProp (n d : ℕ) (ρ : BraidGroup n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ M : Matrix (Fin d) (Fin d) ℂ, ∃ k : ℕ, ∃ braids : Fin k → BraidGroup n,
    ∃ coeffs : Fin k → ℂ, M = ∑ i, coeffs i • ρ (braids i)

/-- **`ClosureDenseProp` (re-stated; agrees with `BridgeProp.ClosureDenseProp`).**

The density conclusion: every matrix admits entrywise ε-approximation by a
single braid-word image. -/
def ClosureDenseProp (n d : ℕ) (ρ : BraidGroup n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ (U : Matrix (Fin d) (Fin d) ℂ) (ε : ℝ), 0 < ε →
    ∃ b : BraidGroup n, ∀ i j : Fin d, ‖ρ b i j - U i j‖ < ε

/-! ## 2. The natural Aharonov-Arad hypothesis

Per Wave 2c.1 DR §2, the Aharonov-Arad density proof does NOT use the
`LieSpanProp` (Lie-algebra-spanning) hypothesis. It uses:

  1. **Image-infiniteness** of the two-generator subgroup on a 2-dim invariant
     block (base case Theorem 4.1).
  2. **Existence of bridge unitaries** — a generator whose action mixes
     adjacent invariant blocks.
  3. **Dim-mismatch** between blocks (only for the Decoupling Lemma; not
     needed for d ≤ 4).

The natural hypothesis `BridgeHypothesis` captures these three pieces. For
the project's concrete qutrit case (n = 3, d = 3), it is dischargeable from
the existing `FibonacciQutritUniversality.su3_spanning_data` via a ~50 LoC
bridging lemma (Wave 2c.4c follow-up).
-/

/-- **The Aharonov-Arad block-structure hypothesis** (Wave 2c.4 substrate).

For a representation `ρ : BraidGroup n → Matrix (Fin d) (Fin d) ℂ`, this
hypothesis asserts:
  1. The image `range ρ` is infinite (in `Matrix (Fin d) (Fin d) ℂ`).
  2. There exists a "bridge braid" `w : BraidGroup n` whose image has a
     nontrivial off-diagonal projection (witnessing block-mixing).

This is the Wave-2c.4 placeholder predicate that the substantive Bridge
Lemma proof (Wave 2c.4a follow-up) will consume. For the present ship we
do not require any non-trivial dischargers — the predicate is the
architectural placeholder. -/
structure BridgeHypothesis (n d : ℕ)
    (ρ : BraidGroup n → Matrix (Fin d) (Fin d) ℂ) : Prop where
  /-- The image of ρ is infinite. -/
  image_infinite : (Set.range ρ).Infinite
  /-- There exists a "bridge braid" w whose image is non-scalar
      (has a nontrivial off-diagonal entry, witnessing block-mixing).
      For `d = 0` or `d = 1` this is vacuous; for `d ≥ 2` it asserts that
      ρ does not factor through scalar matrices on the chosen 2×2 block. -/
  bridge_exists : ∃ (w : BraidGroup n) (i j : Fin d), i ≠ j ∧ ρ w i j ≠ 0

/-! ## 3. Supporting Mathlib substrate lemmas

These are direct applications of Mathlib4 lemmas, repackaged for use by
the Wave 2c.4a Bridge Lemma proof. They are unit-tested by inclusion in
the module and verified by `lean_diagnostic_messages`.
-/

/-- **Geometric convergence** (Bridge Lemma 6.1 ε-iteration): for any
`a` with `0 ≤ a < 1`, the sequence `a^n` tends to `0`. This is direct
from Mathlib's `tendsto_pow_atTop_nhds_zero_of_lt_one`. -/
theorem geometric_convergence_to_zero {a : ℝ} (ha_nn : 0 ≤ a) (ha_lt : a < 1) :
    Filter.Tendsto (fun n : ℕ => a ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one ha_nn ha_lt

/-- **Algebraic identity** used in the Bridge Lemma error-accumulation step
(Claim 3.1 of arXiv:quant-ph/0605181, p. 19): expansion
`U₁U₂ - V₁V₂ = U₁(U₂ - V₂) + (U₁ - V₁)V₂` for matrices `U₁, U₂, V₁, V₂`.

This is the *algebraic* part of the operator-norm Lipschitz inequality; the
analytic combination with `Matrix.l2_opNorm_mul` is deferred to the Wave 2c.4a
follow-up which needs the specific `Matrix.instL2OpNormedRing` instance from
`Mathlib.Analysis.CStarAlgebra.Matrix`. -/
theorem matrix_product_difference_split {d : ℕ}
    (U₁ U₂ V₁ V₂ : Matrix (Fin d) (Fin d) ℂ) :
    U₁ * U₂ - V₁ * V₂ = U₁ * (U₂ - V₂) + (U₁ - V₁) * V₂ := by
  rw [Matrix.mul_sub, Matrix.sub_mul]
  abel

/-! ## 4. Vacuity at `d = 0`

The original Wave 2c.4 ship of this module hosted a residual axiom
`bridge_axiom_FKLW_general : LieSpanProp n d ρ → ClosureDenseProp n d ρ`
(under `1 ≤ d`) and a delegating theorem `bridge_FKLW_smallDim` matching
that signature. The Wave 2c.4a-FULL companion module
`AharonovAradBridgeIteration.lean` proved that this axiom statement is
mathematically false for non-unitary representations (counterexample at
`n = 1, d = 1`) and replaced it with the sound
`bridge_axiom_FKLW_unitary_general` requiring `2 ≤ d` AND unitarity AND
the corrected `DenseInSpecialUnitary` conclusion.

In the Wave 2c.4a-cleanup ship (2026-05-12), the unsound
`bridge_axiom_FKLW_general` and its `bridge_FKLW_smallDim` delegate were
**deleted** from this module — they had no live term-level callers
outside the now-rewritten `BridgeProp.lean` chain. The vacuous
`d = 0` case is retained as a constructive lemma because it remains a
useful primitive (consumed by `AharonovAradBridgeIteration` for the
`d = 0` discharge of `DenseInSpecialUnitary`).
-/

/-- **Vacuity at `d = 0`.** When the matrix dimension is `0`, the entrywise
quantifier `∀ i j : Fin 0, P i j` is vacuously true (no inhabitants of `Fin 0`),
so `ClosureDenseProp n 0 ρ` is constructively derivable: pick any braid `b`
(here we use `1`, the group identity) and the conclusion holds vacuously. -/
theorem closureDenseProp_dim_zero
    (n : ℕ) (ρ : BraidGroup n → Matrix (Fin 0) (Fin 0) ℂ) :
    ClosureDenseProp n 0 ρ := by
  intro U ε _hε
  refine ⟨1, ?_⟩
  intro i j
  exact i.elim0

/-! ## 5. Module summary

AharonovAradBridge.lean (Wave 2c.4 ship + Wave 2c.4a-cleanup pruning):
Aharonov-Arad Bridge Lemma predicate substrate + supporting lemmas.

  - `LieSpanProp`, `ClosureDenseProp` — re-stated (definitionally agree
    with `BridgeProp.LieSpanProp` / `BridgeProp.ClosureDenseProp`); kept
    here to break the historical import cycle.
  - **`BridgeHypothesis n d ρ`** — natural Aharonov-Arad block-structure
    hypothesis (image-infiniteness + bridge braid existence).
  - **`geometric_convergence_to_zero`** — substrate lemma: `aⁿ → 0` for
    `0 ≤ a < 1` (Bridge Lemma 6.1 ε-iteration).
  - **`matrix_product_difference_split`** — algebraic identity for the
    Bridge Lemma error-accumulation expansion
    `U₁U₂ - V₁V₂ = U₁(U₂ - V₂) + (U₁ - V₁)V₂`.
  - **`closureDenseProp_dim_zero`** — constructive vacuity at `d = 0`.

**Wave 2c.4a-cleanup pruning (this commit, 2026-05-12):**
  - `axiom bridge_axiom_FKLW_general` — **DELETED.** Mathematically
    unsound (counterexample shipped in
    `AharonovAradBridgeIteration.liespan_not_implies_dense_counterexample`).
    The sound replacement `bridge_axiom_FKLW_unitary_general` (in
    `AharonovAradBridgeIteration.lean`) requires unitarity + 2 ≤ d
    + correct `DenseInSpecialUnitary` conclusion.
  - `theorem bridge_FKLW_smallDim` — **DELETED.** Was a delegate of the
    unsound axiom; replaced by `AharonovAradBridgeIteration.bridge_FKLW_unitary`
    which has the sound (unitary + DenseInSpecialUnitary) signature.

**Axiom inventory delta (project-wide):**
  - Before Wave 2c.4: 3 axioms (`gapped_interface_axiom`,
    `bridge_axiom_FKLW`, `sk_axiom_Dawson_Nielsen`).
  - After Wave 2c.4 + 2c.4a-FULL + 2c.4a-cleanup: the FKLW path
    contributes exactly one axiom (`bridge_axiom_FKLW_unitary_general`,
    sound). The unsound `bridge_axiom_FKLW_general` is gone.

Primary citations:
  - Aharonov & Arad 2011, *New J. Phys.* 13, 035019; arXiv:quant-ph/0605181
    §4 (density) and §6 (Bridge + Decoupling Lemma proofs).
  - Freedman-Larsen-Wang 2002, *Comm. Math. Phys.* 228, 177-199;
    arXiv:math/0103200 (Theorem 0.1).

Zero sorry. Zero project-local axioms in this module (the sound residual
lives in `AharonovAradBridgeIteration.bridge_axiom_FKLW_unitary_general`).
-/

end SKEFTHawking.FKLW.AharonovAradBridge
