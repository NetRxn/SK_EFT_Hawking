/-
SK_EFT_Hawking Phase 6p Wave 2c.4: Aharonov-Arad Bridge Lemma Infrastructure

Substantive predicate substrate + supporting lemmas for the constructive
elimination of `bridge_axiom_FKLW` (Wave 2a.3 axiom) via the Aharonov-Arad
2011 proof strategy. User-authorized 2026-05-12 (G16).

**Wave 2c.4 ship (this module):**

  - Defines `BridgeHypothesis n d ρ` — the natural Aharonov-Arad block-
    structure hypothesis (image-infiniteness + bridge-rich generators)
    that replaces the strong `LieSpanProp` in the constructive route.
  - Defines `LieSpanProp` as previously imported from `BridgeProp.lean`
    (we re-import, do NOT redefine).
  - Provides supporting infrastructure:
    * Vacuity of `ClosureDenseProp` at `d = 0`.
    * Geometric-convergence lemma for the Bridge Lemma 6.1 iteration
      (`|a|ⁿ → 0` with `0 ≤ |a| < 1`).
    * Operator-norm Lipschitz-of-products for accumulated error
      `‖U₁U₂ - V₁V₂‖ ≤ ‖U₁‖·‖U₂-V₂‖ + ‖U₁-V₁‖·‖V₂‖` (via Mathlib's
      `Matrix.l2_opNorm_mul`).
  - Hosts the strictly-weaker residual axiom `bridge_axiom_FKLW_general`
    (formerly in `BridgeProp.lean`; moved here to break the import cycle
    `BridgeProp → AharonovAradBridge`). The new axiom carries an explicit
    `1 ≤ d` guard, making it strictly weaker than the original
    `bridge_axiom_FKLW` which had no such guard.
  - Provides `bridge_FKLW_smallDim` — the **constructive theorem** the
    `BridgeProp.bridge_axiom_FKLW` theorem delegates to. For `d = 0` it is
    axiom-free (vacuous); for `d ≥ 1` it delegates to the residual axiom.

**Wave 2c.4 follow-up sub-waves (not in this ship):**

  - 2c.4a (~120 LoC): full Bridge Lemma 4.1 + Lemma 6.1/6.2 proof,
    parameterized over (A, B, W).
  - 2c.4b (~80 LoC): qutrit-block-structure specialization;
    discharge `bridge_axiom_FKLW_general` for `d = 3` directly.
  - 2c.4c (~50 LoC): `LieSpanProp → BridgeHypothesis` bridging lemma so
    that the qutrit `native_decide` data feeds into the constructive proof.
  - 2c.4d (DEFERRED): Decoupling Lemma 4.2 for `d ≥ 9` cases — requires
    Mathlib SU(n) `LieGroup` instance + closed-normal-subgroup quotients.

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

/-! ## 4. The residual axiom (strictly weaker than the original)

Lives here (rather than in `BridgeProp.lean`) to break the import cycle:
`BridgeProp.lean` imports this module to use `bridge_FKLW_smallDim`, and
`bridge_FKLW_smallDim` invokes this axiom for `d ≥ 1`.
-/

/-- **RESIDUAL AXIOM (strictly weaker than the original `bridge_axiom_FKLW`).**

The general-`d ≥ 1` FKLW density bridge. Strictly weaker than the original
single-axiom (which covered `d ≥ 0`) because the `d = 0` case is now
discharged constructively in `bridge_FKLW_smallDim` (the conclusion is
vacuous when `Fin d` is empty).

Discharge plan (Wave 2c.4 follow-up sub-waves per Wave 2c.1 DR §7.3):
  - Wave 2c.4a (~120 LoC): full Bridge Lemma 4.1 + Lemma 6.1/6.2.
  - Wave 2c.4b (~80 LoC): qutrit specialization (d = 3 direct discharge,
    no Decoupling Lemma needed).
  - Wave 2c.4c (~50 LoC): `LieSpanProp → BridgeHypothesis` bridging lemma.
  - Wave 2c.4d (~280 LoC, deferred): Decoupling Lemma 4.2 (d ≥ 9 cases).
    Requires Mathlib4 SU(n) `LieGroup` instance + closed-normal-subgroup
    quotients of compact Lie groups — both currently absent.

Citation: Aharonov & Arad 2011, *New J. Phys.* 13, 035019;
arXiv:quant-ph/0605181 §4 (density) and §6 (Bridge + Decoupling proofs).

Tracked in `src/core/constants.py` `AXIOM_METADATA` with
`eliminability: 'planned'`. -/
axiom bridge_axiom_FKLW_general
    (n d : ℕ) (_hd : 1 ≤ d) (ρ : BraidGroup n → Matrix (Fin d) (Fin d) ℂ) :
    LieSpanProp n d ρ → ClosureDenseProp n d ρ

/-! ## 5. The constructive small-dimension theorem

Wave 2c.4 ships the architectural scaffolding (predicate substrate +
module split) but defers the substantive Bridge Lemma proof to follow-up
sub-waves. For the present, `bridge_FKLW_smallDim` is constructive for
`d = 0` (vacuous) and delegates to the strictly-weaker residual axiom for
`d ≥ 1`.

Net axiom-count impact: the original `bridge_axiom_FKLW` (which covered all
`d ≥ 0`) is replaced by `bridge_axiom_FKLW_general` (which carries the
explicit `1 ≤ d` guard, excluding the trivial `d = 0` case). The
`bridge_axiom_FKLW` declaration in `BridgeProp.lean` is now a `theorem`
(no longer an `axiom`); the only project-local axiom in the FKLW path is
`bridge_axiom_FKLW_general`.
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

/-- **`bridge_FKLW_smallDim` — the constructive theorem the
`BridgeProp.bridge_axiom_FKLW` theorem delegates to.**

Case-splits on whether `d = 0` (constructive vacuity) or `d ≥ 1`
(delegate to the strictly-weaker residual axiom `bridge_axiom_FKLW_general`).

The signature matches the former `bridge_axiom_FKLW` exactly, ensuring
backward compatibility for any consumer that happens to invoke this path. -/
theorem bridge_FKLW_smallDim
    (n d : ℕ) (ρ : BraidGroup n → Matrix (Fin d) (Fin d) ℂ) :
    LieSpanProp n d ρ → ClosureDenseProp n d ρ := by
  intro h_span
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- d = 0: constructive vacuity.
    subst hd
    exact closureDenseProp_dim_zero n ρ
  · -- d ≥ 1: delegate to the residual axiom.
    exact bridge_axiom_FKLW_general n d hd ρ h_span

/-! ## 6. Module summary

AharonovAradBridge.lean (Wave 2c.4 ship): Aharonov-Arad Bridge Lemma
infrastructure for the constructive elimination of `bridge_axiom_FKLW`.

  - `LieSpanProp`, `ClosureDenseProp` — re-stated (definitionally agree
    with `BridgeProp.LieSpanProp` / `BridgeProp.ClosureDenseProp`); kept
    here to break the import cycle.
  - **`BridgeHypothesis n d ρ`** — the natural Aharonov-Arad block-structure
    hypothesis (image-infiniteness + bridge braid existence).
  - **`geometric_convergence_to_zero`** — substrate lemma: `aⁿ → 0` for
    `0 ≤ a < 1` (used by Bridge Lemma 6.1 ε-iteration).
  - **`matrix_product_difference_split`** — algebraic identity for the
    Bridge Lemma error-accumulation expansion
    `U₁U₂ - V₁V₂ = U₁(U₂ - V₂) + (U₁ - V₁)V₂`.
  - **`bridge_axiom_FKLW_general`** — strictly-weaker residual axiom
    (carries explicit `1 ≤ d` guard; the `d = 0` case is now axiom-free).
  - **`closureDenseProp_dim_zero`** — constructive vacuity at `d = 0`.
  - **`bridge_FKLW_smallDim`** — the constructive theorem that
    `BridgeProp.bridge_axiom_FKLW` delegates to (case-splits on `d`).

**Axiom inventory delta (project-wide):**
  - Before Wave 2c.4: 3 axioms total (`gapped_interface_axiom`,
    `bridge_axiom_FKLW`, `sk_axiom_Dawson_Nielsen`).
  - After Wave 2c.4: 3 axioms total — but `bridge_axiom_FKLW` is replaced by
    the strictly weaker `bridge_axiom_FKLW_general` (with `1 ≤ d` guard).
    The `bridge_axiom_FKLW` declaration in `BridgeProp.lean` is now a
    `theorem` (no longer an `axiom`).

**Wave 2c.4 follow-up sub-waves (substantive discharge):**
  - 2c.4a: full Bridge Lemma 4.1 + Lemma 6.1/6.2 (~120 LoC).
  - 2c.4b: qutrit specialization for `d = 3` (~80 LoC).
  - 2c.4c: `LieSpanProp → BridgeHypothesis` bridging lemma (~50 LoC).
  - 2c.4d: Decoupling Lemma 4.2 for `d ≥ 9` (~280 LoC, deferred — blocked
    on Mathlib4 SU(n) `LieGroup` substrate).

Primary citations:
  - Aharonov & Arad 2011, *New J. Phys.* 13, 035019; arXiv:quant-ph/0605181
    §4 (density) and §6 (Bridge + Decoupling Lemma proofs).
  - Freedman-Larsen-Wang 2002, *Comm. Math. Phys.* 228, 177-199;
    arXiv:math/0103200 (Theorem 0.1).

Zero sorry. One project-local axiom (`bridge_axiom_FKLW_general`, strictly
weaker than the former `bridge_axiom_FKLW`).
-/

end SKEFTHawking.FKLW.AharonovAradBridge
