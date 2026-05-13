/-
SK_EFT_Hawking Phase 6p Wave 2c.4c (2026-05-12): Aharonov-Arad Bridge
constructive content — the `LieSpanProp → bridge_exists` bridging lemma.

This module ships SUBSTANTIVE constructive content for the project's
`bridge_axiom_FKLW_general` elimination plan. It does NOT introduce any
new axioms (per Pipeline Invariant #15: "you are ELIMINATING an axiom, not
adding one"). What it ships is the axiom-free **bridging lemma** that the
substantive Bridge Lemma proof will consume.

**Substantive content (axiom-free)**:

  - **`LieSpan_implies_bridge_exists`** (Wave 2c.4c): at `d ≥ 2`, the strong
    `LieSpanProp` (full ℂ-linear-spanning of the d²-dim matrix space) forces
    the existence of at least one braid `w` whose image has a non-zero
    off-diagonal entry. This is the `bridge_exists` half of the natural
    Aharonov-Arad `BridgeHypothesis`. **Clean linear-algebra contradiction**:
    if every `ρ b` were diagonal, the ℂ-linear span of the image would be
    contained in the d-dim diagonal subspace, not the full d²-dim matrix
    space.

  - **`LieSpan_and_infiniteImage_imply_BridgeHypothesis`** (Wave 2c.4c):
    packages `LieSpanProp` + an externally supplied `image_infinite` witness
    into the natural `BridgeHypothesis`. The `image_infinite` half is NOT
    derivable from `LieSpanProp` alone (a finite set CAN ℂ-span a finite-dim
    space), so it must be supplied as a separate structural input. For the
    project's qutrit case the relevant infiniteness fact is provable from
    Burau-faithfulness type data (the existence of distinct braids with
    distinct images), which is established by direct construction in
    `FibonacciQutrit` (σ₁ ≠ σ₃, etc.).

**What is NOT shipped here (per Pipeline Invariant #15)**:

  - The substantive Bridge Lemma 4.1 + 6.1/6.2 iteration proof itself
    (the "BridgeHypothesis ⟹ ClosureDenseProp" direction) requires SU(d)
    compactness, path-connectedness, and a Lemma 6.2-style basis-rotation
    iteration. This is ~400-500 LoC of in-tree Mathlib-grade infrastructure
    plus the actual iteration proof. It is documented as the Wave 2c.4a.full
    follow-up.

  - The `image_infinite` derivation (would require Burau-type
    representation theory machinery not currently in Mathlib4).

  - The d = 0, d = 1 base cases (d = 0 is already constructive via
    `AharonovAradBridge.closureDenseProp_dim_zero`; d = 1 requires Kronecker-
    Weyl density on `Circle` for the cyclic subgroup `⟨ρ σ₀⟩`).

**Axiom inventory delta**: ZERO. This ship is purely additive: it adds an
axiom-free theorem (the bridging lemma) that downstream consumers can use
once the full Aharonov-Arad iteration discharge lands. The existing
`bridge_axiom_FKLW_general` (in `AharonovAradBridge.lean`) is retained
unchanged.

**Why this is the right scope for this session**: the full Bridge Lemma
proof requires substantial Mathlib4 infrastructure (SU(d) topology) that
is not buildable in a single session. The bridging lemma is the genuinely
tractable substantive piece; it eliminates the GAP between `LieSpanProp`
and `BridgeHypothesis` for the project's `d ≥ 2` use cases. Shipping it
axiom-free creates downstream-ready scaffolding without violating the
zero-new-axiom invariant.

Primary citation: Aharonov & Arad 2011, *New J. Phys.* 13 035019;
arXiv:quant-ph/0605181 §4 (Bridge Lemma 4.1) + §6 (Lemma 6.1, 6.2).
-/

import Mathlib
import SKEFTHawking.BraidGroup
import SKEFTHawking.FKLW.AharonovAradBridge

set_option autoImplicit false

namespace SKEFTHawking.FKLW.AharonovAradBridge

open scoped Matrix

/-! ## 1. The substantive bridging lemma (Wave 2c.4c)

This is the substantive content shipped here. The strong `LieSpanProp` says
every matrix is a finite ℂ-linear combination of ρ-values; we show that
this forces, for `d ≥ 2`, the existence of at least one braid `w` whose
image has a non-zero off-diagonal entry.

**Proof strategy**: By contradiction. Suppose every `ρ b` is diagonal (no
off-diagonal entries). Then every ℂ-linear combination of ρ-values is also
diagonal (the diagonal subspace is closed under ℂ-linear combinations).
But `LieSpanProp` requires every matrix — including the off-diagonal matrix
unit `E_{0,1}` (which has entry 1 at position (0,1) and 0 elsewhere) — to
be such a linear combination. The off-diagonal entry (0,1) of `E_{0,1}`
is 1, but the same entry of any ℂ-linear combination of diagonals is 0.
Contradiction: `1 = 0` in ℂ.
-/

/-- **Substantive bridging lemma (Wave 2c.4c)**: at `d ≥ 2`, the strong
`LieSpanProp` forces the existence of at least one braid whose image has
a non-zero off-diagonal entry.

This is the `bridge_exists` half of `BridgeHypothesis n d ρ`. The
`image_infinite` half is NOT derivable from `LieSpanProp` alone — see the
companion `LieSpan_and_infiniteImage_imply_BridgeHypothesis` for the
packaging convenience.

Axiom-free. Pure linear algebra. -/
theorem LieSpan_implies_bridge_exists
    (n d : ℕ) (h_d : 2 ≤ d)
    (ρ : BraidGroup n → Matrix (Fin d) (Fin d) ℂ)
    (h_span : LieSpanProp n d ρ) :
    ∃ (w : BraidGroup n) (i j : Fin d), i ≠ j ∧ ρ w i j ≠ 0 := by
  by_contra h_no_bridge
  push_neg at h_no_bridge
  -- `h_no_bridge : ∀ w i j, i ≠ j → ρ w i j = 0` (every image is diagonal)
  have h_zero_lt : (0 : ℕ) < d := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) h_d
  have h_one_lt : (1 : ℕ) < d := lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) h_d
  let i0 : Fin d := ⟨0, h_zero_lt⟩
  let i1 : Fin d := ⟨1, h_one_lt⟩
  have h_neq : i0 ≠ i1 := by
    intro h
    have hcv := congrArg Fin.val h
    simp [i0, i1] at hcv
  -- The off-diagonal matrix unit at (i0, i1).
  let E01 : Matrix (Fin d) (Fin d) ℂ := Matrix.single i0 i1 (1 : ℂ)
  obtain ⟨k, braids, coeffs, h_expr⟩ := h_span E01
  -- Evaluate at entry (i0, i1).
  have h_E01_val : E01 i0 i1 = 1 := by
    simp [E01, Matrix.single_apply_same]
  have h_rhs_zero : (∑ i, coeffs i • ρ (braids i)) i0 i1 = 0 := by
    rw [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    have h_ρ_zero : ρ (braids i) i0 i1 = 0 := h_no_bridge (braids i) i0 i1 h_neq
    simp [Matrix.smul_apply, h_ρ_zero]
  have h_one_eq_zero : (1 : ℂ) = 0 := by
    have h_eval : E01 i0 i1 = (∑ i, coeffs i • ρ (braids i)) i0 i1 := by
      rw [h_expr]
    rw [h_E01_val] at h_eval
    rw [h_eval, h_rhs_zero]
  exact one_ne_zero h_one_eq_zero

/-! ## 2. Packaging convenience: LieSpan + image_infinite ⟹ BridgeHypothesis

The bridging lemma above gives the `bridge_exists` half. For the
`image_infinite` half, we'd need a structural fact that `LieSpanProp` plus
the representation being non-scalar implies the image is infinite. **This
does NOT follow from `LieSpanProp` alone** — a finite set can ℂ-span a
finite-dim space (e.g., {I, σ₁, σ₂, σ₃} ℂ-spans the 4-dim 2×2-matrix
space). We supply `image_infinite` as an additional substantive hypothesis
on the representation. For the project's qutrit case, the witness comes
from the Burau-faithfulness fact `σ₁ ≠ σ₃` and the structure of distinct
braid words.
-/

/-- **Hypothesis-packaging convenience (Wave 2c.4c)**: given `LieSpanProp`
(which gives `bridge_exists` via the bridging lemma) plus a separate
`image_infinite` witness, package both into `BridgeHypothesis`.

This is the input shape that the Wave 2c.4a.full follow-up Bridge-Lemma
proof will consume.

Note: We do NOT claim `image_infinite` follows from `LieSpanProp` alone
(it doesn't — a finite set can ℂ-span a finite-dim space). The qutrit
project usage will supply both halves independently. -/
theorem LieSpan_and_infiniteImage_imply_BridgeHypothesis
    (n d : ℕ) (h_d : 2 ≤ d)
    (ρ : BraidGroup n → Matrix (Fin d) (Fin d) ℂ)
    (h_span : LieSpanProp n d ρ)
    (h_infinite : (Set.range ρ).Infinite) :
    BridgeHypothesis n d ρ :=
  { image_infinite := h_infinite
    bridge_exists := LieSpan_implies_bridge_exists n d h_d ρ h_span }

/-! ## 3. Witness extraction for the qutrit case (d = 3)

A concrete `BridgeHypothesis` witness for the n=3, d=3 qutrit case
requires both halves. The `bridge_exists` half follows from the bridging
lemma above once `LieSpanProp 3 3 ρ` is supplied. The `image_infinite`
half for the FibonacciQutrit representation is a substantive structural
fact established by Burau-faithfulness, which is a multi-wave follow-up
in itself. We document the packaging without re-deriving the
infinite-image witness here.
-/

/-! ## 4. Module summary

AharonovAradBridgeProof.lean (Wave 2c.4c ship, 2026-05-12):

  - **`LieSpan_implies_bridge_exists`** (substantive, axiom-free): at
    `d ≥ 2`, the strong `LieSpanProp` forces the existence of a braid
    with non-zero off-diagonal image entry. Clean linear-algebra
    contradiction via off-diagonal matrix unit `E_{0,1}`. ~25 LoC proof.

  - **`LieSpan_and_infiniteImage_imply_BridgeHypothesis`** (packaging):
    combines the bridging lemma with an externally supplied
    `image_infinite` witness to produce `BridgeHypothesis`.

**What this ship achieves**:

  - Closes the GAP between the strong `LieSpanProp` and the natural
    Aharonov-Arad `BridgeHypothesis` (modulo the separately-supplied
    `image_infinite` witness). When the full Bridge Lemma iteration
    discharge lands, this bridging lemma will be the load-bearing
    connector between the project's `LieSpanProp`-based usages and the
    (then-constructive) `BridgeHypothesis → ClosureDenseProp` direction.

  - Establishes Pipeline Invariant #15 compliance for this wave (ZERO
    new axioms shipped).

  - The d=3 qutrit case is currently NOT discharged constructively (the
    `image_infinite` witness is not derivable from `su3_spanning_data`
    alone, and the Bridge Lemma iteration proof is the gating work).
    This ship correctly identifies and documents this gap rather than
    papering over it with new axioms.

**Honest status assessment**:

  - **The `bridge_axiom_FKLW_general` axiom is NOT eliminated by this
    ship** — the substantive analytic content (Bridge Lemma 4.1 iteration
    + SU(d) topology) remains for a future wave.

  - **Substantive progress**: ~30 LoC of axiom-free linear-algebra content
    that downstream Aharonov-Arad iteration proofs can build on.

  - **Why not more in one session**: the full Aharonov-Arad iteration
    proof requires (a) `IsCompact (Matrix.specialUnitaryGroup (Fin d) ℂ)`
    (~80 LoC in-tree, since Mathlib has the group definition but no
    compactness instance), (b) `PathConnectedSpace` on the same (~120 LoC,
    via spectral decomposition), (c) the iteration proof itself with
    Lemma 6.1 vector transport + Lemma 6.2 basis-rotation (~200 LoC).
    Total: ~400 LoC of substantive new content. Pursuing this is the
    Wave 2c.4a.full follow-up.

**Wave 2c.4a.full follow-up scope (deferred)**:

  - SU(d) `IsCompact` instance in-tree (~80 LoC).
  - SU(d) `PathConnectedSpace` instance in-tree (~120 LoC).
  - Bridge Lemma 4.1 + 6.1 + 6.2 iteration proof (~200 LoC).
  - d=1 case via Kronecker-Weyl on `Circle` (~120 LoC, if pursuing the
    full discharge rather than admitting d=1 as a separate weaker axiom).

Primary citation: Aharonov & Arad 2011, *New J. Phys.* 13 035019;
arXiv:quant-ph/0605181 §4 (Bridge Lemma 4.1) + §6 (Lemma 6.1 + 6.2 proofs).

Zero sorry. Zero new project-local axioms (the existing
`bridge_axiom_FKLW_general` in `AharonovAradBridge.lean` is unchanged).
-/

end SKEFTHawking.FKLW.AharonovAradBridge
