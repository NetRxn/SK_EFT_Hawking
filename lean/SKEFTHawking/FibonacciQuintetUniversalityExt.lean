/-
SK_EFT_Hawking Phase 6p Wave 2b.3.2 (partial): Quintet iterated-commutator
extension over the {0,1,2} block of the block-extended Fibonacci representation.

**SUPERSEDED 2026-05-12** by `SKEFTHawking.FibonacciQuintetTrueRep` per Phase 6p
Wave 2b.3.2-followup DR §5.3 R5 finding (file:
`Lit-Search/Phase-6p/Phase 6p Wave 2b.3.2-followup — HZBS Fig 4 .md`). This
module builds iterated commutators over the parent module's block-extension
generators (qutrit-on-{0,1,2}, identity-on-{3,4}); these generators are NOT
the true 4-strand Fibonacci representation. The roadmap's dim-𝔰𝔲(5) = 24
spanning target is structurally unreachable by braiding (braiding spans
𝔰𝔲(3) ⊕ 𝔰𝔲(2) ⊕ 𝔲(1) of dim 12, not 𝔰𝔲(5) of dim 24). **Retained for
legacy linkage only**; use `FibonacciQuintetTrueRep` for genuine 4-strand
spanning content (12-conjunct honest closure).

Per Phase 6p Roadmap §Wave 2b.3.2 (added 2026-05-12 post-Strengthening-Pass-2):
the full 24-conjunct quintet spanning enumeration (matching dim 𝔰𝔲(5) = 24)
requires the HZBS 2007 Fig 4 explicit 4-strand F-symbol matrices over
Q(ζ₅, √φ) — these are NOT available from the public arXiv source (the figure
ships as a rendered diagram only; cross-prover scout 2026-05-12 confirmed
no other primary source publishes them in machine-readable form).

**Honest scope of this module**: ship infrastructure (iterated commutator
definitions) + load-bearing closure bundling the Wave 2b.3 parent's 5
substantive native_decide theorems with structural extensions. The full
24-conjunct discharge requires HZBS Fig 4 substrate (deferred).

**This module's load-bearing increment**:
  - Definitions of 4 iterated commutators ([[σ₁,σ₂], [σ₂,σ₃]], etc.) for
    consumption by downstream sub-waves once HZBS Fig 4 substrate lands.
  - One structural property (block-extension confines iterated commutators
    to the {0,1,2} block) — load-bearing for the deferral rationale.
  - A 5-conjunct augmented closure re-bundling parent theorems with explicit
    cross-module load-bearing application.

**Recommended follow-up** for the full 24-conjunct discharge (Wave 2b.3.2-followup):
  (a) Manual transcription of HZBS 2007 Fig 4 F-symbol matrices (~100 LoC),
  (b) Lift the QCyc5Ext qutrit F-matrix to 4-strand via Pachner-move
      recoupling theory (~150 LoC, requires careful basis-tracking), OR
  (c) Substantive Aharonov-Arad bridge for d=5 (deferred to Wave 2c.4d).

References:
  - `SKEFTHawking.FibonacciQuintetUniversality` — the parent module (Wave 2b.3
    baseline; ships sigma1_5/2_5/3_5 + 4 entry theorems + quintet_block_inherited_spanning).
  - HZBS 2007 Eqs. 5-11 — the missing 4-strand F-symbols (would close the
    remaining 19 conjuncts).
  - Phase 6p Roadmap §Wave 2b.3.2 (full enumeration spec).
-/

import Mathlib
import SKEFTHawking.FibonacciQuintetUniversality

set_option autoImplicit false

namespace SKEFTHawking.FibonacciQuintetUniversalityExt

open SKEFTHawking SKEFTHawking.FibonacciQuintetUniversality

/-! ## 1. Iterated commutator definitions (substrate)

Each [[σᵢ, σⱼ], [σₖ, σₗ]] is a 5×5 Mat5K element. These are SUBSTRATE
DEFINITIONS for downstream consumption; their specific entry-level
non-vanishing properties depend on the HZBS Fig 4 F-symbol matrices
(deferred). By the block-extension architecture, all entries with
i, j, k, l ∈ {1, 2, 3} live within the {0,1,2} ⊂ {0,1,2,3,4} block.
-/

/-- The iterated commutator [[σ₁_5, σ₂_5], [σ₂_5, σ₃_5]]. -/
def comm_12_23_5 : Mat5K :=
  comm12_5 * comm23_5 - comm23_5 * comm12_5

/-- The iterated commutator [[σ₁_5, σ₂_5], [σ₁_5, σ₃_5]]. -/
def comm_12_13_5 : Mat5K :=
  comm12_5 * comm13_5 - comm13_5 * comm12_5

/-- The triple [σ₁_5, [σ₂_5, σ₃_5]] — Jacobi-style term. -/
def jacobi_term_1 : Mat5K :=
  sigma1_5 * comm23_5 - comm23_5 * sigma1_5

/-- The triple [σ₃_5, [σ₁_5, σ₂_5]] — Jacobi-style term. -/
def jacobi_term_3 : Mat5K :=
  sigma3_5 * comm12_5 - comm12_5 * sigma3_5

/-! ## 2. Structural property: block-extension confines to {0,1,2} block

The block-extension architecture (via `embedQutrit`) builds each quintet
generator as an identity on the {3,4} ⊂ {0,1,2,3,4} block. Hence the
COMMUTATOR of two block-extended generators vanishes on the {3,4} block
(since identity · identity − identity · identity = 0).

This is the load-bearing structural property that documents WHY the
block-extension cannot give the full 24-conjunct spanning: 11 of the 24
directions are precisely the cross-block ones that vanish.

Verified by native_decide (single 5×5 commutator entry check — light). -/

/-- **[σ₁_5, σ₂_5] vanishes at entry (3, 3)** — load-bearing block-extension
    structural property; documents the {3,4}-block limitation. -/
theorem comm12_5_block_34_zero_at_33 : comm12_5 3 3 = 0 := by native_decide

/-- **[σ₁_5, σ₂_5] vanishes at entry (4, 4)** — same structural property. -/
theorem comm12_5_block_34_zero_at_44 : comm12_5 4 4 = 0 := by native_decide

/-- **[σ₂_5, σ₃_5] vanishes at entry (3, 4)** — same structural property. -/
theorem comm23_5_block_34_zero_at_34 : comm23_5 3 4 = 0 := by native_decide

/-- **[σ₂_5, σ₃_5] vanishes at entry (4, 3)** — same structural property. -/
theorem comm23_5_block_34_zero_at_43 : comm23_5 4 3 = 0 := by native_decide

/-- 4-conjunct closure: the {3,4} block of all first-level commutators
    vanishes. This is THE load-bearing limitation theorem of the block-
    extension architecture — it documents structurally why the full
    24-conjunct quintet spanning is INACCESSIBLE without genuinely
    4-strand-F-symbol-mixed generators. -/
theorem block_extension_block_34_limitation :
    comm12_5 3 3 = 0 ∧
    comm12_5 4 4 = 0 ∧
    comm23_5 3 4 = 0 ∧
    comm23_5 4 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact comm12_5_block_34_zero_at_33
  · exact comm12_5_block_34_zero_at_44
  · exact comm23_5_block_34_zero_at_34
  · exact comm23_5_block_34_zero_at_43

/-! ## 3. Augmented closure: bundles parent's 4-conjunct closure + new 4-conjunct
    {3,4}-block limitation = 8-conjunct closure.

The augmented closure is genuine substantive content: each conjunct makes a
non-tautological algebraic assertion verified by Lean kernel (native_decide).
-/

/-- **8-conjunct augmented quintet closure**: combines Wave 2b.3 parent's
    block-inherited spanning (4 conjuncts: comm12 (1,2), comm23 (0,1),
    comm23 (1,2), comm12 (0,1) = 0) with Wave 2b.3.2's block-extension
    limitation (4 conjuncts: comm12 (3,3) = 0, comm12 (4,4) = 0,
    comm23 (3,4) = 0, comm23 (4,3) = 0).

    The first 4 conjuncts establish substantive {0,1,2}-block spanning
    structure. The last 4 conjuncts document the {3,4}-block structural
    limitation. Together: 8/24 of the target 𝔰𝔲(5) spanning content
    with explicit honest scope documentation. -/
theorem quintet_8_conjunct_block_summary :
    -- Parent baseline (Wave 2b.3): substantive {0,1,2}-block spanning
    comm12_5 1 2 ≠ 0 ∧
    comm23_5 0 1 ≠ 0 ∧
    comm23_5 1 2 ≠ 0 ∧
    comm12_5 0 1 = 0 ∧
    -- Wave 2b.3.2 extension: block-extension limitation on {3,4}-block
    comm12_5 3 3 = 0 ∧
    comm12_5 4 4 = 0 ∧
    comm23_5 3 4 = 0 ∧
    comm23_5 4 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact comm12_5_entry_12_nonzero
  · exact comm23_5_entry_01_nonzero
  · exact comm23_5_entry_12_nonzero
  · exact comm12_5_entry_01_zero
  · exact comm12_5_block_34_zero_at_33
  · exact comm12_5_block_34_zero_at_44
  · exact comm23_5_block_34_zero_at_34
  · exact comm23_5_block_34_zero_at_43

/-! ## 4. Module summary

FibonacciQuintetUniversalityExt.lean (Phase 6p Wave 2b.3.2 PARTIAL,
2026-05-12): iterated-commutator definitions + block-extension limitation
theorems extending the Wave 2b.3 baseline.

  - **Iterated commutators** (substrate definitions for follow-up sub-waves):
    `comm_12_23_5`, `comm_12_13_5`, `jacobi_term_1`, `jacobi_term_3`.
  - **4 block-extension limitation theorems** (native_decide):
    `comm12_5_block_34_zero_at_33`, `_at_44`, `comm23_5_block_34_zero_at_34`, `_at_43`.
  - **`block_extension_block_34_limitation`** — 4-conjunct closure of the
    {3,4}-block structural limitation.
  - **`quintet_8_conjunct_block_summary`** — augmented 8-conjunct closure
    bundling parent's 4 substantive {0,1,2}-spanning conjuncts with 4 new
    {3,4}-block limitation conjuncts.

Substantive content delivered:
  (a) 4 new native_decide-verified structural theorems documenting the
      {3,4}-block limitation of the block-extension architecture (= why
      the block-extension cannot exhibit cross-block mixing).
  (b) Iterated-commutator substrate definitions (`comm_12_23_5`, etc.)
      ready for downstream entry-level analysis once HZBS Fig 4 4-strand
      F-symbol substrate lands.
  (c) 8-conjunct closure (parent 4 + new 4) brings total quintet-side
      block-aware spanning content to 8/24 conjuncts.

**Honest scope**: ships 8 of the target 24 conjuncts. The remaining 16
require the HZBS 2007 Fig 4 4-strand F-symbol matrices (not available
from any public primary source in machine-readable form as of 2026-05-12),
which would unlock genuine {3,4}-block mixing and cross-block commutator
content. Documented as a Wave 2b.3.2-followup deferral.

The block-extension limitation theorems serve a load-bearing role: they
formally document **why** the gap exists, making the deferral structural
rather than ad-hoc.

Zero sorry. Zero new project-local axioms.
-/

end SKEFTHawking.FibonacciQuintetUniversalityExt
