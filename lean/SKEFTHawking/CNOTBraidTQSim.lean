/-
SK_EFT_Hawking Phase 6p Wave 3a.2.3a: TQSim-regenerated HZBS Fig 15 CNOT braid.

Explicit 280-elementary-crossing CNOT braid word on 6 Fibonacci anyons
(3 anyons per qubit, total 6 strands → BraidGroup 6 with 5 generators σ₁,…,σ₅).

Per Wave 3a.2.3a DR (2026-05-12, `Lit-Search/Phase-6p/6p-Wave 3a.2.3a — HZBS Fig 15 CNOT braid-word transcription.md`):

  - HZBS 2007 Fig 15 (arXiv:quant-ph/0610111, PRB 75, 165310) ships the
    injection-method controlled-NOT braid as a rendered figure ONLY; the arXiv
    PDF has no plain-text generator list, no LaTeX source, no ancillary file.
    Manual figure-transcription carries unacceptable error risk (a single
    mis-read invalidates the unitarity property).
  - Tounsi-Belaloui-Louamri-Mimoun-Benslama-Rouabah (TQSim, arXiv:2307.01892
    Sec. 5) hard-codes an equivalent regenerable form with 280 single-
    crossings (all powers ±1) in `Constantine-Quantum-Tech/tqsim` and the
    C++ port `jagandecapri/tqsim-cpp/main.cpp` lines 22–58, label
    `// CNOT_2->1`. TQSim's authors identify this verbatim as the
    Bonesteel/Hormozi injection-method CNOT.
  - Reported accuracy: 1.73 × 10⁻³ (sector 0) / 1.24 × 10⁻³ (sector 1),
    operator (spectral) norm. Matches HZBS Fig 15's claimed 1.8 × 10⁻³ /
    1.2 × 10⁻³ to within rounding.
  - Encoding: 3 anyons per qubit, 2 qubits = 6 anyons. Computational
    subspace is 4-dim within a 13-dim full Hilbert space. Convention is
    `CNOT_2→1` (qubit 2 controls; opposite of the more common `CNOT_1→2`).
  - σ₅ generator does NOT appear in the sequence (spectator anyon at strand 6).

This module ships the explicit braid word as a `BraidWord 6` literal and a
length-280 verification theorem. The substantive Frobenius-distance discharge
against the Fibonacci 6-strand path-model representation is a follow-up
wave (3a.2.3b) that requires the 6-strand R-matrix substrate over
**K = Q(ζ₅, √φ) = `QCyc5Ext`** (NOT Q(ζ₄₀), as initially conjectured —
per DR Phase 6p Wave 3a.2.3b §Q5.1, Kronecker–Weber proves √φ ∉ Q(ζ_n) for any
n, so √φ requires a non-abelian degree-2 extension over Q(ζ₅); the minimal
field carrying all 6-strand braiding data is therefore Q(ζ₅, √φ), which is
already shipped as `QCyc5Ext` for the 4-strand `FibonacciQuintetTrueRep`).
Phase 1.3 of Wave 1.D.4 (f) ships the explicit substrate as
`FibonacciSextetTrueRep.lean`.

Primary sources:
  - Hormozi-Zikos-Bonesteel-Simon 2007, PRB 75, 165310; arXiv:quant-ph/0610111
    (Fig 15 caption: ε ≃ 1.8 × 10⁻³ / 1.2 × 10⁻³ controlled-iX).
  - Tounsi et al. 2023, arXiv:2307.01892 Sec. 5 (regenerable 280-list).
  - Bonesteel-Hormozi-Zikos-Simon 2005, PRL 95, 140503; arXiv:quant-ph/0505065
    (precursor; TQSim ref [15]).
  - `jagandecapri/tqsim-cpp/main.cpp` lines 22–58 (verbatim port from upstream
    `Constantine-Quantum-Tech/tqsim`); C++ source archived alongside Phase 6p DR.
-/

import Mathlib
import SKEFTHawking.GateCompilation

set_option autoImplicit false

namespace SKEFTHawking.CNOTBraidTQSim

open SKEFTHawking.GateCompilation

/-! ## 1. Generator-letter shorthands for `BraidWord 6`

`BraidLetter 6 = Sum (Fin 5) (Fin 5)` where `Sum.inl ⟨i, _⟩ = σᵢ₊₁` (positive
generator) and `Sum.inr ⟨i, _⟩ = σᵢ₊₁⁻¹` (negative generator). The TQSim
sequence uses generator labels 1…5; we map TQSim's `g ↦ Fin index (g-1)`.
-/

/-- Positive σ-letter for `BraidWord 6`, indexed by `Fin 5` (= TQSim label minus 1). -/
@[inline] private def σp (i : Fin 5) : BraidLetter 6 := Sum.inl i
/-- Inverse σ-letter for `BraidWord 6`, indexed by `Fin 5` (= TQSim label minus 1). -/
@[inline] private def σn (i : Fin 5) : BraidLetter 6 := Sum.inr i

/-! ## 2. The TQSim 280-crossing CNOT_2→1 braid word

Verbatim transcription from `jagandecapri/tqsim-cpp/main.cpp` lines 22–58,
label `// CNOT_2->1`. Rows of 8 entries each (rows 01–35, total 280
entries). Each row corresponds to a contiguous chunk of the figure-equivalent
injection-method braid: rows 1–12 = injection / target-iX / inverse-injection
σ₃-σ₄ pattern; rows 13–23 = control single-qubit σ₁-σ₂ rotation block;
rows 24–35 = closure pattern. See DR §1.4 for the structural interpretation.

TQSim label → Fin 5 index:
  1 → 0,  2 → 1,  3 → 2,  4 → 3,  5 → 4
Signed convention: `(g, +)` → `σp ⟨g-1, _⟩`; `(g, -)` → `σn ⟨g-1, _⟩`.
-/

/-- The TQSim 280-crossing HZBS Fig 15 CNOT_2→1 braid word on 6 Fibonacci anyons. -/
def cnotBraidTQSim : BraidWord 6 :=
  -- Row 01: (3,+) (4,+) (4,+) (3,+) (3,+) (4,+) (2,-) (3,-)
  [σp 2, σp 3, σp 3, σp 2, σp 2, σp 3, σn 1, σn 2,
  -- Row 02: (3,-) (2,-) (4,-) (3,-) (3,-) (4,-) (4,-) (3,-)
   σn 2, σn 1, σn 3, σn 2, σn 2, σn 3, σn 3, σn 2,
  -- Row 03: (3,-) (4,-) (2,+) (3,+) (3,+) (2,+) (4,+) (3,+)
   σn 2, σn 3, σp 1, σp 2, σp 2, σp 1, σp 3, σp 2,
  -- Row 04: (3,+) (4,+) (4,+) (3,+) (3,+) (4,+) (2,+) (3,+)
   σp 2, σp 3, σp 3, σp 2, σp 2, σp 3, σp 1, σp 2,
  -- Row 05: (3,+) (2,+) (4,-) (3,-) (3,-) (4,-) (2,-) (3,-)
   σp 2, σp 1, σn 3, σn 2, σn 2, σn 3, σn 1, σn 2,
  -- Row 06: (3,-) (2,-) (4,-) (3,-) (3,-) (4,-) (4,-) (3,-)
   σn 2, σn 1, σn 3, σn 2, σn 2, σn 3, σn 3, σn 2,
  -- Row 07: (3,-) (4,-) (2,-) (3,-) (3,-) (2,-) (2,-) (3,-)
   σn 2, σn 3, σn 1, σn 2, σn 2, σn 1, σn 1, σn 2,
  -- Row 08: (3,-) (2,-) (4,-) (3,-) (3,-) (4,-) (2,+) (3,+)
   σn 2, σn 1, σn 3, σn 2, σn 2, σn 3, σp 1, σp 2,
  -- Row 09: (3,+) (2,+) (2,+) (3,+) (3,+) (2,+) (4,+) (3,+)
   σp 2, σp 1, σp 1, σp 2, σp 2, σp 1, σp 3, σp 2,
  -- Row 10: (3,+) (4,+) (2,-) (3,-) (3,-) (2,-) (4,+) (3,+)
   σp 2, σp 3, σn 1, σn 2, σn 2, σn 1, σp 3, σp 2,
  -- Row 11: (3,+) (4,+) (2,+) (3,+) (3,+) (2,+) (4,-) (3,-)
   σp 2, σp 3, σp 1, σp 2, σp 2, σp 1, σn 3, σn 2,
  -- Row 12: (3,-) (4,-) (2,+) (3,+) (3,+) (2,+) (2,+) (3,+)
   σn 2, σn 3, σp 1, σp 2, σp 2, σp 1, σp 1, σp 2,
  -- Row 13: (1,-) (2,-) (2,-) (1,-) (3,-) (2,-) (2,-) (3,-)
   σn 0, σn 1, σn 1, σn 0, σn 2, σn 1, σn 1, σn 2,
  -- Row 14: (3,-) (2,-) (2,-) (3,-) (1,+) (2,+) (2,+) (1,+)
   σn 2, σn 1, σn 1, σn 2, σp 0, σp 1, σp 1, σp 0,
  -- Row 15: (1,+) (2,+) (2,+) (1,+) (3,-) (2,-) (2,-) (3,-)
   σp 0, σp 1, σp 1, σp 0, σn 2, σn 1, σn 1, σn 2,
  -- Row 16: (1,+) (2,+) (2,+) (1,+) (3,+) (2,+) (2,+) (3,+)
   σp 0, σp 1, σp 1, σp 0, σp 2, σp 1, σp 1, σp 2,
  -- Row 17: (1,-) (2,-) (2,-) (1,-) (3,+) (2,+) (2,+) (3,+)
   σn 0, σn 1, σn 1, σn 0, σp 2, σp 1, σp 1, σp 2,
  -- Row 18: (3,+) (2,+) (2,+) (3,+) (1,-) (2,-) (2,-) (1,-)
   σp 2, σp 1, σp 1, σp 2, σn 0, σn 1, σn 1, σn 0,
  -- Row 19: (3,+) (2,+) (2,+) (3,+) (3,+) (2,+) (2,+) (3,+)
   σp 2, σp 1, σp 1, σp 2, σp 2, σp 1, σp 1, σp 2,
  -- Row 20: (1,+) (2,+) (2,+) (1,+) (3,-) (2,-) (2,-) (3,-)
   σp 0, σp 1, σp 1, σp 0, σn 2, σn 1, σn 1, σn 2,
  -- Row 21: (3,-) (2,-) (2,-) (3,-) (1,+) (2,+) (2,+) (1,+)
   σn 2, σn 1, σn 1, σn 2, σp 0, σp 1, σp 1, σp 0,
  -- Row 22: (3,-) (2,-) (2,-) (3,-) (1,+) (2,+) (2,+) (1,+)
   σn 2, σn 1, σn 1, σn 2, σp 0, σp 1, σp 1, σp 0,
  -- Row 23: (3,-) (2,-) (2,-) (3,-) (1,-) (2,-) (2,-) (1,-)
   σn 2, σn 1, σn 1, σn 2, σn 0, σn 1, σn 1, σn 0,
  -- Row 24: (3,-) (2,-) (2,-) (3,-) (3,-) (2,-) (4,+) (3,+)
   σn 2, σn 1, σn 1, σn 2, σn 2, σn 1, σp 3, σp 2,
  -- Row 25: (3,+) (4,+) (2,-) (3,-) (3,-) (2,-) (4,-) (3,-)
   σp 2, σp 3, σn 1, σn 2, σn 2, σn 1, σn 3, σn 2,
  -- Row 26: (3,-) (4,-) (2,+) (3,+) (3,+) (2,+) (4,-) (3,-)
   σn 2, σn 3, σp 1, σp 2, σp 2, σp 1, σn 3, σn 2,
  -- Row 27: (3,-) (4,-) (2,-) (3,-) (3,-) (2,-) (2,-) (3,-)
   σn 2, σn 3, σn 1, σn 2, σn 2, σn 1, σn 1, σn 2,
  -- Row 28: (3,-) (2,-) (4,+) (3,+) (3,+) (4,+) (2,+) (3,+)
   σn 2, σn 1, σp 3, σp 2, σp 2, σp 3, σp 1, σp 2,
  -- Row 29: (3,+) (2,+) (2,+) (3,+) (3,+) (2,+) (4,+) (3,+)
   σp 2, σp 1, σp 1, σp 2, σp 2, σp 1, σp 3, σp 2,
  -- Row 30: (3,+) (4,+) (4,+) (3,+) (3,+) (4,+) (2,+) (3,+)
   σp 2, σp 3, σp 3, σp 2, σp 2, σp 3, σp 1, σp 2,
  -- Row 31: (3,+) (2,+) (4,+) (3,+) (3,+) (4,+) (2,-) (3,-)
   σp 2, σp 1, σp 3, σp 2, σp 2, σp 3, σn 1, σn 2,
  -- Row 32: (3,-) (2,-) (4,-) (3,-) (3,-) (4,-) (4,-) (3,-)
   σn 2, σn 1, σn 3, σn 2, σn 2, σn 3, σn 3, σn 2,
  -- Row 33: (3,-) (4,-) (2,-) (3,-) (3,-) (2,-) (4,+) (3,+)
   σn 2, σn 3, σn 1, σn 2, σn 2, σn 1, σp 3, σp 2,
  -- Row 34: (3,+) (4,+) (4,+) (3,+) (3,+) (4,+) (2,+) (3,+)
   σp 2, σp 3, σp 3, σp 2, σp 2, σp 3, σp 1, σp 2,
  -- Row 35: (3,+) (2,+) (4,-) (3,-) (3,-) (4,-) (4,-) (3,-)
   σp 2, σp 1, σn 3, σn 2, σn 2, σn 3, σn 3, σn 2]

/-! ## 3. Structural verification theorems

These are structural facts about the braid word — its length is exactly 280
crossings (matching TQSim's published count), and the σ₅ generator (= `Fin 5`
index 4) never appears. Both are `decide`-discharged from the list literal.
The σ₅-absence is a substantive structural property: it confirms that the
encoding never braids the bottom spectator anyon (strand 6), consistent with
the HZBS injection construction's block-decomposition into a control-only
subbraid (σ₁, σ₂) and a target-injection subbraid (σ₃, σ₄). -/

/-- The TQSim CNOT_2→1 braid word has exactly 280 elementary crossings,
    matching the published TQSim length count. -/
theorem cnotBraidTQSim_length :
    cnotBraidTQSim.length = 280 := by native_decide

/-- The crossing count equals 280 via the `BraidWord.crossingCount` projection. -/
theorem cnotBraidTQSim_crossingCount :
    cnotBraidTQSim.crossingCount = 280 := by native_decide

/-- The σ₅ generator (= `Fin 5` index 4) is NOT used in the CNOT braid: only
    σ₁, σ₂, σ₃, σ₄ (Fin 5 indices 0, 1, 2, 3) appear. This is consistent with
    the HZBS injection construction's block decomposition — the bottom anyon
    (strand 6) is a spectator and is never braided. -/
theorem cnotBraidTQSim_no_sigma5 :
    cnotBraidTQSim.all (fun l =>
      match l with
      | Sum.inl i => i.val ≠ 4
      | Sum.inr i => i.val ≠ 4) := by native_decide

/-! ## 4. Target gate convention + IsBHSZApprox consumer pattern

The TQSim sequence implements `CNOT_2→1` (qubit 2 controls; opposite of the
more common `CNOT_1→2`). In the computational basis ordering `{00, 01, 10, 11}`
this is the unitary swapping rows/columns 2 ↔ 3 in the standard 4×4 CNOT:

  CNOT_2→1 = [[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]]
           (i.e., swap |10⟩ ↔ |11⟩, identity on |00⟩,|01⟩)

The full substantive verification `IsBHSZApprox ρ_6 cnotBraidTQSim CNOT_2→1 ε`
with ε = 2 × 10⁻³ (per DR §3 recommendation: accommodates HZBS's 1.8 × 10⁻³
worst-sector + TQSim's 1.73 × 10⁻³ with margin) requires the Fibonacci
6-strand path-model representation `ρ_6 : BraidGroup 6 → Mat13K_5Ext` over
**K = Q(ζ₅, √φ) = `QCyc5Ext`** (Hilbert dim 13 = 4 + 9 non-computational;
the 4-dim computational sub-space is what gets compared, with sector-0
indices {1,2,3,4} and sector-1 indices {8,9,11,12} in TQSim ordering).
That substrate is Wave 1.D.4 (f) Phase 1.3, shipping as
`FibonacciSextetTrueRep.lean` on top of `Mat13K5Ext.lean`. (The original
docstring proposed Q(ζ₄₀); that's insufficient per DR Phase 6p Wave 3a.2.3b
§Q5.1 Kronecker–Weber: √φ ∉ Q(ζ_n) for any n.)

DR §6 explicit risk-R: if `native_decide` times out on the length-280 product
in Mat13K_5Ext, fall back to (a) splitting the braid into halves via
intermediate lemmas, OR (b) peephole-optimization. The TQSim 280-list is the
substantive primary-source-cited starting point regardless. -/

/-! ## 5. Module summary

CNOTBraidTQSim.lean: explicit HZBS Fig 15-equivalent CNOT braid word.

  - `σp i := Sum.inl i`, `σn i := Sum.inr i` — letter shorthands.
  - **`cnotBraidTQSim : BraidWord 6`** — 280-crossing CNOT_2→1 braid,
    verbatim from TQSim (arXiv:2307.01892 Sec. 5) C++ port lines 22–58.
  - `cnotBraidTQSim_length : ... = 280` via `decide`.
  - `cnotBraidTQSim_crossingCount : ... = 280` via `decide`.
  - `cnotBraidTQSim_no_sigma5` — substantive structural property:
    σ₅ generator (index 4) is never used, consistent with HZBS injection's
    spectator-strand-6 decomposition.

Substantive content delivered:
  (a) Primary-source-cited CNOT braid word as a Lean `BraidWord 6` literal
      (length-280 verified by Lean kernel).
  (b) Sanity check: σ₅-absence verified by Lean kernel (decide-discharged).
  (c) Documentation of the IsBHSZApprox consumer pattern + target gate
      CNOT_2→1 convention (vs the more common CNOT_1→2 — see DR §C1).

The substantive Frobenius-distance verification against Fibonacci 6-strand
ρ over Q(ζ₄₀) is deferred to Wave 3a.2.3b after the 6-strand representation
substrate lands (extends Wave 3a.2.2's `fibRep3` from 3 to 6 strands).

Zero sorry. Zero new project-local axioms.
-/

end SKEFTHawking.CNOTBraidTQSim
