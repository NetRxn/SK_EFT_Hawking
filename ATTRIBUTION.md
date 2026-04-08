# Attribution

## Authors

- **John Roehm** — project lead, research direction, experimental design, validation architecture,
  parameter verification, editorial decisions

## AI-Assisted Development

This project was developed with extensive assistance from AI tools. Varying degrees of validation are applied during development, commits with the tag **wip** indicate work in progress. The validation framework is described in `docs/validation/VALIDATION_REPORT.md` and the validation reports can be found in `docs/validation/reports/`. The following is a breakdown of contributions by tool:

### Claude Deep Research (Anthropic)
- In-depth literature review and technical analysis - deep integration with all stages of development

### Claude Code (Anthropic)
- Code generation across Python and Lean 4
- Proof development, theorem statement design, module architecture
- Pipeline infrastructure (validation, provenance, claims review)
- Paper drafting and figure generation
- https://claude.ai/claude-code
- Agentic review of figures and claims
- Visualization of provenance pipeline

### Aristotle (Harmonic)
- Automated theorem proving for Lean 4 sorry gaps
- 307 theorems proved across 43+ submissions
- Key contributions (non-exhaustive list): Hopf algebra structure (U_q(sl_2) coproduct/counit/antipode),
  categorical infrastructure (quantum dimensions, trace properties),
  Onsager algebra (Davies isomorphism, Chevalley embedding),
  number field computations (F-symbol involutory, associativity),
  S-matrix verification (unitarity, Verlinde formula),
  and statistical estimator bounds
- Run IDs tracked in `src/core/constants.py` → `ARISTOTLE_THEOREMS`
- https://aristotle.harmonic.fun
- Citation per Aristotle docs: https://aristotle.harmonic.fun/dashboard/docs/citation

### Lean 4 Kernel
- All 2200+ theorems verified by the Lean 4 type checker (`lake build`)
- ~600 theorems use `native_decide` — kernel-evaluated computation over
  decidable types (number fields, finite fusion data, matrix identities)
- No `sorry` in any theorem used by paper claims or downstream proofs

## Extracted Libraries

- **lean-tensor-categories** — categorical hierarchy + number fields extracted
  for Mathlib contribution, located in `NetRxn/lean-tensor-categories/`.
  See that library's ATTRIBUTION.md for extraction-specific provenance.

## Provenance Tracking

- Every experimental parameter traced to a published source via
  `PARAMETER_PROVENANCE` in `src/core/provenance.py`
- Every Aristotle-proved theorem registered in `ARISTOTLE_THEOREMS`
  in `src/core/constants.py` with run UUID
- Every formula references its Lean theorem in `src/core/formulas.py`
- Claims-reviewer agent cross-checks paper claims against computation pipeline

## License

All rights reserved. Individual components may be released under
open-source licenses (see lean-tensor-categories for Apache 2.0).
