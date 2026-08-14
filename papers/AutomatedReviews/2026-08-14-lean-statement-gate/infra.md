# No gate compares a paper's stated proposition to the Lean it cites

**Found by** tracing why five Stage-13 rounds passed a false universally-quantified
statement in D3, attributed to a real theorem.

---

## Findings

### 1 — 🔴 Every prose→Lean check asserts EXISTENCE; none asserts CORRESPONDENCE

- **Severity:** critical
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `scripts/validation/checks/prose_lean_refs.py`,
  `scripts/validation/checks/lean_substrate.py`, `scripts/validation/checks/reviews.py`
- **Observed:** the check inventory contains no assertion that a paper's rendered claim
  matches the statement of the Lean declaration it cites. Measured over the live roster:

  | check | what it actually asserts |
  |---|---|
  | `prose_theorem_reference_coverage` | the name RESOLVES in `lean_deps.json` |
  | `formula_grounding` | resolves to a real, non-placeholder theorem |
  | `placeholder_not_cited` | placeholders are not cited as verified |
  | `disclosure_consistency` | a vacuous theorem is not sold as establishing a result |
  | `chain_backing_targets_resolve` | the named target EXISTS |
  | `bundle_lean_module_coverage` | registered modules are reached by the draft |

  All six are satisfied by a citation that points at something real. **None is falsified by
  a citation that points at something real which says something else.**
- **Evidence:** `papers/D3/paper_draft.tex:658-666` displays
  `∀ χ_vest ∈ [0.1,10], |c_GW(χ_vest) − c| > 3×10⁻¹⁵ c`
  and attributes it: "and is theorem `second_sound_graviton_natural_range_universally_falsified`
  (zero `sorry`)". That theorem is real, kernel-pure, non-vacuous, non-placeholder, and
  resolves — and its statement is `¬ ∃ χ, (χ = lower ∨ χ = upper) ∧ LigoSatisfied (...)`, a
  **two-point disjunction**. The displayed proposition is false (χ=1 lies in the interval and
  satisfies the cap; L1's own `ligo_satisfied_at_chi_one` proves it). Every gate passed.
- ⚠️ **The failure is silent in the direction that matters.** A wrong citation TARGET is
  caught; a wrong citation MEANING is not. The stronger the Lean substrate gets — kernel-pure,
  zero-sorry, non-vacuous — the more authority a mis-described theorem borrows.
- ⚠️ **This defect has been absorbed by review agents, at high cost and unreliably.** It
  survived Stage-13 rounds 1, 2, 3, the 2026-05-11 sweep and the 2026-06-10 sweep, and was
  caught on the sixth pass. Agent review is non-deterministic, expensive, and was standing in
  for a check. `bundle_consistency` cannot cover it either: it compares bundles to each
  other, so three bundles carrying the same wrong statement agree and it passes.
- **Expected:** a displayed proposition attributed to a named Lean declaration is checked
  against that declaration's statement, or the attribution is rejected.
- **Fix:** design required — route through the `architecture-change` skill. The tractable
  core is quantifier-and-shape correspondence rather than full LaTeX↔Lean semantics: extract
  the attributed declaration's statement from `lean_deps.json`, extract the displayed
  proposition's binder structure from the draft, and fail when a paper displays `∀ x ∈ S, P`
  against a declaration whose statement quantifies over a finite disjunction, or vice versa.
  An explicit machine-checkable correspondence annotation at each attribution site is the
  alternative and may be cheaper to make sound.
  ⛔ Do NOT close this by strengthening `bundle_consistency` — comparing bundles to each
  other is the proxy; the Lean is the decider.
- **Verify:** `uv run python scripts/validate.py --check bundle_readiness`
