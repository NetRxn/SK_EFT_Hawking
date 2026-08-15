---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-15T20:10:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# Invariant #9 covers `PLACEHOLDER_THEOREMS` and not `VACUOUS_STATEMENT_BASELINE`

## Summary

**1 MAJOR.** Pipeline Invariant #9 — *a placeholder theorem MUST NOT be referenced by any
paper claim* — is enforced by `placeholder_not_cited`, whose population is
`PLACEHOLDER_THEOREMS` (statements that are literally `True := trivial`).

`VACUOUS_STATEMENT_BASELINE` is a **second, larger** register of declarations the project
has already measured as content-free: reflexive or tautological statements whose substance
lives in a docstring rather than in the type. Nothing connects it to the citation rule. A
declaration the project has formally recorded as saying nothing may therefore be cited in a
manuscript as verified backing, and every gate stays green.

⚠️ **Found live, in a bundle being redrafted for submission.**
`papers/D2/paper_draft.tex` cites `hom_tensor_adjunction_dim` as discharging hypothesis
**H2**. The declaration, at `lean/SKEFTHawking/ChangeOfRings.lean:67`, is:

```lean
/-- dim Hom_A(A tensor_B P, k) = dim Hom_B(P, k) = rank(P). -/
theorem hom_tensor_adjunction_dim (rank : ℕ) :
    rank = rank := rfl
```

The docstring carries the whole claim; the statement mentions no Hom, no tensor, no
adjunction and no dimension. It is in `VACUOUS_STATEMENT_BASELINE`, so the project already
knows. Its own module's docstring separately records that **H2 is OPEN** and that all four
hypotheses remain — so the manuscript cites a tautology as closing a hypothesis the
substrate says is open.

A sibling case in the same bundle: `hidden_sector_required` is cited for a claim about
Standard-Model field content and states only that every nonzero element of ℤ/16 has a
nonzero additive inverse.

**Both guards are correct about their own populations.** `placeholder_not_cited` passes
because neither declaration is a `True := trivial` placeholder; `vacuous_statement_audit`
passes because both are inside the frozen baseline. This is the failure shape this project
keeps recording — two mechanisms, each sound, and the seam between them unasserted.

### 1.1 — 🔴 MAJOR — a baselined-vacuous theorem can back a paper claim

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python -m pytest tests/test_d5_lean_substrate.py -q -k "vacuous and cited"`
  *What it asserts:* that a declaration in `VACUOUS_STATEMENT_BASELINE` cited in a bundle
  draft fails a check. Exits 1 at HEAD — no such leg exists.
- **Gate:** LeanProofSubstance
- **Location:** `scripts/validation/checks/lean_substrate.py` — `check_placeholder_not_cited`;
  `src/core/constants.py` — `VACUOUS_STATEMENT_BASELINE`, `PLACEHOLDER_THEOREMS`
- **Observed:** Invariant #9's enforcement reads one register; the project maintains two.
- **Evidence:** Measured 2026-08-15. `hom_tensor_adjunction_dim` ∈ baseline (48 entries),
  ∉ `PLACEHOLDER_THEOREMS`; both `placeholder_not_cited` and `vacuous_statement_audit`
  green at HEAD while D2 cites it as discharging H2.
- **Expected:** Invariant #9 binds every declaration the project has recorded as
  content-free, whichever register records it.
- **Fix:** Extend `placeholder_not_cited`'s population to the union of both registers.
  ⚠️ **MEASURE BEFORE EXTENDING, AND EXPECT IT TO BE RED ON ARRIVAL.** The baseline holds
  48 entries and the corpus has never been checked against it, so the honest sequence is
  extend → measure → report the population → remediate the citations, NOT extend and
  baseline whatever comes out. A citation is repaired by strengthening the theorem or by
  removing the claim — never by adding the declaration to a suppression list, which would
  rebuild this defect one register deeper.
- **Related:** the same shape as `count_literals` (digits only, blind to words) and the
  `\bibitem`-as-proxy defect retired in `d39d2ffb` — a guard whose population is narrower
  than its stated purpose, so its silence is not evidence. ADR-004 class 1
  (defining-the-conclusion) is the failure this citation rule exists to stop reaching print.
- **Cache:** N/A.

### 1.2 — 🔴 MAJOR — the vacuity predicate is SYNTACTIC, so an existential discharged by `refl` is invisible to both registers

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python -m pytest tests/test_d5_lean_substrate.py -q -k "vacuous and existential"`
  *What it asserts:* that a statement whose only witness is an identity/`refl` construction is
  detected as content-thin. Exits 1 at HEAD — no such leg exists.
- **Gate:** LeanProofSubstance
- **Location:** `scripts/validation/checks/lean_substrate.py` — `check_vacuous_statement_audit`
- **Observed:** `vacuous_statement_audit` looks for **reflexive or tautological** statement
  SHAPES (`a = a`, `True`). A statement can be semantically empty without having that shape.
- **Evidence:** Measured 2026-08-15, `lean/SKEFTHawking/Z16AnomalyComputation.lean:51`:

  ```lean
  theorem dai_freed_spin_z4 : ∃ (φ : ZMod 16 ≃ ZMod 16), Function.Bijective φ :=
    ⟨Equiv.refl _, (Equiv.refl _).bijective⟩
  ```

  It is named for the bordism identification `Ω₅^{Spin^ℤ₄} ≅ ℤ₁₆` and establishes only that
  ℤ/16 admits a bijective self-equivalence — true of every type, witnessed by the identity,
  carrying no bordism content whatever. `hidden_sector_required` is the sibling case: cited
  for a claim about Standard-Model field content, it states that every nonzero element of
  ℤ/16 has a nonzero additive inverse.

  **Neither is in `VACUOUS_STATEMENT_BASELINE` and neither is in `PLACEHOLDER_THEOREMS`.**
  So §1.1's gap is the milder half: that one concerns declarations the project has RECORDED
  as empty. These were never detected at all, and both are cited in a bundle being redrafted
  for submission.
- **Expected:** A statement whose witness is an identity, `Equiv.refl`, or an equivalent
  no-content construction is flagged, whatever its syntactic shape.
- **Fix:** Extend the audit from statement shape to **witness triviality** — a proof term
  that is `rfl`, `Equiv.refl`, `id`, or a structure literal of those, for a statement that
  quantifies over nothing the witness constrains. `lean_deps.json` carries types and not
  `def` bodies, so this needs the proof term, which means the extractor or `lean_verify`,
  not a type walk.
  ⚠️ **MEASURE BEFORE FREEZING, AND DO NOT BULK-BASELINE THE RESULT.** The honest sequence
  is extend → measure → report → strengthen the theorems. Adding the newly-detected set to
  `VACUOUS_STATEMENT_BASELINE` would convert a detection into a permission, which is how
  §1.1's gap arose in the first place.
- **Related:** ADR-004 class 1 names this exact failure — "substantive content is discharged
  into a definition … so the headline theorem's proof is a trivial `rfl` / `decide` /
  field projection", and notes all three existing guards pass simultaneously on it. This is
  that class, surviving the guard written for it because the guard reads the statement and
  the emptiness is in the proof.
- **Cache:** N/A.
