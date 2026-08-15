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

---

## Addendum 2026-08-15 — the sharpest instance, found by a Stage-10 drafter

A D2 section drafter, working the redraft under the "contradictions between the brief and the
sources" instruction, met the superseded `papers/D2/paper_draft.tex` §303-317 and declined to
reproduce it. That passage is the clearest specimen of this defect class in the corpus, because
it **states the vacuity in reader-facing prose and presents it as a discharge**:

> "...\texttt{E8Lattice.e8\_det\_one} discharges unimodularity... The Serre algebraic bound is
> then automatic ($8 \mid 8$); \texttt{e8\_sigma\_not\_div\_16} records that $E_8$ exhibits the
> algebraic floor... The validity of the characteristic-square pairing on $E_8$ itself is closed
> by \texttt{AlgebraicRokhlin.char\_sq\_valid\_e8}."

Three separate problems, none of which any gate caught:

1. **`e8_sigma_div_8` is `(8 : ℤ) ∣ (8 : ℤ) := dvd_refl 8`** (`E8Lattice.lean:98`), cited at
   `D2:678` as what "underlies the $E_8$-lattice signature". The prose's own parenthetical
   `($8 \mid 8$)` is a correct reading of the theorem — and it is offered as though a bound had
   been established.
2. **`char_sq_valid_e8` evaluates `selfPairing` at the zero vector**, and is cited as closing
   "the validity of the characteristic-square pairing on $E_8$".
3. **The cited chain is not the chain that proves the result, and is not kernel-pure.**
   `e8_det_one`, `e8_diagonal_all_two`, `e8_symmetric` and `e8_minor_1` are all proved by
   `native_decide` (`E8Lattice.lean:43,54,63,72`), putting `Lean.ofReduceBool` in their axiom
   set. The theorems that actually carry `eight_dvd_latticeSig` are about the *literal* matrix
   `E8lit`, proved kernel-pure by inverse exhibition and by the `C8ᵀC8 = 4·E8lit` certificate.
   **There is no in-tree theorem `E8lit = CartanMatrix.E₈`**, so the two developments are not
   linked at all — the manuscript attributes the kernel chain's E8 evaluation to declarations
   that are neither kernel-pure nor on the chain.

**Verified by the lead, 2026-08-15**, directly against `E8Lattice.lean` and `RokhlinArfNoGo.lean`,
not from the drafter's report. Checked for blast radius: `I1:1658` also names `e8_det_one` but is
**not** an instance — it lists the declaration descriptively as one of twenty-five a single
Aristotle run registered, and argues that yield of that kind is a poor proxy for value.
`papers/paper10_modular_generation/paper_draft.tex:377` discloses `native_decide` in-line.

The D2 Stage-10 redraft replaces the passage and cites the `E8lit` chain instead, so the live
prose instance closes with that redraft. **What does not close is the register gap this finding
is about:** none of the three problems above was detectable by `placeholder_not_cited`
(population too narrow), `vacuous_statement_audit` (statement shape, not witness triviality), or
the `native_decide` ratchet (which tracks the debt but does not know the declarations are cited
as backing). A drafter reading the source caught what three guards could not.

**Consequence for the fix in §1.1/§1.2.** The missing `E8lit = CartanMatrix.E₈` bridge shows the
population must be widened on a third axis as well: a citation can be defective not only because
the cited theorem is empty, but because it is *sound and irrelevant* — true, kernel-checked, and
not on the path to the claim it is offered for. That is not caught by any vacuity predicate and
should be scoped explicitly before the extension in §1.1 is built.
