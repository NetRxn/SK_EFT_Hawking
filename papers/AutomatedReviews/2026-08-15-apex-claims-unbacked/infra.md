---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-15T23:40:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# What the apex-vacuity measurement surfaced and this commit does not fix

## Summary

**5 MAJOR, 1 MINOR.** ADR-016 shipped `apex_claims_not_vacuous` and, with it, the first
portfolio-wide measurement of the declared-apex claim surface against the project's
vacuity registers. It was **red on arrival**, as
`papers/AutomatedReviews/2026-08-15-baselined-vacuous-theorems-may-be-cited/infra.md`
predicted: **20 of 635 declared apexes across 9 of 21 bundles resolve to a declaration the
project records or derives as content-free, and 15 of those do not say so.**

D2's rows were repaired in the same commit because D2 is measured and merged (ADR-016 D7).
The rest are filed here rather than fixed, for a stated reason: repairing a `claims` string
without reading the draft it indexes is how the number above would stop meaning anything.

Two of the findings are not about the ratchet at all — §1.4 is the axis ADR-016 D6
deliberately scoped **out**, and §1.6/§1.7 are reds the redraft campaign left behind in
neighbouring guards.

⚠️ **Corpus state at filing, recorded so nobody attributes it here.** A full
`pytest tests/` at HEAD is RED on 29 tests, and the twenty-one-bundle redraft campaign
running concurrently — D1, D2, D4, E1, L3 all merged today — is what moved the populations
under a dozen ratchets. This work touches **no `.tex`**, so every draft-derived one is
someone else's: `bundle_lean_module_coverage` (161 absent modules), `bundle_sentence_length`,
`bundle_tables_use_pipeline` (5 against 1), `spelled_out_census_figures`, `counts_fresh`,
`prose_theorem_reference_coverage`, `numerical_literals` (§1.6). `bundle_stage13_claim_consistent`
is red on **both** legs — per-bundle open-REQUIRED (D1 13>2, D2 10>3, D4 13>4, E1 7>1,
L3 5>0, none of them `infra`) and unattributed open-blocking (53 against a limit of 44,
which is **47 without this document's six** — already breached). Only §1.6 and §1.7 are
filed, because they are the two whose repair is a decision rather than the campaign's own
next commit; filing the rest would inflate the very population the second leg measures.

---

### 1.1 — 🔴 MAJOR — 15 published apex claims assert content their statement does not carry, without saying so

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python scripts/validate.py --check apex_claims_not_vacuous --no-archive | grep -q "0 of them UNDISCLOSED"`
  *What it asserts:* that no declared apex resolving to a content-free declaration leaves
  its `claims` string silent about it. Exits 1 at HEAD — 15 do.
- **Gate:** LeanProofSubstance
- **Location:** `papers/{D1,D3,D4,D5,D8,D10,F}/bundle_metadata.json` — `apex_theorems[].claims`
- **Observed:** the declaration a bundle elected as a published result proves nothing, or
  proves it only definitionally, and the `claims` string describes physics.
- **Evidence:** measured 2026-08-15 by `apex_claims_not_vacuous`, which names every row on
  every run. Per bundle: **D5 9** · **D4 1** (of 3; its other two disclose) · D1 1 · D3 1 ·
  D8 1 · D10 1 · F 1. The registers hit are `MODELING_ASSUMPTION_THEOREMS[definitional]`
  (5 rows), a trivial `rfl` / identity-return witness (13 rows),
  `VACUOUS_STATEMENT_BASELINE` (2) and a thin statement (3); a row may carry several.
- **Expected:** each row is repaired by **strengthening the theorem**, **withdrawing the
  apex**, or **stating what the statement actually carries** in the `claims` string —
  ADR-016 D5's disclosure escape, which is how D4 (2 of 3) and E2 already pass.
- **Fix:** per bundle, with the draft open beside the metadata. ⚠️ **Not by adding any
  name to `VACUOUS_STATEMENT_BASELINE` or to any other register** — that is the move that
  created the gap ADR-016 closes, and ADR-016 D4 refuses it. `APEX_UNDISCLOSED_VACUITY_CEILING`
  falls by one per repaired row and never rises.
- **Related:** the §1.1/§1.2 finding this discharges; ADR-004 class 1
  (defining-the-conclusion); ADR-015 D3.
- **Cache:** N/A.

### 1.2 — 🔴 MAJOR — D5 carries 9 of the 20, and its claims strings are per-TRACK boilerplate rather than per-declaration

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python scripts/validate.py --check apex_claims_not_vacuous --no-archive | grep -c "^  . apex_content_free  —  D5:" | grep -qx 0`
  *What it asserts:* that D5 declares no apex resolving to a content-free declaration.
  Exits 1 at HEAD — 9 do.
- **Gate:** LeanProofSubstance
- **Location:** `papers/D5/bundle_metadata.json`
- **Observed:** D5's Track-B rows all carry the identical claims string —
  *"§9 Track B — the 8/8 unanimous entropic-gravity NO-GO, the bundle's substantive new
  claim — <declaration name>"* — and its Track-C rows the identical
  *"§10/§11 Track C … — <declaration name>"*. The string names the **track's headline**
  and then repeats the declaration's own name, so what each individual declaration
  contributes is never stated. Four of the Track-B declarations are
  `MODELING_ASSUMPTION_THEOREMS[definitional]` — bookkeeping over a candidate list — and
  five Track-C declarations are `rfl` against a record field
  (`volovikJannes_he3a_extended.depletion = 1`, `flsBEC.universalCoupling = false`).
- **Evidence:** measured 2026-08-15. `r_d_independent_count_eight` is
  `EntropicGravityDarkEnergy.rDIndependentCount = 8`, is registered `definitional`, and
  `disclosure_consistency` already forbids D5's **prose** from saying it "establishes" the
  8/8 closure — the metadata says exactly that and no check read it until ADR-016.
- **Expected:** one claims string per declaration, stating what that declaration adds, with
  the definitional ones disclosed as the register already describes them.
- **Fix:** D5 metadata pass, with `MODELING_ASSUMPTION_THEOREMS`' own `reason` /
  `discloses` fields as the source for the four definitional rows.
- **Related:** `disclosure_consistency` — same rule, other surface. ADR-016 D5.
- **Cache:** N/A.

### 1.3 — 🔴 MAJOR — four declarations named for physics results state `n ∣ n`, and are in no register

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python -c "import json,sys;sys.path[:0]=['.','scripts'];from validation.checks.lean_statements import _thin_type_label as t;d=json.load(open('lean/lean_deps.json'));n=[r['name'] for r in d if isinstance(r,dict) and r.get('kind') in ('theorem','lemma') and str(t(r.get('type') or '')).startswith('reflexive-literal')];print(n);sys.exit(1 if n else 0)"`
  *What it asserts:* that no project theorem's statement is a relation applied to two
  identical numeric literals. Exits 1 at HEAD, naming four.
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/E8Lattice.lean`, `lean/SKEFTHawking/GenerationConstraint.lean`
- **Observed:** `sm_with_nu_R_anomaly_free : (16 : ℤ) ∣ (16 : ℤ)` — a theorem named *"the
  Standard Model with ν_R is anomaly free"* whose entire content is `dvd_refl 16`. Also
  `e8_sigma_div_8 : (8:ℤ) ∣ (8:ℤ)`, `serre_mod_8_for_E8 : (8:ℤ) ∣ (8:ℤ)`,
  `constraints_with_nu_R : (3:ℕ) ∣ (3:ℕ)`.
- **Evidence:** measured 2026-08-15 by ADR-016 D3's new `reflexive-literal (R n n)` label,
  which was written narrowly on purpose: allowing a bound variable (`∀ a, R a a`) matched
  12 declarations of which 8 are legitimate reflexivity lemmas; closed literals leave
  exactly these 4, all vacuous. None is in `PLACEHOLDER_THEOREMS`,
  `VACUOUS_STATEMENT_BASELINE` or `MODELING_ASSUMPTION_THEOREMS`.
- **Expected:** each states the fact its name asserts, over the object it names — a
  signature, a spectrum, an anomaly coefficient — or is deleted.
- **Fix:** strengthen in Lean. The label is deliberately **not** in `_THIN_HARD`
  (ADR-016 D3) precisely so that this finding is the pressure, rather than a hard-failing
  gate whose only available repair would be baselining the four.
- **Related:** the 2026-08-15 §1.2 finding — same class, reached from the statement side
  rather than the witness side.
- **Cache:** N/A.

### 1.4 — 🔴 MAJOR — a citation can be SOUND AND IRRELEVANT, and no mechanism measures it

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python scripts/validate.py --list --no-archive | grep -qi "apex.*relevan\|off-chain\|citation_on_path"`
  *What it asserts:* that some registered check measures whether a declared apex is on the
  path to the claim it backs. Exits 1 at HEAD — none exists, and ADR-016 D6 scopes it out
  rather than letting a vacuity predicate be read as covering it.
- **Gate:** LeanProofSubstance
- **Location:** `scripts/validation/checks/bundles_readiness.py`; `lean/SKEFTHawking/E8Lattice.lean`
- **Observed:** D2's `e8_det_one`, `e8_diagonal_all_two` and `e8_diagonal_even` are proved
  by `native_decide` against Mathlib's `CartanMatrix.E₈`, while the theorems that carry
  `eight_dvd_latticeSig` are about the literal matrix `E8lit`. **There is no in-tree
  theorem `E8lit = CartanMatrix.E₈`**, so the two developments are not linked: the
  declarations are true, kernel-checkable in principle, and not on the chain they were
  offered for. No vacuity predicate catches this, because relevance is a property of the
  path from the cited declaration to the claim, not of a statement or a witness.
- **Evidence:** verified by the lead 2026-08-15 by direct search over `lean_deps.json` and
  the E8 modules; recorded in the addendum to the finding ADR-016 discharges. D2's three
  `claims` strings now state the disconnection, which fixes the instance and not the class.
- **Expected:** a mechanism that can say whether a declared apex is reachable from the
  bundle's other declared results, or is an island the prose has to bridge in words.
- **Fix:** a graph query over data `bundle_closure.build_closures` already computes — an
  apex whose closure intersects no other apex's closure in the same bundle is off the
  bundle's own chain. Cheap to compute; the design question is what the honest threshold
  is, since a genuinely independent cross-check is legitimately an island (D1 §8.2's
  cross-checks were exactly that). **Specify before building.**
- **Related:** ADR-016 D6; ADR-002 (`native_decide` debt is tracked and does not know the
  declarations are cited as backing).
- **Cache:** N/A.

### 1.5 — 🟡 MINOR — the `LeanProofSubstance` readiness gate is blind to the metadata apex surface

- **Severity:** minor
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && grep -q "apex_theorems" scripts/readiness_gates.py`
  *What it asserts:* that the gate evaluator reads the declared-apex table. Exits 1 at
  HEAD — it reads only formula-grounding edges and prose `\texttt` references.
- **Gate:** LeanProofSubstance
- **Location:** `scripts/readiness_gates.py` — `_eval_lean_proof_substance`
- **Observed:** the gate resolves cited theorems two ways — Formula→`VERIFIED_BY` edges,
  and Lean names extracted from the draft prose — and intersects them with
  `PlaceholderMarker` nodes. `bundle_metadata.json.apex_theorems` is a third citation
  surface it does not read, so a bundle whose only placeholder citation is a declared apex
  passes the gate.
- **Evidence:** measured 2026-08-15. **Latent, not live**: `apex_claims_not_vacuous`
  measures 0 placeholder apexes corpus-wide, so nothing is passing today that should not.
  Filed because the validation check and the readiness gate now disagree about what the
  citation surface is, and the gate is the one a reader treats as the verdict.
- **Expected:** one definition of "cited" across the check layer and the gate layer.
- **Fix:** add the declared-apex table as a third source in `_eval_lean_proof_substance`,
  or record in `VALIDATION_GATE_TOPOLOGY.md` §4 that the gate's population is prose +
  formula edges and that the metadata surface is the check layer's.
- **Related:** ADR-016 D1; the §1.1 finding's "two mechanisms, each sound, and the seam
  between them unasserted".
- **Cache:** N/A.

### 1.6 — 🔴 MAJOR — `NUMERICAL_LITERAL_CEILING` is 25 over its live population after the D2 redraft, and the suite is RED at HEAD

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python -m pytest tests/test_validate_public_surface.py -q -k "ceiling_matches_the_live_population"`
  *What it asserts:* that the inline-numerical-literal population is within its ceiling.
  Exits 1 at HEAD: live 142 (unit-leg 16 + `\times` leg 126) against a ceiling of 117.
- **Gate:** FixPropagation
- **Location:** `src/core/constants.py` — `NUMERICAL_LITERAL_CEILING`;
  `tests/test_validate_public_surface.py::TestNumericalLiteralPopulationComposition`
- **Observed:** a ratchet on inline numerical literals across all paper drafts, exceeded.
- **Evidence:** measured 2026-08-15, and **not caused by this commit** — verified by
  measuring with the ADR-016 changes reverted, and by the fact that ADR-016 touches no
  `.tex`. The D2 Stage-10 redraft (`9e829c07`, merged `e5dea4fb`) is the change that moved
  the population; the ratchet was not re-derived with it.
- **Expected:** either the new literals are traced to their computations (the ratchet's
  purpose) or the ceiling moves with a stated reason and a measurement, in the commit that
  moved the population.
- **Fix:** re-derive per draft, attribute the delta to D2's new prose, then decide. ⚠️ A
  ceiling raised without reading the literals it now admits is the ratchet failing open.
- **Related:** TODO-D37 (the predicate's population composition is pinned by two sibling
  tests, both of which still pass — only the ceiling leg is red).
- **Cache:** N/A.

### 1.7 — 🔴 MAJOR — 30 `Verify:` lines are not runnable commands, and the check written for that is RED at HEAD

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python scripts/validate.py --check review_verify_is_one_command --no-archive`
  *What it asserts:* rule 4 of the review-document marker contract. Exits 1 at HEAD: 30 of
  204 lines violate it.
- **Gate:** FixPropagation
- **Location:** `papers/AutomatedReviews/2026-08-15-d1-stage10-redraft/D1.md`
- **Observed:** every violation is the same shape — a `Verify:` line whose command is
  `uv run python -c "` followed by a Python program containing double quotes, so the
  backtick span closes early and the contract's single-command matcher sees a truncated
  command. `close_finding.py` would run that truncated string under a shell, so all 30
  findings in that document are **stranded**: neither verifiable nor closable except by
  amending it.
- **Evidence:** measured 2026-08-15. **Pre-existing and not caused by this commit** — the
  document is committed at `b3bdbe42` and unmodified in the working tree, and this
  commit's own six `Verify:` lines all pass the same matcher (one of them is a
  `python -c` one-liner written with the quoting the contract requires).
  `review_verify_is_one_command` shipped earlier the same day and recorded its population
  as *"129 `Verify:` lines corpus-wide, 0 violating"*; the corpus has since grown to 204.
- **Expected:** a `Verify:` line is one backticked command that a shell can run verbatim.
- **Fix:** re-quote the 30 lines in `D1.md` — single-quote the Python program, or move the
  probe into a file and call it. The check needs no change; it is doing its job.
- **Related:** the `2026-08-15-verify-contract-unenforced` finding that produced the check.
- **Cache:** N/A.
