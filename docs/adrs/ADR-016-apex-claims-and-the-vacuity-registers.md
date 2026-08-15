# ADR-016 — The apex `claims` surface meets the vacuity registers

**Status:** Accepted · **Date:** 2026-08-15 · **Lane:** `infra`

**Supersedes nothing. Extends** ADR-015 D3 (which introduced `apex_theorem_claims_grounded`
and states in its own docstring that theorem SUBSTANCE is out of its scope), ADR-004
(substrate integrity gates — the vacuity registers and their guards) and ADR-010 §Open
(`bundle_apex_resolves`, the apex-name resolver).

**Discharges** `papers/AutomatedReviews/2026-08-15-baselined-vacuous-theorems-may-be-cited/infra.md`
§1.1 and §1.2, and scopes the third axis its addendum identifies.

---

## Context

`papers/<BUNDLE>/bundle_metadata.json` declares `apex_theorems[]`, each with a `claims`
string saying what the theorem establishes. Three mechanisms read parts of that structure
and none reads this one:

* `bundle_apex_resolves` reads the **name** — does it resolve, is it a theorem.
* `apex_theorem_claims_grounded` (ADR-015 D3, shipped earlier the same day) reads the
  **claims string** for three decidable properties: present, not a restatement of the
  theorem's own name, numerals present in the statement. Its docstring names substance as
  explicitly out of scope: *"that the theorem is SUBSTANTIVE. `vacuous_statement_audit`
  owns that."*
* `placeholder_not_cited` enforces Invariant #9 — a placeholder theorem must not be cited
  as verified — over **paper draft prose**, in a window around a verification-claim phrase,
  with a hedge escape.

The seam none of them covers: **a `claims` string is a bare, unhedged assertion of physics
content, sitting beside a Lean name, in a file no vacuity guard reads.** `vacuous_statement_audit`
knows which declarations are content-free and does not know they are cited; the metadata
knows what is cited and does not know it is content-free.

The registers the project maintains, and what each is blind to:

| register | populated by | guarded by | blind to |
|---|---|---|---|
| `PLACEHOLDER_THEOREMS` | literal `True := trivial` | `placeholder_not_cited` (draft prose) | the metadata claim surface |
| `VACUOUS_STATEMENT_BASELINE` | reflexive / tautological statements | nothing that connects it to citation | citation of any kind |
| `MODELING_ASSUMPTION_THEOREMS` (`definitional` / `vacuous_proxy`) | disclosed bookkeeping | `disclosure_consistency` (draft prose verbs) | the metadata claim surface |
| trivial witness (`rfl`, `Equiv.refl`, identity-return) | — | `proxy_body_audit`, **name-gated** by `_STRUCTURAL_NAME_RE` | a trivially-witnessed theorem whose NAME is not structural |

The fourth row is the finding's §1.2 and is the largest population measured below: a
declaration is not in any register, its statement is not syntactically thin, and its proof
is `rfl` against a definition that was rigged to make it so. `proxy_body_audit` computes
exactly this and then discards it unless the theorem's *name* matches a structural regex —
a filter that is right for an unsolicited corpus sweep and wrong for a declaration a bundle
has **elected as an apex result**, because the election is what makes the claim.

---

## Measured at HEAD, 2026-08-15

Every figure re-derived from the live artifacts for this ADR. The population is every
declared apex in every bundle that resolves in `lean/lean_deps.json`; the classifiers are
the project's own, reused, not re-implemented.

| what | measured |
|---|---|
| bundles declaring apexes | 21 of 21 |
| resolved apex claims, before this ADR's D2 repair | 639 |
| resolved apex claims, after it | 638 |
| …after E1's Stage-10 redraft merged mid-work (`978aa349`, 7 apexes → 4) | **635** |
| apexes resolving to a `PLACEHOLDER_THEOREMS` declaration | **0** |
| apexes whose statement is `True` or reflexive `X = X`, before the repair | **1** (D2 `hom_tensor_adjunction_dim`) |
| …after it | **0** |
| apexes in `VACUOUS_STATEMENT_BASELINE` | 2 (both D4) |
| apexes disclosed `definitional` / `vacuous_proxy` in `MODELING_ASSUMPTION_THEOREMS` | 5 rows (D5 ×4, F ×1) |
| apexes with a trivial witness (`rfl` / identity-return), name-gate removed | 13 rows |
| apexes whose statement is a closed numeric fact or `R n n` on literals | 3 (D2 ×2, D3 ×1) |
| **distinct flagged apex rows, after the repair** | **20, across 9 of 21 bundles** |
| …of which the bundle's own `claims` string discloses the thinness | 5 |
| …of which it does **not** | **15** |
| bundles with zero flagged apexes | 12 — D6, D7, D9, D11, D12, E1, I1, I2, I3, L1, L2, L3 |

**Per bundle** (flagged / undisclosed): D1 1/1 · D2 2/0 · D3 1/1 · D4 3/1 · D5 9/9 ·
D8 1/1 · D10 1/1 · E2 1/0 · F 1/1.

⚠️ **The population moved WHILE this was being measured**, and that is recorded rather than
smoothed over: the D4 and E1 Stage-10 redrafts merged from concurrent work between the
first measurement and the ceilings being set, and E1's withdrew the one flagged row it
carried. The redraft campaign will keep moving it. That is the ratchet working — a redraft
that withdraws a claim the substrate never supported is the remediation — and every
lowering is expected to name its merge commit and its count, as `APEX_CLAIMS_SCORED_FLOOR`
now does for both.

**The measurement was red on arrival, as the finding predicted**, and D5 carries nine of
the twenty — six `rfl`-witnessed Track-C verdicts and four disclosed-definitional
Track-B counts, all sharing one `claims` string per track that names the track's headline
rather than the declaration's content.

Two figures that are *not* defects and are recorded so nobody re-derives them as such:
`_thin_type_label` reports 148 ground-arithmetic and 40 reflexive statements corpus-wide;
only 3 of those are declared apexes. The corpus population is a different, older question
(`vacuous_statement_audit` owns it); this ADR is about the citation surface.

---

## Decisions

### D1 — The check reads the SEAM, and reuses every classifier rather than re-deriving one

`apex_claims_not_vacuous` (`scripts/validation/checks/bundles_readiness.py`) joins two
things that already exist: the declared-apex table and the vacuity classifiers. It
imports `PLACEHOLDER_LEAN_NAMES`, `VACUOUS_STATEMENT_BASELINE` and
`MODELING_ASSUMPTION_THEOREMS` from `src/core/constants.py`, `_thin_type_label` from
`lean_statements.py`, and `_TRIVIAL_BODY_RES` / `_NONTRIVIAL_MARKER_RE` /
`_scan_lean_theorem_bodies` from `lean_substrate.py` and `build_graph.py`.

It writes **no new register and no new predicate of its own**, which is the whole point:
a fifth vacuity opinion beside four existing ones is the failure `CLAUDE.md` rule 1 names.

⛔ **What it does NOT do, restated so its silence is not over-read.** It does not resolve
apex names (`bundle_apex_resolves` owns that and hard-fails), does not judge whether the
claim *describes* the theorem (ADR-015 D3 established that prose↔type equivalence is not
decidable and this ADR does not revisit it), and does not judge hypothesis parity
(`atlas_hypothesis_discipline`, `claims-reviewer` HD).

### D2 — The name gate comes off for a DECLARED apex, and only for a declared apex

`proxy_body_audit`'s `_STRUCTURAL_NAME_RE` exists because a corpus-wide trivial-body sweep
without it drowns in legitimate `rfl` plumbing. That reasoning does not transfer: an apex
is a declaration a bundle **elected** to present as a result, so the election supplies what
the name filter was standing in for. The name gate is dropped **here** and left in place
**there**; the two checks now measure different populations for a stated reason.

Measured consequence: 13 of the 20 flagged rows are visible only because of this decision.

### D3 — Content-free is classified in FIVE registers, and the fifth is one new label on the SHARED classifier

`_thin_type_label` gains one label, `reflexive-literal (R n n)`: a relation applied to two
identical **numeric literals**, e.g. `Int.instDvd.dvd 8 8` — `dvd_refl 8` wearing a physics
name. It is deliberately **not** in `_THIN_HARD`, so `vacuous_statement_audit` reports it
as advisory rather than hard-failing four declarations it has never seen.

The narrowness is measured, not guessed. `R x x` over a *bound variable* matched 12
declarations, and 8 of them are legitimate reflexivity lemmas (`causal_refl`,
`weldRel_refl`, `WittEquivalent_refl`, `IntCongr.rfl` …) where `∀ a, R a a` is a real
theorem. Restricting to closed literals leaves exactly 4, every one of them vacuous:

| declaration | statement |
|---|---|
| `e8_sigma_div_8` | `(8 : ℤ) ∣ (8 : ℤ)` |
| `serre_mod_8_for_E8` | `(8 : ℤ) ∣ (8 : ℤ)` |
| `constraints_with_nu_R` | `(3 : ℕ) ∣ (3 : ℕ)` |
| `sm_with_nu_R_anomaly_free` | `(16 : ℤ) ∣ (16 : ℤ)` |

The last is the specimen that justifies the label existing: a theorem named *"the Standard
Model with ν_R is anomaly free"* whose entire content is `dvd_refl 16`.

### D4 — Two legs are HARD at zero; the rest are RATCHETS, and a ratchet is not a suppression list

* **HARD, zero, no ceiling constant:** an apex resolving to a `PLACEHOLDER_THEOREMS`
  declaration. This is Invariant #9 carried from draft prose to the metadata surface, and
  it is the finding's §1.1 in its strictest form.
* **HARD, zero, no ceiling constant:** an apex whose statement is `True` or reflexive
  `X = X` (`_THIN_HARD`). Live population 1 before the D2 repair below, 0 after.
* **RATCHET `APEX_UNDISCLOSED_VACUITY_CEILING = 15`:** a flagged apex whose own `claims`
  string does not disclose the thinness.
* **RATCHET `APEX_VACUITY_CEILING = 20`:** flagged apexes in total, so that disclosing one
  never becomes room to add another.
* **FLOOR:** the scored population, sharing ADR-015 D3's `APEX_CLAIMS_SCORED_FLOOR` rather
  than introducing a second floor over the identical set.

⚠️ **The distinction the finding is emphatic about, and why these ceilings do not violate
it.** A *suppression list* takes a named declaration out of a detector's population — that
is what `VACUOUS_STATEMENT_BASELINE` does, and adding this measurement to it would convert
a detection into a permission. These ceilings remove nothing from any population: every
flagged row is re-derived and **printed by name on every run**, the counts may only fall,
and no per-declaration exemption key exists to grant. What the ceilings buy is the property
the finding actually asked for — the number cannot grow while the twenty are remediated
bundle by bundle.

### D5 — The escape from the ratchet is DISCLOSURE IN THE CLAIMS STRING, not an exemption

A bundle may keep a content-thin apex by saying so in the `claims` string a referee reads —
the same posture as `MODELING_ASSUMPTION_THEOREMS` (`reason` + `discloses`) and
`bundle_native_decide_debt`'s disclosure leg. Disclosure moves a row out of the undisclosed
ratchet and **not** out of the total ratchet, so it is a way to be honest, never a way to be
quiet.

Measured: 5 of 20 rows already disclose, three of them written by drafters without any check
asking for it (D4 ×2 — *"⚠️ DEFINITIONAL ENCODING … an `rfl` sanity-check"*; E2 —
*"disclosed as a rfl-discharge with the substantive content upstream"*). The convention
existed before the guard; this decision makes it the guard's own escape hatch.

### D6 — The SOUND-BUT-IRRELEVANT axis is explicitly OUT OF SCOPE, and named

The finding's addendum identifies a fourth axis: a citation can be defective by being
**true, kernel-checked and not on the path to the claim it is offered for**. Its live
instance is D2's `e8_det_one` / `e8_diagonal_all_two` / `e8_diagonal_even`, proved by
`native_decide` against Mathlib's `CartanMatrix.E₈`, while the theorems that actually carry
`eight_dvd_latticeSig` are about the literal matrix `E8lit` — and **there is no in-tree
theorem `E8lit = CartanMatrix.E₈`**, verified by direct search, so the two developments are
not linked at all.

**No vacuity predicate catches this, and this ADR does not pretend one could.** Relevance
is a property of the *path from the cited declaration to the claim*, which is a graph
question over the apex closure, not a property of a statement or a witness. It is
**deliberately not folded in**, because folding it in would mean widening "content-free" to
mean "not useful here", which would make every ratchet above uninterpretable.

What ships instead: the D2 metadata now *states* the disconnection in the three `claims`
strings, and the general mechanism is filed as
`papers/AutomatedReviews/2026-08-15-apex-claims-unbacked/infra.md` §1.4, with a `Verify`
that fails at HEAD. The sketch there — an apex whose statement shares no project
declaration with any other apex of the same bundle is off the bundle's own chain — is a
graph query over data the closure builder already computes.

### D7 — D2's metadata is repaired in this commit, because it is measured and merged

D2's Stage-10 redraft landed at `e5dea4fb` and cites **none** of the declarations below
(verified: zero occurrences of each name in `papers/D2/paper_draft.tex`). The prose was
disarmed and the metadata was not, so a later bundle lift reading `claims` would regenerate
the overclaim verbatim. Repairs, all of them *corrections of false statements about what
exists* rather than reclassifications:

| declaration | before | after |
|---|---|---|
| `hom_tensor_adjunction_dim` | *"substantively discharging hypothesis H2"* | **apex entry removed** — statement is `∀ rank : ℕ, rank = rank`, and the module's own docstring records H2 as OPEN |
| `e8_sigma_div_8` | *"σ(E8) = 8; the same 8 as the Witten ℤ₂"* | states the type is `(8:ℤ) ∣ (8:ℤ)` and carries neither |
| `char_sq_valid_e8` | *"validity of the characteristic-square pairing"* | states it evaluates `selfPairing` at the zero vector |
| `rokhlin_gap` | *"the structural gap"* | states the type is closed arithmetic on 16, 2, 8 |
| `FK.spectral_gap` | *"the Fidkowski–Kitaev eight-Majorana spectral gap"* | states the complete type is `0 − (−14) = 14` |
| `constraints_without_nu_R` | *"lcm(16,3) = 48 … forces N_f ∈ 48ℤ"* | **retraction recorded**: `3 ∣ N_f` already follows from the sixteen-component spectrum and at fifteen components modular invariance gives `16 ∣ N_f` — the ℤ₁₆ condition itself — so the minimum is 16 and each condition excludes `N_f = 3` alone |
| `e8_det_one`, `e8_diagonal_all_two`, `e8_diagonal_even` | unimodularity / evenness *"of E8"* | `native_decide` over `CartanMatrix.E₈`, no `E8lit` bridge, not on the `eight_dvd_latticeSig` chain (D6) |

Also corrected: `stage10_status` `pending` → `pending-redo` (the field was `green` at
`bf153836` and demoted to `pending` by `bundle_append.py`'s green→pending rule at
`14ba438c`; `pending-redo` is the declared value for *a completed stage invalidated by a
later append*, and the full redraft is a stronger invalidation than the append that
demoted it), and `compiled_pages` 11 → **18**, re-derived by running
`scripts/compile_bundle_pdf.py D2 --force` rather than hand-edited — that field has a
single writer and a hand-edit is indistinguishable from a stale one.

Every other bundle's rows are filed, not fixed: they are unmeasured drafts, and repairing a
`claims` string without reading the draft it indexes is how the numbers this ADR reports
would stop meaning anything.

---

## Consequences

* Invariant #9 now binds on two surfaces — draft prose and the bundle metadata claim
  surface — with the metadata surface reading four registers instead of one.
* 15 undisclosed rows across 7 bundles become visible, named on every validation run, and
  cannot grow. They are remediation work owned by
  `papers/AutomatedReviews/2026-08-15-apex-claims-unbacked/infra.md`, per bundle.
* `vacuous_statement_audit` gains 4 advisory rows from D3's new label and hard-fails on
  none.
* `proxy_body_audit` is unchanged; the two checks now deliberately disagree about the name
  gate, which D2 records.
* `APEX_CLAIMS_SCORED_FLOOR` falls 639 → 638 → 635, the stated reasons being D7's apex
  removal and E1's redraft withdrawing three.
* The sound-but-irrelevant axis stays open and is named as open, in an ADR decision rather
  than in a paragraph a later reader can mistake for coverage.

## Alternatives rejected

* **Extend `placeholder_not_cited`'s population to the union of the registers**, which is
  the finding's own §1.1 fix text. Rejected after measuring what it would do: that check
  scans draft **prose** with a 320-character verification-claim window and a hedge escape,
  so pointing it at `VACUOUS_STATEMENT_BASELINE` would ask a prose-window heuristic to
  adjudicate a structured field that has no window and no hedge. The union of registers is
  the right idea and the metadata table is the right surface for it.
* **Add the 21 rows to `VACUOUS_STATEMENT_BASELINE`.** This is the move the finding names
  as the way its own gap arose. Refused.
* **Make the trivial-witness leg hard-fail.** It would be red for as long as the nine D5
  rows take to remediate, and a permanently red gate is a gate people learn to route
  around.
* **Put the reflexive-literal label in `_THIN_HARD`.** It would hard-fail four
  declarations with no repair available except baselining them, i.e. it would manufacture
  the exact pressure this ADR refuses.
* **A per-declaration allow-list with dispositions**, in the shape of
  `SIMP_PROJECTION_ALLOWLIST`. Rejected as the suppression shape D4 forbids; the identity
  information it would carry is already printed on every run.
