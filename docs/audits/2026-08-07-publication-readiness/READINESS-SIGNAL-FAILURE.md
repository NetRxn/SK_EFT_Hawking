# Why GREEN means unreviewed

**Read this before quoting any bundle's readiness verdict.**

---

## 1. The mechanism

`readiness` is GREEN iff **0 blockers** AND **≤5 advisories** AND **a recorded Stage-13 review**.
`blockers_open` is derived from `ReviewFinding` graph nodes. `ReviewFinding` nodes are minted by
reviews. Therefore:

> A bundle that has never been reviewed has no findings, no blockers, and qualifies for GREEN.

The formula rewards the absence of the very evidence it is meant to summarise. Every term is
individually correct; composed, they invert.

## 2. The measurement

Sentence-level review depth against readiness verdict, all 21 bundles:

| bundle | readiness | blockers | sentences reviewed |
|---|---|---:|---:|
| D9 | **GREEN** | 0 | **0** |
| D8 | YELLOW | 0 | 84 |
| E2 | YELLOW | 0 | 56 |
| D10 | YELLOW | 0 | 14 |
| D6 | YELLOW | 0 | **0** |
| I1 | RED | 16 | 290 |
| D12 | RED | 46 | 179 |
| D11 | RED | 23 | 169 |
| I2 | RED | 19 | 142 |
| D2 | RED | 19 | 72 |
| L1 | RED | 2 | 69 |
| L3 | RED | 6 | 58 |
| D7 | RED | 12 | 36 |
| D4 | RED | 1 | 34 |
| E1 | RED | 5 | 28 |
| D5 | RED | 17 | 16 |
| L2 | RED | 16 | 16 |
| D1 | RED | 37 | 14 |
| D3 | RED | 7 | 8 |
| I3 | RED | 16 | 2 |
| F | RED | 23 | 0 |

Non-RED bundles average **31** sentences reviewed; RED bundles average **71**.

⚠️ **F is the instructive exception**: RED with 23 blockers and 0 sentences reviewed. Its
blockers were minted by review *documents* (`review_docs_mint_findings`), not by the
sentence-level claims reviewer. So the two finding channels are independent, and a bundle can be
RED through one while invisible to the other. Do not read "0 sentences reviewed" as "no findings
possible."

## 3. Why nothing catches it

Three verified gaps, each sufficient on its own.

**3.1 No code path writes a `stage*_status` of `"green"`.**
Every assignment across `scripts/` sets `"pending"`: `bundle_source_manifest.py:129-131`
initialises three fields to `"pending"`; `bundle_append.py:320-325` *demotes* green to
`"pending"` when new content lands. **Every green in the corpus is a hand edit.**

**3.2 The "Stages 9 and 10 before 13" rule has no enforcement point.**
`BUNDLE_LIFT_PROCEDURE.md` §10 states it as a hard pre-condition. No check reads the fields to
gate on them — `bundle_append.py` reads them only to demote. Observable consequence: D6 and D7
sit at `stage13_status: green` with `stage9_status: not_started`.

**3.3 The Stage-13 record does not distinguish review kinds.**
`last_stage13_review` and `stage13_review_doc` accept any document. D9's points at
`docs/audits/stage13_attribution_sweep_2026-06-10.md` — a 16-anchor *attribution* sweep, not an
adversarial review. The field cannot express the difference, so a targeted sweep and a full
adversarial pass are indistinguishable downstream.

## 4. Corroborating artifacts

`audit_log.jsonl` is **0 bytes** in D6, D8, D9, D10 and F. Four of the five non-RED bundles are
in that set. `claims_review.json` is **absent entirely** in D6 and D9 — the two bundles carrying
the portfolio's best verdicts.

D9's own `bundle_metadata.json` `notes` field contains both states in one string:

> `stage13_redo_required=true: never reviewed; Stage 9/10/13 pending the reviewer triple.`
> `| 2026-06-10 attribution-content sweep (...): GREEN.`

while the structured fields read `stage13_status: green`, `stage13_redo_required: false`,
`stage10_status: pending`, `last_stage10_review: None`.

## 5. What this invalidates

- **Any portfolio decision taken on readiness verdicts.** The verdicts rank bundles roughly by
  inverse review effort.
- **"Zero blockers" as evidence of quality**, for D6, D8, D9, D10 specifically.
- **Stage-13 completion counts.** 19 of 21 bundles are marked `stage13: green`; the field is
  hand-set, unenforced, and cannot distinguish a sweep from an adversarial review.

## 6. Remediation — NOT built (per audit constraint)

Filed for `ARCHITECTURE_TODOs.MD`:

1. **`readiness` must distinguish *no findings* from *not measured*.** The `measured` field
   already exists on `CheckResult` for exactly this at the check layer (ADR-009 D2); the bundle
   layer has no equivalent. A bundle with no `claims_review.json` should be UNMEASURED, never
   GREEN.
2. **A check asserting every bundle has a `claims_review.json` with a non-trivial sentence
   count.** Currently nothing notices its absence.
3. **An enforcement point for Stage-9/10-before-13**, or an explicit decision that the rule is
   advisory — it is currently stated as hard and enforced nowhere.
4. **`stage13_review_doc` must record the review KIND.** A sweep and an adversarial pass must not
   be interchangeable.
5. **Writers for `stage*_status`.** Either the reviewer agents gain a write path, or the fields
   are removed. A field only ever set by hand and never read as a gate is decoration.
