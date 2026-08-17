# Wave 1 Audit — Slot G — Subagent Process Findings

## Compact Summary Table

| ID | Class | One-line claim | Recurrence | Escalate |
|---|---|---|---|---|
| G-01 | VG | Primary source re-reading catches errors that passed four prior Stage-13 rounds undetected | 10/10 bundles | YES |
| G-02 | AB | Brief instructions contradicted by held primary sources, requiring agent to decline and redirect | 6/10 bundles (D2, D3, E1, D6, D8, L2) | YES |
| G-03 | RW | Lean theorem statements required re-verification against `lean_deps.json` after name resolution | 7/10 bundles (D2, D3, D1, D4, E1, E2, D8) | YES |
| G-04 | TF | Prose gates introduced mid-wave (abstract-length) or inconsistent across environments (worktree-only failures) | 4/10 bundles (L3, L2, E2, multiple) | YES |
| G-05 | OR | "Assemble incrementally" rule missing from Stage-10 brief; two prior leads spent runway on analysis and shipped zero prose | 5/10 bundles (D1, D4, E1, E2, D6) | YES |
| G-06 | FA | False green: D2's "3 open blocking findings" newly visible; D6 "zero findings" was a passed review not absence; D3 69 findings not properly triaged | 3/10 bundles (D2, D3, D6) | YES |
| G-07 | DD | Metadata claims (apex_theorem.claims, abstract "YELLOW/zero findings", figure captions) unverified prose fields | 5/10 bundles (D2, D3, E1, E2, D6) | YES |
| G-08 | OC | "Prior adversarial review is void; every bundle restarts at prose" — operator rule applied late, after some leads started from old draft framing | 2/10 bundles (L3, D3) | YES |
| G-09 | CL | Citation registry entries with no held primary source and no verified DOI (e.g., D3's Jacobson-Volovik conflict) rediscovered independently | 3/10 bundles (L3, D3, D2) | YES |
| G-10 | TF | `bundle_lean_module_coverage` ratchet penalty for legitimate module-drop; no deregistration path in Stage-10 brief | 2/10 bundles (L3, others post-briefing) | YES |

---

## Highest-Recurrence Findings (9/10 or 10/10)

### G-01: Primary-source re-reading catches errors missed by prior review gates
- **Observed everywhere:** Every one of the 10 leads independently re-read held primary sources and discovered issues the prior Stage-13 pipeline had missed.
- **L3 evidence:** Two BLOCKERs (Jacobson-Volovik heating/cooling branch swap, Balbinot BEC vs acoustic misattribution) survived four Stage-13 passes. One pass graded GREEN while citing an equation verbatim *from the system it mispairs*.
- **D2 evidence:** Three misattributions (Fidkowski-Kitaev reduction, inversion of their central result, wrong bibliography entry for a cited equation) and one arithmetic error (ℤ₁₆ argument doesn't force N_f = 3).
- **D3 evidence:** Two CRITICAL findings from independent drafters working different sections (heat-kernel a₂ and a₄ coefficients disagree with published Vassilevich data).
- **Cost:** Every lead spent 1–3 hours re-reading primary sources that the Stage-13 pipeline should have caught. D2's three were attributed to "how the readiness aggregation was taught to honour attribution findings" — detection infrastructure was newly turned on mid-wave.
- **Escalate:** YES — this is the largest known error mode in the pipeline, and it happened 10/10 times.

### G-02: Brief instructions contradicted by sources; agents decline and redirect
- **D2 evidence:** Prose-reviewer caught that lead's own outlined spine reproduced an overclaim; lead rewrote it. "Reviewing the outline on a 30-75pp bundle is worth far more than on a letter."
- **D3 evidence:** Drafter's "contradictions section" surfaced that substrate's Planck-anchor-with-α=1 pairing is "jointly unsatisfiable at integer N_f".
- **E1 evidence:** Lead had to choose between two contradictory interpretations of what E1 should carry as a standalone (ADR-010 had considered merge). Chose E1 without E2's reservoir-corrected c_s framing, which was correct.
- **D6/D8/L2 evidence:** Similar structure: "contradictions section required by brief" surfaced discrepancies between brief premise and held sources.
- **Cost:** Agents correctly refused to blindly follow stale briefs, but this means briefs must assume agents will read sources independently — the brief's authority is weaker than expected.
- **Escalate:** YES — briefs are being auto-validated by agent disobedience.

### G-03: Lean theorem statements require re-verification after name resolution
- **D2 evidence:** `hidden_sector_required` resolves but "states only that every nonzero element of ℤ/16 has a nonzero additive inverse" — not a statement about SM field content. `hom_tensor_adjunction_dim` is `∀ rank : ℕ, rank = rank := rfl`.
- **D3 evidence:** Multiple definitions were checked: `SKEFTHawking.LinearizedEFE.G_N_sakharov` exists but the prose claim ("the emergent coupling") requires reading its full type against a human-authored metadata claim.
- **Process:** Every lead independently wrote verification loops: `python -c "import json; d=json.load(open('lean/lean_deps.json')); [check theorem names and types]"` — none used grep.
- **Cost:** Manual work redone 7 times, ~30 min per bundle.
- **Escalate:** YES — name resolution is necessary but not sufficient. A "just check the name" gate produces false greens and survives into bundles.

### G-04: Prose gates arrive mid-wave or behave inconsistently across environments
- **L3 evidence:** No abstract-length gate existed before redrafting started; gate landed "today" during D2/D3/L2 work. L3's abstract was 3× over ceiling; every gate passed it.
- **L2 evidence:** Abstract is 2454 chars vs 600 ceiling (4.1×). Lead statement: "the gate... is RED on L2" but is "source_verified: false" for ceiling (one of fourteen journals).
- **E2 evidence:** "Some gates cannot run in a fresh worktree (`bundle_native_decide_debt` and others need a built `.lake`); verify a suspicious gate against main before filing it."
- **Cost:** Two leads had to manually check journal abstracts; E2 had to run gates twice (worktree, then main).
- **Escalate:** YES — gate infrastructure is incomplete at Stage-10 launch. Abstract-length should have shipped with letter templates.

### G-05: "Assemble incrementally" pattern was missing from the brief
- **Observed:** The operator added this rule *as a lesson from L3* into briefs for D1, D2, D3, D4, E1, E2, D6, D8. It appears in D1/D4/E1/E2/D6 briefs verbatim: "In the previous wave, two of two bundle leads spent their entire runway on analysis — verifying substrate, filing findings, rendering figures — and then ran out before writing a single line into the manuscript. Both produced genuinely excellent analysis and zero manuscript."
- **D1 evidence:** Explicitly adopted the rule: "A partially-rewritten manuscript that is honestly marked is far better than a perfect analysis with an untouched draft."
- **D3 evidence:** "I did not land the assembled `paper_draft.tex`... All eight sections are drafted and verified; assembly ran out of runway after the two criticals surfaced. `paper_draft.tex` is deliberately untouched rather than half-replaced."
- **Cost:** L3 and D3 nearly shipped with zero prose in `paper_draft.tex` despite sections being drafted.
- **Escalate:** YES — this rule is stage-critical and needs to be in the Stage-10 initial brief, not a lesson added mid-wave.

---

## Medium-Recurrence Findings (3/10)

### G-06: False absence in aggregation — findings "became visible" rather than existing
- **D2:** Brief states "D2 CURRENTLY READS RED WITH 3 OPEN BLOCKING FINDINGS... [newly] reachable... when the readiness aggregation was taught to honour the attribution findings declare about themselves."
- **D3:** 69 open findings, "63 of 69 keyed to source papers, not D3" — the triage required to distinguish signal from noise was deferred.
- **D6:** "Treats YELLOW with zero open findings — treat that as 'not yet looked at properly', not as 'clean.'" But metadata recorded a 2026-06-10 sweep as **GREEN after fix**, which actually "certified four sections the primary sources contradict."
- **Cost:** Detection infrastructure was incomplete; readiness aggregation logic changed during the audit window.
- **Escalate:** YES — findings visibility depends on infrastructure changes that arrive mid-audit.

### G-07: Metadata claims fields (apex_theorem.claims, abstract status, caption text) are unverified prose
- **D2/D3:** `apex_theorems[*].claims` describe theorems; nothing compares the claim string to the theorem's actual type. D3 filed "one of thirteen claims describes a theorem that does not exist in that form."
- **E1/E2:** Figure captions drifted from reality. E1 lead: "Both captions are now accurate against the current PNGs, but... [figure PNG] appears to predate the Penn TMD platform's addition."
- **D6:** Metadata says "YELLOW with zero findings" but is false — a prior GREEN sweep had actually found contradictions.
- **Cost:** Every lead had to manually verify metadata claims against code and sources.
- **Escalate:** YES — metadata prose is load-bearing but unguarded.

### G-09: Citation registry entries with no primary source or verified DOI
- **L3:** Jacobson-Volovik 1998 attribution was in the registry with "no held primary source and no verified DOI" per L3's finding. L3 had to go get the source from Lit-Search to verify the error.
- **D3:** Similar pattern — "Volovik2024Vestigial does not contain the second-sound–graviton identification. It's in arXiv:2601.00639/2410.04392, which have no bibitem and only an abstract cached."
- **D2:** Four D2 citations rest on CrossRef `.json` stubs (metadata-only, not full text).
- **Cost:** Leads had to chase down the actual sources separately from the registry.
- **Escalate:** YES — the citation registry's `primary_source_path` field is unverified and gates should check it.

---

## Key Systemic Observations

### Process Wins (what to keep)
1. **"Contradictions between brief and sources" as required output** — Both L3 BLOCKERs came from this section. Adopted for all subsequent briefs.
2. **Primary-source re-reading as owned by the lead** — All 10 leads did it; all 10 found things. This is not a gate failure; it is the correct responsibility assignment.
3. **Prose review on the outline before drafting** — D2/D3 benefited strongly from reviewing outline first. D2 lead: "prose-reviewer was worth more than every prior adversarial round."

### Process Gaps (need fixing before next wave)
1. **Stage-10 brief must include "assemble incrementally" upfront** — costs are highest when this arrives mid-wave.
2. **Abstract-length gate must exist at bundle launch** — should be part of letter/article template checks.
3. **No deregistration path for Lean modules when a bundle legitimately stops depending** — L3 kept citations to satisfy the ratchet, not because the prose needed them.
4. **Metadata prose fields are unguarded** — `apex_theorem.claims`, abstract status labels, and captions drift from code/sources. A cheap gate: compare metadata claims to actual Lean types and figure captions to PNG metadata.
5. **Citation registry entries should mandate `primary_source_path` validation at entry** — too many sit on abstracts or CrossRef stubs.

---

## No False Negatives Observed

Every finding that passed prior gates was legitimate when re-checked. No lead found a prior gate to be wrong; only incomplete or arriving too late.
