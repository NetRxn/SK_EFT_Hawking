---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-15T23:30:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# The D6/D9 merge decision rests on a number whose POPULATION is never stated

## Summary

**1 MAJOR.** ADR-010 proposes consolidating the roster 21 → 16, and names the D6/D9 overlap as
its strongest evidence: *"D6 ∩ D9 = 78 theorems … the merge case for D6+D9 is real and is the
strongest single result in this pass."*

D6's Stage-10 redraft re-measured and reported **0 declarations, 0 theorems, 0 shared modules,
Jaccard 0.000**, concluding the merge case is dead.

**Neither number refutes the other, because they measure different populations, and no document
states which population the merge decision is supposed to turn on.**

### What I measured, 2026-08-15

| population | D6 | D9 | shared |
|---|---|---|---|
| declared `apex_theorems` (bundle_metadata.json) | 23 | 27 | **0** |
| manuscript refs via `\texttt` + `\thm` | 16 | 4 | 3 (axiom names only) |
| manuscript refs via `\verb` + `\texttt` + `\thm` | 52 (pre-redraft) | 4 | 3 (axiom names only) |
| ADR-010 audit, "resolved declaration references" | 175 | 169 | **78 theorems** |

**D9's manuscript contains 15 `\texttt{}` spans in total.** 169 resolved references cannot come
from its prose. So the audit's figure is a **closure-level** measurement — declarations reachable
from what each bundle names — while D6's redraft measured the **apex set**, and my first pass
measured **literal prose references**. Three levels, three answers, all internally correct.

### ⚠️ This exact claim has now defeated three separate measurers

`MEASUREMENTS.md` §M4(a) records the audit's own near-miss: *"My first measurement of this
returned ZERO, and I nearly filed 'the audit is wrong.' D6 writes its references as `\verb`, which
my extractor did not read."* Fixed in `c5f384b4`; the corrected pass produced 78.

Measuring it again today I reproduced that blind spot **twice in one sitting** — first by reading
`\texttt`/`\thm` and missing `\verb` (D6's style), then, after fixing that, by finding D9 yields
only 4 parseable refs against the audit's 169. A claim that has broken three extractors is not a
claim anyone should re-derive with a fourth ad-hoc one.

### 1.1 — 🔴 MAJOR — a roster decision turns on an unstated population

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && grep -q "population:" docs/audits/2026-08-05-adr010-measurement/MEASUREMENTS.md && grep -A3 "M4(a)" docs/audits/2026-08-05-adr010-measurement/MEASUREMENTS.md | grep -q "apex\|closure\|prose"`
  *What it asserts:* that §M4(a) names the population its 78 is counted over. Exits 1 at HEAD.
- **Gate:** PortfolioCoherence
- **Location:** `docs/adrs/ADR-010-*.md` (the 21→16 recommendation);
  `docs/audits/2026-08-05-adr010-measurement/MEASUREMENTS.md` §M4(a);
  `papers/AutomatedReviews/2026-08-15-d6-stage10-redraft/D6.md` (the counter-measurement)
- **Observed:** §M4(a) reports "resolved declaration references" without defining resolution
  scope. The three natural readings — apex set, prose references, reachable closure — differ by
  two orders of magnitude on this pair.
- **Expected:** the merge decision names its population, and any re-measurement uses the audit's
  own instrument rather than a new extractor.
- **Fix:** ⚠️ **Do NOT correct ADR-010 from either new number.** Re-run the audit's own instrument
  (the one fixed in `c5f384b4`) at HEAD and compare like with like. If the closure-level overlap
  has genuinely collapsed — plausible, since D6's redraft deleted the cross-reference carrying the
  absorbed QuantumNetwork modules — that is a real change and the ADR should record it as such,
  with the population named. If it has not, D6's "do not merge" conclusion is scoped to apexes and
  should say so.
- **Related:** `reference-measurement-traps-false-absence` (narrow alternation; reference ≠ write).
  Same shape as the crossover gate that pinned a wrong formula: an instrument and a claim agreeing
  with each other while neither is checked against the thing being decided.
- **Cache:** N/A.
