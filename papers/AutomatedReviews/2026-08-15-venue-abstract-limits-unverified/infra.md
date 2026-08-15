---
paper: infra
bundle: infra
bundle_target: infra
tier: 0
reviewer: lead
model: claude-opus-5
review_date: 2026-08-15T00:00:00Z
readiness_gates_version: 1
kind: infra-finding
prior_reviews:
  - papers/AutomatedReviews/2026-08-15-l3-stage10-redraft/L3.md#51
---

# infra — the abstract gate's venue ceilings are declared but not primary-sourced

## Summary

**1 REQUIRED.** `bundle_abstract_length` shipped 2026-08-15 (ADR-015 D2) and is RED on
four bundles. The gate is correct and the failures are real — L1, L2, E1 and E2 are
3.1x, 4.1x, 3.2x and 3.6x their declared ceiling. What is *not* established is the
ceiling itself: no venue's abstract limit in this repo has been confirmed against its
primary author guide, because every relevant publisher blocks automated retrieval.

---

## Findings

### 1.1 — 🟡 REQUIRED — Every declared `abstract_ceiling` is UNVERIFIED against its primary author guide

- **Severity:** required
- **Lane:** `research`
- **Verify:** `cd "$REPO" && uv run python -c "import json,glob,os; bad=[os.path.basename(os.path.dirname(p)) for p in glob.glob('papers/*/bundle_metadata.json') if ((json.load(open(p)).get('length_target') or {}).get('abstract_ceiling') or {}) and not ((json.load(open(p))['length_target']['abstract_ceiling']).get('source_verified')); assert not bad, bad"`
  *What it asserts:* asserts no bundle carries an abstract ceiling whose provenance is
  still unconfirmed. Exits 1 at HEAD, naming L1, L2, L3, E1, E2.
- **Gate:** CitationIntegrity
- **Location:** `papers/{L1,L2,L3,E1,E2}/bundle_metadata.json`
  (`length_target.abstract_ceiling.source_verified: false`);
  `scripts/validation/checks/bundles_readiness.py` (`check_bundle_abstract_length`);
  `docs/adrs/ADR-015-redraft-safe-bundle-gates.md` §D2
- **Observed:** The five letter bundles declare `abstract_ceiling: {unit: characters,
  ceiling: 600}`, sourced to the PRL author guide. The check prints the unverified
  provenance on every run, including a passing one, so no green here can be read as
  "confirmed venue-conformant". Sixteen bundles declare no ceiling at all and are
  reported UNMEASURED by name.
- **Evidence:** A `research-scout` pass over fourteen journals on 2026-08-15 returned
  exactly **one** primary-verified answer. `journals.aps.org/robots.txt` — which itself
  loaded — disallows automated agents, so all six Physical Review titles return 403;
  ScienceDirect (CPC, Physics Reports) and AIP (J. Chem. Phys.) return 403 to every
  request including `robots.txt`; Springer (JHEP, Comm. Math. Phys., Living Reviews)
  redirects to a login wall; `quantum-journal.org` and `jhep.sissa.it` are outside the
  egress whitelist. The one verified result is JOSS
  (`https://joss.readthedocs.io/en/latest/paper.html`): it states **no separate abstract
  limit**, only "The paper should be between 750-1750 words." The scout also flagged that
  the "150-250 words" figure surfaced by search for BOTH Comm. Math. Phys. and Living
  Reviews in Relativity shows signs of search-engine cross-contamination between the two,
  and should not be trusted for either.
- **Expected:** Each declared `abstract_ceiling` carries `source_verified: true` and a
  quoted sentence from the venue's own author guide; each venue with no published limit
  is recorded as such rather than left undeclared.
- **Fix:** Operator or a human-run deep-research pass confirms the fourteen venues
  against their author guides — this needs an access path the sandboxed scout does not
  have, which is why it is filed rather than retried. Then set `source_verified: true`
  with the quote in `source`, and declare a ceiling (or an explicit "no published limit")
  for the sixteen currently-unmeasured bundles.
- **Priority note:** This does NOT block the redraft campaign. The four failing bundles
  are 3-4x over; no plausible correction to a ~600 figure changes any live verdict. What
  it blocks is treating a *pass* as venue conformance.
- **Cache:** N/A — the primary sources are unreachable by this toolchain, which is the
  finding.
