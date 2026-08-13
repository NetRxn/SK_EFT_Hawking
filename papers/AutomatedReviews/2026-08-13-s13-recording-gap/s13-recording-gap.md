# The Stage-13 review-kind recording gap — 2026-08-13

**Found by** the ADR-012 P9b Flow board, on its first run over the live roster.

**What it is.** `stage13_review_kind` is absent from **all 21** `bundle_metadata.json` files.
Only `full-adversarial` earns a GREEN readiness verdict (`_KINDS_SUFFICIENT_FOR_GREEN`), so
**no bundle can reach Stage-13 green today regardless of its `stage13_status`.** Every S13
cell on the board reads non-green for a reason that is not "the review failed".

⚠️ **This is a RECORDING gap, not 21 failed reviews, and the distinction is the finding.**
20 of the 21 bundles have genuine Stage-13 review evidence on disk. What is missing is a
record of *what kind* of review it was.

**The asymmetry that caused it, measured.** `resolve_stage13_reviews` has an evidence-based
fallback for the review **date** — `find_stage13_review_evidence` walks
`papers/AutomatedReviews/`, and `backfill=True` writes the date back with an audit note,
"evidence-based backfill only — never fabricated". Its sibling field has **no such path**:
`kind` is read from metadata and from nowhere else. So a bundle reviewed before
`record_review.py` existed can prove *when* it was reviewed and can never prove *what kind*.

## Measured population

| | count |
|---|---|
| bundles carrying `stage13_review_kind` in metadata | **0 of 21** |
| bundles with Stage-13 evidence on disk | **20 of 21** |
| …whose evidence document **declares** a kind in its front matter | **2** |
| …declaring `full-adversarial` | **1** (I1) |
| …declaring `adjudication` — **not in the accepted vocabulary** | **1** |
| …with evidence but **no declared kind** | **18** |
| bundles with no evidence at all | **1** |

Accepted kinds: `full-adversarial` · `attribution-sweep` · `section-scoped` · `figure-only`.

---

## Findings

### 1 — 🔵 The Stage-13 kind has no evidence path, while its sibling date does

- **Severity:** minor
- **Lane:** infra
- **Gate:** `bundle_stage13_claim_consistent`
- **Location:** `scripts/bundle_readiness.py:279`
- **Observed:** `rec["kind"] = md.get("stage13_review_kind")` is the only assignment. When
  metadata carries no kind — all 21 bundles — the resolver reports `None`, which the
  readiness layer treats identically to "no review of a sufficient kind". The date resolves
  through a documented evidence fallback three lines below; the kind does not.
- **Evidence:** measured across the roster, table above. `find_stage13_review_evidence`
  returns a document for 20 of 21 bundles, and two of those documents declare their own kind
  in front matter (`kind: full-adversarial`, `kind: adjudication`).
- **Expected:** a declared kind in the evidence document is usable, on the same
  "evidence-based only, never fabricated" terms the date backfill already states.
- **Fix:** read `kind:` from the evidence document's front matter as a fallback. ⚠️ **A
  DIRECTORY NAME IS NOT A KIND.** `…-bundle-stage13/` says the pass was bundle-level; it does
  not say whether it was full-adversarial or a scoped sweep. Mapping the directory to
  `full-adversarial` would manufacture the exact evidence the P1 gate exists to demand, for
  18 bundles at once. The 18 stay unknown.
- **Verify:** `uv run python scripts/validate.py --check bundle_stage13_claim_consistent`

### 2 — 🔵 "Reviewed, kind unrecorded" is indistinguishable from "never reviewed"

- **Severity:** minor
- **Lane:** infra
- **Gate:** `bundle_stage13_claim_consistent`
- **Location:** `scripts/bundle_readiness.py:437`
- **Observed:** `readiness == "GREEN" and review_kind not in _KINDS_SUFFICIENT_FOR_GREEN`
  collapses two states into one `UNMEASURED`: a bundle nobody has reviewed, and a bundle
  reviewed with the kind never written down. The reader cannot tell which, and the remedy
  differs completely — one needs a review, the other needs a record.
- **Evidence:** the display string names `review_kind or 'unrecorded'`, so the information
  exists at render time and is discarded at decision time.
- **Expected:** three states, not two, the way `release_condition_met` already returns
  three and `CheckResult.measured` distinguishes did-not-measure from measured-and-failed.
- **Fix:** carry an explicit `kind_evidence` alongside `kind` so a caller can distinguish
  *unreviewed* from *reviewed-kind-unknown*. Neither earns green; only one is a review
  backlog item.
- **Verify:** `uv run python -m pytest tests/test_d5_bundles_readiness.py -k stage13 -q`

### 3 — 🔵 A review document declares a kind outside the accepted vocabulary

- **Severity:** minor
- **Lane:** prose
- **Gate:** `bundle_stage13_claim_consistent`
- **Location:** `papers/AutomatedReviews/`
- **Observed:** one bundle's newest evidence declares `kind: adjudication`, which is not one
  of the four accepted kinds. Nothing validates the token, because nothing reads it.
- **Evidence:** measured across all 20 evidence documents; exactly one carries it.
- **Expected:** an unrecognised kind is **preserved verbatim and never coerced**, on the same
  rule the bundle status enum follows — `BUNDLE_READINESS_HEATMAP` surfaces non-enum values
  as themselves rather than rounding them to the nearest known state.
- **Fix:** preserve it and report it as undeclared. Do not silently map it to a neighbour,
  and do not drop it — either would lose the fact that a reviewer used a word the system
  does not know.
- **Verify:** `uv run python -m pytest tests/test_d5_bundles_readiness.py -k stage13_kind -q`
