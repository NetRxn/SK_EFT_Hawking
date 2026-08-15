---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-15T02:40:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# `validate_review_doc.py` does not enforce the one `Verify:` rule that strands findings

## Summary

**1 MAJOR.** The review-document marker contract has four rules. `validate_review_doc.py`
delegates to the registered checks for severity declaration and finding minting, so
rules 1–3 are enforced. **Rule 4 — `Verify:` is ONE command — is enforced nowhere.**
It is stated in the validator's own docstring and in the `close_finding.py` docstring,
and checked by neither.

The consequence is not cosmetic. `close_finding.py` parses `Verify:` as a single line
and executes it, so a line carrying explanatory prose after the command is not runnable
and the finding **cannot be closed at all** — discovered 2026-08-14 when all seventeen
findings in one review document were unclosable, including four blockers.

---

### 1.1 — 🔴 MAJOR — Rule 4 of the marker contract is stated in two docstrings and enforced by nothing

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python -m pytest tests/test_d5_reviews.py::TestReviewVerifyIsOneCommand -q && uv run python scripts/validate.py --check review_verify_is_one_command`
  *What it asserts:* that the check fires on trailing prose, on a second command, and on an empty walk; stays silent on a correctly-formed line; is red when the defect is seeded into a real review document; and is green over the live corpus. Exits 1 at HEAD.
  ⚠️ **Amended 2026-08-15 — the original asserted EXISTENCE, which is a proxy.** It was
  `hasattr(reviews, 'check_review_verify_is_one_command')`, satisfied by a function that
  returns `passed=True` unconditionally, or by one whose glob matches nothing. Rule 4's
  whole problem was a requirement stated and not enforced; a verify that a stub satisfies
  reproduces that at one remove. Assert what the mechanism RETURNS.
- **Gate:** FixPropagation
- **Location:** `scripts/validate_review_doc.py:43-45` (rule 4, stated), `scripts/close_finding.py` (`_run_verifications`, the consumer), `scripts/validation/checks/reviews.py` (where the check belongs)
- **Observed:** `_REVIEW_DOC_CHECKS = ("review_severity_declared", "review_docs_mint_findings")`.
  Neither examines the shape of a `Verify:` line. A document whose every `Verify:` carries
  trailing prose validates clean.
- **Evidence:** Measured 2026-08-14/15.
  - `papers/AutomatedReviews/2026-08-14-l1-stage13/L1.md` shipped with **17 of 17**
    `Verify:` lines in the form `` `<command>` — <prose> ``. `close_finding.py` refused
    every closure with *"declares a verification command and --verify is a different one"*.
    Four were blockers.
  - Corpus-wide at the time: **106 of 123** `Verify:` lines were clean, so the convention
    is right and one review violated it 17/17 — precisely the authoring-time defect a
    pre-commit validator exists to catch.
  - `validate_review_doc.py` reported that document **✓ satisfies the marker contract**.
- **Expected:** A document that cannot be closed through the sole ledger writer does not
  validate clean.
- **Fix:** Add `check_review_verify_is_one_command` to
  `scripts/validation/checks/reviews.py` and register it in `_REVIEW_DOC_CHECKS`. The
  predicate is the consumer's own parse — a `Verify:` line must be a single backticked
  command with nothing after the closing backtick. ⚠️ **Derive it from `close_finding.py`'s
  parser rather than re-implementing the rule**, or this becomes a second mechanism beside
  the one that matters and drifts from it the first time either changes (`CLAUDE.md` rule 1).
  Ship with a production-seeded test per `CHECK_AUTHORING_GUIDE` §2.4: seed a malformed
  `Verify:` into a real review document and observe red.
- **Blast radius:** measured 2026-08-15 — **0 documents** would newly fail. The 17
  malformed lines were normalised in commit `28379af7`; a corpus sweep for `` ` — `` on
  `Verify:` lines now returns nothing. The check ships green and stays green, which is the
  right time to add a ratchet.
- **Related:** `papers/AutomatedReviews/2026-08-14-accepted-status-unreachable/infra.md` —
  the other half of the closure lifecycle being unreachable. Both edit governed
  machinery and run through the `architecture-change` skill.
- **Cache:** N/A.
