---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-15T04:10:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# A ledger record with `status: "open"` makes its finding permanently unclosable

## Summary

**1 MAJOR.** `close_finding.py` refuses to write when a prior ledger record carries a
*different* status — correctly, because the reader is last-wins and a silent second
record is the defect the writer exists to prevent. But the guard has no exception for
`status: "open"`, and an `open` record is **inert**: findings are born `open`
(`build_graph.py` BIRTH-STATUS INVARIANT), so such a record asserts nothing and closes
nothing. It exists only as bookkeeping.

The result is that the *presence of a record that does nothing* makes the finding
impossible to close through its sole writer. There is no amend path, and the refusal
message's advice — "amend the existing record deliberately instead" — names an operation
the tool does not offer. The only route left is hand-editing the ledger, which is exactly
what this writer was built to eliminate.

Measured at HEAD 2026-08-15: **10 findings carry an inert `open` record**, of which
**5 are open BLOCKING findings on the 21 submission bundles** — and at least two of those
five have been independently verified as remediated and are being held open solely by this
guard.

---

### 1.1 — 🔴 MAJOR — `_guard_prior` treats an inert `open` record as a conflicting status

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python -m pytest tests/test_close_finding.py::TestAnInertOpenRecordDoesNotBlockClosure -q`
  *What it asserts:* that a closure with an inert `open` prior succeeds, records `supersedes_inert_open`, and that an `accepted` prior and a below-the-bar `fixed` prior are both STILL refused. Exits 1 at HEAD.
  ⚠️ **Amended 2026-08-15 — the original command asserted a PROXY for its own purpose.** It
  was `assert 'open' in ast.dump(_guard_prior)`, which the function's *docstring* already
  satisfied: it could pass over a guard that still refused every inert record, and it said
  nothing at all about the neighbouring refusals the fix must not widen. Assert what the
  mechanism RETURNS, not what its source contains — the same defect class as
  `2026-08-15-textbook-exemption-rewards-absent-metadata` and the `\bibitem`-as-proxy
  defect retired in `d39d2ffb`.
- **Gate:** FixPropagation
- **Location:** `scripts/close_finding.py` — `_guard_prior` (the `prior_status != status` branch) and `_plan`
- **Observed:** Closing `review:2026-05-01-L3-bundle-stage13:L3:6.1` — a BLOCKER whose defect is
  demonstrably remediated (`papers/L3/paper_draft.tex:246` now states Israel's third law the right
  way round) — is refused because a 2026-05-01 record carries `{"status": "open"}` with the
  finding's original description as its evidence.
- **Evidence:** Measured 2026-08-15 over `docs/review_finding_supersessions.json`:
  - 10 finding ids whose last record is `status: "open"`.
  - 5 of them are open blocking findings on the 21 bundles:
    `2026-05-01-1500…:I1:5.1`, `2026-05-01-L3…:L3:6.1`, `2026-07-31-1524…:D12:8.2`,
    `2026-07-31-1530…:D11:4.1`, `2026-07-31-2220…:D12:2.2`.
  - `D12:8.2` and `D12:2.2` were adjudicated STALE with passing verify commands in this same
    session and could not be recorded.
  - `build_graph.py` births every finding `open`, so none of these records changes any
    reader's answer.
- **Expected:** An inert `open` prior does not block a closure. A genuinely conflicting
  prior (`fixed` vs `accepted`, or a closure being reversed) still refuses.
- **Fix:** In `_guard_prior`, treat `prior_status == "open"` as absent — fall through to the
  normal write, and record in the new closure that it supersedes an inert `open` record so
  the history stays legible. ⚠️ Do **not** widen the guard generally: the `fixed`↔`accepted`
  refusal and the below-the-bar-`fixed` refusal are both load-bearing and were each written
  to close a real defect. Ship with a production-seeded test per `CHECK_AUTHORING_GUIDE`
  §2.4: seed an inert `open` record for a real finding, observe the closure succeed, then
  seed a `fixed` record and observe it still refuse.
- **Related:** this is the third closure-lifecycle gap found in one day, alongside
  `2026-08-14-accepted-status-unreachable` (fixed, `cc260834`) and
  `2026-08-15-verify-contract-unenforced`. All three share a shape: **the writer is strict
  in the right direction but has no path for a legitimate exception**, so real remediation
  sits unrecorded and the corpus reads worse than it is.
- **Cache:** N/A.
