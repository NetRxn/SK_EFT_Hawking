---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-15T09:40:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# A closure reported `✓ wrote 1 record(s)` and the record was not in the ledger

## Summary

**1 MAJOR.** `close_finding.py` writes the supersession ledger by
**read-modify-write**: `_read_ledger()` parses the whole 645 KB file, `_plan()` appends
records to the in-memory list, and the writer serialises the entire structure back. There
is no lock, no compare-and-swap, and no re-read between the parse and the write.

Observed directly, not theorised: closing
`review:2026-07-31-1823-internal-adversarial:D12:8.6` printed
`✓ wrote 1 record(s)` and exited 0. Four minutes later the record was **absent** from the
ledger, while `…:D12:8.2` — written *earlier* in the same session — was present. The
closure was re-run and persisted on the second attempt.

⚠️ **This is the exact failure the writer exists to prevent**, one layer down. ADR-012
built `close_finding.py` so that a closure could not silently do nothing; here the tool
reported success, exit 0, and the finding stayed open. Every guard in `_guard_prior` reads
a snapshot that another process may already have replaced.

⚠️ **It is silent by construction.** The success line is printed from the in-memory plan,
not from a read-back of the file, so nothing in the tool's own output can distinguish a
durable write from a clobbered one. The only reason this was caught is that the follow-up
`git commit` reported "no changes added to commit" — a coincidence of workflow, not a
guard.

---

### 1.1 — 🔴 MAJOR — the ledger writer has no concurrency control and does not verify its own write

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python -m pytest tests/test_close_finding.py -q -k "readback or concurren"`
  *What it asserts:* that a successful `close()` has re-read the ledger and confirmed its records are present before reporting success. Exits 1 at HEAD (no such test exists).
- **Gate:** FixPropagation
- **Location:** `scripts/close_finding.py` — `_read_ledger`, `_plan`, and the write path that follows them
- **Observed:** Read-modify-write over a shared tracked file with no advisory lock. Two
  processes that both parse before either writes will each serialise their own view, and
  the second to finish silently discards the first's records. The window is the whole
  duration of `_run_verifications`, which shells out to a `--verify` command and can run
  for minutes.
- **Evidence:** Measured 2026-08-15 during a five-worker parallel remediation run.
  - `close_finding.py --doc …/2026-07-31-1823-internal-adversarial/D12.md --section 8.6`
    → `✓ wrote 1 record(s)`, exit 0.
  - Immediately after: `git status --porcelain docs/review_finding_supersessions.json`
    printed **nothing**, and the last three ledger records were `…:infra:1.1`,
    `…:D12:8.4`, `…:D12:8.2` — the 8.6 record absent, and the three surviving records all
    predating it.
  - Re-running the identical command wrote it, and a read-back confirmed
    `finding_id` present. Nothing about the invocation differed.
  - Five subagents were running concurrently at the time. They were instructed not to
    touch the ledger and none reports having done so, so the clobbering writer is **not
    yet identified** — which is itself the finding: no mechanism records who wrote the
    ledger last, and the file carries no generation counter to detect a lost update.
- **Expected:** A closure that reports success has durably written. At minimum the tool
  re-reads the ledger after writing and asserts its own records resolve, failing loudly if
  not. Better, the write takes an exclusive lock for the read-modify-write window so a
  concurrent writer blocks rather than clobbers.
- **Fix:** Two parts, and the second is the one that makes the first honest.
  1. **Read-back verification.** After the write, re-parse and assert every id in `to_add`
     is present with the intended status; if not, exit non-zero with the ids that did not
     survive. This converts a silent loss into a loud one **without** solving the race.
  2. **An advisory lock** (`fcntl.flock` on the ledger, or a sidecar lockfile) held across
     `_read_ledger` → write, so a second writer waits instead of building on a stale
     snapshot. ⚠️ Scope the lock to the file operations only — **do not hold it across
     `_run_verifications`**, which shells out and can run for minutes; re-read under the
     lock after verification instead.
  ⚠️ **Do not "fix" this by serialising callers by convention** ("only the lead writes the
  ledger"). That is the same class as the `open`-record guard retired this morning: a rule
  a tool cannot enforce is not a guard, and this failure happened *under* exactly such a
  convention.
- **Related:** `2026-08-15-inert-open-record-blocks-closure` (same file, same morning) and
  `2026-08-15-verify-contract-unenforced`. All three are the closure writer reporting an
  outcome it did not achieve. This one is the most serious because the tool's success line
  is *unfalsifiable from its own output*.
- **Cache:** N/A.
