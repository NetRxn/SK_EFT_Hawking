---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-14T21:05:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# `close_finding.py` — `accepted` is unreachable for any finding whose verify encodes the unfixed state

## Summary

**1 MAJOR.** ADR-012 gives the finding lifecycle three terminal statuses:
`fixed`, `accepted`, `reopened`. `accepted` means *a recorded decision not to
fix*. But `close_finding.py` runs the finding's declared `Verify:` command
unconditionally, for every status, so `accepted` can only be recorded when the
fix's own verification already passes — i.e. only when the finding is, in fact,
fixed. For the normal case, where the verify encodes precisely the state the
decision declines to change, `accepted` is unreachable and the finding is
stranded open forever.

Found while closing `review:2026-08-14-l1-stage13:L1:3.2`, which is the exact
shape: its declared verify asserts that `GravitationalWaves` depends on
`VestigialSusceptibility`. The correct disposition is to accept that it does
not and must not — the module's parameters are free by design — but that
disposition cannot be recorded.

---

### 1.1 — 🔴 MAJOR — `_run_verifications` is not status-aware, so `accepted` is gated on the fix it declines

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python -c "import ast,sys; src=open('scripts/close_finding.py').read(); t=ast.parse(src); fn=[n for n in ast.walk(t) if isinstance(n,ast.FunctionDef) and n.name=='_run_verifications'][0]; assert any('status' in ast.dump(a) for a in ast.walk(fn)), '_run_verifications takes no status argument, so it cannot skip verification for an accepted decision'"`
  *What it asserts:* that the verification runner can see the status it is gating. Exits 1 at HEAD, where `_run_verifications(minted, nodes, verify)` has no status parameter.
- **Gate:** FixPropagation
- **Location:** `scripts/close_finding.py:116` (call site), `:138` (`_run_verifications`), `:62` (`CLOSING_STATUSES`)
- **Observed:** `close_finding.py --status accepted` runs the declared verify and refuses the write when it fails. Passing no `--verify` does not help: the command is read from the finding document, not from the flag.
- **Evidence:** Reproduction at HEAD, 2026-08-14:

  ```
  uv run python scripts/close_finding.py \
    --doc papers/AutomatedReviews/2026-08-14-l1-stage13/L1.md \
    --section 3.2 --status accepted --date 2026-08-14 --evidence '<200 chars>'
  → AssertionError: GravitationalWaves has NO dependency on VestigialSusceptibility
  ```

  `scripts/close_finding.py:109` gates the *evidence bar* on
  `status in CLOSING_STATUSES`, so the file already distinguishes closing from
  non-closing statuses. `:116` then calls `_run_verifications(minted, nodes,
  verify)` for every status without consulting it.
- **Expected:** For `status=accepted`, the declared verify is **recorded, not
  enforced**. An acceptance is a decision about a finding the project has chosen
  to live with; requiring its fix-verification to pass first inverts the meaning
  of the status. `fixed` must keep the current fail-closed behaviour unchanged —
  that gate is load-bearing and is not in question here.
- **Fix:** Make `_run_verifications` status-aware. For `accepted`, run the
  command and store its outcome in `verified_by` (so the record shows the state
  at acceptance, which is the useful forensic datum) but do not fail the write.
  For `fixed`, no change. ⚠️ This edits the ADR-012 sole ledger writer, so it
  runs through the `architecture-change` skill, and ADR-012 needs the
  `accepted`-semantics sentence stated explicitly — at present the ADR describes
  the status but not whether its verify is enforced, which is why the code could
  drift from the intent without anything catching it.
- **Blast radius:** 122 project-wide `accepted` findings already exist
  (counted in `readiness_gates.py:918-926`), so the status is in real use; every
  one of them was recorded either before the declared-verify gate existed or with
  a verify that happened to pass. Nothing regresses if acceptance stops
  enforcing, because no gate reads the verify outcome — `_eval_fix_propagation`
  keys on `status` alone.
- **Cache:** N/A.

---

## Consequence for L1

`review:2026-08-14-l1-stage13:L1:3.2` stays **open** until this is fixed. Its
remediation is already shipped — the overstated "computed in the RPA" claim is
removed from `papers/L1/paper_draft.tex` at both sites, the
`chi_RPA`-is-the-bubble-integral conflation is corrected, and
`GravitationalWaves.lean`'s module docstring now states that `χ_vest` and `γ`
are free parameters and that the module has no project dependencies by design.
Only the ledger record is blocked, so L1 continues to show
`FixPropagation` blocked on a finding whose substance is resolved.
