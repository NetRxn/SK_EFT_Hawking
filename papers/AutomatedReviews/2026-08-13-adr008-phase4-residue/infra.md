# Residue from ADR-008 Phase 4 — Claude slot activation, 2026-08-13

**Found by** wiring the Claude activation change set and exercising the control plane end-to-end
(`acquire --client claude` → `prepare` → live MCP dispatch → `release`). These are things the
activation surfaced that it did not itself close.

---

## Findings

### 1 — 🔵 Two heavy Lean backends run permanently, against a vnode ceiling a third of what the ADR assumes

- **Severity:** minor
- ⚠️ **Severity re-measured down from `major` at filing time.** The first assignment came from the
  vnode figure alone. Measured: 2 backends against a limit of 3, host file table at 10695/491520,
  no ENFILE, `doctor` green on `heavy_backend_limit`. ADR-008 § *Risks* states the heavy-backend
  semaphore — not vnode headroom — is the resource invariant, and the semaphore is holding. There is
  no demonstrated failure, and the "fix" is an operator decision about steady-state policy. That is
  an advisory, not a blocker.
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `config/lean-slots.public.json` (`server`, no `backend_policy`),
  `scripts/lean_slots/state.py::backend_expected`
- **Observed:** the public inventory declares no `backend_policy`, so it defaults to `"default"`,
  under which `backend_expected` returns `True` for an **unleased** slot. `slotctl supervisor start`
  therefore launches a heavy Lean LSP backend for every slot not held by another repository — two
  today — and they stay up whether or not any work is leased.
- **Evidence:** `slotctl doctor` reports `heavy_backend_limit: 2/3 running` with all three slots
  FREE. Measured host ceiling is **`kern.maxvnodes = 263168`**, not the `786432` ADR-008 § *Context*
  asserts; the raise did not survive a host reboot. ENFILE from process/vnode pressure is the
  original incident this whole ADR exists to prevent (historical constraint 7).
- **Expected:** a backend is a **consequence of a lease**, not of the supervisor being up. The
  `"leased"` policy already exists and is exercised by the downstream fixture in
  `tests/test_lean_slots.py`.
- ⚠️ **`prepare` is not the obstacle.** `paused_backend()` restarts the backend unconditionally
  rather than consulting `backend_expected` (`supervisor.py:357-367`), so the `PREPARING` state does
  not strand a slot. The real work is what `supervisor start` should do for an unleased slot and
  whether anything must reconcile when a lease goes ACTIVE outside a `prepare`.
- **Why it was not done in the activation:** it changes steady-state resource behaviour for **both**
  clients, so it is its own decision with its own tests — not a rider on a Claude wiring change.
- **Fix:** decide the public `backend_policy`; if `"leased"`, add the reconcile path and a test that
  a slot reaching ACTIVE by any route has its backend up.
- **Verify:** `uv run python -m pytest tests/test_lean_slots.py -q` and
  `uv run python scripts/slotctl.py doctor`

### 2 — 🔵 A controller edit silently invalidates the running endpoints mid-session

- **Severity:** minor
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `scripts/lean_slots/supervisor.py::_runtime_fingerprint`, `_spawn`
- **Observed:** the proxy records a fingerprint of the implementation it loaded. After editing
  `scripts/lean_slots/*`, `doctor` reports `proxy=False` **while the port is still open and
  serving**, and the next `prepare` fails `"proxy for wtN is not healthy"` and moves the slot to
  `QUARANTINED` — costing a reclaim that is blocked for `lease_timeout_seconds` (900s).
- **Evidence:** hit twice while shipping this change; both times `supervisor stop && supervisor
  start` cleared it. `_spawn` already raises a precise message for this case; `doctor` does not
  surface it, reporting only `proxy=False`, which reads as "the process died".
- **Expected:** `doctor` distinguishes *not running* from *running stale code*. The mechanism is
  correct and must not be weakened — only its report is ambiguous.
- **Fix:** in the endpoint check, when the recorded pid is alive but the fingerprint differs, say
  so and name the remedy, as `_spawn` already does.
- **Verify:** `uv run python -m pytest tests/test_lean_slots.py -q`

### 3 — 🔵 A quarantine costs 15 minutes even when the slot is provably clean and self-owned

- **Severity:** minor
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `scripts/lean_slots/controller.py::reclaim`
- **Observed:** `reclaim` refuses until `heartbeat_at` is older than `lease_timeout_seconds`, with
  no exception for a lease this session **owns** and whose worktree is clean and fully integrated.
  A failed `prepare` therefore strands its own slot for 15 minutes.
- **Evidence:** three refusals at 178s / 395s / 547s during this session's activation. The eventual
  clean path was `release`, which *does* accept `QUARANTINED` from the owner — but only once owner
  identity resolved correctly, which is exactly what was broken at the time.
- **Expected:** the staleness threshold guards against reclaiming **someone else's** live lease. It
  is not load-bearing when the caller is the recorded owner and the git audit is clean.
- ⚠️ **Do not relax the audit itself** — dirty or unabsorbed work must still block, and a
  non-owner must still wait. Only the age gate is over-broad here.
- **Fix:** permit owner-initiated reclaim of a `QUARANTINED` slot without the age gate, keeping
  every dirty/unabsorbed check.
- **Verify:** `uv run python -m pytest tests/test_lean_slots.py -q`
