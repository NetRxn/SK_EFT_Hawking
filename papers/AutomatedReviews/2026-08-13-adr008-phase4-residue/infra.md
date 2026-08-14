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
- ⚠️ **CORRECTED 2026-08-14 — `prepare` WAS the obstacle, and this line was wrong.** It said
  `paused_backend()` restarts the backend unconditionally so `PREPARING` could not strand a slot.
  It does restart on exit, but it also called `assert_healthy` **at entry**, which requires a
  running *backend* — exactly what a freshly-acquired leased slot lacks. `prepare` was therefore
  unreachable under the policy, i.e. `"leased"` was declared in the schema but never usable. The
  downstream fixture missed it because the paired path uses `activating_from`. Found by running it,
  after two contradictory conclusions drawn from reading the same code.
- **Why it was not done in the activation:** it changes steady-state resource behaviour for **both**
  clients, so it is its own decision with its own tests — not a rider on a Claude wiring change.
- **Fix:** decide the public `backend_policy`; if `"leased"`, add the reconcile path and a test that
  a slot reaching ACTIVE by any route has its backend up.
- **Verify:** `uv run python -m pytest tests/test_lean_slots.py -q`

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
- **Evidence:** three refusals at 178s / 395s / 547s during this session's activation. The clean path
  is `release`, which *does* accept `QUARANTINED` from the owner — it was unavailable at the time only
  because owner identity was itself the thing broken.
- ⚠️ **Impact re-measured 2026-08-14, downward.** Two further self-owned quarantines (a stale-proxy
  `prepare` failure, then the `leased`-policy `prepare` failure) both cleared **immediately** with
  `slotctl release --slot N`. So the 15-minute stall is not the normal experience — it is what a
  caller hits after reaching for `reclaim`, which reads like the recovery verb but is the one for
  *someone else's* dead lease. The defect is closer to a naming/routing problem than a wait.
- **Also worth fixing:** the `reclaim` refusal message states the threshold but does not mention that
  an owner holding a clean slot should use `release` instead.
- **Expected:** the staleness threshold guards against reclaiming **someone else's** live lease. It
  is not load-bearing when the caller is the recorded owner and the git audit is clean.
- ⚠️ **Do not relax the audit itself** — dirty or unabsorbed work must still block, and a
  non-owner must still wait. Only the age gate is over-broad here.
- **Fix:** permit owner-initiated reclaim of a `QUARANTINED` slot without the age gate, keeping
  every dirty/unabsorbed check.
- **Verify:** `uv run python -m pytest tests/test_lean_slots.py -q`

### 4 — 🟠 A failed `reclaim` refreshes the heartbeat it gates on, so retrying can never succeed

- **Severity:** major
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `scripts/lean_slots/state.py::Inventory.save_lease`,
  `scripts/lean_slots/controller.py::_quarantine`
- **Observed:** `save_lease` unconditionally stamps `heartbeat_at = now`, and `_quarantine`
  writes through it. Every failed `reclaim` therefore re-quarantines with a fresh heartbeat,
  and `reclaim`'s own staleness gate (`age < lease_timeout_seconds` → refuse) reads that value.
  A lease that is genuinely three weeks stale becomes **unreclaimable by retry**: each attempt
  resets the clock to zero.
- **Evidence:** the wt2 lease carried `acquired_at: 2026-07-23T19:32:03Z`. One failed reclaim on
  2026-08-14 (refused on the paired-dependency pin) rewrote `heartbeat_at` to `2026-08-14T12:17:10Z`
  — 67s old — so the immediate retry was refused for staleness rather than for the real reason.
  The true age was still visible in `acquired_at`, which the gate does not consult.
- **Expected:** `heartbeat_at` records **owner liveness**. A controller-side write that the owner
  did not initiate must not stand in for a heartbeat. Staleness should be judged against the last
  owner-initiated `heartbeat`/`acquire`, or against `quarantined_at`, never against a bookkeeping
  write.
- ⚠️ **Do not fix by lowering the threshold or skipping the gate.** The gate is what stops one
  session reclaiming another's live lease. The defect is the *input*, not the bar — this is the
  "assert the decider, not a proxy" shape: `heartbeat_at` is being used as a proxy for owner
  liveness while also serving as a generic write timestamp.
- **Fix:** give `save_lease` an explicit `touch_heartbeat: bool` (default False for state
  transitions, True only on `acquire`/`heartbeat`), or record owner liveness in a separate field
  the quarantine path never writes.
- **Verify:** `uv run python -m pytest tests/test_lean_slots.py -q`

### 5 — 🟠 `reclaim` tests absorption against the lease's RECORDED base, not against where the work actually went

- **Severity:** major
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `scripts/lean_slots/controller.py::reclaim` (the `merge-base --is-ancestor
  HEAD base_sha` audit), `::release` (same shape)
- **Observed:** the audit asks *"is the slot's HEAD contained in the base this lease recorded?"*
  That is a **proxy** for the question that matters — *"would freeing this slot lose work?"* —
  and the two diverge whenever the recorded base is superseded or deleted. A slot whose commits
  were long ago merged into the integration branch reads as **unabsorbed**, and no controller
  verb can free it.
- **Evidence:** the wt2 lease recorded `base_ref: feature/graphene-rational-proof-slot`
  (`f297d8b8`). That branch no longer exists, so `reclaim` first fails outright at
  `rev-parse --verify`. With the ref restored the audit would still refuse: the slot HEAD
  `d821936` is **not** an ancestor of `f297d8b8`, while it **is** an ancestor of the private
  `main`. Both of the slot's commits are in `main` by full SHA and the worktree is clean —
  nothing is at risk, and the controller still cannot say so.
- **Expected:** absorption is containment in **some reachable integration ref**, not in one
  recorded SHA. Test `HEAD` against the repository's current integration branch (or `--contains`
  across refs) and treat the recorded base as a hint, not the authority.
- ⚠️ **Do not widen this into "free the slot if anything looks merged".** The audit's job is
  still to refuse when work would be lost; only its *reference point* is wrong. A deleted or
  superseded base must fail **loudly and recoverably**, not become an unresolvable state.
- ⚠️ **Missing verb.** There is no way to re-point or retire a lease whose base is gone. Every
  path — `release` (owner mismatch), `reclaim` (this audit) — is closed, so the only exit is
  removing runtime state by hand, which is exactly what S-C tells operators not to do casually.
- **Fix:** judge absorption against the integration ref, and add an explicit operator verb for
  retiring a lease whose base no longer resolves, with the same dirty/unabsorbed protections.
- **Verify:** `uv run python -m pytest tests/test_lean_slots.py -q`
