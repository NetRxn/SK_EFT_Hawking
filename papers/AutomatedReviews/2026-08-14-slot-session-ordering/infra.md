# Slot MCP tools register on an idle slot but cannot be used after it is leased

**Found by** dispatching the first real `lean-worker` onto a prepared slot. Every
`mcp__skeft_wt1__*` call failed for the worker AND for the lead, while the endpoint itself
was healthy.

---

## Findings

### 1 — 🔴 A session that registers slot tools while the slot is IDLE cannot call them once it is LEASED

- **Severity:** critical
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** ADR-008 decision S-P; `scripts/lean_slots/proxy.py`, `scripts/lean_slots/supervisor.py`
- **Observed:** MCP tools attach at session start. ADR-008 S-P makes an idle slot advertise its
  tools so they register then. But the client's MCP session is established against the idle
  proxy, and acquiring a lease starts the backend and re-establishes the proxy's downstream —
  after which the client's existing session no longer resolves. Every subsequent
  `tools/call` returns `MCP error -32602: Invalid request parameters`, permanently, for the
  life of that session. The tools remain visible and are unusable.
- **Evidence:** measured 2026-08-14 against `wt1` while `slotctl doctor` reported the slot
  `public:ACTIVE`, `heavy_backend_limit: 1/3`, backend pids 43096/43107 healthy on port 18761:

  | actor | call | result |
  |---|---|---|
  | dispatched `lean-worker` | `mcp__skeft_wt1__*` | `-32602` on every tool, both path forms |
  | lead (same session) | `mcp__skeft_wt1__lean_local_search` | `-32602` |
  | **fresh session** | `POST 127.0.0.1:8761/mcp?client=claude` → `initialize` | **HTTP 200**, Lean LSP 1.27.0, session id issued |
  | **fresh session** | same session → `tools/call lean_local_search` | **200**, returned the target declaration |

  The endpoint is not broken. Only sessions predating the lease are.
- ⚠️ **THE PORT TRAP that cost two independent diagnoses.** The rendered client config points at
  the **proxy** (`127.0.0.1:8761`); the lean-lsp backend listens on **18761**. Probing 18761
  directly returns `401 invalid_token`, which reads like a lease/auth rejection and is simply
  the backend refusing a direct connection. Both the worker and the lead reached the same wrong
  conclusion from the same wrong port. `trusted-local` auth takes the client identity from the
  URL query hint (`?client=claude`, `proxy.py:56`), so a probe without it is unauthenticated by
  construction.
- ⚠️ **This is the precise inverse of what S-P bought.** S-P was validated this session on the
  claim "an idle endpoint advertises its tools", and that claim is true. It was over-read as
  "the swarm is dispatchable at 3/3". **Tool registration and tool usability are different
  properties**, and only the first was tested. The swarm's work half has still never run
  through the sanctioned MCP path.
- **Consequence:** a worker dispatched into a slot leased *after* session start has no Lean
  MCP. The worker that hit this built its own gate (direct `lean` elaboration over the slot's
  prebuilt oleans) and delivered correct, kernel-pure work — but three concurrent workers each
  hand-rolling a Lean gate is not the design, and the fallback bypasses the slot isolation the
  control plane exists to provide.
- **Expected:** either a session can use a slot leased after it started, or the ordering
  requirement is stated where an operator and a lead will act on it.
- **Fix:** the operating constraint is **acquire and prepare slots BEFORE starting the session
  that will use them** — or restart the client after preparing. Record it in
  `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md` and in the `lean-worker` prompt, and amend
  ADR-008 S-P to state that advertising tools on an idle slot is necessary but not sufficient.
  ⚠️ Do NOT "fix" this by having workers fall back to direct `lean` invocation — that discards
  build isolation and the `lean_build` denial the worker endpoint enforces.
  A protocol-level repair (proxy re-issuing or migrating sessions across a backend start) would
  remove the constraint entirely and is the better end state; it is not attempted here.
- **Verify:** `uv run python scripts/slotctl.py doctor`
