# ADR-008 trusted-local authentication amendment — adversarial implementation review

**Review date:** 2026-07-23

**Scope:** public control plane, generated Codex configuration, fixed-root MCP proxy, lease gate, process supervisor, and downstream-overlay contract.

**Disposition:** **PASS after remediation**, with one accepted trust-boundary limitation and one deferred validation gate for the inactive bearer mode.

## Decision under review

The single-user workstation deployment uses `server.client_auth = "trusted-local"` and binds MCP front doors to loopback. Codex needs no bearer-token environment variable. A nonsecret `client` URL label preserves lease routing/collision checks. Environment-backed bearer authentication remains available only through the explicit `server.client_auth = "bearer"` feature flag.

## Adversarial threat model

| Threat | Required behavior | Result |
|---|---|---|
| LAN or nonlocal caller | Trusted-local mode must not bind beyond loopback. | PASS: inventory loading rejects nonloopback hosts. |
| Codex/Claude collision on one slot | Dispatch must match the active lease's client, repository role, worktree, endpoint, and dependency pin. | PASS. |
| Released or stale MCP session | Every nondiscovery request must recheck an ACTIVE lease. | PASS. |
| Worker-triggered authoritative build | `lean_build` must remain absent and denied. | PASS at backend, proxy, generated-config, and policy layers. |
| Authentication-mode change during a lease | Existing lease must not be silently reinterpreted. | PASS: lease records `client_auth`; controller commands reject mode mismatch. |
| Proxy code/config changes while a process is already running | Supervisor must not call stale policy current. | PASS after remediation: process metadata fingerprints loaded code, inventory, command, and slot data; reuse fails closed on drift. |
| Future shared-user host | Trusted-local assumptions must not be presented as sufficient. | PASS: bearer mode is explicit and trusted-local is loopback constrained. |

## Findings and remediation

### F1 — High: bearer authentication was an unrequested reliability dependency

The original implementation made normal MCP startup depend on `LEAN_SLOT_CODEX_TOKEN`, even though processes running as the workstation owner can already read the same repositories and runtime state. Missing inherited shell state caused all three MCP clients to fail before any lease interaction.

**Resolution:** trusted-local is now the active/default mode. Generated top-level and worker configurations contain no `bearer_token_env_var`; session setup exports no token; leases contain no token hash. Bearer generation, rotation, hashing, and header checks remain covered behind the explicit feature flag.

### F2 — High: a plain supervisor start could reuse stale authentication policy

The proxy command line points to an inventory path, so its process command did not change when `server.client_auth` or proxy source changed. A healthy old process could therefore be mistaken for the current implementation until manually stopped.

**Resolution:** supervisor metadata now records a runtime fingerprint over the relevant command, server/slot inventory, repository role, and proxy source files. `supervisor start` refuses stale managed processes and instructs the operator to stop then start. Mode changes under an active lease also fail independently at the controller boundary.

### F3 — Accepted limitation: trusted-local client labels are spoofable by the same OS user

The `?client=codex` label is routing identity, not authentication. Another process running as the workstation owner can claim it.

**Disposition:** accepted for the stated single-user trusted-host boundary. It is not described as protection from same-user processes. Any move to a shared-user or remotely reachable deployment must switch to bearer mode (or a stronger OS-authenticated transport) before activation.

### F4 — Deferred: inactive bearer mode has not received a live client acceptance run

Bearer-mode credential discovery, token mismatch, lease hashing, rotation gates, and generated configurations are unit tested. The currently active deployment has been live-tested only in trusted-local mode.

**Disposition:** acceptable because bearer is inactive/banked. Activating it requires a dedicated end-to-end client test and explicit supervisor restart; it must not be represented as live-validated before that gate passes.

## Evidence

- Focused public control-plane/policy suite: all tests passed after the amendment and remediations.
- Broad public suite: 4,770 tests passed in the sandbox; the eight environment-blocked cases all passed when rerun with the required macOS process-introspection and Metal access.
- Live token-free discovery: all three public endpoints initialized, listed 21 tools, omitted `lean_build`, and cleaned up successfully with `LEAN_SLOT_CODEX_TOKEN` explicitly absent.
- Live token-free active dispatch: wt2 acquired without a token hash, prepared, served a real Lean diagnostic request, and released cleanly.
- Generated repository/workspace TOML parsed successfully and contains token-free MCP URLs with explicit nonsecret client labels.
- No active deferred-client configuration or plugin file is changed by this amendment.

## Final assessment

The amendment removes a brittle security ritual without weakening the controls that matter for this deployment: loopback confinement, one authoritative cross-client lease, identity checks on every dispatch, the global three-backend limit, deterministic process ownership, and orchestrator-only builds. The implementation is suitable for the trusted local workstation. Bearer mode remains deliberately non-active until separately live-validated for a shared-user scenario.
