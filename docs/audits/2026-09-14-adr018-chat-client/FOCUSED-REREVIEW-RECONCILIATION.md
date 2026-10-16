# ADR-018 focused re-review reconciliation

**Focused reviewed head:** `8407079f935ba3dd758a4f2c288b3cd43ec5239e`

**Focused verdict:** `ACCEPT_WITH_CHANGES`

**Closure table:**

| Finding | Focused disposition |
|---|---|
| B1 — removal/revocation | `PARTIALLY_CLOSED` |
| B2 — lifecycle owner / heartbeat / ready→absorb | `CLOSED` |
| B3 — private/downstream migration | `CLOSED` |
| B4 — renderer vs admission boundary | `CLOSED` |
| B5 — production-bridge Gate A | `CLOSED` |
| B6 — ADR-008/operator-guide reconciliation | `CLOSED` |

**New blockers:** none beyond residual B1.

This artifact records the focused reviewer result and the author/control-plane reconciliation. It is not itself acceptance evidence or implementation authorization.

## Residual B1

The focused reviewer accepted the quiescent/restart-bound removal model but identified one remaining specification gap:

1. ADR-018 says an active lease whose client is no longer admitted must be reported as an invalid migration state, but the measured `Controller.doctor()` lease predicate currently treats any non-`QUARANTINED` lease as healthy and does not compare `lease.client` with the admitted roster.
2. The bearer cleanup ordering was ambiguous because `session_environment(client)` is intended to reject an unadmitted client before token processing, so a procedure that expects post-removal token cleanup through that path can be impossible.

## Reconciliation

The residual is specified document-first in:

- `docs/adrs/ADR-018-b1-removal-preflight-addendum.md` — D13/D14;
- `docs/superpowers/specs/2026-09-14-adr018-b1-removal-preflight-design.md` — S18-14..16;
- `docs/superpowers/plans/2026-09-14-adr018-b1-removal-preflight.md`.

### D13 / S18-14 — non-disruptive mismatch predicate

Doctor/removal-preflight must compare live lease `client` with the current/prospective roster and report red when the lease client is absent. The predicate is read-only and must not strand the lease: legitimate owner cleanup remains possible under ADR-008.

The non-vacuity test seeds the mismatch into the real lease/inventory artifacts the health path reads, proves red, proves no mutation, then proves owner cleanup and completed post-restart removal.

### D14 / S18-16 — bearer cleanup ordering

Bearer credential deletion/rotation occurs while the client is still admitted and quiescent, before the roster edit. Later re-admission must not resurrect the pre-removal credential. Trusted-local mode has no token cleanup step.

## Remaining gate

Because residual B1 was a blocking finding, implementation remains blocked until a fresh independent reviewer performs a narrow closure re-review of the current PR head and accepts D13/D14 / S18-14..16 as closing B1 without weakening ADR-008 cleanup authority.