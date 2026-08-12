# Closure refusals — the ADR-012 pilot batch, 2026-08-12

`scripts/close_finding.py` refused **5 of 106** manifest rows. **None was forced.**

⚠️ **A refusal is information.** This whole thread began with a ledger containing a false
closure — a record asserting it had cleaned up duplicate keys in 57 registry entries that
still carried them. Overriding a refusal to make a batch look complete is how that record
got there.

Every refusal here is the same class: **a record already exists for the finding, with a
different status.** `_load_supersession_ledger` is last-wins and does not say so, so
appending a second record would mean one of the pair silently does nothing. The writer
refuses rather than guessing which is right.

⚠️ **Two of these predate this branch; three were created BY it.** Task 9's re-key moved
seven inert records onto ids that minted nodes — and five of those ids are also manifest
targets. That is the re-key working: those findings now have a live closure. It also means
the manifest's disposition and the re-keyed record's status have to be reconciled by hand.

| finding | manifest says | ledger says | what to decide |
|---|---|---|---|
| `review:2026-05-01-1500-bundle-stage13:I1:3.1` | `superseded` → `accepted` | `fixed` | whether it was FIXED or merely ACCEPTED — the two are not interchangeable, and `accepted` removes it from the blocking set on a recorded decision |
| `review:2026-05-01-L3-bundle-stage13:L3:6.1` | `fixed` → `fixed` | `open` | why a record asserts `open`; that is not a closing status, so the finding reads open today and the manifest disagrees |
| `review:2026-05-11-1251-bundle-stage13:D2:1.2` | `not-a-defect` → `accepted` | `fixed` | whether it was FIXED or merely ACCEPTED — the two are not interchangeable, and `accepted` removes it from the blocking set on a recorded decision |
| `review:2026-05-11-1251-bundle-stage13:I3:5.1` | `superseded` → `accepted` | `fixed` | whether it was FIXED or merely ACCEPTED — the two are not interchangeable, and `accepted` removes it from the blocking set on a recorded decision |
| `review:2026-06-08-2242-internal-adversarial:paper10_modular_generation:6.1` | `fixed` → `fixed` | `open` | why a record asserts `open`; that is not a closing status, so the finding reads open today and the manifest disagrees |

## How to resolve one

Amend the existing record deliberately — do not append a second. The existing record's
`evidence` and the manifest row's `evidence` are both on the record; reconcile them into
one, and if the disposition genuinely changed, say so in the evidence rather than leaving
two records to be silently ordered.

**101 of 106 wrote cleanly** (99 new records, 2 idempotent no-ops).
