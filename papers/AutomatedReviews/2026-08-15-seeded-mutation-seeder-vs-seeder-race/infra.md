---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-15T18:40:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# Two concurrent seeders of the same file interleave their restores, and the seed survives

## Summary

**1 MAJOR.** `scripts/seed_journal.py` made production-seeded mutation survive a **killed**
run — the defect filed as `2026-08-15-seeded-mutation-survives-a-killed-run` and fixed the
same day. It does not guard the other concurrency axis: **two live seeders of the same
file**.

Both processes read the original, both write their seed, both restore — and whichever
restores *first* writes back a copy that already contains the other's seed, or the second
restore reinstates a version the first had cleaned. The journal then reports clean, because
each seeder completed its own transaction correctly. Nothing was killed and nothing was
orphaned; the invariant broken is a *pairwise* one that neither transaction can observe.

⚠️ **This is not hypothetical and it produced a fabricated CRITICAL in the corpus, twice in
one day, by two different mechanisms.**

- **2026-08-12 → 08-15, by a killed run.** `review:2026-08-12-0200-citation-integrity:D10:99.9`
  — *"seeded mutation"* — counted as an open CRITICAL on bundle D10 for three days, and was
  very nearly frozen into `docs/required_open_ceilings.json` as an acceptable blocker during
  the 2026-08-15 ratchet re-derivation. Removed in `7a63e17f`.
- **2026-08-15, by this race.** The identical stanza reappeared in the identical file while
  two test suites ran concurrently, this time carrying the `SKEFT-SEEDED-BY-TEST-SUITE`
  marker. Caught by `seed_residue_absent`'s **corpus** leg, reported `ORPHANED`; its
  **journal** leg reported clean, which is exactly the split that check was designed with.

### 1.1 — 🔴 MAJOR — `seeded_mutation` serialises nothing against a second seeder

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python -m pytest tests/test_seed_residue_guard.py -q -k "concurrent or race or exclusive"`
  *What it asserts:* that two seeders contending for the same production path cannot both
  proceed — one waits or fails. Exits 1 at HEAD: no such test, and no such guard.
- **Gate:** CorpusIntegrity
- **Location:** `scripts/seed_journal.py` — `seeded_mutation`, `seeded_artifact`, `journalled`
- **Observed:** The journal records `(path, original bytes, mtime, owning pid)` per
  transaction and repairs orphans. Transactions against the same path are independent; no
  lock is taken, so their read-seed-restore windows interleave freely.
- **Evidence:** Measured 2026-08-15. A second suite reintroduced the D10 stanza while the
  journal reported `0 in flight`. Confirmed the working-tree diff was the seed alone before
  repairing with `git checkout --`; `seed_residue_absent` green after.
- **Expected:** A production path is seeded by at most one process at a time. A second
  seeder blocks until the first restores, or refuses with a message naming the holder.
- **Fix:** Take a per-path exclusive lock (`fcntl.flock` on a lockfile beside the journal
  entry) for the whole seed→assert→restore window. `scripts/close_finding.py` already uses
  this pattern for the supersession ledger and is the precedent to copy — including its
  read-back-after-write discipline, which is what would have caught this class here.
  ⚠️ **The lock must not be held across a subprocess that itself seeds**, or the suite
  deadlocks against itself; scope it to the file transaction, not the assertion.
- **Related:** the same shape as the ledger's lost write (`2026-08-15-closure-write-lost-under-concurrency`)
  — two writers, each internally correct, no serialisation between them. Corpus residue is
  worse than a lost write because it does not vanish: it *mints a finding*, and a fabricated
  CRITICAL is indistinguishable from a real one to every consumer downstream.
- **Cache:** N/A.
