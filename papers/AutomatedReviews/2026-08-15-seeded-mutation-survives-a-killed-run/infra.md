---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-15T11:20:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# A production-seeded mutation that mutates a TRACKED file leaves a phantom finding when the run is killed

## Summary

**1 MAJOR.** Production-seeded mutation tests are this project's strongest non-vacuity
instrument, and several of them write a defect into a **tracked** artifact and restore it
in a `finally`. A `finally` does not run when the process is killed. When that happens the
seed is left in the working tree, and for the review corpus specifically the seed **is a
finding** — so a killed test run silently adds a blocking finding to the graph.

Observed, not theorised. Measuring open blocking findings on 2026-08-15 returned **D10: 1**
where D10 had been at zero minutes earlier. The finding was
`review:2026-08-12-0200-citation-integrity:D10:99.9`, severity `critical`, titled
"seeded mutation" — residue from
`tests/test_d5_bundles_readiness.py::TestTheOpenRequiredPopulationRatchets::test_A_REAL_NEW_BLOCKING_FINDING_TURNS_THE_LEG_RED`,
left after a test process was terminated. Two commands in that session had been killed at a
timeout (`exit 143`).

⚠️ **The residue is indistinguishable from a real finding to every consumer.** It has a
declared severity, it mints a node, it emits a `FLAGS` edge, it counts against the bundle
ratchet, and it moves `readiness_submission_gate`. Nothing marks it as synthetic.

---

### 1.1 — 🔴 MAJOR — a seed in a tracked file is durable, and for review documents it is a finding

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python -m pytest tests/test_seed_residue_guard.py -q`
  *What it asserts:* that a marker-bearing seed left in the tracked corpus is detected rather than minted as a finding. Exits 1 at HEAD (no such test or guard exists).
- **Gate:** FixPropagation
- **Location:** `tests/test_d5_bundles_readiness.py` (the seeding test), `scripts/build_graph.py` (`extract_review_finding_nodes`, which mints it)
- **Observed:** The seeding test is correctly written — it saves the original, writes in a
  `try`, restores in a `finally`, and asserts byte-identity afterwards. None of that
  survives `SIGKILL`, and `SIGTERM` only survives if the handler completes. The test is not
  the defect; the assumption that a `finally` is a durable guarantee is.
- **Evidence:** Measured 2026-08-15.
  - `git diff` on `papers/AutomatedReviews/2026-08-12-0200-citation-integrity/D10.md`
    showed exactly the six seeded lines and nothing else.
  - The graph minted it: one open `critical` flagging `paper:D10`, against a bundle that
    was otherwise at zero open blockers.
  - Restored with `git checkout --` on that single path; D10 returns to zero.
  - At least three registered checks are production-seeded against tracked files
    (`architecture_inventory_fresh`, `chain_backing_targets_resolve`, `module_census_fresh`),
    so the review corpus is the most consequential instance of a general hazard, not the
    only one.
- **Expected:** A seed that outlives its test is DETECTED, not silently consumed as data.
- **Fix:** Two candidates; the first is cheap and strictly additive.
  1. **A marker the extractor refuses.** Have seeding tests write a sentinel
     (`<!-- SEEDED-MUTATION -->` or a reserved section number the minter skips), and have
     `extract_review_finding_nodes` skip it AND a registered check FAIL when one is present
     in the tree. The seed then cannot become a finding, and its survival is loud.
  2. **Seed a copy, not the original** — the pattern used by
     `tests/test_close_finding.py::TestAnInertOpenRecordDoesNotBlockClosure`, which copies
     the production ledger into `tmp_path` and repoints the module constant. This keeps the
     production DATA as the input while making the mutation unable to touch the tree.
     ⚠️ Not universally applicable: a check that resolves paths relative to the repo root
     cannot be pointed at a copy, which is why several tests seed in place.
  ⚠️ **Do not "fix" this by removing the production seeding.** It is the only thing that
  distinguishes a check that finds nothing from a check that cannot fire, and
  `FIXTURE_ONLY_CEILING` exists to push tests toward it.
- **Related:** `2026-08-15-closure-write-lost-under-concurrency` — both are cases where an
  operation that looks atomic in source is not atomic against a process that dies.
- **Cache:** N/A.
