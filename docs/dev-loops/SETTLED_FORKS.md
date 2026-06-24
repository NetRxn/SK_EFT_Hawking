# SETTLED FORKS — NEVER RE-DERIVE

The **negative half** of the Live-Anchor split (spec `LIVE_ANCHOR_REDESIGN_SPEC.md`, Move 2):
dead / banned / superseded routes that no *code* artifact records, so the loop keeps
re-deriving them across compactions (System-2 finding `compaction-summary-quality`; the harvest
repeatedly catches the loop re-opening a settled fork or re-deriving a committed engine).

**This is a MANDATED READ** (FIRST_ACTION): grep this register BEFORE any "this is impossible /
needs a banned route / let me re-derive whether X works" reasoning. `repo_state_probe.py` surfaces
the count + IDs as a pointer; the *reasons* live here.

**Schema** (one `## <route-id>` block per fork):
- `verdict`: `dead` | `banned` | `superseded`
- `tier`: `automatic` | `agent-reviewed` | `human-reviewed` (governance; mirrors System-2)
- `authored_by`: `kernel-no-go` | `coach` | `harvest` | `debrief`
- `killed_by`: the commit / kernel-check / decision that settled it
- `reason`: one line — why; what it would have needed
- `memory`: `[[note-slug]]` cross-link to project memory
- `created_ts` (REQUIRED) · `reviewed_ts` (set when `/debrief` reviews/modifies)

**Authoring & governance (ruling 2026-06-24):** a **kernel-checked no-go settles a fork
decisively** (`authored_by: kernel-no-go`, tier `automatic` — the kernel is the authority, so the
loop MAY record these mid-run). The **coach** may author/influence (`agent-reviewed`); the harvest
may *propose* (`automatic`). **`/debrief`** is the human review/modify layer (promote tier, edit,
retire) — no entry is immutable. Every entry carries datetime metadata.

> Seeded 2026-06-24 from the existing `Lit-Search/Phase-5qF/L2/LAB_NOTEBOOK_INDEX.md` register +
> project memory. The forks below are RECORDS of prior settled decisions; do not re-litigate them.

---

## routeC-snake-mv-ses
- verdict: banned
- tier: human-reviewed
- authored_by: debrief
- killed_by: user ruling (goal marker `20260617T231250` SETTLED LOCKS: "B<->C thrashed for DAYS — NON-NEGOTIABLE")
- reason: the snake / MV-SES + SnakeInput route is a multi-wave rebuild kept ONLY as a last-resort fallback; never re-open, re-cost, or re-litigate Route B vs C.
- memory: [[project-L2-routes-B-C-compaction-prep-2026-06-22]]
- created_ts: 2026-06-22T00:00:00Z
- reviewed_ts: 2026-06-24T00:00:00Z

## homology-class-square-lift
- verdict: dead
- tier: agent-reviewed
- authored_by: coach
- killed_by: reverted 2026-06-22 (needs the false `hmem`; stay at CHAIN-pairing altitude, never lift to the homology-CLASS square)
- reason: lifting the connecting square to the homology-class level requires a membership fact (`hmem`) that is false at cover level; the close stays whnf-dodged at chain-pairing altitude with the z_seam ∃-bound.
- memory: [[project-L2-routes-B-C-compaction-prep-2026-06-22]]
- created_ts: 2026-06-22T00:00:00Z
- reviewed_ts: 2026-06-24T00:00:00Z

## kronecker_cap_chainIncl_eq_rcap_chainIncl-MatchLHS83
- verdict: dead
- tier: agent-reviewed
- authored_by: coach
- killed_by: FALSE-POSITIVE confirmed (lean_multi_attempt empty-goals ≠ an in-file close; verify with lean_diagnostic / lake build)
- reason: `kronecker_cap_chainIncl_eq_rcap_chainIncl` (MatchLHS:83) appears to close under multi_attempt but does NOT close in-file — do not re-attempt it as a real close path.
- memory: [[project-L2-routes-B-C-compaction-prep-2026-06-22]]
- created_ts: 2026-06-22T00:00:00Z
- reviewed_ts: 2026-06-24T00:00:00Z

## mfd-equals-H1-dead-end
- verdict: dead
- tier: automatic
- authored_by: kernel-no-go
- killed_by: kernel-checked `dataBordism_two_torsion_of_revStr_trivial` (Phase 5q.F)
- reason: the `Mfd := H¹` construction is a kernel-checked dead-end; do not re-attempt it.
- memory: [[project-phase5qF-strict-retirement]]
- created_ts: 2026-06-15T00:00:00Z
- reviewed_ts: 2026-06-24T00:00:00Z

## cap-sigmaR-connecting-needs-banned-formula
- verdict: superseded
- tier: human-reviewed
- authored_by: coach
- killed_by: committed engine `cap_coboundary_cochainSplit_eq` / `_subdiv` (a3f217e1 / 2f58618c, kernel-pure)
- reason: the recurring WORRY that "cap σR-connecting needs the banned `relCohomMvConnecting_eq` formula / non-degeneracy, so it's dead" is FALSE — the committed engine proves it GAP-FREE (only `cap_relCochains_subspaceChains_eq_zero` + `cap_leibniz` + ℤ/2, NEVER the formula). Coach-resolved 4×; a recurring re-seed. NEVER re-derive; NEVER reach for `relCohomMvConnecting_eq`.
- memory: [[project-L2-sigmaR-connecting-resolved-2026-06-23]]
- created_ts: 2026-06-23T00:00:00Z
- reviewed_ts: 2026-06-24T00:00:00Z

## kronecker-altitude-respine
- verdict: banned
- tier: human-reviewed
- authored_by: coach
- killed_by: reverts `a79f1912` (of_hcup_linked re-seed → cap-altitude `8cb87e5c`) + `3ea6b739` (kronecker_pd_fold_fund / `_of_crossRealization` re-seed, ~15 commits `ae6a1210`→`ac415397` → cap-altitude `ccdd0aef`); user + coach (2nd dispatch) goldfish-reseed ruling
- reason: re-spining the L2 close to the KRONECKER ALTITUDE (the `_of_crossRealization` / `kronecker_pd_fold_fund` / `of_hcup_linked`-as-spine family) is THE dominant 5q.F spiral — started 3×, hard-reverted 2×, each time framed as a "whnf-dodge breakthrough" (that framing is the re-seed tell). The L2 close SPINE stays at CAP altitude (cap-Leibniz); the σR side joins via the pairing adjunction `relKroneckerH_relCohomMvConnecting` as a SUB-step (Fact A), never as the spine. The ban is on the ALTITUDE, not on any single lemma name (kronecker sub-lemmas inside the Fact-A step are fine). The tactical cap-altitude whnf is a SYMPTOM, dodged AT cap altitude (def-head-match), never by re-spining. Verify present state by ROUTE/ALTITUDE, not "commit present."
- memory: [[project-L2-kronecker-reseed-reverted-2026-06-24]]
- created_ts: 2026-06-24T00:00:00Z
- reviewed_ts: 2026-06-24T00:00:00Z
