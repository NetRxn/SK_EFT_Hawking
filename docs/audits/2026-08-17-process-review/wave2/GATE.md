# Wave 2 — Cluster GATE: validation gates that cannot fire, or assert a proxy

Window: t0 = 2026-08-15 09:46 CDT to HEAD (`4c81c2ec`). Cache running in that window: `f33dc0a1`.
Unloaded plugin commits: `fd6cac3d`, `e9e5e314`, `c4b1a1ca`, `f58a3fe4` (none touch the files below).

---

### GATE-1 — `NarrativeGrounding` queries a `SUPPORTS` edge no extractor emits

- **Wave-1 source IDs:** F-11, H-03
- **Verdict:** RE-DIAGNOSED (real, unaddressed, but not "structurally unpassable" — bimodal, not uniformly vacuous)
- **Evidence at HEAD:**
  - `grep -c SUPPORTS scripts/build_graph.py` → `0`. Confirmed: no extractor emits a `SUPPORTS` edge.
  - `scripts/readiness_gates.py:678-733` (`_eval_narrative_grounding`, Gate 7 P1): for each paper, if the
    paper has ≥1 `ProseClaim` tagged `interesting` and none carries an outgoing `SUPPORTS` edge (which is
    every one, since none exist), the gate sets `state = 'blocked'` — a **hard, permanent fail** for that
    paper. If the paper has **zero** interesting claims, the gate reports `state = 'passed'` — vacuously.
  - `scripts/validation/checks/graph_atlas.py:480-507` already **discloses** this exact defect in
    `GATE_EDGE_TYPES_WITHOUT_EMITTERS["SUPPORTS"]`, and a dedicated check
    `gate_edge_types_are_emitted` (added `a3bb20a0`, 2026-08-06 — **before the window**) derives both the
    consumed-edge-type set (AST-walking `readiness_gates.py`) and the emitted-edge-type set (AST-walking
    `build_graph.py`) and fails if a *new*, undisclosed dead edge type appears. `SUPPORTS` is disclosed, so
    this check currently passes — it makes the defect visible, it does not fix it.
- **Population:** measured live via `python -c "from scripts.build_graph import build_graph_json; ..."`
  (fresh graph build, not the stale `figures/provenance_graph.json` which dates to 2026-04-03 and has 0
  `ProseClaim` nodes). Live: 466 `ProseClaim` nodes, **7 tagged `interesting`**, **0** `SUPPORTS` edges,
  across **6 of 64** `Paper` nodes: `D10`, `D5`, `D8`, `paper10_modular_generation` (×2), `paper12_polariton`,
  `paper6_vestigial`. Those 6 papers are **permanently blocked** on Gate 7 (P1, submission-blocking) with no
  way to clear it while the edge is unemitted. The other 58 papers pass Gate 7 vacuously — the gate examined
  nothing for them.
- **Already-addressed by:** no. `SUPPORTS` emission is still absent at HEAD; the disclosure/ratchet
  machinery around it (`a3bb20a0`) predates the window and doesn't fix the root cause.
- **Mechanism:** `build_graph.py` never implements a `SUPPORTS`-edge extractor (prose claim → formal
  artifact), so `idx.outgoing(pc['id'], 'SUPPORTS')` is empty for every `ProseClaim` node, unconditionally.
  The gate's own fallback logic then produces two different failure shapes from the same missing edge
  depending on whether the paper has any `interesting`-tagged claims at all.
- **Recurs on the next bundle?** YES — any bundle whose abstract gets a `ProseClaim` flagged `interesting`
  (the extraction that decides this is unrelated to `SUPPORTS`) lands in the permanently-blocked set the
  moment it's flagged, with no remediation available except building the `SUPPORTS` extractor.

---

### GATE-2 — Per-bundle ratchet ceilings frozen far above live population (A-04)

- **Wave-1 source IDs:** A-04
- **Verdict:** ALREADY-ADDRESSED (the specific claim); broader "house rule not followed" premise does not
  hold on remeasurement
- **Evidence at HEAD:**
  - The dict A-04 quotes (`{'D1': 14, ... 'D12': 44}`, total 232) does not exist anywhere in the tree today
    (`grep -rn "232" src/ scripts/ docs/` → no ratchet hit). It was real at the moment wave-1's source
    transcript observed it (spine `main-2026-08-15.md:8628-8637`, ~15:22 CDT: a failing
    `tests/test_d5_bundles_readiness.py` assertion `{'D12': 5, 'L1': 1} == {'D1': 14, ... 'D12': 44}`, live
    population 6 against ceiling 232) — but it was fixed **the same day, in-window, twice**:
    `7a63e17f` (2026-08-15 11:41 CDT, "Re-freeze the per-bundle ratchets") and `d9f2f49a` (2026-08-15 12:26
    CDT, "Read the attribution a review document DECLARES, and re-derive both ratchet legs" — a
    predicate-correction re-derivation, not a raise). Both are ancestors of HEAD
    (`git log --oneline HEAD | grep <sha>` finds each).
  - Current ceiling lives in `docs/required_open_ceilings.json` (data, not a Python literal, by deliberate
    design — see its own `_why_not_python` field), read by
    `scripts/validation/checks/bundles_readiness.py:361` (`_required_open_ceilings`).
  - **Remeasured now** via the check's own instrument
    (`uv run python scripts/validate.py --check bundle_stage13_claim_consistent`): the ratchet is **not**
    unfireable — it is currently **RED**, the opposite direction from A-04's claim. Population *grew* past
    the 08-15 freeze (new blockers found by wave-1's own primary-source re-reading, G-01): `D1 13>2, D2
    10>3, D3 14>1, D4 13>4, D8 6>0, E1 7>1, L3 5>0`; unattributed leg `57>44`. The ratchet is firing exactly
    as designed — it blocks new debt, it does not silently pass over it.
- **Population — every down-only ratchet in `src/core/constants.py` + `docs/required_open_ceilings.json`,
  measured with each check's own instrument** (`uv run python scripts/validate.py --check <name>`,
  2026-08-17):

  | Ratchet | Ceiling | Live | Slack | State |
  |---|---|---|---|---|
  | per-bundle open-blocking (`required_open_ceilings.json`) | re-frozen 08-15 | grew again | **negative**, 7 bundles over | FAIL |
  | unattributed open-blocking leg | 44 | 57 | **-13** | FAIL |
  | `NATIVE_DECIDE_DECL_CLOSURE_CEILING` | 530 | 530 | 0 | PASS |
  | `ARISTOTLE_REGISTRY_UNRESOLVED_CEILING` | 14 | 14 | 0 | PASS |
  | `PROVENANCE_UNRESOLVABLE_CEILING` | 58 | 58 | 0 | PASS |
  | `CITATION_UNDECLARED_CLASS_CEILING` | 78 | 78 | 0 | PASS |
  | `COUNT_LITERAL_CEILING` | 95 | 91 | +4 | PASS (advisory: "lower the ceiling") |
  | `NUMERICAL_LITERAL_CEILING` | 117 | 149 | **-32** | FAIL |
  | `SENTENCE_OVER_100_CEILING` | 18 | 23 | **-5** | FAIL |
  | `LEAN_MODULE_ABSENT_CEILING` (bundle_lean_module_coverage) | 147 | 185 | **-38** | FAIL (see GATE-3) |
  | apex numeral-noise ceiling | 31 | 33 | **-2** | FAIL |
  | `EXISTENTIAL_MISNAMED_CEILING` | 7 | 7 | 0 | PASS |
  | `EXISTENTIAL_ESCAPE_CEILING` | 0 | 0 | 0 | PASS |
  | `LEGACY_DRAFT_DANGLING_REF_CEILING` | 1 | at ceiling | 0 | PASS |

  Commands run: `uv run python scripts/validate.py --check native_decide_regression --check
  count_literals --check numerical_literals --check spelled_out_census_figures --check
  bundle_lean_module_coverage --check bundle_apex_resolves --check apex_theorem_claims_grounded --check
  apex_claims_not_vacuous --check ledger_ids_resolve --check citation_primary_sources_present --check
  bibitem_title_primary_source --check bundle_cross_references_resolve --check parameter_provenance
  --check theorems --check vacuous_statement_audit --check existential_witness_disclosure --check
  bundle_sentence_length` and `--check bundle_stage13_claim_consistent --json` for exact ceiling/measured
  pairs.
- **Already-addressed by:** `7a63e17f`, `d9f2f49a` (both 2026-08-15, in-window).
- **Mechanism:** the house rule ("lower the ceiling in the same commit as the debt reduction") **is**
  followed here, tightly — 8 of 13 ratchets checked sit at exactly zero slack, one at a harmless +4, and
  the rest are currently in violation (population grew, ceiling correctly did not move, check correctly
  fails) rather than sitting with unfired headroom. A-04's failure mode (a large stale ceiling silently
  eating new debt) is not the current state of any ratchet measured.
- **Recurs on the next bundle?** NO for A-04's specific shape (large positive slack from a stale freeze) —
  the pattern that produced it (a big closure event on 2026-08-14 with no same-day re-freeze) was caught
  and fixed same-day. The *inverse* risk is live and ongoing: several ratchets are currently RED because
  new debt (found by the redraft wave itself) has not yet been paid down or the ceiling deliberately not
  raised — that is the ratchet working as intended, not a gate defect, but it does mean **the suite cannot
  currently reach a green merge gate** until that debt is fixed.

---

### GATE-3 — `bundle_lean_module_coverage` punished a legitimate module-drop with no escape path

- **Wave-1 source IDs:** G-10
- **Verdict:** ALREADY-ADDRESSED
- **Evidence at HEAD:**
  - Check exists: `scripts/validation/checks/bundles_readiness.py:1119`
    (`@register_check("bundle_lean_module_coverage", ...)`) — a ratchet on modules a bundle registers as
    contributing but its draft never reaches (`LEAN_MODULE_ABSENT_CEILING`, line 1097).
  - A deregistration path **exists at HEAD**: `scripts/bundle_append.py --deregister-lean-modules` (added
    by commit `d8c3b858`, 2026-08-15 13:00 CDT — **in-window**, "Three gates the redraft campaign needs, and
    one that was making manuscripts worse"). The commit message names the exact failure wave-1 caught:
    *"L3's lead KEPT TWO THEOREM CITATIONS PURELY TO SATISFY THE RATCHET, and the prose-reviewer
    independently flagged those exact two as belonging to a different paper's argument."* The check now
    scores the **net** registration set (register → drop → re-register, order-sensitive), and the ceiling
    was not raised — deregistration only lowers the live count.
  - Documented at: `docs/adrs/ADR-015-redraft-safe-bundle-gates.md`, `docs/BUNDLE_LIFT_PROCEDURE.md` (both
    reference `--deregister-lean-modules`).
  - Live use confirmed: `uv run python scripts/validate.py --check bundle_lean_module_coverage` reports
    *"185 registered-but-absent module(s) across 18 bundle(s) (441 net-declared **after 3
    deregistration(s)**)"* — the path is not just present, it is already exercised by 3 bundles.
- **Population:** at the time wave-1 observed it, 1 bundle (L3) confirmed forced into a bad citation; "2/10
  bundles" per G-10's own recurrence count. Today: 0 bundles are forced into this trap (mechanism exists),
  while the underlying coverage ratchet itself is separately RED (185 > 147, see GATE-2 table) because
  registered-but-uncited modules grew — a different, legitimate-debt problem the deregistration path does
  not by itself resolve (a module can be absent from the draft without being deregisterable, if the draft
  genuinely still rests on it).
- **Already-addressed by:** `d8c3b858` (2026-08-15, in-window).
- **Mechanism:** `bundle_append.py` now records `lean_modules_deregistered` events with a required
  rationale in the append log; `check_bundle_lean_module_coverage`'s net-registration walk
  (`_bundle_lean_registration_ledger`-style logic) subtracts deregistered modules from the ratcheted
  absence population, and a hard-fails if a deregistered module is still reachable by name or citation
  (production-seeded guard, live population 0).
- **Recurs on the next bundle?** NO — the escape path is now general (any bundle, not L3-specific) and
  already in use by 3 bundles.

---

### GATE-4 — Metadata staleness is warn-only at the gate that matters

- **Wave-1 source IDs:** E-10, E-2
- **Verdict:** RE-DIAGNOSED (real, but the diagnosis "nothing gates on it" is too strong — a gate exists,
  scoped narrower than the claim implies)
- **Evidence at HEAD:**
  - Flag: `freshness_stale` (bool), owned exclusively by `scripts/check_bundle_source_freshness.py`
    (docstring, line 22: *"Default: advisory; promotable to FAIL at the Phase 8 submission gate via
    `validate.py --strict`"*). Consumers found via `grep -rln freshness_stale scripts/ docs/`: writer
    (`check_bundle_source_freshness.py`, `bundle_append.py`, `bundle_source_manifest.py`), one reader/display
    (`bundle_readiness.py`, dashboard-facing), and the merge-gate check
    (`scripts/validation/checks/bundles_readiness.py:568-574`), which **explicitly and deliberately does
    not** assert it — a code comment documents that an earlier attempt to gate on it (D12 Stage-13 round-8)
    conflated two unrelated meanings ("source newer than last_lift" vs. "blockers open") and made two
    writers fight, producing a non-idempotent `validate.py`. That's a considered design choice, not an
    oversight, at the merge-gate layer.
  - A gate **does** exist, but at a different, later stage: `scripts/validation/checks/freshness.py:1030`
    registers `bundle_source_freshness`; running `uv run python scripts/validate.py --check
    bundle_source_freshness --strict` flips all 68 current sub-findings from WARN to **FAIL**. `--strict` is
    wired into `gate_precheck.py submission` (confirmed live: `grep -rn "validate.py --strict"
    scripts/check_bundle_source_freshness.py` and cross-referenced against
    `docs/adrs/ADR-009-validation-suite-modularization.md:724`, corroborated 2026-08-05).
  - The **merge gate** — `scripts/verify_scope.py --merge-gate`, the one CLAUDE.md names as the actual
    pre-landing gate — never passes `--strict` (`grep -n strict scripts/verify_scope.py` → no hits; it runs
    `validate.py --ci --no-memo` and friends only). So staleness genuinely **does** survive every merge; it
    is only enforced at the separate, rarer, manually-invoked submission gate.
  - **Population, measured with the check's own instrument:**
    `uv run python scripts/validate.py --check bundle_source_freshness` → default mode: *"68 sub-findings:
    0 FAIL / 68 WARN / 0 PASS"* — every one of the 20 bundles checked carries at least one stale dimension
    right now (`stage13_redo_required`, Lean-modules-changed-after-`last_lift`, or
    source-paper-modified-after-`last_lift`). `--strict` mode: all 68 flip to FAIL.
  - E-2's specific instance is a **separate mechanism**: D8's `bundle_metadata.json` `claims` field carries
    a hand-authored prose note *"⚠️ Also named by D4 §9's substrate list"* (`papers/D8/bundle_metadata.json:6`).
    This is not a computed flag at all — no extractor or check reads or verifies it. Confirmed stale now:
    `grep -n "^\\\\section" papers/D4/paper_draft.tex` shows D4's current draft has no section 9 (8
    top-level sections total, 1512 lines). Nothing catches this class of drift, warn or otherwise, because
    nothing treats it as structured data.
- **Already-addressed by:** no.
- **Mechanism:** two distinct staleness surfaces. (1) `freshness_stale` is a real, computed, ratcheted flag
  with a real enforcement path — but that path is scoped to the submission gate by deliberate design, so it
  is silent at every merge, which is where E-10's "survives a merge" claim is accurate. (2) Cross-reference
  prose notes like D8's are unstructured text with no computation behind them at all — a strictly weaker
  problem than a mis-wired gate, since there is no gate to wire.
- **Recurs on the next bundle?** YES for (1) — every bundle that lifts new content without also re-running
  submission-gate `--strict` accumulates staleness invisibly at merge time; currently 100% (20/20 measured
  bundles) carry it. YES for (2) as well, at a lower rate, wherever a bundle's metadata narrates a fact
  about another bundle's structure.

---

## Compact table

| ID | Verdict | Population | Recurs |
|---|---|---|---|
| GATE-1 | RE-DIAGNOSED | 6/64 papers permanently blocked; 58/64 pass vacuously | YES |
| GATE-2 | ALREADY-ADDRESSED (`7a63e17f`, `d9f2f49a`, 2026-08-15) | 0 ratchets currently show A-04's failure shape; 5/13 measured ratchets currently RED from *new* debt instead | NO (for A-04's shape); inverse risk live |
| GATE-3 | ALREADY-ADDRESSED (`d8c3b858`, 2026-08-15) | 0 bundles currently forced into the trap; escape path used by 3 bundles already | NO |
| GATE-4 | RE-DIAGNOSED | 68/68 sub-findings WARN-only across 20/20 bundles at merge gate; 1 confirmed-stale hand-written cross-ref (D8→D4) | YES |
