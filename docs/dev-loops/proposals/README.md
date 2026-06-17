# GAP-A gate proposals (System-2 → structural prevention)

Draft `proposals/<finding-id>.md` files land here when a System-2 finding recurs across
**≥ 3 distinct compact-events** (spec §13 GAP-A; ADR-004 pathway-2: mechanize a recurring
discipline into a gate). They are written by `scripts/system2_register.py --propose-gate`
(run by the harvest's Opus consolidation step).

**Each proposal is a DRAFT for human sign-off — never auto-applied.** Promote (or reject) a
proposal via `/skeft-qa:debrief`; only a human turns a proposal into a live `validate.py`
check / `goal-prompt` reference tweak / automation. This honors the axiom / hard-rule
sign-off posture (spec §1 principle 6 — "self-improving, never self-mutating").
