# Substrate Integrity Gates — `/goal` prompt

Self-contained `/goal` prompt to execute ADR-004 (**3,994 chars — under the 4k convention**). Paste the block below after `/goal`. Full per-wave detail lives in `SubstrateIntegrityGates_Roadmap.md`; this prompt is the kickoff.

---

GOAL: Execute Substrate Integrity Gates (ADR-004) — 5 standing validate.py gates (R1–R5) shifting proof-substance + assumption-disclosure detection left to Stages 2/5/7, re-closing qi-leanproofsubstance + qi-assumptiondisclosure via STRUCTURAL PREVENTION (not per-finding), giving Inv #4/#9 teeth, adding Inv #16, fixing the paper7 overclaim #3. PUBLIC repo SK_EFT_Hawking/.

READ FIRST: docs/roadmaps/SubstrateIntegrityGates_Roadmap.md (authoritative tracker — full per-wave spec + gates + entry-state; KEEP ITS STATUS TABLE CURRENT; this prompt is only the kickoff); ADR-004 ("Overlap reconciliation" §); ADR-002 (P4 gate axiom_closure_allowlist OWNS native_decide — R2/R4/R5 defer) + ADR-003 (topo posture); WAVE_EXECUTION_PIPELINE.md + Inv #4/#9/#15; QI_REGISTER.md.

WAVES (sequential; land each check BEFORE clearing its backlog; @register_check):
- W1: PLACEHOLDER_THEOREMS 11→26; --check placeholder_not_cited (FAIL if a paper cites a placeholder as "verified"); FIX #3 — reprose paper7 general-G Z(Vec_G)≅Rep(D(G)) to "ℤ/2+S₃ concrete, general-G statement-level" + rename gauge_emergence_statement/half_braiding_gives_action/chirality_independent_of_G→*_TODO.
- W2: generalize the Phase-5q.T T5 detector (build_graph.py _PLACEHOLDER_BODY_PATTERNS) — flag NAME-claims-a-structural-quantity ∧ trivial-body (rfl/cases<;>rfl/struct-projection/:=h/trivial); --check proxy_body_audit + a MODELING_ASSUMPTION_THEOREMS whitelist (compliant = registry entry + disclosing docstring; template = topo). EXCLUDE native_decide/decide (ADR-002 owns them). Triage the roadmap's known set + unit-test.
- W3: COLLAPSE the two DISJOINT tracked-hyp ledgers to ONE = HYPOTHESIS_REGISTRY (add a prose field; absorb the doc's Props), and AUTO-GENERATE PERMANENT_TRACKED_HYPOTHESES.md from it (render script + tracked_hypotheses_fresh check). --check tracked_hypothesis_ledger: every consumed (h:Prop) + Prop-valued struct field (topo) maps to a registry entry; topo ALREADY covered by rokhlin_sigma_mod_16 (don't double-register); cover the ~42 consumed H_*. Add Inv #16.
- W4: build lean_grounding_audit (unbuilt Wave-21) + --check formula_grounding — assert each formulas.py entry's cited Lean STATEMENT (lean_deps.json) encodes its relation (not just the name); cover ALL formulas, not the 7-pair map. Restate Inv #4 as content-grounding.
- W5: surface ADR-002's EXISTING decl-closure count (axiom_closure_allowlist; 546, NOT call-sites) + clusters into counts.json via update_counts.py, regression threshold. Elimination stays ADR-002.
- W6: edit WAVE_EXECUTION_PIPELINE.md (R1–R5 into Stage 5/7 gates; restate #4, strengthen #9, add #16; Stage-14 policy — substance/disclosure QI close ONLY via pathway #2). Re-open + structurally-close the 2 substance/disclosure QIs (+ 2 related open ones). ADR-004→ACCEPTED. update_counts + Inventory.

HARD INVARIANTS: NO new axiom / native_decide / sorry / maxHeartbeats in proof bodies (gates must not introduce what they detect). Detectors ship the whitelist + unit tests so DISCLOSED modeling choices PASS — flag, don't re-derive Mathlib-walled math (topo/prime-density/Caves stay tracked-hyp). PUBLIC: never reference the private RD repo (its dir name trips the pre-commit hook); if sharing main, stage only your own paths (never add -A/.), don't push unless asked. Advisory-first only if a clean suite is otherwise blocked → hard-fail same wave.

CLOSURE: validate.py green incl all new checks; #3 fixed; ONE tracked-hyp source (doc generated)+Inv #16; PLACEHOLDER_THEOREMS==26; pipeline-doc+QI+ADR-004 consistent; Inventory+counts synced; roadmap table COMPLETE. Then a fresh-context reviewer (claims-reviewer on paper7 + adversarial pass on the checks).

/goal mode: stop hook = GO. Ship the next gate-passing increment each turn, update the roadmap table + memory, until every gate is green + the reviewer passes. NEVER hold/await/next-session/budget reasoning. Blocked only on a real user-only decision → diligence, take the clear option, ask ONCE, keep shipping else.