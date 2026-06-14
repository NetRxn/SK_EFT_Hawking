# Phase 6a Center-Bridge — CHAINED overnight `/goal` prompt (Wave 8 → 7B → 9)

**This is the prompt to run for unattended overnight execution.** It chains all three center-bridge
waves in strict sequence. The three per-wave prompts on disk are the authoritative specs; this
prompt carries the chain control-flow, the shared invariants, and the completion condition. The
user is UNAVAILABLE until morning — by design this chain never stalls for input.

**Paste-ready ≤4000-char `/goal` condition: `Phase6a_CenterBridge_chained_goal_CONDITION.txt`**
(the `/goal` condition field caps at 4000 chars; this `.md` is the full reference spec).

---

GOAL: Phase 6a Center-Bridge Discharge — execute the FULL three-wave program end-to-end, fully
autonomously and UNATTENDED overnight, in STRICT SEQUENCE: **Wave 8 (A — consistency conditions) →
Wave 7B (B — genuine literal-Verlinde Laplace) → Wave 9 (C — Frolov–Fursaev induced-gravity 1/4).**
PUBLIC repo (SK_EFT_Hawking). Read FIRST, in order: CLAUDE.md, docs/WAVE_EXECUTION_PIPELINE.md,
docs/roadmaps/Phase6a_Roadmap.md ("RE-OPENED 2026-06-13 — Center-Bridge Discharge" §), then the
three per-wave prompts: `Phase6a_Wave8_goal_prompt.md`, `Phase6a_Wave7B_goal_prompt.md`,
`Phase6a_Wave9_goal_prompt.md`. Each per-wave prompt's tasks + closure are authoritative; follow
them exactly.

SHARED HARD INVARIANTS (ALL three waves): axioms exactly {propext, Classical.choice, Quot.sound};
NO new project-local `axiom`; NO `native_decide`; NO `sorry`; NO `maxHeartbeats` in proof bodies
(decompose into `have` sub-lemmas; maxRecDepth bumps OK); never weaken a statement to pass; every
new Prop ships a witness AND a falsifier (no `True`-dressed-vacuous fields); apply the preemptive-
strengthening checklist (#4 trivial-discharge, #5 defining-the-conclusion) to EVERY statement. Dev
loop = lean-lsp MCP (lean_goal → lean_multi_attempt → write; `lean_verify` each module); lean4
semantic search (not grep) for Mathlib/physlib decl existence.

PARALLEL-AGENT HYGIENE (the 5QE / 16-convergence `/goal` runs concurrently on `main` tonight):
stage ONLY your own explicit paths — NEVER `git add -A`/`-a`/`.`; commit your own completed-wave
files at each closure gate so progress is durable across compacts/crashes (if the git index is
locked by the parallel agent, wait and retry — do not force); NEVER push; NEVER touch their
uncommitted files; NEVER `rm -rf .lake/build` (shared build — use `lake build SKEFTHawking.<Module>`
+ `lake build SKEFTHawking.ExtractDeps`). SCOPE FENCE: touch only the center-bridge surface
(`BHEntropyMicroscopic` + the new `LaplaceMethodAsymptotic` / induced-gravity modules + their
consumers + paper26 + the Phase6a roadmap/registry/counts/Inventory). Do NOT touch Phase 5qE files
or anything the parallel agent is editing.

CONTROL FLOW (strict — do NOT parallelize or reorder):
1. **Wave 8 (A)** per `Phase6a_Wave8_goal_prompt.md`. Drive to its CLOSURE GATE: full validate.py
   green · `lake build` of BHEntropyMicroscopic + any new module + ExtractDeps clean · `lean_verify`
   axiom-pure on every new theorem · all consumers compile · Fib+Ising instances proven · the two
   `True`s + the F4 tautology discharged · counts + Inventory + roadmap Wave-8 status updated ·
   commit own paths.
2. ONLY after Wave 8's gate is green → **Wave 7B (B)** per `Phase6a_Wave7B_goal_prompt.md` (do its
   decision gate FIRST: Hardy–Ramanujan vs direct saddle; recheck Mathlib). Drive to its closure
   gate (`H_VerlindeKMLiteralSumDerivation` discharged; `verlindeEntropy_SU2k` no longer its own
   saddle limit); commit own paths.
3. ONLY after Wave 7B's gate is green → **Wave 9 (C)** per `Phase6a_Wave9_goal_prompt.md`. Drive to
   its closure gate (`frolov_fursaev_quarter_coefficient` + consistency + witness + falsifier;
   Gate A.2 CLOSED); commit own paths.
Do NOT skip ahead if a wave's closure isn't clean — keep working THAT wave (decompose, MCP-iterate).
A wave is "done" only when its closure gate is green.

UNATTENDED-OVERNIGHT POLICY (user cannot be reached — NEVER block):
- The `/goal` stop hook is a GO signal, not coercion: each firing = ship the next substantive
  increment THIS turn, kernel-pure, across as many auto-compacts as it takes. NEVER "hold" /
  "await direction" / "next session" / context-budget reasoning. Auto-compact is handled safely;
  quality does not drop across a compact boundary.
- Two sanctioned walls have FALLBACKS so the chain never stalls:
  (a) A step would need a NEW project-local `axiom` → DO NOT ship the axiom (policy) and DO NOT ask
      (user away). Ship the tracked-hypothesis Prop fallback (witness + falsifier + register in
      `PERMANENT_TRACKED_HYPOTHESES.md`), leave a MORNING-REVIEW flag, and CONTINUE — but CIRCLE
      BACK after all other waves close and work toward genuine discharge.
  (b) A genuine product/narrative tradeoff with no clear default → take the best-supported option,
      document the decision + alternatives as a MORNING-REVIEW flag in the roadmap, and CONTINUE.
- A specific sorry that survives the exhausted MCP loop → isolate it behind a tracked-Prop (NOT an
  axiom, NOT a sorry), flag it, and proceed to the rest of that wave + the next wave. One stuck
  lemma must never halt the chain.

COMPLETION CONDITION (the goal is met ONLY when ALL hold):
- Wave 8: the two `True`s + the F4 tautology discharged; consumers compile; Fib+Ising proven.
- Wave 7B: `H_VerlindeKMLiteralSumDerivation` discharged via genuine Laplace (or the documented
  direct saddle); `verlindeEntropy_SU2k` redefined to the literal sum.
- Wave 9: `frolov_fursaev_quarter_coefficient` + consistency theorem + Dirac witness + falsifier;
  Gate A.2 closed.
- AND full validate.py green; AND a per-wave adversarial self-review (Stage 13) with findings
  remediated; AND counts + Inventory + Inventory_Index + roadmap all synced.
- AND any tracked-Props / Hypotheses ADDED during this session are discharged (not left open),
  followed by a FINAL adversarial review across the whole center-bridge surface.
THEN: write a concise MORNING SUMMARY block to Phase6a_Roadmap (what landed per wave; every
MORNING-REVIEW flag; any tracked-Prop fallbacks shipped; any narrative defaults taken) + a memory
note, and dispatch the closure reviewer. Only THEN is the goal complete.

MORNING HANDOFF (write this also if the chain genuinely cannot proceed further): a clear status
block — current wave + gate state, what is green, what is flagged, the exact next action — so the
user can resume in a single read.
