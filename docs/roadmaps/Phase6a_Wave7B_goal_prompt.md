# Phase 6a Wave 7B `/goal` prompt — center-bridge B (genuine literal-Verlinde Laplace)

Follow-on `/goal` for the center-bridge discharge. PREREQUISITE: run AFTER Wave 8 (A). Completes
the genuine-Laplace half of 6a.7 that the 2026-04-27 "axiom retirement" deferred. Full context:
`docs/roadmaps/Phase6a_Roadmap.md` → Wave 7 entry (lines ~341–421) + "RE-OPENED 2026-06-13" §, and
`docs/audits/SUBSTRATE_WEAKNESS_AUDIT_2026-06-13.md` finding #13.

---

GOAL: Phase 6a Wave 7B — discharge `H_VerlindeKMLiteralSumDerivation` by building the LITERAL
SU(2)_k Verlinde-sum entropy and deriving `kaulMajumdarS A G_N 0` from it via a GENUINE
Laplace/Watson bounded-remainder, replacing the 2026-04-27 redefinition
(`verlindeEntropy_SU2k := kaulMajumdarS A G_N 0`, its own saddle limit, which makes
`gaussianSaddleAsymptotic` prove `|x−x| = 0` — substrate-audit finding #13,
"defining-the-conclusion"). This makes the −3/2 log + the area-law FORM genuinely
derived-from-counting. PREREQUISITE: Wave 8 landed. PUBLIC repo (SK_EFT_Hawking). Read CLAUDE.md,
docs/WAVE_EXECUTION_PIPELINE.md, docs/roadmaps/Phase6a_Roadmap.md Wave 7 entry (the full Sub-task
A/B/C breakdown) + RE-OPENED 2026-06-13 §, docs/audits/SUBSTRATE_WEAKNESS_AUDIT_2026-06-13.md #13,
and the Phase-5h Mathlib-contribution deep-research note FIRST.

HARD INVARIANTS: axioms exactly {propext, Classical.choice, Quot.sound}; NO new project-local
`axiom` (sign-off rule); NO `native_decide`; NO `sorry`; NO `set_option maxHeartbeats` in proof
bodies (decompose into `have` sub-lemmas; maxRecDepth bumps OK); never weaken a statement to pass.
PARALLEL AGENT may share `main`: stage ONLY your own explicit paths (never `git add -A` / `-a` /
`.`), never push, never touch others' uncommitted files, DO NOT `rm -rf .lake/build` (use
`lake build SKEFTHawking.<Module>` + `lake build SKEFTHawking.ExtractDeps`). Dev loop = lean-lsp MCP
(lean_goal → lean_multi_attempt → write; lean_verify each module). Use lean4 skill semantic search,
not grep, for Mathlib decl existence.

DECISION GATE (do FIRST, document the verdict before building):
1. Recheck Mathlib master for a landed Laplace-method / Watson's-lemma lemma (the Wave 7 gate).
2. Settle whether the literal SU(2)_k Verlinde sum genuinely REQUIRES the Hardy–Ramanujan `p(n)`
   asymptotic, or admits a DIRECT Watson/Laplace saddle on the specific sum — the latter shrinks
   the wave substantially. Do not assume Hardy–Ramanujan is needed without checking.

Sub-task A — generic Laplace-method bounded-remainder lemma (`laplace_method_asymptotic` +
`|integral − leading| ≤ C/A`). Mathlib-PR-grade presentation; ship project-local
`lean/SKEFTHawking/LaplaceMethodAsymptotic.lean` if no upstream PR (Wave 7 fallback path).

Sub-task B — literal `verlindeSum : ℝ → ℝ → ℝ` (the SU(2)_k horizon state count) + port the
Kaul–Majumdar 2000 §3 `I₀ − I₁` cancellation → an explicit
`verlindeEntropy_SU2k A G_N = A/(4G) − (3/2)·log(A/4G) + RemainderTerm A G_N`, with `RemainderTerm`
an explicit `O(1/A)` quantity bounded via Sub-task A.

Sub-task C — compose A + B → `gaussianSaddleAsymptotic_proved`; REDEFINE `verlindeEntropy_SU2k` to
the literal sum (NOT its own saddle limit); rewire consumers
(`kaulMajumdar_asymptotic_within_OoneOverA`, `verlinde_matches_kaul_majumdar_at_large_area`);
discharge `H_VerlindeKMLiteralSumDerivation`.

NOTE: the leading 1/4 is STILL γ-tuned after this wave — that is the separate C-spike. This wave
makes the −3/2 and the FORM derived-from-counting; it does NOT derive the coefficient. Keep paper26
prose honest on that boundary.

CLOSURE: full validate.py; file-gate + `lake build` of new/changed modules + ExtractDeps;
`lean_verify` axiom-purity on every new theorem; AXIOM_METADATA gaussianSaddleAsymptotic →
`closed` with evidence (if the axiom path is touched); update_counts.py + Inventory +
Inventory_Index + Phase6a Wave-7 status (genuine derivation COMPLETE) + audit #13 → remediated;
Stage-13 for paper26 (the −3/2 no longer rests on a definition-equals-target move).

/goal autonomous mode: the stop hook is a GO signal, not coercion — do the next increment THIS
turn. Ship kernel-pure increments across auto-compacts until the gate + Sub-tasks A/B/C + closure
are done. NEVER "hold" / "await direction" / "next session" / context-budget reasoning. Blocked on a
user-only decision → diligence first, take the clearly-best option, ask once only on a real
no-clear-default tradeoff, keep shipping everything else.
