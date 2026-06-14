# Phase 6a Wave 8 `/goal` prompt — center-bridge A (consistency conditions)

Self-contained `/goal` prompt for Phase 6a Wave 8. The active wave of the center-bridge
discharge. Run this now; Wave 7B (B) and the C-spike are separate. Full context:
`docs/roadmaps/Phase6a_Roadmap.md` → "RE-OPENED 2026-06-13 — Center-Bridge Discharge" §.

---

GOAL: Phase 6a Wave 8 (6a.8) — discharge the center-bridge CONSISTENCY conditions in
`lean/SKEFTHawking/BHEntropyMicroscopic.lean`: replace `H_HorizonBoundaryCondition.modularInvariant
: True` and `.anomalyMatch : True` (≈line 383–384) with genuine FALSIFIABLE Props, and strengthen
the F4 falsifier `H_HorizonBoundaryCondition_falsifier_quarterCoefficient` (currently
`rw [← h_match]; exact h_fail` — a P5 identity-wrapper tautology) into a real quantitative
comparison. The −3/2 log is already proven; this is the well-posedness layer that makes the bundle
non-vacuous. PUBLIC repo (SK_EFT_Hawking). Read CLAUDE.md, docs/WAVE_EXECUTION_PIPELINE.md,
docs/roadmaps/Phase6a_Roadmap.md (RE-OPENED 2026-06-13 § + Wave 8 entry),
SK_EFT_Hawking_Inventory_Index.md, and the deep-research file `Lit-Search/Phase-6a/6a-Horizon MTC
boundary conditions for Bekenstein-Hawking entropy- a literature survey for Wave 3.md` FIRST.

HARD INVARIANTS: axioms exactly {propext, Classical.choice, Quot.sound}; NO new project-local
`axiom` (sign-off rule — if you believe one is unavoidable, STOP and ask the user, keep shipping
everything else); NO `native_decide`; NO `sorry`; NO `set_option maxHeartbeats` in proof bodies
(decompose into `have` sub-lemmas; maxRecDepth bumps OK); never weaken a statement to pass. Every
new bundle field ships BOTH a satisfying instance AND a falsifier instance — no `True`-dressed
vacuous fields; apply the preemptive-strengthening checklist #4 (trivial-discharge) + #5
(defining-the-conclusion) to EVERY statement. PARALLEL AGENT shares `main` (5QE / 16-convergence
goal running concurrently): stage ONLY your own explicit paths (never `git add -A` / `-a` / `.`),
never push, never touch their uncommitted files, and DO NOT `rm -rf .lake/build` (shared build —
use `lake build SKEFTHawking.BHEntropyMicroscopic` and `lake build SKEFTHawking.ExtractDeps`). Dev
loop = lean-lsp MCP (lean_goal → lean_multi_attempt → write; lean_verify each module). Use lean4
skill semantic search (local_search / leansearch / loogle) — not grep — for "does decl X exist?".

KEY INSIGHT — the two fields are ONE anomaly: `(ST)³ = e^{2πi c₋/8}·S²` (Gauss–Milgram:
`Σ_a d_a² θ_a = D·e^{2πi c₋/8}`). The phase obstructing `(ST)³ = S²` IS `c₋ mod 8`, exactly the
Walker–Wang Z₂ inflow `anomalyMatch` checks. Build ONE chiral-central-charge-mod-8 / Gauss–Milgram
object and derive both fields + the F4 strengthening from it.

STAGE 2 (do first): grep/search every consumer of `H_HorizonBoundaryCondition` (the 5 in-file
falsifiers F1–F5, plus `QECHolographyBridge`, plus any others). Parameterizing the bundle changes
its signature — all consumers must keep compiling.

A1 — modularInvariant. Parameterize `H_HorizonBoundaryCondition` with the instance's
`RibbonCategory.PreModularData ℝ` (`md`); set `modularInvariant := md.modular` (S non-degenerate).
Reuse PROVEN witnesses `FibonacciMTC.fib_modular`, `RibbonCategory.su2k1_modular` / `su2k2_modular`.
DO NOT add S/T fields to `HorizonMTCBC` (external consumers incl. `HolographicCFunctionMTC`).
Falsifier: a premodular non-modular instance (degenerate S) fails the bundle. Literal SL(2,ℤ)
`(ST)³ = e^{2πi c₋/8} S²` with the T-matrix = OPTIONAL strengthening only if the core lands clean.

A2 — anomalyMatch. Define an honest Gauss–Milgram / chiral-`c₋`-mod-8 inflow-matching Prop,
reusing `ModularInvarianceConstraint.lean` (24∣c₋, framing anomaly), `WangBridge` (c₋=8N_f),
`KMatrixAnomaly` (gapped boundary). Get the physics honest: a T-invariant bulk forces a specific
`c₋ mod 8`; Fibonacci alone is chiral (c₋=14/5), so use a non-chiral/doubled instance OR state the
bulk inflow value as the matching target. Prove it for one instance where it GENUINELY holds AND
ship a falsifier instance where it FAILS (chiral c₋ ≢ matching value). Template:
`HolographicCFunctionMTC.lean` (real Props on the carrier, proven per-instance).

A3 — F4 strengthening. Replace `_quarterCoefficient`'s tautology with a real quantitative falsifier
tying the leading coefficient to `1/(4 G)` (`norm_num`-backed where a constant is load-bearing). Do
NOT derive κ=1/4G here — that is the research-open C-spike. Make the FALSIFIER substantive.

A4 — instances + paper. Prove the upgraded bundle satisfied for Fibonacci + su2k₂(Ising). Update
paper26 prose so the two conditions read as real, not placeholders (read PAPER_STRATEGY +
PAPER_DRAFT_MAPPING for paper26's bundle; hedge honestly; keep bundle-aware).

CLOSURE: full `uv run python scripts/validate.py`; file-gate + `lake build
SKEFTHawking.BHEntropyMicroscopic` + any new module + `lake build SKEFTHawking.ExtractDeps`;
`lean_verify` axiom-purity on EVERY new theorem; `update_counts.py` + Inventory + Inventory_Index +
Phase6a_Roadmap Wave-8 status + Gate A.2 note; Stage-13 claims/figure review for paper26's bundle;
cross-link the Vacuous Statement Sweep. Do NOT start Wave 7B (B) or any 1/4-derivation (C) — out of
scope.

/goal autonomous mode: the stop hook is a GO signal, not coercion — it means "do the next
increment THIS turn." Ship the next substantive increment each turn (kernel-pure, invariants
respected), update memory/roadmap, across as many auto-compacts as it takes, until A1–A4 + closure
are done. NEVER "hold" / "await direction" / "next session" / context-budget reasoning. If
genuinely blocked on a user-only decision: run full diligence, take the clearly-best option if one
exists, ask once only on a real no-clear-default tradeoff — and keep shipping everything else.
