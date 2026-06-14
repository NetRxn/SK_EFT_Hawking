# Phase 6a Wave 7C `/goal` prompt — the `−3/2` rate + faithful `verlindeEntropy_SU2k` (finishes center-bridge B)

Follow-on `/goal` that finishes 6a.7 to full strength. Wave 7B derived the Kaul–Majumdar `−3/2` to
`O(1)` from the literal Catalan singlet count but stopped short of (i) the `≤C/A` *rate* and (ii) the
named-function redefinition `verlindeEntropy_SU2k = literal sum, not its own saddle` — both because the
real-`A` continuum needs a `Real.Gamma` Stirling-with-remainder not yet in Mathlib. **This wave BUILDS
that infrastructure and finishes the job.** Full context: `docs/roadmaps/Phase6a_Roadmap.md` → Wave 7C
entry + Wave 7B entry + RE-OPENED 2026-06-13 §, and `docs/audits/SUBSTRATE_WEAKNESS_AUDIT_2026-06-13.md`
finding #13.

---

GOAL: Phase 6a Wave 7C — finish the literal-Verlinde `−3/2` to FULL STRENGTH. Five deliverables, all
required, no residual: (1) strengthen the discrete asymptotic from `O(1)` to a quantitative rate —
identify the literal constant `c₀ = −½·log π` and prove `log(catalan m) − (2m·log2 − (3/2)·log m −
½·log π) =O[atTop] (fun m ↦ (1:ℝ)/m)`, kernel-pure from Mathlib quantitative factorial Stirling
(`Stirling.log_stirlingSeq_sub_log_stirlingSeq_succ`); (2) BUILD the upstream `Real.Gamma`
Stirling-with-remainder — `Real.log (Real.Gamma x) − ((x−1/2)·log x − x + (1/2)·log (2π)) =O[atTop]
(fun x ↦ 1/x)` — in a new Mathlib-PR-shaped `lean/SKEFTHawking/GammaStirling.lean`, a GENUINE
CONSTRUCTIVE PROOF via the Bohr–Mollerup convexity squeeze (`Real.convexOn_log_Gamma` +
`Real.Gamma_nat_eq_factorial` + factorial Stirling, squeeze width `O(1/x)`), NOT an axiom; (3) define a
faithful `Real.Gamma`-continuum singlet count / Verlinde dimension `ℝ → ℝ` and prove its `2x·log2 −
(3/2)·log x − ½·log π + O(1/x)` asymptotic from (2); (4) REDEFINE `verlindeEntropy_SU2k` to the faithful
literal/continuum form so the headline function IS the literal log-dimension and `kaulMajumdarS` (the
Gaussian saddle) becomes a DERIVED corollary (`kaulMajumdar_saddle_of_verlinde`), re-anchoring
`gaussianSaddleAsymptotic` + every consumer — the saddle is now a genuine theorem ABOUT the literal
entropy, no longer the `|x−x|=0` self-reference (audit #13 fully closed); (5) restate +
discharge `H_VerlindeKMLiteralSumDerivation` at the strong `≤C/A` rate (`faithful entropy − saddle =
O(1/A)`) from (2)/(3), superseding the `O(1)` discharge. PUBLIC repo (SK_EFT_Hawking). Read CLAUDE.md,
docs/WAVE_EXECUTION_PIPELINE.md, the Phase6a_Roadmap.md Wave 7C + 7B entries, audit #13, and the
relevant Lit-Search/Phase-* analysis blueprints FIRST.

HARD INVARIANTS: axioms exactly {propext, Classical.choice, Quot.sound}; NO new project-local `axiom`
(the Gamma Stirling is PROVEN — that is the point of the wave); NO `native_decide`; NO `sorry`; NO
`set_option maxHeartbeats` in proof bodies (decompose into `have` sub-lemmas; maxRecDepth bumps OK);
never weaken a statement to pass. PARALLEL AGENT may share `main`: stage ONLY your own explicit paths
(never `git add -A` / `-a` / `.`), never push, never touch others' uncommitted files, DO NOT
`rm -rf .lake/build` (use `lake build SKEFTHawking.<Module>` + `lake build SKEFTHawking.ExtractDeps`).
Dev loop = lean-lsp MCP (lean_goal → lean_multi_attempt → write; lean_verify each module). Use lean4
skill semantic search, not grep, for Mathlib decl existence. Every new Prop ships a witness AND a
falsifier; preemptive-strengthening checklist before every statement.

BUILD ORDER (lay the bricks in this sequence; each is shippable kernel-pure on its own):
discrete rate (strengthen `LaplaceMethodAsymptotic.log_singletCount_sub_isBigO`, identify `c₀`)
→ `GammaStirling.lean` convexity-squeeze lemmas → the `log∘Gamma` `O(1/x)` Stirling
→ continuum count + its asymptotic → faithful `verlindeEntropy_SU2k` redefinition + saddle-as-corollary
+ consumer rewire → `H_VerlindeKMLiteralSumDerivation` rate restatement + discharge.

NO-DEFERRAL MANDATE (decisive — per memory `feedback-no-hypothesis-based-descope`): the following are
NOT valid outcomes and MUST NOT be written into any roadmap, summary, or status note — "absent from
Mathlib," "no foothold," "needs new infrastructure," "the Γ-continuum is a large build," "could take
weeks/months," "deserves its own /goal," "tracked-Prop / documented-residual / awaiting-sign-off
fallback." Building the `Real.Gamma` Stirling-with-remainder IS THE WAVE. The decision at every
stop-hook firing is binary: CONTINUE building the next brick, or — only if the work is genuinely
finished or genuinely impossible — CLAIM HONESTLY what is proven. Magnitude, effort, and Mathlib-absence
are ELIMINATED from that decision. The ONLY honest stop is (1) a PROVED mathematical no-go
(decomposition-backed impossibility), or (2) a genuine product decision only the user can make — and
this wave has NEITHER (the Catalan and Gamma asymptotics are standard true results). Funded autonomous
time left unexecuted while the goal is unmet is itself a failure mode.

CLOSURE (all required before the goal is met): full validate.py green; file-gate + `lake build` of
new/changed modules + `lake build SKEFTHawking.ExtractDeps`; `lean_verify` axiom-purity on every new
theorem; AXIOM_METADATA `gaussianSaddleAsymptotic` reason updated (now a genuine theorem about the
literal entropy, audit #13 closed); HYPOTHESIS_REGISTRY reconciled (the `H_VerlindeKMLiteralSumDerivation`
entry now a discharged rate, not an O(1) placeholder); update_counts.py + Inventory + Inventory_Index;
paper26 + D3 + D4 prose updated (the −3/2 now has a derived RATE; the saddle is a corollary of the
literal entropy — keep the boundary honest: the leading 1/4 remains the Wave-9 induced-gravity result,
this wave does not touch it); Stage-13 fresh-context adversarial review for paper26 at 0 blockers;
commit own explicit paths only (autogen reconcile at the close if a parallel agent shares the tree);
write the morning summary into the Phase6a_Roadmap.md Wave 7C section + a memory note; dispatch the
closure reviewer.

/goal autonomous mode: the stop hook is a GO signal, not coercion — do the next increment THIS turn.
Ship kernel-pure increments across auto-compacts until ALL five deliverables + closure are done. NEVER
"hold" / "await direction" / "next session" / context-budget reasoning / "Mathlib-gap so I'll stop."
Blocked on a genuine user-only decision → diligence first, take the clearly-best option, ask once only
on a real no-clear-default tradeoff, keep shipping everything else.
