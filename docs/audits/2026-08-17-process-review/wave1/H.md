# Wave 1 Audit — Slot H (Subagent & Substrate Correction Reviews)

## Findings Summary

| ID | Class | Claim | Recurrence | Escalate |
|---|---|---|---|---|
| H-01 | RW | Redrafts re-discovered the same verification checks (statement-reading discipline) that ten agents on Aug 15 already established | 3 independent redrafts (D9, D10, D7) | YES |
| H-02 | OC | Brief called carrier types "one-field structures"; D10 redraft found carriers are **uninhabited across all modules** (zero external instantiation) | D10 confirmed; E2 read same substrate; independent finding | YES |
| H-03 | AB | D10 redraft brief stated probe-gate NarrativeGrounding "blocks on SUPPORTS edge," but `grep -c SUPPORTS scripts/build_graph.py` → **0**; gate structurally unpassable | Gate already filed as live defect (graph_atlas.py); D10 redraft re-discovered it | YES |
| H-04 | VG | D7 redraft found KZM exponent labeled "defect-density" but proved as "freeze-out-time"; primary source (Tindall et al., Fig. 5) measures the **reciprocal** (`μ = (1+νz)/ν`), not the density | D7-01 CRITICAL + substrate correction agent independently confirmed | YES |
| H-05 | CL | D10 brief mentioned "lab notebook at LAB_NOTEBOOK_INDEX.md" but file **does not exist**; brief called it "durable entry point" then contradicted itself ("if notebook missing, code wins") | Brief itself internally inconsistent; redraft worked from goal prompt instead | YES |
| H-06 | DD | D9 brief claimed "`\texttt` count = 15 → audit's 169 references cannot be prose," but D9 defines `\lean` macro (using texttt) **196 times**; prose population is 176, not 15 — token-level scan trap | D9 redraft found and reported; brief warned about this exact trap | YES |
| H-07 | FA | Heat-kernel correction agent searched for Vassilevich Eq. (4.40) "Christensen-Duff convention" but 4.40 is the **DeWitt initial condition** (massless scalar), not a coefficient table — brief's citation attribution was wrong | Agent re-read PDF; found correct equations (4.27, 4.28, 4.35, Table 1) | YES |
| H-08 | TF | D7 prose-review output task (`a57b4fdea41aedce2`) reported it "never returned"; agent waited ~45min then gave up; no fallback mechanism for timed-out subagent output | Agent was designed to wait; task was silently killed; lead only learned from explicit "not done" report | YES |
| H-09 | TP | D3 heat-kernel redraft discovered **two independent physics sign errors** (`a₂` missing spinor trace × 4; `a₄` coefficients all flipped) — both had **passed prior review** | Redraft re-verified from primary sources; both defects confirmed kernel-false; required statement rewrites | YES |
| H-10 | VG | KZM substrate agent found `surface_gravity_bounds_kzm_exponent` headline stated "surface gravity bounds exponent" but κ-independent (κ cancels out); docstring mislabeled the dependent variable | Agent confirmed via algebra; D7-02 MAJOR | YES |

---

## Pattern: Verification Discipline Regresses

**Three redrafts, ten Aug-15 agents, same finding.** Both D9 and D7 redrafts report re-discovering that "read the actual statement in Lean" catches errors (tautologies, reflexive equality, wrong theorems cited by name, rfl-bodied definitions), and the brief warned about this. Yet D10 redraft also spent time **re-learning that `lean_local_search` returns empty even for declarations that exist**, which the brief warned about twice. The eight checks (`lean_verify`, carrier-type inspection, statement-vs-docstring comparison) are load-bearing and have been validated 11 times now. 

**Cost:** Each agent spends 10–15% of runway re-verifying mechanics that have become standard. Redrafts do not inherit the Aug-15 agents' developed discipline; each starts from the brief.

**Recommendation:** Archive this discovery as a pre-decision block: "Always read substrate statements via Lean, never by name; `lean_local_search` empty ≠ absent." Load it into each fresh redraft via SessionStart boilerplate.

---

## Pattern: Carrier-Type Defects Evade Initial Capture

**D10's uninhabited carriers passed initial review.** The brief instructed carrier-type checking; D10 redraft discovered the carriers (`GroundStateData`, `DensityVariational`, `LevyLiebData`) are referenced in no external module and inhabited nowhere. A theorem over an uninhabited type is universally true, and D10's docstring used this to paper over missing content ("the proof is empty because the hypothesis is refuted"). This is a **class of defect the verification-discipline rules are supposed to catch**, yet it surfaced only in the redraft. Two causes: (a) the carriers are in the *same* file, so `grep -rn "GroundStateData"` doesn't trigger a secondary-consumer check; (b) the gate `LeanProofSubstance` and the brief's carrier-type instruction didn't combine to a joint check — each agent read one instruction in isolation.

**Cost:** D10's redraft had to reclassify three theorems as "not substantive"; a structural audit before redrafting would have surfaced this.

**Recommendation:** `lean_local_search` should report *all* references (including same-file neighbors), not just cross-module. Or: add a gate that flags theorem-carrying structures with zero external instantiation.

---

## Pattern: Physics Sign Errors Survive Layered Review

**Heat-kernel `a₂` (spinor-trace omission, 4× error) and `a₄` (five independent coefficient errors) passed two prior reviews.** The manuscript claimed both and the Lean claimed to prove them; both are false. The errors are **not model-dependent or encoding-swaps** — they are arithmetic misreadings (Vassilevich Eq. 4.27: `6E + R = -R/2`, traced as `tr 1 = 4N_f`, not 1). The substrate-correction agent re-read the primary source at page level and caught both via first-principles derivation. The D3 redraft never ran because the correction happened first.

**Cost:** Two theorems with false statements sat downstream in `G_N_from_a2`, `higherCurvature_stelle_sum_eq`, and cross-bridges (`LinearizedEFE.G_N_emerg_at_alpha_one`). A production run would have certified these claims.

**Recommendation:** For high-consequence numerics (effective coupling, quantum bounds), require the drafter to **re-derive from primary sources independently** before writing the Lean. This is not new — the CLAUDE.md rule already forbids "we cite what we have not read" — but the redraft process did not enforce it as a stage gate.

---

## Contradiction: Brief vs. Sources (KZM Exponent)

The heat-kernel substrate-correction agent's brief stated D7's findings and asked to "fix the substrate." D7 redraft filed D7-01 (CRITICAL): the KZM exponent is mislabeled "defect-density" but constrained as "freeze-out-time." The substrate agent verified this at the source and discovered **the brief had it backwards**: Tindall et al.'s Fig. 5 axis label is `d̃ = t_a^{-1/μ} d`, meaning `μ = (1+νz)/ν`, which is the reciprocal of the time exponent. The module proves the time exponent is < 1; the density exponent is > 1 in 3D. Neither the "defect-density" label nor `α < 0` was correct; both required remeasurement and restatement. The brief's confidence in "either the name or the constraint is wrong" proved **both were wrong, and the correction involved a reciprocal law, not a swap**.

**Escalation:** The brief was a corrective brief (operator already knew the module was wrong). The substrate agent re-verified from first principles and found a different error than briefed. This is correct process — source-of-truth is the PDF, not the brief — but it shows the brief itself was missing a layer of grounding.

