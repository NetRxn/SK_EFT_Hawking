# Phase 5q.G — Genuine unconditional `Ω₄^{Pin⁺} ≅ ℤ/16` (clean-room restart of the full-strength program)

**Status:** 🆕 OPENED 2026-06-24 as a **clean-room restart** of the full-strength unconditional goal that
5q.F pursued. 5q.F's *verified results* are inherited as bedrock; 5q.F's *in-flight L2 state* (the polluted
route-thrash) is **left behind, not carried**. Every item seeded here was **ground-truth-vetted against Lean
source + git + `counts.json`** (not against the 5q.F lab notebooks, which are the suspect record we are
deliberately not trusting). Vetting provenance: `Lit-Search/Phase-5qF/L2_DEVELOPMENT_TRACE.md` PARTs III–VI
(the 5q.F post-mortem) + the 2026-06-24 verification pass logged in this roadmap's §3–§4.

**Owner workstream:** public `SK_EFT_Hawking` Lean.
**Tracker = this file.** Lab notebook: `Lit-Search/Phase-5qG/LAB_NOTEBOOK_INDEX.md` (INDEX entry point) +
`Lit-Search/Phase-5qG/LAB_NOTEBOOK.md` (active log). Negative register: `docs/dev-loops/SETTLED_FORKS.md`.
Continuation of [Phase 5q.F](Phase5qF_GeometricBordism_Roadmap.md) — the geometric-bordism / 16-convergence work.

---

## 0. Why 5q.G exists (read first)

5q.F **proved a great deal of genuine mathematics** (see §3 bedrock) but its endgame — the *fully
unconditional* full-carrier `Ω₄^{Pin⁺} ≅ ℤ/16` — never landed, and its final days degenerated into a
**route-thrash spiral**: 5 reverts in ~36 h, two of them structurally-identical "kronecker-altitude"
re-seeds, driven by a harness that re-injected a dead route as the "current state" every compaction
(`5d7eb484 "bug: goal prompt (example of what never to do with re-injection - caused 5qf L2 churn for 24h)"`).
The diagnosis is in `L2_DEVELOPMENT_TRACE.md` PART V.

5q.G is the corrective: **a clean roadmap + clean notebook seeded only with what is verified-complete or
verified-settled**, so the next `/goal` loop re-orients from a *true* anchor, not a polluted one. Two
disciplines are non-negotiable here and are the reason this restart exists:

1. **Everything seeded is vetted.** No claim enters this roadmap or the 5q.G notebook unless it was confirmed
   in source/git/`counts.json`. "The notebook says it's done / dead" is not evidence — the **kernel and the
   git history are**. (This is the lesson of the 5q.F pollution: notebook self-claims drifted from ground
   truth, and re-seeds were built on stale "current state.")
2. **No-gos are typed by *strength*, never inflated.** A *kernel-checked impossibility* is permanent; a
   *policy/route ban* is a choice; an *off-path-but-sound* lemma is neither. Mislabeling an off-path lemma or
   an over-defer conclusion as a "wall" is itself pollution — it walls off live territory. See §4.

---

## 1. The directive (read every bootstrap/compaction — a goal-mode agent MUST NOT re-defer this)

This phase finishes the **fully unconditional** convergence: genuine `Ω₄^{Pin⁺} ≅ ℤ/16` (with
`ker(abkGrade) = ⊥`) and genuine `Ω₅^{Spin-ℤ₄} ≅ ℤ/16`, dropping **every** disclosed binder
(`SmithInflow`, `pin4_abutment`, `PinPlusBordismLandmark`) and the **posited carrier**
`Omega4PinPlusBordism`, so `CommonOrigin.sixteen_convergence_*` carries no hypothesis. The mechanism is the
geometric **w₂/Wu tower L1→L5**, of which **L2 (Poincaré duality via the cap-product MV connecting square)
is the single unlock**.

**Continue-vs-stop rule (locked, inherited from 5q.F, user 2026-06-14/15):**
- Legitimate stops are ONLY (1) a *proved* (decomposition-backed, kernel-checked) mathematical no-go, or
  (2) a genuine product/strategy decision only the user can make.
- **NOT stops — build straight through:** "absent from Mathlib," "no foothold," "needs upstream infra,"
  "multi-week/month," "large program." We routinely build upstream infra; absence is the work. (memory
  `feedback-no-hypothesis-based-descope`, `feedback-no-disclosure-stopping-in-goal-mode`,
  `feedback-no-context-window-judging`.)
- Kernel-purity is non-negotiable: axioms EXACTLY `{propext, Classical.choice, Quot.sound}`; **no new
  project-local `axiom` without explicit user sign-off**; no `sorry`/`native_decide`; no
  `maxHeartbeats`/`synthInstance.maxHeartbeats` in proof bodies (a heartbeat wall = wrong architecture →
  decompose). A genuinely-absent named landmark is carried as ONE disclosed tracked `Prop` (registry +
  discharge plan), never an axiom, and only after the surrounding infra is built.

**Anti-spiral rules (NEW — the 5q.F failure-mode guards; PART V/VI of the trace):**
- **No frozen "CURRENT STATE" that names engines.** The live state is *recomputed* from git + the notebook
  FRONTIER each turn (the live-anchor harness, `LIVE_ANCHOR_REDESIGN_SPEC.md`), never a prose snapshot that
  can name a dead route. The 5q.F marker's `CURRENT STATE: … kronecker_cap_eq_kronecker_rcap …` block is the
  exact re-seed vector that cost 24 h — it must not be reproduced.
- **The altitude lock is by ALTITUDE, not by name.** The L2 close spine stays at **cap-altitude
  (cap-Leibniz)**; the σR side joins via the **pairing adjunction as a sub-step (Fact A)**, never by
  re-spining the whole close to the kronecker altitude. Any framing of `_of_crossRealization` /
  `kronecker_pd_fold_fund` / `kronecker_cap_eq_kronecker_rcap` / `chainIncl_rcap_cover_agree` /
  `of_hcup_linked` as "the close spine" or "a whnf-dodge breakthrough" **is the re-seed tell** — stop.
- **SETTLED_FORKS is FIRST_ACTION.** Before any "this is impossible / needs a banned thing / let me
  re-derive whether X works" reasoning, grep `docs/dev-loops/SETTLED_FORKS.md` + §4 below. If it's listed,
  it's decided.
- **Verification invariant = ROUTE/ALTITUDE, not "commit present."** When asked to verify state after a
  compaction, check that the *route and altitude* match the register — not merely that a commit exists.
  "Commit present" ≠ "on the sanctioned route" (the 5q.F false-all-clear).

---

## 2. The goal (what "genuine unconditional" requires)

The four-facet convergence (5q.E built every box at the ℤ₁₆-algebra level; 5q.F derived much of it but on a
**posited carrier** / behind a **disclosed landmark**):

```
Ω₅^{Spin-ℤ₄} ≅ ℤ16  ──(Smith hom)──►  Ω₄^{Pin⁺} ≅ ℤ16  ──┬─► σ mod 16 (Rokhlin)
                                                          └─► c₋ mod 16 (Kitaev)
```

**The genuine-unconditional target = collapse the carrier and drop the disclosures:**
1. The bordism group is the **genuine** `DataBordismGrp` (real structured `SingularManifold`s over Mathlib),
   NOT the posited `Omega4PinPlusBordism` (= `Quotient (M ~ N ↔ 16 ∣ σ_M − σ_N)`, a signature-mod-16
   quotient posit — near-definitional injection — the 5q.F source itself defers "to Phase 7+").
2. The grade is **injective (`ker = ⊥`, the floor collapse)** and **surjective (ABK ≤16 completeness)** —
   both *derived*, not posited. ⚠ This requires the **complete/faithful** Pin⁺ grade (the w₂-refined
   tangential datum, the landmark's `ξ`), NOT the *current* `abkGrade` on `pinPlusData`: the source states
   plainly (`PinPlusTangentialData.lean:265-268`) that the current `abkGrade`'s kernel is the genuinely
   nontrivial `Ω^O` floor, so `ker(abkGrade) = ⊥` is "**unreachable here**." G3 builds the faithful grade;
   it does not try to collapse the current one. See §3b/G3.
3. The lower bound (order-16 generator) is **geometric** — the Guillou–Marin/Kirby–Taylor square-root
   relation `hGM` discharged, not carried as a hypothesis.
4. `CommonOrigin.sixteen_convergence_*` drops `SmithInflow` / `pin4_abutment` / `PinPlusBordismLandmark`.

The L1→L5 w₂/Wu tower is the route: L1 `[M]` fundamental class ✅ → **L2 Poincaré duality (the unlock —
architecture now RESOLVED, see G1: the close is the ∈-boundaries PAIRING discharge of the KEY [route ii],
NOT the exact χ [route i, unreachable — σR has no exact-chain bridge] and NOT a kronecker re-spine [route
iii, banned]; remaining work is the grind, not the route)** → L3 Wu/Sq² floor-collapse criterion ✅(parametric) →
L4 build the faithful grade + w₂ bordism-invariance ⟹ `ker = ⊥` → L5 ABK completeness + geometric `hGM`
⟹ surjective / `≤16` cap discharged.

---

## 3. VERIFIED BEDROCK — carry forward, DO NOT rebuild (vetted 2026-06-24, source-grounded)

All of the following were confirmed by **reading the actual Lean source at HEAD `7d893548`** and
cross-checking library membership against `counts.json`'s `module_names`. ⚠ **Provenance note:** `counts.json`
itself was last regenerated at `b7b91c81` (2026-06-22); the ~131-commit delta to HEAD is harness / security /
L2-WIP only (no library-math change), so its module list + aggregate (0 axioms, 0 sorry, 14152 substantive
theorems) still describe the library — but a fresh `update_counts.py` regen is part of G6 closure, and the
bedrock below is certified by the per-item source reads, not by that snapshot's numbers. **Genuine =
hypothesis-free, real Mathlib content, no posit.** ("Key declarations" lists theorems AND defs/modules; the
"Module(s)" column names the in-library home.)

### 3a. Genuine-complete (seed as solid bedrock)
| Item | Key declarations | Module(s) (all in-library) |
|---|---|---|
| W1 Brown ℤ₈ (ABK heart) | thm `brownStd_order_eight`, `gaussSum4_*`; def `gaussSum4`, struct `Z4Quadratic` | `BrownInvariant.lean` |
| W2 general Brown extraction | thm `brown_stdQuadratic_add`, `brown_stdQuadratic_surjective`; def `brown` | `BrownInvariant.lean` |
| W4 finite Ext height-4 cap | thm `col4_height_eq_four = 4` (genuinely `decide`-able); supporting modules `KspResolution`, `JokerModule`, `PinPlusExtBound` | `PinPlusHeight4.lean` (+ named modules) |
| W5 regular-value + Smith infra | `SmithRegularValueGeneral`, `SmithLineBundle`, `ManifoldRegularValue`, `smithDataHom` | `Smith*.lean` |
| L1 fundamental class | `fundamentalClass_ne_zero`, `homologyTopEquivZMod2` (genuine: CompactSpace + ChartedSpace, no posit) | `SingularFundamentalClassExist.lean` |
| Bordism machinery | `BordismGroup`, `DataBordismGrp`, `pinPlusData`, `abkGrade`, the from-scratch singular ℤ/2 (co)homology + excision + MV substrate | `BordismGroup.lean`, `TangentialDataBordism.lean`, `PinPlusTangentialData.lean`, `Singular*.lean` |
| L2 descent (reducers, in-library, sorry-free) | `subHomConnecting_openDuality_of_hcup_linked` (the residual carried as an honest ∀-Prop hypothesis) | `SingularConnSquareClose.lean:262` |

### 3b. Verified but **CONDITIONAL** — these LOOK done but are parametric / define-the-target / posited-carrier (the subtle 5q.F pollution; **these are precisely what 5q.G must discharge**)
| Item | What makes it conditional | Full-strength replacement (the 5q.G work) |
|---|---|---|
| W3 lower bound `pinPlus_RP4_order16_from_ABK` | takes `hGM` (Guillou–Marin/Kirby–Taylor √-relation) as a **disclosed input**; concrete corollary uses a **posited `signature = 1`** | discharge `hGM` geometrically (G4/L5) |
| W6/W7 sandwich + Ω₅ (`*_via_sandwich`) | hypothesis-free in signature BUT rest on the **posited carrier** `Omega4PinPlusBordism` = `Quotient(16 ∣ σ-diff)`; genuine Pin⁺/η relation "deferred to Phase 7+" | recast on the **genuine** `DataBordismGrp` (G5) |
| W8 `adamsAbutment := ZMod(2^height4)` | self-described **"define-the-target move"** | derive the abutment from the genuine carrier, or retire it (G5) |
| W8 unconditional quotient `dataBordism_quotient_abk_equiv_zmod16` | genuine carrier + hypothesis-free, BUT it is `DataBordismGrp ⧸ ker(abkGrade)` with **`ker ≠ ⊥`** (the Ω^O floor) — near-definitional | the **floor collapse `ker = ⊥`** (G3/L4) upgrades this to the genuine *full-carrier* iso |
| W8 `sixteen_convergence_finite_discharge` / `_genuine_carrier` | carry `pin4_abutment` / `PinPlusBordismLandmark` (bundling Kirby–Taylor ≥16 + AHSS ≤16 as **hypothesis fields**) | drop the binders after G3+G4 (G5) |
| L3 Wu/Sq² | `wuW2_eq_zero_iff` proven **parametric over abstract PD data**; consumer is the L2 PD instance | instantiate on the genuine PD from G1/L2 (G2) |

### 3c. Salvageable engine leads (NOT bedrock — OFF the corrected G1 path; re-vet before use)
> Two leads were uncommitted 5q.F WIP; to keep the 5q.G working tree clean for the arm they were **stashed**
> 2026-06-24 (`git stash@{0}` "5qf leads preserved pre-5qG arm"). Recover with `git stash show -p stash@{0}` /
> `git stash pop`. Both are OFF the corrected G1 ∈-boundaries route (per the audit), so they are LOW-value now
> — recoverable insurance, not part of the live plan:
- `cap_relCycle_homology_singularSd` (was untracked `HcupAbstract.lean`, sorry-free) — cap subdivision-invariance
  (homology-class); the corrected G1 route uses the pairing form, not this. **Stashed; re-verify kernel-pure
  before any use.**
- `mvSes_shortExact` (was an uncommitted edit to `SingularChainComplexCat.lean`, NOT in committed HEAD / not
  in the library) — route-c's SES brick; route-c is policy-banned. **Stashed; re-verify kernel-pure before any
  use.**
- `cap_fund_eq_cap_z0` / `cap_fundCycleW_eq_cap_z0` (committed in `SingularConnSquareCloseNC.lean`, a non-library
  WIP file) — proven in source, currently **unused/off-path** (NOT a no-go); re-vet on import; available if a
  future close-path needs them.

---

## 4. SETTLED FORKS — typed by strength (seed into the 5q.G notebook register; mirror `SETTLED_FORKS.md`)

> Read FIRST before any impossibility/route reasoning. Typed by *strength* — do not inflate.

**RESOLVED — do NOT re-derive the worry (settled, with the resolution carried):**
- **"cap σR-connecting needs the banned `relCohomMvConnecting_eq` formula / Kronecker non-deg"** → FALSE /
  SUPERSEDED (coach-resolved 4× — the #2 goldfish fork). The committed engine `cap_coboundary_cochainSplit_eq`
  / `_subdiv` (`a3f217e1` / `2f58618c`, kernel-pure) proves the chain-level σR-side identity **gap-free** —
  its proof uses only `cap_relCochains_subspaceChains_eq_zero` + `cap_leibniz` + ℤ/2, **never** the formula.
  (`ω = g_rep`, the source cocycle, NOT σR_rep.) Already in `SETTLED_FORKS.md` as
  `cap-sigmaR-connecting-needs-banned-formula`. Seed the **resolution** (the engine), not just the caution.

**KERNEL-CHECKED IMPOSSIBLE (permanent, certain):**
- **`Mfd := H¹`** — `dataBordism_two_torsion_of_revStr_trivial` (`PinPlusGenuineCarrierIso.lean:65`, in
  library): trivial `revStr` ⟹ `x+x=0` ⟹ 2-torsion ⟹ never ℤ/16. The genuine carrier MUST use a
  non-trivial conjugation (`pinPlusData`). **Never re-attempt `Mfd := H¹`.**

**POLICY / ROUTE BANS (a choice, not an impossibility — human-reviewed):**
- **Kronecker-altitude close of L2** (`_of_crossRealization`, `kronecker_pd_fold_fund`,
  `of_hcup_linked`-as-spine) — reverts `a79f1912`, `3ea6b739`. Banned as an **altitude/route**; the L2 spine
  stays at cap-altitude. (The kronecker *sub-lemmas* used inside the pairing adjunction Fact-A step are fine;
  the ban is on making kronecker the *spine*.)
- **Route-c (snake / MV-SES + `SnakeInput`)** — user ruling ("B↔C thrashed for DAYS — NON-NEGOTIABLE").
  Last-resort fallback only. NOTE `mvSes_shortExact` is proven & reusable — the route is not mathematically
  dead, only ruled out as a path.

**CAUTIONS (argued/tooling, NOT kernel no-gos — do not inflate to "impossible"):**
- **Homology-class square lift / false `hmem`** (`relCohomMvConnecting_eq_mk_coboundary_cochainSplit`,
  `SingularRelCohomMvConnectingGeom.lean:134`) — the lemma is TRUE & proven *conditional on `hmem`*; `hmem`
  is *argued* (not kernel-checked) undischargeable at cover level. Stay at chain-pairing altitude; don't seed
  as kernel-impossible.
- **`congrArg` direct chain-equality (X=Y) for `hmatch`** — revert `b02b0d08`; X=Y is *strictly stronger than
  the truth* (`hmatch` holds iff `X+Y ∈ boundaries`, the cocycle slack is load-bearing). Use the
  ∈-boundaries form. Argued unsound, not kernel-disproven.
- **`kronecker_cap_chainIncl_eq_rcap_chainIncl` (MatchLHS:83)** — the *lemma is true & proven*; only the
  `lean_multi_attempt` "it closes" signal is a **tooling false-positive** (empty-goals ≠ in-file close).
  Verify closes with `lean_diagnostic`/`lake build`. Do NOT ban the lemma.

**OFF-PATH-NOT-DEAD (do NOT seed as no-gos):**
- **σR z₀-reduction** (`cap_fund_eq_cap_z0`, `cap_fundCycleW_eq_cap_z0`) — sound, proven, currently unused.
  Off the live close-path, NOT banned.

**ANTI-NO-GOS — REJECTED over-defer conclusions (seed the NEGATION as a trip-wire):**
- **"A fully-unconditional proof is precluded"** — REJECTED (user + stop-hook). `dataBordism_quotient_abk_equiv_zmod16`
  is strictly unconditional; the floor-collapse is a build-list, not a wall. If you find yourself concluding
  this, that IS the over-defer failure mode.
- **"The topological grounding / upper bound is the wall (needs absent spectral-sequence infra)"** —
  REJECTED; the route was finite all along (decidable height-4 cap). Absence of Mathlib infra is the *work*.

---

## 5. The open program — gates (the forward plan)

Each gate: target · consumes · DONE criteria · status. **G1 is the unlock; G2–G5 cascade from it.**

### G1 — L2 close (THE UNLOCK): discharge Poincaré duality
- **⛔⛔ RESOLVED — DO NOT RE-LITIGATE (the close architecture is FINAL; this is the project's single most
  re-discovered fork — 5q.F: 5 reverts in ~36 h; 5q.G turns 1–10 re-derived it AGAIN). The L2 close is ROUTE (ii):
  the PAIRING discharge of the ∈-boundaries KEY, keeping `of_chainMatch` as the cap-Leibniz SPINE.** Any future
  session that concludes "grind the exact χ at NC:1040" (route i) OR "re-spine via `of_hcup_linked`/`of_match`/
  `of_crossRealization`" (banned) has re-entered the spiral → STOP and re-read this block. Verified end-to-end
  against the live proof + engine signatures + git history on 2026-06-24 (turn 10).

- **The three routes, with FINAL status (code-grounded — engine signatures are the arbiter):**
  - **(i) Witness / exact-χ route** — `connecting_square_close_cocycle_fund` → the exact CHAIN χ@`NC:1040`
    `cap σR_rep fund_∩ = chainIncl(U∪V)(∂(chainIncl_U zA)) + cap g_rep ∂ρ`. ❌ **UNREACHABLE BY CONSTRUCTION:** it
    needs `σR_rep` as an EXACT chain, but `relCohomMvConnecting` has only (a) the **banned** cochain realization
    (`relCohomMvConnecting_eq_mk_coboundary_cochainSplit` Geom:134) whose `hmem` is genuinely false (δφ is not a
    union-cochain un-subdivided — *even at `infCompactᶜ`, which is itself the union `legSplitUᶜ∪legSplitVᶜ`, same
    straddling simplices*), and (b) the scalar pairing (Geom:73; + non-deg ⟹ **mod-boundary**, never an exact
    chain). The χ@1040 is an OVER-REDUCTION (`connecting_assembly_zmod2` + `cap_chainBoundary_relBoundaries_transport`),
    same over-strength class as the reverted `b02b0d08` X=Y route. ⚠ **The turn-6 "coach decision B" correctly
    banned of_hcup-as-spine but then WRONGLY pointed the FRONTIER at this route** ("the cap-altitude χ at NC:1040");
    that pointer was itself a drift, repeated again at the turn-8 coach. The claim "`cap_coboundary_cochainSplit_subdiv_fund`
    discharges the σR-side gap-free" is imprecise — that engine (ω=g_rep) discharges the **g_rep/δφ** side (`hVleg`);
    σR still needs Fact-A. **DO NOT grind route (i).**
  - **(ii) Pairing discharge of the ∈-boundaries KEY — ✅ THE CLOSE.** The spine (`of_chainMatch` → `hmatch_close`
    → `factB_transport`, NC:885–915) already leaves the **∈-boundaries KEY** (`NC:~924`, confirmed by `lean_goal`):
    `seam²(boundaryExtract zB) + pullbackDualityₗ(infCompactᶜ)(U∩V)(fundCycleW…) σR_rep ∈ boundaries(sub(U∩V))(p+1)`.
    Discharge it via the PAIRING: `Homology.mk_eq_zero` (SingularCapHomology:48 — the KEY chain is a cycle) →
    `homology_eq_zero_of_kroneckerH` (PD:75) → ∀ cocycle `a'rep`, cup-cap adjunction `kronecker_cap_eq_kronecker_rcap`
    (MatchLHS:73) → the σR leg via the UNCONDITIONAL `relKroneckerH_relCohomMvConnecting_cover_partition` (Geom:73)
    + `hσR` (cocycle pairing — slack dies); seam + g_rep legs via the committed cap engines → cancel. **DROP**
    `connecting_assembly_zmod2` + the entire witness route (NC:924–1040). σR is handled ONLY via the pairing —
    there is NO exact-chain σR bridge; this is a MATH FACT, not a route preference. Then wire the cross-realization
    descent → `PoincareDual4Mid`/`PoincareDual4Lo` become theorems.
  - **(iii) `of_match` / `of_hcup_linked` / `of_crossRealization` AS THE SPINE** — ❌ **BANNED** (`SETTLED_FORKS.md`
    `kronecker-altitude-respine`; reverts `a79f1912`, `3ea6b739`, `673c075d`). These pair the WHOLE square at the
    top (re-spine the close to kronecker altitude). **Categorically different from (ii)**, which keeps the cap-Leibniz
    spine and pairs only the final KEY sub-step.

- **🔑 THE distinction that ENDS the spiral (spine vs sub-step):** routes (ii) and (iii) both *use the pairing*, but
  (ii) uses it as the **final ∈-boundaries SUB-step discharge** of the KEY (cap-Leibniz spine kept) while (iii) makes
  it the **SPINE**. `SETTLED_FORKS` says it exactly: *"Kronecker sub-lemmas inside the Fact-A pairing step are fine;
  the ban is on the spine."* And the ALTITUDE LOCK: *"σR joins via the pairing adjunction … as a SUB-step / the final
  ∈-boundaries discharge, NEVER as the spine."* Route (ii) IS that sanctioned sub-step. Both prior errors —
  route (i) (turns 6–9: doomed exact χ) and route (iii) (turns 1–5 + the 5q.F reverts: banned re-spine) — are now
  named and closed.
- **Banned-route tell (safeguard while grinding (ii)):** if the discharge needs the SPECIFIC `a79f1912`-reverted
  bricks (`cup_pair_fund_eq_pair_z0`, the cup→absolute simp, `relKroneckerH_relCohomMvConnecting_rep`,
  `kronecker_eq_relKroneckerH_mk`), that is spine-relocation in disguise → STOP. Use Geom:73 + the standard cup-cap
  adjunction (`kronecker_cap_eq_kronecker_rcap`) only. Final-discharge homology non-deg = `kroneckerH_injective`
  (LEGIT); chain-level Kronecker σR↔g_rep bridging is the BANNED non-deg. The `of_chainMatch` castChain whnf →
  dodge at cap-altitude via def-head-match, NEVER via the kronecker fold (that whnf-dodge-as-re-spine WAS the spiral).
- **Consumes:** the in-library descent reducers + cap-Leibniz engines (§3a/§3b); the salvageable leads (§3c).
- **⚠ Integration scope:** the descent reducer `subHomConnecting_openDuality_of_hcup_linked` is in-library
  (`SingularConnSquareClose`) but the WIP χ files (`SingularConnSquareCloseNC`, `SingularChainComplexCat`)
  are NOT — NC is imported by 0 files and `SingularConnSquareClose` does not import it. "Wire into the
  library" is therefore real integration work (re-home the χ + its engines into an imported module), not just
  "delete the sorry."
- **DONE:** the L2 close file is zero-sorry & wired into the library; `#print axioms` of the close theorem =
  EXACTLY `{propext, Classical.choice, Quot.sound}`; `PoincareDual4Mid`/`Lo` are theorems; `lake build` +
  `validate.py` clean; fresh `skeft-qa:adversarial-reviewer` (separate context) ZERO BLOCKER.
- **Status:** OPEN — **architecture FINAL (route ii, resolved turn 10); grinding.**
  - **✅ Brick 1 (turn 11, GREEN + kernel-pure `{propext, Classical.choice, Quot.sound}`):**
    `mem_boundaries_of_kroneckerH_zero` (`SingularConnSquareCloseNC.lean:889`) — the route-ii **final
    ∈-boundaries discharge engine**: a cycle pairing to 0 against every cocycle is a boundary
    (`homology_eq_zero_of_kroneckerH` + `Homology.mk_eq_zero`). General, reusable, no banned formula.
  - **✅ Brick 2 (turn 12):** backed the apex up — dropped the witness route (old 924–1055) + `connecting_assembly_zmod2`;
    `subHomConnecting_openDuality` now applies `mem_boundaries_of_kroneckerH_zero` at the ∈-boundaries KEY (NC:937),
    splitting into (A) cycle + (B) pairing.
  - **✅ Brick 3 (turn 12, GREEN — verified `goals:[] diagnostics:[]`):** Goal A (the KEY chain is a cycle):
    `add_mem` of `mapChain_mem_cycles ×2 ∘ boundaryExtract_mem_cycles` (seam leg) and `pullbackDualityₗ_mem_cycles`
    with `hzS = fundCycleW_boundary` (σR leg). NC:938–947.
  - **◐ Brick 4 (the pairing discharge) — DECOMPOSED (turn 13):**
    - **✅ ℤ/2 wrapper PROVEN GREEN:** `rw [kronecker_add_right, add_eq_zero_iff_eq_neg, CharTwo.neg_eq]` splits +
      ℤ/2-reduces Goal B to the **LEG MATCH** (NC:949–956). (Note `CharTwo.add_eq_zero_iff_eq` does NOT exist.)
    - **◐ Leg-match (= hcross at the pairing level) — σR-LEG DONE (turn 15, GREEN):** the ℤ/2 wrapper reduces Goal B
      to `kronecker ω.1 (seam²(boundaryExtract zB)) = kronecker ω.1 (pullbackDualityₗ σR_rep fund)`. **✅ σR-leg
      reduced:** `conv_rhs => change kroneckerH (p+1) (mk ω) (relativeDualityK _ _ (N+1+1) p _ _ fundCycleW_boundary
      (RelativeCohomology.mk _ (N+1+1) σR_rep))` (defeq via relativeDualityK_mk + kroneckerH_mk_mk) then
      `rw [kroneckerH_relativeDualityK_mk_eq_relKroneckerH … (chainIncl_rcap_mem_relCycles … fundCycleW_boundary … ω)]`
      → the σR side is now `relKroneckerH (infCompactᶜ) (mk σR_rep) [chainIncl(U∩V)(rcap ω fund)]`. (Friction notes:
      `change` needs k written as `N+1+1` not `N+2`, and the cohomology as `RelativeCohomology.mk` not `Quotient.mk`,
      to match the bridge pattern; hWcyc provided inline.)
    - **▶ Leg-match remaining (the ONLY L2 sorry, NC:962):** `kronecker ω.1 (seam²(boundaryExtract zB)) =
      relKroneckerH (infCompactᶜ) (mk σR_rep) [chainIncl(rcap ω fund)]`. NEXT: `hσR` (σR_rep = relCohomSetCongr
      (relCohomMvConnecting g_rep↾)) → Geom:73 / `rhs_pairing_reduce` (RHSPairing:42) evaluates the connecting pairing
      → `kronecker(δφ)(Sdʲ…)`; then the SEAM leg → cover-partition V-part → match. Observe the banned-route tell.
  - Then re-home the χ + engines into an imported module and wire the cross-realization descent →
    `PoincareDual4Mid`/`Lo` become theorems. (Turns 1–10 = re-seed-correction + the architecture audit/resolution;
    turn 11 = first Lean brick.)

### G2 — L3 instantiation: w₂ floor-collapse criterion on the genuine PD
- **Target:** instantiate `wuW2_eq_zero_iff` (proven parametric, §3b) on the genuine PD instance from G1.
- **Consumes:** G1; L3 (`PoincareDualityWuFormula`, `SingularCupH13`, `SingularBockstein`).
- **DONE:** `w₂ = 0 ↔ v₂ = v₁²` holds on the real closed-4-manifold data, kernel-pure.
- **Status:** OPEN (gated on G1). L3 itself is built.

### G3 — L4 floor-collapse: build the FAITHFUL grade, prove ITS kernel `= ⊥`
- **⚠ Framing (source-checked, `PinPlusTangentialData.lean:265-268`):** the *current* `abkGrade` on
  `pinPlusData` is **deliberately not** the complete grade — its kernel is the genuinely-nontrivial `Ω^O`
  floor, so `ker(abkGrade) = ⊥` is **"unreachable here."** G3 is NOT "collapse the current grade's kernel"
  (that is impossible and re-deriving it is a goldfish trap). G3 = **construct the complete/faithful Pin⁺
  grade** (the w₂-refined tangential datum, i.e. the landmark's `ξ` with `w₂(TM)` as a genuine manifold
  invariant making the conjugation non-trivial) and prove **its** kernel is `⊥`.
- **Target:** w₂(TM) bordism-invariance (from the L1–L3 tower) ⟹ the `Ω^O` floor is refined away for the
  faithful grade ⟹ `ker = ⊥`, upgrading the near-definitional quotient iso (§3b) to the genuine full-carrier
  `Ω₄^{Pin⁺} ≅ ℤ/16`. (The `≤16` upper-bound half is G4.)
- **Consumes:** G1 (PD), G2 (Wu criterion), the bordism machinery (§3a), G4's `≤16` cap.
- **DONE:** the faithful grade is constructed and `ker = ⊥` of it is kernel-pure; genuine full-carrier
  injectivity holds.
- **Status:** NOT STARTED.

### G4 — L5 ABK ≤16 completeness + the geometric lower bound
- **Target:** geometric Kirby–Taylor ⟹ `abkGrade` surjective/complete (the genuine upper bound, replacing
  the disclosed AHSS/height-4 ≤16 cap as a *hypothesis*); discharge the W3 `hGM` √-relation geometrically
  (the genuine order-16 generator).
- **Consumes:** §3a (Brown/ABK, height-4 cap as a *computation* now backed by geometry), G3.
- **DONE:** `abkGrade` surjective kernel-pure; `hGM` discharged (no posited `signature = 1`).
- **Status:** NOT STARTED.

### G5 — genuine-carrier assembly + drop all disclosures
- **Target:** assemble (inj G3 + surj G4) ⟹ genuine `dataBordism_iso_zmod16_of_complete_grade`; recast the
  Smith map / Ω₅ (W6/W7) on the genuine `DataBordismGrp` (retire posited `Omega4PinPlusBordism`); drop
  `SmithInflow` / `pin4_abutment` / `PinPlusBordismLandmark` from `CommonOrigin.sixteen_convergence_*`.
- **Consumes:** G3, G4, §3a/§3b.
- **DONE:** `CommonOrigin.sixteen_convergence_*` carries NO disclosed binder; posited carrier retired;
  `#print axioms` exact on the apex theorems.
- **Status:** NOT STARTED.

### G6 — closure
- **Target:** trusted clean baseline + full validation + fresh adversarial review.
- **DONE:** `rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps` clean; `validate.py` N/N;
  `#print axioms` exact on every apex theorem; fresh `skeft-qa:adversarial-reviewer` ZERO BLOCKER;
  counts/inventory/INDEX synced.
- **Status:** NOT STARTED.

---

## 6. Process / harness notes
- The 5q.G `/goal-prompt` is authored via `/skeft-qa:goal-prompt` against the **live-anchor harness**
  (commit `7cf6a5d4` + `LIVE_ANCHOR_REDESIGN_SPEC.md`) with §1's anti-spiral rules baked in. **It must not
  contain a frozen "CURRENT STATE" naming engines** (the 5q.F re-seed vector).
- **DURABLE-ONLY condition rule (the deeper form of the same lesson):** the persistent `/goal` condition is
  re-injected verbatim every compaction, so it must hold ONLY **durable, position-independent** rules
  (the gate goal, source-of-truth pointers, the altitude lock, kernel-purity, SETTLED_FORKS-first, the
  per-gate DONE criteria, legitimate stops). It must NOT hold any **transient/positional kickoff** — no
  "first do the audit," no "start at G1," no "current state = …". A one-time instruction baked into a
  forever-re-injected condition re-creates the 5q.F driver: after the loop is past that step, the condition
  keeps ordering it redone. **All transient next-step state lives ONLY in the recomputed live FRONTIER**
  (notebook INDEX, recomputed from git each turn), never in the condition. One-time kickoffs (e.g. the G1
  exact-vs-mod-boundary **audit**) are done in an **early interactive session**, off the persistent loop;
  only their *outcome* is recorded (in the FRONTIER + the relevant gate), and the persistent loop is armed
  from the post-kickoff state.
- **The done-evaluator sees ONLY the transcript — inline the granular ACs.** The `/goal` done-condition is
  judged by an evaluator that does NOT read this roadmap or the notebook, so every gate's checkable AC
  (G1→G6) must be inlined verbatim in the composed condition (named theorems/anchors, the build/validate/axiom
  checks, the binder-drop), not deferred to "per roadmap §5." The staged condition with these ACs inlined is
  `docs/dev-loops/Phase5qG/goal_condition_DRAFT.md` (durable-only, < 4000 chars, post-G1-audit) — the input
  for `/skeft-qa:goal-prompt`.
- Source-of-truth on every compaction: this roadmap + `Lit-Search/Phase-5qG/LAB_NOTEBOOK_INDEX.md` (FRONTIER
  + the §4 settled-forks register) + `docs/dev-loops/SETTLED_FORKS.md` + `docs/dev-loops/PRE_DECISIONS.md`.
- Vetting discipline (the reason 5q.G is clean): **no item is added to this roadmap or the notebook without
  source/git/kernel verification.** Explore-agent findings and DR references are scrutinized, not folded.

---

*Compiled 2026-06-24, then adversarially reviewed (fresh-context agent) and corrected the same day (B1–B3 +
warnings). Bedrock + no-go inventory ground-truth-vetted by **reading Lean source at HEAD `7d893548`** and
cross-checking library membership against `counts.json`'s module list (`counts.json` itself snapshotted at
`b7b91c81`; delta to HEAD is harness/security/WIP-only — a fresh regen is a G6 task). Companion post-mortem:
`Lit-Search/Phase-5qF/L2_DEVELOPMENT_TRACE.md` PARTs III–VI.*
