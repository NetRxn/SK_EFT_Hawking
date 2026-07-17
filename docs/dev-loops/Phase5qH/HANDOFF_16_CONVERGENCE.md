# Phase 5q.H — The 16-Convergence: Overview & Handoff

**Written:** 2026-07-15; **fully refreshed 2026-07-17** (post the close-out arm's
teardown — the operator ended the arm after an API-instability window; see §0).
**Header re-synced 2026-07-17** to the post-#210 HEAD, then advanced again by the #211
partials-harvest (the teardown-refresh header was written at `6a8c298d`/`0ee11ba1`; the #210
seam-transfer no-go block advanced main to `9f81a5ad`; the #211 hBbord-partials harvest then
advanced it to `936de9ca` — now reconciled).
**Ground state:** main `936de9ca`, library green + kernel-pure throughout (the #211 harvest
registered the S²×D³ partial modules; 10,080+ jobs), fence **22 kernel forks / 53 aliases**
(fork 22 = `seam-transfer-open-support-uninhabitable`) + 9 SETTLED_FORKS prose entries,
`nogo_substrate_integrity` green. **Extraction/counts are one harvest behind — run
`/skeft-qa:sync` to refresh them for the #211 modules (last full sync at `9f81a5ad`).**
**Budget posture (2026-07-17):** ~93% of the weekly **Fable** budget was consumed in the
close-out arm's 24h (a large share burned by worktree/subagent API stalls, not work).
Until the budget resets: **Fable-grade problems are worked DIRECTLY by the lead session
(which is Fable) — no Fable subagents**; worker dispatches are Opus/Sonnet only, and
every remaining item below is specced so an Opus worker can push it.
**This document:** part 1 is the big picture for anyone catching up cold; part 2 is the
detailed plan for the remaining work, in dependency order. The always-authoritative live
resume map is the **frontier block** in
[LAB_NOTEBOOK_INDEX.md](LAB_NOTEBOOK_INDEX.md) — if this document and the INDEX ever
disagree, the INDEX wins.

---

## Part 1 — The big picture

### The goal

Formalize in Lean 4, fully **unconditionally**, the classical Kirby–Taylor result

> **Ω₄^{Pin⁺} ≅ ℤ/16**,

on a **faithful** carrier — a genuine bordism-of-manifolds substrate (T2 carrier, smooth
k ≥ 1 data, structure-extension bordism relation with the Brown/ABK invariant *computed*,
not posited) — with:

- the isomorphism **injective and surjective**, zero posits;
- kernel axiom set exactly `{propext, Classical.choice, Quot.sound}`;
- no project-local `axiom`, no `sorry`, no `native_decide`, no `maxHeartbeats`;
- every completeness Prop passed through the **W-A vacuity-attack gate** (a Fable
  adversarial round) *before* anything consumes it.

### Why the carrier is the hard part

The original Phase 5q.H carrier collapsed in 2026-07-13's **T2-collapse finding**: the old
`DataBordismGrp` was non-faithful — a degenerate (non-Hausdorff) "bordism" could relate
anything to anything, making the ℤ/16 statement vacuously satisfiable. Arm 3 rebuilt the
substrate as a *gated* carrier; arm 4 (2026-07-14→15, ~55 green merges) drove it to its
final form and decomposed the remaining mathematics into a gated leaf row. Six gate rounds
this arm (5–10) each caught or certified real structural content; the registry now holds
**16 kernel-encoded no-go forks / 34 aliases** — provably-false paths a fresh session must
not re-derive (see `KERNEL_NOGO_REGISTRY` in `src/core/constants.py`).

### The architecture (four interlocking pieces)

1. **The carrier** — `pinPlusCharPairData` over `CharPairBorRealizedTethered`
   (`lean/SKEFTHawking/PinPlusCharPairCarrier.lean`, `PinPlusCharPairBorTethered.lean`).
   The bordism relation is *realized and tethered*: every membrane comes with a closed
   embedding `ιW` into the bordism manifold W and pointwise glue data — the round-6 gate
   proved anything weaker lets a free membrane fake the relation. All 8 carrier ops are
   wired through a **σ-threaded per-op provider** (`CharPairWProviderPerOp`), which
   supplies the W-admissibility data (Lefschetz–Wu, relative fundamental class) each op
   needs. **Gate round 7 PASSED this carrier** — the first structural pass of the arc.

2. **Surjectivity — done since arm 3.** `charPairBrown : →+ ZMod 8` is surjective and
   `[ℝP⁴] ≠ 0` on a fully concrete ℝP⁴ witness (smooth atlases, unconditional
   `hchar_pairing`). This is the negation of the old collapse falsifier.

3. **Injectivity / order 16 — the W-D decomposition.** Follows Kirby–Taylor §5. The
   minimal consumption unit is the gated TRIPLE `{KernelReducesToSpin, SpinImageIsTwo,
   KTNonSplit}` (rounds 8–10 proved every 2-subset admits a degenerate model — it is
   triple-or-nothing). The **assembly of record is PROVEN**:
   `kt_equiv_zmod16_of_two_leaves` (`PinPlusKTLemma53Wave.lean` + the gate modules) gives
   `G ≃+ ZMod 16` from three leaf inputs: **{KRS-supply, dC, dA}** (detailed in part 2).
   The ÷32 upper bound's research gap dissolved — it is KT's own Lemma 5.3, in the local
   corpus (`Lit-Search/Phase-5qH/ScoutReport_KT_Lemma53_div32_Habegger_Enriques.md`), and
   its arithmetic is banked in-tree with the K3 (σ = −16) witness.

4. **The provider + the surgery foundation — the geometric substrate.**
   - **Track 2 is COMPLETE**: the entire cylinder [W,∂W] ladder (hcls, hdet, nondeg
     through the EZ cross-product layer, and the singular normalization theorem proved
     ∀M via a Dold–Kan bridge). Consequence: **the provider INHABITS**
     (`nonempty_provider_of_wuLeaf_and_disconnectedCoreND`) modulo exactly two named
     residuals — the per-M Wu leaf (`CylinderWuResidual`, a Sq-suspension computation)
     and the disconnected core (`DisconnectedCylCoreND`, whose clopen-split engine and
     D-datum are already built). Every ∀-provider W-D statement is live.
   - **The surgery foundation (waves 1–8)** exists to supply KRS's one deep binder: a
     genuine rank-lowering *tethered surgery-trace bordism* (the algebra is fully
     banked). It delivered the first non-product bordism carrier (an adjunction space
     B ⊔_φ Ha), two reusable Mathlib-grade keystones (`chartedSpaceOfOpensCover`,
     `hasGroupoid_of_opensCover`), the packaged `surgeryTraceBordism`, the tether's
     closed embedding free via the membrane weld, **the C⁰ collapse** (all smoothness
     fields free at k = 0, the consumers' grade), the generic disk atlas
     (`instChartedSpaceNDisk`), and the constructed seam collar. The trace bordism's
     remaining input row is the irreducible geometric core:
     **{S ⊆ D⁵, φ, hφtop, SeamCollarDatum, eM′, he_boundary}**.

### Status in one paragraph

*(Updated 2026-07-17, post the close-out arm #137–#211.)* **THE ASSEMBLY IS PROVEN as a
conditional and the phase is now pure row-emptying.**
`kt_equiv_zmod16_of_residuals` (`PinPlusKTAssemblyResiduals.lean` — the provider
INSTANTIATED, never hypothesized) was refined through seven audited variants to the
sharpest current form **`kt_equiv_zmod16_of_residuals_freezeAtoms_ofReducedAtoms`**
(`PinPlusKTSphereProdCohomology.lean`): its hypothesis row IS the phase's complete
remaining geometry, and each variant has a `rokhlin_sixteen_…` twin, so **W-E fires
automatically when the row empties**. Gate rounds 11, 12 AND 13 all ran (Fable,
CONDITIONAL PASS; every fakeability tie kernel-encoded — fence 21 forks / 49 aliases;
**gate 13's seam trace: NO consumption seam needs a fix before the assembly fires**).
The provider is unconditional; the KRS leaf is one ∀-p row; hcyc+h2 collapsed into the
single atom hΦg; hcol is the per-object collapse-datum supply; hBbord is maximally
reduced (the (1,4) Wu leg proven FREE, hwu ⟺ v₂ = 0, the cohomology atoms reduced to
homological roots); the σ/Novikov tower road is one inhabitation from firing end-to-end.
What remains is the **terminal geometric floor** (§1), then W-F and the closure gates.
No unknown walls; every remaining atom is named, located, and gate-specced.

---

## Part 2 — The detailed remaining-work plan

### 0. Environment checklist at resume (before any Lean work)

- If the machine rebooted since 2026-07-14: re-apply
  `sudo sysctl -w kern.maxvnodes=786432` (it reverts on reboot; the default 263k ceiling
  causes machine-wide ENFILE under parallel Lean).
- Run the CLAUDE.md session-start lean-lsp trim (kill off-repo lean-lsp-mcp servers).
- Posture: **3 workers authorized** (operator, 2026-07-16, after the maxvnodes bump)
  with guardrails — no lead full-library `lake build` while all 3 lanes are hot; on any
  ENFILE symptom drop back to 2. `ulimit -n 65536`, `LEAN_NUM_THREADS=4`, serialize cold
  header imports and builds. Lake 5.0.0 has no `-j` flag.
- Model tiering **(2026-07-17 budget revision)**: Sonnet = mechanical bricks, Opus =
  deep geometry AND (until the weekly budget resets) everything below; **Fable = the
  LEAD SESSION works Fable-grade problems directly — do NOT spawn Fable subagents**
  (~93% of the weekly Fable budget went in 24h, much of it burned by subagent API
  stalls, not work).
- **API-instability lesson (2026-07-16→17, ~9 worker deaths/stalls):** workers COMMIT
  after their FIRST green brick and every ~3 after (committed work survived every
  death; uncommitted triage did not). Resume-kick a stalled agent while its transcript
  holds triage; fresh-hand after 2–3 deaths; during an active instability window,
  prefer the lead working directly over re-spawning.
- The wt3 stash `stash@{0}` is old pre-5qG 5qf-leads material, deliberately preserved —
  do not pop or drop it.

### 1. The work queue — the terminal floor, atom by atom

*(Rewritten 2026-07-17 at teardown. F1 is DONE — the assembly chain landed and gate 13
cleared every consumption seam. The queue below is the assembly row's remaining atoms,
grouped by lane, each with its sharpest current form, the consuming variant, and the
recommended model tier. Task IDs #209/#210/#211 in the session task list hold ready
worker briefs for the first three items.)*

**THE ROW** (`kt_equiv_zmod16_of_residuals_freezeAtoms` grain, refined by
`_ofCoboundary`/`_ofDegenerate14`/`_ofReducedAtoms` on slot 5):
`{H (KRS ∀-p row) · row (σ-presentation) · hCob · hBase · hBbord · hcolD · hker · hΦg}`.
Empty it ⟹ `kt_equiv_zmod16` + Rokhlin-16 unconditional.

**Lane 1 — the σ/Novikov tower (closest payoff; task #209, Opus-ready):**
The full chain is built (#192→#196→#201→#205 + the #209 salvage: hbdnd discharged, the
narrowed constructor + latticeSig bridge in `PinPlusKTTowerInhabit.lean`). ONE
inhabitation remains: **`GenuineBoundingWTower`** = the finite-free ℤ-bases {Bw, Br, B}
of the genuine H²(W)/H³(W,∂W)/H²(∂W) (the `intH2_basis_datum` atom class — the atlas's
#3 open assumption, gates 6; the cylinder findim machinery #64/#78/#164/#9 is the
route) + hexactRev/hnondeg (ℝ Props — dimension-count arguments) + the blockDiag
splitting datum (likely pure re-indexing of the banked #190 identification). **If it
lands, the σ-lane floor fires END-TO-END** (`lagrangian_of_genuineTower`,
`novikovRealPairLES_of_genuineTower`), feeding the hbord-grade content hker and the sig
descent consume. Round-13 spec 1 binds: genuine objects only, data inspection.

**Lane 2 — the KRS supply / hypothesis H (★ ADJUDICATED 2026-07-17, lead-direct):**
Everything but one atom is built: zS pinned to the fundamental generator (#191); the
split engine + subdivision-detection-transfer + EXACT free-sphere hvOut at V = Sᶜ
(#194/#198); the Ctrl supplier + `ofSharedSeam` constructor (#198/#204); the disk half
inverted (#207). **THE #210 VERDICT (road D): the 3×-circled shared-cSeam barrier was
NOT a machinery gap — the as-shipped open-support transfer shape is PROVABLY
UNINHABITABLE** (`PinPlusTraceSeamTransferNoGo.lean`; fork 22
`seam-transfer-open-support-uninhabitable`: htransfer forces closed-seam support,
char-2 forces both split pieces to be cycles, and a fundamental class cannot decompose
as seam-cycle + off-cycle over H₄-null regions). Do NOT re-attempt cSeam construction
against that shape at any depth. **THE REPAIR (designed; task #212, Opus-ready,
GATE-PENDING):** the COLLAR-PAIR split — a shrunk closed core K ⊂ int(range φ); wAtt
supported in the CLOSED attach image (the #189 engine's U₁ := int A output has no
spill), wOut in topface ∖ K; do NOT route through hbd_ofTransfer (the literal seam
cancellation is unreachable) — wire into `hasClass_ofTransferCorrector` (the #178
crossChain/MV-partition machinery absorbs the seam mismatch; the collar-pair splits
feed hagree/hpS). The full analysis: SETTLED_FORKS
`seam-transfer-open-support-uninhabitable` REPAIR ANALYSIS. After it: hdetAB (corrector
form banked) + the row tail (τ-datum terminal, hsNe/hsConn, mv homeos — #186).

**Lane 3 — hBbord / hypothesis 5 (near-tractable; task #211, Opus-ready):**
Maximally reduced (#203: membrane/atlas layers DONE; #206: the (1,4) Wu leg PROVEN
FREE, hwu ⟺ v₂ = 0; #208: the cohomology atoms reduced to homological roots via ℤ/2
Kronecker UC). Remaining: **the concrete S²×D³ provider** — the Bordism object over
the banked SphereDiskFreezeB/J5 atlas + the three roots on the concrete W
(Subsingleton H₁ via retraction to S² + `sphere_homology_one`; Subsingleton H₄rel;
`HasRelFundClass` via cross/product-collar templates; the dead agents' triage
confirmed the homotopy-invariance stack handles Root 1) + the slot-matching
interface — then **the pinned (2,3) datum P23** (H²(W) ≅ H³(W,∂W) perfect cup pairing
— the genuine irreducible content) and the v₂ = 0 computation it enables.

**Lane 4 — the deep floor (design-first; do NOT spend workers before a route decision):**

- **hCob + hBase (hypotheses 3–4):** the two Benedetti E1 surgery primitives.
  SETTLED (kernel-adjacent, `freeze-atoms-not-composable-from-sigma-trace`): they do
  NOT compose from the landed Σ-trace — orthogonal axes (enhancement-rank vs b₂). A
  future E1 surgery foundation builds them directly; HandleTradeSplit/HyperbolicPeel
  statement layers exist.
- **hcolD (hypothesis 6):** the rank-0 → empty-surface **membrane-kill** — proven a
  different construction from the rank-lowering trace (which stops AT rank 0,
  `ambientSurgeryDatum_pos_rank`). The per-object `RankZeroCollapseDatum` shape is
  gate-13-audited (honest Skolemized renaming); the bounding construction is the
  content. Round-13 spec 3: the datum's `b` audited by data inspection.
- **hker (hypothesis 7):** the **transversal V representative** (the w₁-dual spin
  submanifold, smooth transversality) — opened at #160 (the single-witness wall:
  bordism gluing absent by design), untouched since. Round-12 spec 1 binds.
- **The E1 atom bundle + K3RealizingElement + hΦg (hypotheses 2, 8):** the
  σ-presentation's terminal atoms. `K3RealizingElement` is DEFINED but inhabited
  NOWHERE (Mathlib has no complex geometry); hΦg = Φ[g] = k₀ rides on it (g = the
  K3-class generator). **DECISION NEEDED before spending workers:** a from-scratch K3
  lattice-realization arc vs re-routing the generator witness — a design pass, not a
  brick.

**Convergence (after the row):**

- **F2 W-E:** fires automatically — every assembly variant carries its
  `rokhlin_sixteen_…` twin.
- **F3 W-F:** the k = ∞ statement + Ω₅ recast = **a genuinely new re-basing arc**
  (verified at #193: the 5q.G capstones live on separate carriers; this is not wiring).
- **F4 closure gates:** `rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps`
  clean; `validate.py` N/N; a fresh `skeft-qa:adversarial-reviewer` 0-BLOCKER run;
  sync + counts; notebook + memory close-out.
- **Gate discipline stands:** any NEW completeness Prop gets a vacuity gate round
  before consumption (under the budget posture, the lead runs gate rounds directly);
  the binding specs live in `PinPlusResidualGate.lean` (round 12) +
  `PinPlusRoundThirteenGate.lean` (round 13) headers; consume the assembly ONLY
  through the audited variant chain.

### 2. Binding architectural laws (do not relearn these)

Settled this arm; violating any of them reproduces a known multi-hour wall:

- **Folded-def / abstract-D discipline:** never unfold concrete cylinder boundary sets
  inside detection equations (the whnf wall class — 2M-heartbeat loops). Keep D abstract;
  state detection via the folded definitions.
- **The three-opacity-state split** for quotient-coercion walls (the αU ≠ 0 mechanism):
  route through `relCycleToHom`, keep `crossChain` opaque, characterize `boundaryExtract`
  once via chainIncl-injectivity.
- **Carrier-metavar traps:** never type-ascribe TopCat coercions (`↑(cyl …)` ascriptions
  were the real 200k-heartbeat trigger); use explicit `(X := …)`/`(N := …)`; composed
  `ChartedSpace.comp` instances need an explicit `letI`.
- **Sealed-wrapper spelling** (bdW/cylBdW) — use the sealed names, never re-derive.
- **σ-threading:** provider fields take `CharPairStrBundled` (bare-s fields are
  uninhabitable — the F7-A lesson).
- **Root-aggregator registration:** every merge must verify new modules are imported in
  `lean/SKEFTHawking.lean` (the orphaning defect recurred twice this arm; job-count jump
  on registration is the tell).
- **Route δ is DISPROVEN** (kernel-encoded): the prism class is flank-supported; never
  re-dispatch a δ-range route for hcls-style detection.
- **Worker hygiene:** `lean_verify` takes `theorem_name`; `lake build` the dependency
  before trusting a fresh cross-module decl's LSP state (false-clean / phantom-sorryAx);
  workers stop-and-report on ENFILE; past ~250–300k transcript tokens hand off to a
  fresh agent with a compact state brief (confirm the old agent is dead by sampling slot
  file mtimes over ~60 s first).
- **Never re-enter a registry fork:** **21 forks / 49 aliases** in `KERNEL_NOGO_REGISTRY`
  (+ 8 SETTLED_FORKS prose entries), surfaced via `/skeft-qa:frontier` (negative
  frontier). Name the relevant forks in every worker brief.
- **The waves-13–16 proof-mechanics laws** (bought expensively; violating any
  reproduces a wall): predicate sets (`{‖v‖=1}`) never `ModelWithCorners.boundary`;
  `.choose`-hide concrete points; abstract-X package acyclicity/connecting arguments,
  instantiate late; pin `(X := TopCat.of …)`/`(m := …)` binders (metavar Nat
  unification blows isDefEq; `RelFundClassDatum`/`RelativeCohomology` take X
  IMPLICITLY); extract heavy structure data to NAMED defs (iota-projection never
  whnf's a tactic-proof field — inline literals blow 200k heartbeats); explicit
  literal sets to `chainBoundary_mem_subspaceChains` blow the budget — infer via `_`;
  an unresolved identifier / missing `open` masquerades as a whnf timeout — check name
  resolution FIRST; `lean_multi_attempt` is NOT a reliable heartbeat signal — trust
  `lake build`; char-2 rearrangement via `hhom.symm` defeq then the
  add_assoc/ZModModule.add_self chain; raw `Submodule.Quotient.mk` statements are rfl
  — bridge with show/rfl never rw; `+`-heterogeneous checks don't defeq eagerly —
  state fields in the native (`seamLegHa`) shape; `cyl`/`slice`/`ambIncl`/`graphHom`
  live in CrossProduct/HomotopyInvariance/MayerVietorisLES (explicit opens);
  `hWT2.t1Space` = the T2→T1 conversion; `Module.Finite.of_finite` = the v4.29.1
  Subsingleton route; lean_verify rejects non-ASCII decl names and lexically flags
  the word "opaque" even in prose.

### 3. Where the ground truth lives

| What | Where |
|---|---|
| Live resume map (authoritative) | the SAVE-STATE block in [LAB_NOTEBOOK_INDEX.md](LAB_NOTEBOOK_INDEX.md) |
| Per-brick history | [LAB_NOTEBOOK.md](LAB_NOTEBOOK.md) + shards in this directory |
| The task queue | Claude Code task list (#137 pending re-dispatch, #138 pending) |
| Kernel no-gos | `KERNEL_NOGO_REGISTRY` in `src/core/constants.py` → `lean/SKEFTHawking/KernelNoGos.lean` |
| Gate rounds 5–10 records | `PinPlusCharPairFlipGate.lean`, `PinPlusCharPairTetherGate.lean`, `PinPlusKTSectorGate.lean`, `PinPlusKTStepGate.lean`, `PinPlusKTLeafGate.lean` |
| The assembly of record | `kt_equiv_zmod16_of_two_leaves` (`PinPlusKTLemma53Wave.lean` / the leaf-gate module) |
| The ÷32 / Lemma 5.3 dossier | `Lit-Search/Phase-5qH/ScoutReport_KT_Lemma53_div32_Habegger_Enriques.md` |
| Cross-session memory | memory note `project_5qH_nonhausdorff_substrate_bug.md` |
