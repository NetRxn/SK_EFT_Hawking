# Phase 5q.H — The 16-Convergence: Overview & Handoff

**Written:** 2026-07-15 (the operator's usage-limit pause; work resumes ~next week).
**Ground state:** main `404a2bfe`, library **9,981 jobs green**, kernel-pure throughout,
`validate.py` 46/46, `nogo_substrate_integrity` green, extraction fresh.
**This document:** part 1 is the big picture for anyone catching up cold; part 2 is the
detailed plan for the remaining work, in dependency order. The always-authoritative live
resume map is the **"2026-07-16 SAVE-STATE" block** in
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

The theorem-shaped work is done: the carrier is final and gate-certified, the assembly
`G ≃+ ZMod 16` is proven from three named leaves, and the provider that makes all ∀-prov
statements meaningful is inhabited modulo two named residuals. What remains is
**discharging leaves**: finishing the surgery trace's geometric core (KRS-supply),
constructing the two KT-§5 data leaves (dC, dA), closing the two provider residuals, then
one more Fable gate round and the final assembly + capstone + closure gates. No unknown
walls are open — every remaining item is named, located, and has banked machinery
pointing at it.

---

## Part 2 — The detailed remaining-work plan

### 0. Environment checklist at resume (before any Lean work)

- If the machine rebooted since 2026-07-14: re-apply
  `sudo sysctl -w kern.maxvnodes=786432` (it reverts on reboot; the default 263k ceiling
  causes machine-wide ENFILE under parallel Lean).
- Run the CLAUDE.md session-start lean-lsp trim (kill off-repo lean-lsp-mcp servers).
- Posture: **≤ 2 heavy workers** (a lead full-library `lake build` counts as one),
  `ulimit -n 65536`, `LEAN_NUM_THREADS=4`, serialize cold header imports and builds.
  Lake 5.0.0 has no `-j` flag.
- Model tiering: Sonnet = mechanical bricks, Opus = deep geometry, **Fable = gate rounds
  only** (wide latitude, not a brick).
- The wt3 stash `stash@{0}` is old pre-5qG 5qf-leads material, deliberately preserved —
  do not pop or drop it.

### 1. The work queue, in dependency order

Three independent lanes can run in parallel (respecting the 2-worker cap). Items marked
⏸ were never started; nothing below is half-done on disk — every listed item starts
clean from main.

**Lane A — the provider residuals** (makes the provider unconditional):

- **A1 ⏸ Task #137 (re-dispatch; Opus, wt3): the disconnected closer.** The first
  dispatch was accidentally killed ~30 min in by the usage-limit interrupt, before its
  first file write — zero output, nothing to salvage. Brief (unchanged, in the task):
  per-clopen-piece connected detection (the C-piece's `RestrictsToRelGenOn` from the
  in-tree connected `hasRelFundClass_cylGen` machinery) + the nd14/nd23 block-diagonal
  (cup across clopen pieces vanishes; per-component nondeg from
  `ofClosedPDSuspIntertwineNorm`) + per-component hwu aggregation — **all with D
  abstract** (the concrete-unfolding whnf wall class is settled; the folded-def/abstract-D
  architecture binds). Acceptance: `DisconnectedCylCoreND` discharged.
- **A2 ⏸ The Wu leaf (Opus): the per-M `CylinderWuResidual`.** The Sq-suspension
  foundation — prove the cylinder Wu formula v₂(W) = v₁(W)² content per-M.
  `crossHDual_pairing` exists as its base; the M-intrinsic reduction was walled on Sq
  suspension naturality (a genuine foundation arc — the one remaining deep-ish piece).
  Acceptance: the Wu-leaf hypothesis of `nonempty_provider_of_wuLeaf_and_disconnectedCoreND`
  discharged → **the provider is unconditional**.

**Lane B — the KRS-supply (the surgery trace's geometric core):**

- **B1 ⏸ Task #138 (Opus, wt1): the trace-W admissibility opener.** `WAdmPinned` on the
  trace pair (surgery-foundation wave-4 residual 2). The cylinder engine's machinery
  (SumRelFundClass, the ⊔-tower, the clopen-split engine) is the toolkit.
- **B2 ⏸ The membrane presentation** (wave-4 residual 3): `GeoRealizationTied` for the
  Σ-trace + the Weld presentation + glue — connects the surgery trace to the tethered
  carrier's membrane discipline.
- **B3 ⏸ The he_boundary resolution.** The named structural wall:
  `ModelWithCorners.boundary` is chart-choice-dependent at C⁰, so the boundary
  identification needs the **surgered-end packaging** (or a smooth weld) rather than a
  raw boundary computation. This is a packaging/architecture item, not a new theorem arc.
- With B1–B3 + the already-built capstone (`ambientTraceBordism_capstone`), the
  rank-lowering tethered trace exists off the [p] = 0 fibre → **the KRS-supply leaf
  fires** (`kernelReducesToSpin_of_ambientDatumSupply` is banked).

**Lane C — the KT §5 data leaves:**

- **C1 ⏸ The geometric Φ** (Ω₄^Spin → the carrier): the C-leaf /
  `KTSpinPresentationDatum` content. Its hA input = two terminal atoms:
  `HandleTradeCobordism` (⟸ the trace bordism + ξ.Bor — lands with Lane B) and
  `HyperbolicBase`; hB is already discharged. `dataBordismGrp_equiv_int_of_cobordism_and_base`
  (Ω₄^Spin ≅ ℤ) is banked in `PinPlusKTFreezeAssembly.lean`.
- **C2 ⏸ The dA non-circular construction** (`DualSpinForwardDatum`): dA ⟺ `KTNonSplit`
  exactly, so the construction must come from the geometric Φ forward direction + the
  banked ÷32 arithmetic — **the round-10 non-circularity audits are owed** and must be
  run when dA lands (the gate spec is in `PinPlusKTLeafGate.lean`).

**Convergence — strictly after A, B, C:**

- **G ⏸ GATE ROUND 11 (Fable, wide latitude):** vacuity attack on the newest leaf shapes
  (the Wu leaf, the disconnected core discharge, dC, dA, the KRS-supply) **before** their
  discharges are consumed. This is the standing discipline: no completeness Prop is
  consumed ungated.
- **F1 ⏸ The final assembly:** `kt_equiv_zmod16_of_two_leaves` fires with real inputs →
  `kt_equiv_zmod16` on the tethered carrier, unconditional.
- **F2 ⏸ W-E:** the Rokhlin corollary (largely banked from the 5q.B/5q.G era).
- **F3 ⏸ W-F capstone:** the k = ∞ statement + the Ω₅ recast.
- **F4 ⏸ Closure gates:** full `validate.py` N/N; a fresh adversarial reviewer pass;
  the trusted clean rebuild `rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps`;
  sync + counts; notebook + memory close-out.

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
- **Never re-enter a registry fork:** 16 forks / 34 aliases in `KERNEL_NOGO_REGISTRY`,
  surfaced via `/skeft-qa:frontier` (negative frontier). Name the relevant forks in every
  worker brief.

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
