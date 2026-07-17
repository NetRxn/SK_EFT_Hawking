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

*(Updated 2026-07-16, post gate round 12 — the original handoff paragraph is superseded;
the §1 work queue below is rewritten to the current truth.)* The close-out arm has
executed ~55 blocks (#137–#193): **the provider is unconditional**
(`nonempty_charPairWProviderPerOp` — Lanes A+B of the original plan are done), the KRS
leaf is consolidated to ONE ∀-p residual row (`KRSResidualRow` →
`kernelReducesToSpin_of_residualRow`), dC is reduced to the collapse atom's bounding
datum, dA to the honest kernel characterization `ker Φ ⊆ doubles` on the geometric
`spinForgetPhi`, and **gate rounds 11 AND 12 both ran (Fable, CONDITIONAL PASS)** with
their ties kernel-encoded (fence: 20 forks / 45 aliases) and four binding round-12 specs
frozen in `PinPlusResidualGate.lean`. What remains is the **genuine geometric floor**
(§1 below) feeding those residual rows, plus the assembly wiring, W-E, W-F, and the
closure gates. No unknown walls are open.

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
- Model tiering: Sonnet = mechanical bricks, Opus = deep geometry, **Fable = gate rounds
  only** (wide latitude, not a brick).
- The wt3 stash `stash@{0}` is old pre-5qG 5qf-leads material, deliberately preserved —
  do not pop or drop it.

### 1. The work queue, in dependency order

*(Rewritten 2026-07-16 post gate round 12. The original Lanes A/B/C are DONE — the
provider is unconditional, the KRS leaf is consolidated to `KRSResidualRow`, gate rounds
11+12 ran. The queue below is the remaining GENUINE GEOMETRIC FLOOR + convergence. The
per-block detail lives in the lab notebook; task IDs refer to the session task list.)*

**Lane 1 — the hasClass cascade (feeds the KRS ∀-p row):**

- **R1 🔄 #191 (wt3): the concrete sphere-4 cycle zS** with [zS] = betaClass — route (b)
  first (H₄(S⁴;ℤ/2) has one nonzero class; the #168 connecting iso may make ∂(relative
  fundamental disk chain) BE it) → then the cascade: the cone rep → the co-adapted seam
  splits → hdetAB → `hasClass_ofTransfer`. Detection is a rel-homology invariant
  (`relClassOf_eq_of_homologous`), so controlled reps inherit it.
- **R2 ⏸ the mv piece homeos / hcov residuals** (the collar-conflict-free ones landed
  with #181; the rest ride the seam machinery).

**Lane 2 — the σ-descent + hcob tower (feeds dA's honest route + the Novikov atom):**

- **R3 🔄 #192 (wt2): the Int relative cap port** H²(W;ℤ) × H₄(W,∂W) → H₂(W) (the mod-2
  `capRelH` layer is the template) + the hadj mediation. **Round-12 spec 2 binds:** the
  Novikov/hbord discharge must exhibit a GENUINE bounding-W tower — Lagrangian linear
  algebra is kernel-proven zero progress (`novikovLagrangian_iff_hbord`).
- **R4 ⏸ hbord as tower data**: the concrete bounding-W instantiation consuming R3 + the
  #190 form identification (`boundaryInterMatrix_eq_blockDiag`) + the nondeg pair.
- **R5 ⏸ the transversal V representative** (smooth transversality — the deepest leaf;
  dA's `ker Φ ⊆ doubles` geometric feed). **Round-12 spec 1 binds:** any dual-spin supply
  passes by DATA inspection only (amb pinned to the tethered witness).

**Lane 3 — dC + the σ-presentation residuals:**

- **R6 ⏸ the collapse atom's bounding datum** (the round-12 spec-4 debt on
  `SectorIsGeometric`'s discharge).
- **R7 ⏸ the Gram-pin atoms** {the E-Z cross value, the basis-ID} + **the K3
  conditional** (the σ-presentation stock row's last live sector).
- **R8 ⏸ hsNe/hsConn** (the connected engine's certs — flagged by #186's wiring findings).
- **R9 ⏸ the concrete bounding 3-manifold** (the τ-datum builder; terminal-only per #186).

**Convergence:**

- **F1 🔄 #193 (wt1): THE ASSEMBLY WIRING** — `kt_equiv_zmod16_of_residuals`: the
  end-to-end conditional whose hypothesis list IS the remaining geometry above
  (provenance-annotated), + the W-E conditional shape (+ W-F if pure wiring). Then each
  R-item's landing shrinks the hypothesis row until it is empty → `kt_equiv_zmod16`
  unconditional.
- **F2 ⏸ W-E:** the Rokhlin corollary fires unconditionally once F1's row empties.
- **F3 ⏸ W-F capstone:** the k = ∞ statement + the Ω₅ recast.
- **F4 ⏸ Closure gates:** full `validate.py` N/N; a fresh adversarial reviewer pass;
  the trusted clean rebuild `rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps`;
  sync + counts; notebook + memory close-out.
- **Gate discipline stands:** any NEW completeness Prop shaped between here and closure
  gets a Fable gate round before consumption; the four binding round-12 specs
  (`PinPlusResidualGate.lean` header) govern all consumption.

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
