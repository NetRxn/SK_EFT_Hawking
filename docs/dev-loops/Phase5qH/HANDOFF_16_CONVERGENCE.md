# Phase 5q.H — The 16-Convergence: Overview & Handoff

**Written:** 2026-07-15. **Fully re-verified and rewritten 2026-07-27** (lead, directly in the
Lean — every claim below was read out of the tree, not carried forward from a prior revision).

**Ground state at rewrite:** main `12d34743`; last **Lean** commit `66851da4` (the 16 commits
since are harness/CI only). `lake build SKEFTHawking.ExtractDeps` → **exit 0, 10,274 jobs**.
`uv run python scripts/validate.py` → **48/48 checks passed**. Fence: **30 kernel-encoded no-go
forks** (`KERNEL_NOGO_REGISTRY`) + **39** `SETTLED_FORKS.md` prose entries; `nogo_substrate_integrity`
green. One advisory: `update_inventory_index.py` autogen blocks are stale — run `/skeft-qa:sync`.

**This document:** part 1 is the big picture for anyone catching up cold; part 2 is the remaining
work in dependency order; part 3 is the binding architectural law set. The always-authoritative
*live* resume map is the **FRONTIER block** in [LAB_NOTEBOOK_INDEX.md](LAB_NOTEBOOK_INDEX.md) — if
this document and the INDEX disagree, **the INDEX wins**. Objective / constraints / gates /
verified-source index live in the durable roadmap
[`docs/roadmaps/Phase5qH_LiteratureGradeUnconditional_Roadmap.md`](../../roadmaps/Phase5qH_LiteratureGradeUnconditional_Roadmap.md).

---

## Part 1 — The big picture

### The goal

Formalize in Lean 4, fully **unconditionally**, the classical Kirby–Taylor result

> **Ω₄^{Pin⁺} ≅ ℤ/16**,

on a **faithful** carrier — a genuine bordism-of-manifolds substrate (T2 carrier, smooth `k ≥ 1`
data, structure-extension bordism relation with the Brown/ABK invariant *computed*, not posited) —
with the isomorphism injective and surjective, zero posits, kernel axiom set exactly
`{propext, Classical.choice, Quot.sound}`, no project-local `axiom` / `sorry` / `native_decide` /
`maxHeartbeats`, and every completeness Prop passed through a vacuity-attack gate *before* anything
consumes it.

### Why the carrier was the hard part

The original carrier collapsed in the 2026-07-13 **T2-collapse finding**: the old `DataBordismGrp`
was non-faithful — a degenerate (non-Hausdorff) "bordism" could relate anything to anything, making
the ℤ/16 statement vacuously satisfiable. Arm 3 rebuilt the substrate as a *gated* carrier; arm 4
drove it to its final form and decomposed the remaining mathematics into a gated leaf row. That
work is done and its lessons are kernel-encoded.

### The architecture (four interlocking pieces)

1. **The carrier** — `pinPlusCharPairData` over `CharPairBorRealizedTethered`
   (`PinPlusCharPairCarrier.lean`, `PinPlusCharPairBorTethered.lean`). The bordism relation is
   *realized and tethered*: every membrane comes with a closed embedding `ιW` into the bordism
   manifold `W` plus pointwise glue data — gate round 6 proved anything weaker lets a free membrane
   fake the relation. All 8 carrier ops run through a σ-threaded per-op provider
   (`CharPairWProviderPerOp`), which is **unconditional**. Gate round 7 passed this carrier.

2. **Surjectivity — DONE, unconditionally, in the SMOOTH category.**
   `charPairBrown_surjective_smooth` and `rp4_ne_zero_smooth`
   (`PinPlusKTAssemblyResiduals.lean` §R.1) off the real-analytic ℝP⁴ witness. No hypotheses.

3. **Injectivity / order 16 — the W-D decomposition**, following Kirby–Taylor §5. The minimal
   consumption unit is the gated triple `{KernelReducesToSpin, SpinImageIsTwo, KTNonSplit}` (rounds
   8–10 proved every 2-subset admits a degenerate model — it is triple-or-nothing). The assembly of
   record `kt_equiv_zmod16_of_two_leaves` (`PinPlusKTLeafGate.lean:463`) is **proven**.

4. **The provider + surgery foundation.** The cylinder `[W,∂W]` ladder is complete and the provider
   inhabits unconditionally. The surgery foundation supplies KRS's deep binder: a genuine
   rank-lowering tethered surgery-trace bordism.

### Status in one paragraph

**The theorem is proven as a sharp conditional; the phase is row-emptying plus one regularity
lift.** Waves W-A (faithful carrier), W-B (smooth surjectivity), W-C (computed invariant) and W-E
(Rokhlin-16 twin, automatic) are closed. W-D's assembly is proven and its hypothesis row *is* the
remaining mathematics. Since the last rewrite the **entire S²×D³ / Freeze-B geometric coboundary
lane closed** — `hBbord` is no longer a lane. What remains is listed atom-by-atom in part 2.

---

## Part 2 — The remaining work, in dependency order

### 2.0 Environment checklist at resume (before any Lean work)

- If the machine rebooted since the last `sysctl`: re-apply `sudo sysctl -w kern.maxvnodes=786432`
  (reverts on reboot; the default 263k ceiling causes machine-wide ENFILE under parallel Lean).
- Run the CLAUDE.md session-start lean-lsp trim (kill off-repo `lean-lsp-mcp` servers).
- **3 worktree slots authorized** (`wt1/wt2/wt3`, operator-confirmed). `ulimit -n 65536`,
  `LEAN_NUM_THREADS=4`; serialize cold header imports; no lead full-library `lake build` while all
  three lanes are hot. Lake 5.0.0 has no `-j` flag.
- Workers **commit after their first green brick** and every ~3 after (committed work survives an
  agent death; uncommitted triage does not).
- The wt3 stash `stash@{0}` is old pre-5q.G material, deliberately preserved — do not pop or drop.

### 2.1 The two headline statements — and the gap between them

| | statement | carrier | row |
|---|---|---|---|
| **Refined (C⁰)** | `kt_equiv_zmod16_of_residuals_freezeAtoms_sphereDiskPinned` (`PinPlusKTSphereProdP23Close.lean:326`) | `residualProv = residualProvK 0` | 7 atoms + one slot pin |
| **Smooth (k=⊤)** | `kt_equiv_zmod16_of_residuals_smooth` (`PinPlusKTAssemblyResiduals.lean:166`) | `residualProvK ⊤` | the COARSE 8 atoms |

**The goal requires the smooth one.** Roadmap §2 leg 2 is a hard constraint: at `k = 0` the honest
group is topological Pin⁺ bordism `≅ ℤ/2 ⊕ ℤ/8`, the wrong group; the `IsManifold` binder at `k = 0`
is *free* (`PinPlusRegularityFence.isManifoldZero_free`).

**The refinement chain is currently C⁰-only.** `SphereProdCoboundaryWAdm`
(`PinPlusKTSphereProdBordism.lean:215`) is hard-pinned at `k = 0`, so every `freezeAtoms` /
`sphereDisk` refinement — including the closed coboundary lane — exists only at `k = 0`. Kernel fork
`k0-to-k1-transport-refuted` forbids lifting: a smooth-category result must be **re-declared**
`k`-generically, never transported. The underlying content looks `k`-blind (`sphereDiskSmoothData k`
is already `k`-generic; `WAdmPinned` is homological) — **verify that, then re-declare.** Doing this
early prevents every subsequent atom from being paid for twice.

The one genuinely C⁰-tied input is a **smooth handle attachment for the surgery trace**
(`SurgeryFoundation.SmoothSurgeryChartDatum.ofC0` sets `k := 0`;
`SingularSurgeryChartsConcrete.ambientTraceBordism_concrete` builds the boundary embedding's
"smoothness" as continuity). It is on the KRS lane's critical path regardless.

### 2.2 The row — every remaining atom

Grouped by independent program. Nothing here is blocked on anything else in the table except where
stated, so all of it is fan-out-able.

**A · `H` — the KRS leaf** (the KT §5 ambient-surgery row). Reduced to the #212 **collar-pair**
repair, itself down to exactly two obligations on `CollarPairCoreRow`: **`hbd`** and **`hdetAB`**,
at the canonical `cHa := diskDetectChain` (`hcHa`/`hdetHa` fall to the banked
`diskDetectChain_hc`/`_hdet`). The chain to `hasClass` is complete
(`CollarPairCoreRow.toHasClass`, `PinPlusTraceCapstoneCollarPairMatch.lean:609`). **Do not build the
shared-`cCore` co-adaptation** — it is off-path (SETTLED_FORKS). Do not re-attempt `cSeam`
construction against the open-support transfer shape (fork
`seam-transfer-open-support-uninhabitable`).

**B · `row` — the σ-presentation.** Two genuinely separate contents hide here:

- **B1 · `hdvd : ∀ x, 16 ∣ R.sig x` — Rokhlin's theorem. This is the atlas KEYSTONE**
  (`hyp:rokhlin_sigma_mod_16`, gating impact 11 — the highest in the graph). Every in-tree producer
  is conditional: `CharSurfaceRokhlinAssembly.rokhlin_of_bounded_charSurface` needs the [FK]/GM
  congruence for the specific `M` plus the CharSurface tower's leaves
  (`KernelClassesEmbedded`, `KernelCirclesBound`, `MembraneSpinKill`, `KernelLagrangianForB`).
  Its irreducible factor is `2 ∣ σ/8`; `lattice_arf_bridge_refuted` proves it is **not** reachable
  from Arf — Rokhlin mod 16 is irreducibly geometric. Primary route: Matsumoto's elementary proof
  (blueprint `Lit-Search/Phase-5qH/Rokhlin_16_sigma_elementary_blueprint_20260703.md`; the
  À la recherche volume is an outstanding fetch).
- **B2 · the K3 generator** (`g`, `hrank`, `hk3`). The Kummer program — far along. `KummerK3`
  exists as a genuine 16-fold welded carrier, is **smooth** (`isManifold_R4_kummerK3'`, any `k`),
  and **`kummerK3_b2_target_unconditional` (H₂(K3;ℤ) ≅ ℤ²²) is landed with no hypotheses**
  (`KummerChart1NbhdAcyclicInt.lean:893`). Remaining: the three `KummerK3E1Residuals`
  (`KummerK3E1Package.lean:184`) — `orientInput` (H₃(K3;ℤ) 2-torsion-free), `h1Free` (H₁(K3;ℤ)
  free), `pdInput` (integral Poincaré duality) — then the Gram (`IntCongr … k3Form`) and the K9
  spin/`StrMfd` packaging. Each is a homology computation with a known classical answer.
  ⚠ `KummerK7H1Window.h1K3_surjective_from_Q` gives H₁(K3) only as a surjective image of a free
  module — that does **not** give freeness.
  ⚠ State the Gram as `IntCongr … k3Form`, never a literal matrix equality on a chosen basis
  (SETTLED_FORKS, general rule); the 16 exceptional + 6 descended classes span a proper index-2⁸
  sublattice, so a "tabulate the 16+6 block" plan fails on determinant grounds.

**C · `hCob` + `hBase`** — the two Benedetti E1 surgery primitives. SETTLED
(`freeze-atoms-not-composable-from-sigma-trace`): they do **not** compose from the landed Σ-trace —
orthogonal axes (enhancement-rank vs b₂). They need a direct E1 surgery foundation
(Benedetti Ch. 20 handle trades); `HandleTradeSplit`/`HyperbolicPeel` statement layers exist.
Treat `{row, hCob, hBase, hΦg}` as ONE Benedetti cluster, not separate black boxes.

**D · `hcolD`** — the rank-0 → empty-Σ **membrane kill**. Proven a different construction from the
rank-lowering trace (which stops AT rank 0, `ambientSurgeryDatum_pos_rank`). Landed: B0 Wu-sector
split, the B1 interface (`PinPlusKTRankZeroBounding.lean`), B4 (`TauMembraneWeldDatum.ofRankZero`).
Remaining: B5/B6 thin assembly, then the two deep fronts — **B1-inhabitation** (WuNullCarrier ⟹
embedded bounding Q) and **B2** (`TerminalCharacteristicExtensionDatum`).
⚠ The one-sphere/3-handle collapse is UNSOUND without a framing theorem (SETTLED_FORKS); the
winning construction is the global KT characteristic-bordism route.

**E · `hker`** — `KerPhiSubDoubles`, the **w₁-dual spin submanifold** (smooth transversality).
Opened at #160, untouched since; **the least-reconnoitred atom in the phase and the one most likely
to hold a surprise.** Its true route is `KTSharpnessSupply` via `kerPhiSubDoubles_of_row_of_supply`
— **not** the σ/Novikov tower, which is kernel-settled ORPHANED
(`sigma-tower-ORPHANED-not-on-16-convergence-critical-path`; do not revive it).

**F · `hΦg`** — `spinForgetPhi[g] = k₀`. Not independent: derived from `hker` + `hcyc` + `h2` once
`row` exists (`spinForgetPhi_g_eq_ktKernelRep_of_cyclic`). `hcyc`/`h2` were shown non-independent —
h2 outright-discharge IS the ÷32 conclusion (circular), and the ℤ/8 quotient does not force
`2·k₀ = 0`.

**G · `hs2s2`** — `(row.R.s2s2).1 = sphereProdSM4 0`, a slot pin, not geometry. Falls out when the
row is built concretely.

### 2.3 Convergence, after the row

- **W-E** fires automatically — every assembly variant carries its `rokhlin_sixteen_…` twin.
- **W-F**: the `k = ∞` capstone statement + the Ω₅ / `CommonOrigin.sixteen_convergence_*` recast is
  a genuinely new re-basing arc (verified: the 5q.G capstones live on separate carriers — this is
  not wiring).
- **Closure gates**: `rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps` clean →
  `validate.py` N/N → a fresh-context `skeft-qa:adversarial-reviewer` with zero BLOCKER findings →
  `/skeft-qa:sync` + counts → notebook + memory close-out. **Never push.**
- **Gate discipline stands**: any NEW completeness / bounding Prop gets a vacuity-attack round
  before its discharge is consumed; the binding specs live in the `PinPlusResidualGate.lean`
  (round 12) and `PinPlusRoundThirteenGate.lean` (round 13) headers; consume the assembly ONLY
  through the audited variant chain.

---

## Part 3 — Binding architectural laws (do not relearn these)

Violating any of these reproduces a known multi-hour wall.

- **Folded-def / abstract-D discipline:** never unfold concrete cylinder boundary sets inside
  detection equations (the whnf wall class — 2M-heartbeat loops). Keep `D` abstract; state detection
  via the folded definitions.
- **The implicit-`TopCat` `isDefEq` wall:** calls taking `{X : TopCat}` implicitly (`homProjInt`,
  `homIncl`, `connectingInt`, `ambIncl`, `excisionEquivInt`, `seamHomologyEquivInt`,
  `Homology.mapInt_ambIncl`, the `exact_*` family) MUST be written `(X := …)`. Unpinned they unfold
  the `RelHomologyInt` instances into a 200k-heartbeat `isDefEq` wall. Diagnostic: *"(deterministic)
  timeout at isDefEq"* on a one-line `LinearMap.comp` def. This is an ELABORATION wall — the
  "heartbeat ⟹ decompose" rule does not apply and `maxHeartbeats` is the wrong fix (and banned).
- **Carrier-metavar traps:** never type-ascribe TopCat coercions; use explicit `(X := …)`/`(N := …)`;
  composed `ChartedSpace.comp` instances need an explicit `letI`.
- **The three-opacity-state split** for quotient-coercion walls (the `αU ≠ 0` mechanism): route
  through `relCycleToHom`, keep `crossChain` opaque, characterize `boundaryExtract` once via
  chainIncl-injectivity.
- **Sealed-wrapper spelling** (`bdW`/`cylBdW`) — use the sealed names, never re-derive.
- **σ-threading:** provider fields take `CharPairStrBundled` (bare-`s` fields are uninhabitable).
- **Root-aggregator registration:** every merge must verify new modules are imported in
  `lean/SKEFTHawking.lean` (this defect has recurred repeatedly; a job-count jump on registration is
  the tell).
- **Gram targets** are stated as `IntCongr … <form>`, never a literal matrix equality on a chosen
  basis — the extra content is basis normalization, not geometry, and is generically unreachable
  whenever a basis vector comes from a choice.
- **`lean_local_search` returning one hit is NOT a reference check** — it does not surface namespaced
  members. Use `lean_references` or read the module. A direction-shifting claim ("dead", "orphaned",
  "nothing consumes X") must be traced in code, never grep-and-concluded.
- **Proof-mechanics laws** (bought expensively): predicate sets (`{‖v‖=1}`) never
  `ModelWithCorners.boundary`; `.choose`-hide concrete points; package acyclicity/connecting
  arguments abstract in `X` and instantiate late; extract heavy structure data to NAMED defs
  (iota-projection never whnf's a tactic-proof field); an unresolved identifier / missing `open`
  masquerades as a whnf timeout — check name resolution FIRST; `lean_multi_attempt` is NOT a reliable
  heartbeat signal (trust `lake build`); raw `Submodule.Quotient.mk` statements are `rfl` — bridge
  with `show`/`rfl`, never `rw`; `lean_verify` rejects non-ASCII decl names and lexically flags the
  word "opaque" even in prose; the authoritative axiom check is a fresh `lake env lean`
  `#print axioms`.
- **Never re-enter a registry fork** — 30 kernel-encoded forks in `KERNEL_NOGO_REGISTRY` + 39
  `SETTLED_FORKS.md` prose entries, surfaced by `/skeft-qa:frontier` (negative frontier). Name the
  relevant forks in every worker brief; a fresh worker is the highest-risk re-deriver.

---

## Part 4 — Where the ground truth lives

| What | Where |
|---|---|
| Live resume map (authoritative) | the FRONTIER block in [LAB_NOTEBOOK_INDEX.md](LAB_NOTEBOOK_INDEX.md) |
| Objective, constraints, verdicts, gates, sources | [the durable roadmap](../../roadmaps/Phase5qH_LiteratureGradeUnconditional_Roadmap.md) |
| Per-brick history | [LAB_NOTEBOOK.md](LAB_NOTEBOOK.md) + `LAB_NOTEBOOK_W*.md` shards |
| Machine truth of open / settled nodes | the atlas — `/skeft-qa:frontier`, both fronts |
| Kernel-checked impossibilities | `KERNEL_NOGO_REGISTRY` (`src/core/constants.py`) → `lean/SKEFTHawking/KernelNoGos.lean`; prose in `docs/dev-loops/SETTLED_FORKS.md` |
| Gate-round records | `PinPlusCharPairFlipGate/TetherGate`, `PinPlusKTSectorGate`, `PinPlusKTStepGate`, `PinPlusKTLeafGate`, `PinPlusResidualGate`, `PinPlusRoundThirteenGate` |
| The assembly of record | `kt_equiv_zmod16_of_two_leaves` (`PinPlusKTLeafGate.lean:463`) |
| Cross-session memory | `project_5qH_nonhausdorff_substrate_bug.md` |
