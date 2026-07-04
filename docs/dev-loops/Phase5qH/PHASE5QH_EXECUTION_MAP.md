# Phase 5q.H — EXECUTION MAP (genuine unconditional discharge, full strength)

> **THE MULTI-EFFORT ENTRY POINT. Read this FIRST, every session/compaction, before any effort notebook.**
> Strategic tracker = `docs/roadmaps/Phase5qH_LiteratureGradeUnconditional_Roadmap.md` (§10 = the wave path).
> Coherence source = `temporary/working-docs/16Convergence_Reconciliation_Audit_2026-07-04.md` (wins on any conflict).
> This map orchestrates the 5 efforts; each effort has its OWN notebook (two-layer INDEX+shard) under `docs/dev-loops/Phase5qH/E<n>_*/`.

## 0. Decision & posture (binding)

- **OPTION A — GO (operator, 2026-07-04):** build the **genuine L4** `Ω₄^{Pin⁺}≅ℤ/16` — genuine carrier, computed invariant, injective+surjective, **ZERO posits**, kernel-pure. NOT the disclosed-form L3 (that is already done and is retained only as the stepping-stone/fallback).
- **Target theorem:** `PinPlusGMWitness.omega4PinPlusGM_equiv_zmod16 : DataBordismGrp (pinPlusGMData) ≃+ ZMod 16`, axioms exactly `{propext, Classical.choice, Quot.sound}`.
- **Kernel-purity non-negotiable:** no new `sorry`/`native_decide`/`maxHeartbeats` in proof bodies; **no new project-local `axiom` without explicit user sign-off**. A genuinely-hard geometric input is carried as ONE disclosed tracked `Prop` (registry + discharge plan), never an axiom — until its effort discharges it.
- **Posture:** scope is SETTLED (Option A). Do the next increment of real work each turn. Legitimate stops ONLY = a kernel-checked no-go or a genuine user-only decision. Absence-from-Mathlib is the work, not a stop. No PM/LOE estimates in any notebook/roadmap.

## 1. The target, decomposed — the two verified substrates

The genuine close needs **two from-scratch, Mathlib-absent substrates** (verified — reconciliation §0-B; both independently confirmed by direct primary read 2026-07-04):

- **Substrate G (geometric, elementary, spectra-free):** 4-manifold embedded-surface/cobordism topology — tubular neighborhoods, normal framings, handle/surgery traces, Novikov additivity, even fillings, characteristic surfaces, relative PD / PD-with-boundary, the connection-split `TS(V)⊕ℝ≅π*TB⊕π*V`, collar/corner gluing, Whitney-sum spin two-out-of-three. Feeds both the Rokhlin `gm` congruence AND the geometric Smith map + exactness.
- **Substrate S (spectral, non-elementary — the ONE irreducible external input):** the `Ω^{Spin}_*/Ω^{Pin±}_*` base ladder incl. `Ω₆^{Pin⁻}≅ℤ/16` (ABP 1969) / `Ω₄^{Spin}≅ℤ`. **No elementary substitute exists** (reconciliation §0-B; ABK-DAG §4). This is the Adams/ABP tower (Phase 5q.D shelf).

The disclosed-form L3 (already on main) = the algebra that *assembles* G+S into ℤ/16 on the synthetic tied carrier, modulo one Prop packaging G+S.

## 2. The DAG — 5 major efforts (each = its own notebook)

```
                 ┌─────────────────────────────────────────────┐
   E1 (foundation)  Substrate G topology  ──────┬──────────────┐
   [main / lead]                                │              │
                                                ▼              ▼
                              E2 Rokhlin gm        E3 Smith map + exactness
                              [wt, after E1]       [wt, after E1]
                                     │                    │
                                     └──────────┬─────────┘
                                                ▼
                              E4 genuine carrier + assembly  ──►  disclosed-form capstone
                              [main / lead]                        (…_of_smith_inflow), mod E5
                                                                        │
   E5 (independent, START NOW)  Substrate S spectral  ─────────────────┘
   [wt, parallel from day 1]     discharges smith_inflow_z16
                                                                        ▼
                                            omega4PinPlusGM_equiv_zmod16  (UNCONDITIONAL)
```

| Effort | Notebook home | Roadmap | Depends on | Venue | Deliverable |
|---|---|---|---|---|---|
| **E1** Substrate G topology | `E1_SubstrateG_Topology/` | §10 (shared) | — (foundation) | main/lead + pull wt1 | char-surface + PD-with-boundary + surgery/handle/Novikov primitives, kernel-pure |
| **E2** Rokhlin `gm` | `E2_Rokhlin_GM/` | §10 P1.1 | E1 | wt slot | `gm` congruence from geometry → discharge `SmoothSpinManifold4.topo` → genuine 16∣σ |
| **E3** Smith map + exactness | `E3_SmithMap_Exactness/` | §10 P1.2 | E1 | wt slot | geometric Smith map + two-sided exactness → `ker abkGMGrade=⊥` reduced to `smith_inflow_z16` |
| **E4** genuine carrier + assembly | `E4_GenuineCarrier_Assembly/` | §10 P1.3 + H7 | E2, E3 | main/lead | `pinPlusGMData` built; `abkGM8` computed on it; smooth-instance upgrade; disclosed-form injective capstone `…_of_smith_inflow` |
| **E5** Substrate S spectral | `E5_SubstrateS_Spectral/` | §10 P2.1 (Phase 2) | — (independent) | wt slot, parallel | ABP/Adams ℤ/16 tower on `Ext_{A(1)}` → discharge `smith_inflow_z16` |

**Final assembly:** E4's `…_of_smith_inflow` capstone + E5's discharge of `smith_inflow_z16` ⟹ `omega4PinPlusGM_equiv_zmod16`, 100% unconditional.

## 3. Verified-source index (personally verified — direct primary read / kernel check, 2026-07-04)

Every load-bearing external input is verified; nothing rests on a scout's unverified word (operator standing rule). Full trace: reconciliation audit §2.

| Source | Verifies (effort) | What was confirmed |
|---|---|---|
| Taylor **`0802.0111`** "Quadratic Enhancements of Surfaces" | **E2** | Lem 1.2 (surgery-trace extends Pin⁻ ⟺ `q(S¹)=0`, `q∈MSpin₁≅ℤ/2`), Lem 1.3 (bounds disk ⟹ q=0), Thm 1.1 (no-0-handle handlebody + "arc has two ends"), Thm 2.1/Rmk 2.2 (`2β=F•F−σ mod 16`) — **verbatim** |
| Klug **`2011.12418`** "A relative version of Rochlin's theorem" | **E2** | Thm 2 `Arf(F)+Arf(∂F)=(σ−[F]²)/8+μ(∂X) mod 2`; "cap off … closed result … additivity" strategy — **verbatim** |
| DDK⁺ **`2405.04649`** "The Smith fiber sequence" App A | **E3** | Def A.8/A.10 (`S(2Det TM)` δ-model), Lemma A.11 eq (A.12b) two-out-of-three, Lemma A.2 (connection-split), Fig 3 (deg-6 arrow `Ω₆^{Pin⁻}=ℤ/16 →(g) Ω₄^{Pin⁺}=ℤ/16`) — **verbatim** |
| HKT **`1910.14039`** "Anomaly matching…Smith isomorphism" | **E3** | Thm 4.1 (sphere-bundle surjectivity + interval-bundle injectivity), Fig 3 green-curve, eq 4.37 — **verbatim** |
| Debray–Krulewski **`2406.08237`** "Smith homomorphisms and Spin^h" | **E3** | general LES recipe only; **defers** δ-model to DDK⁺ (attribution check) |
| **KT-LMS 151 §5** (`KirbyTaylor_PinStructures_LMS151.pdf`, in-corpus) | **E4** | Thm 5.2, Lemma 5.3 (`ker s=2ℤ ⟹ card(range)=2`), `ψ(ℝP⁴,ℝP³)=+2` — verbatim, pp.216–219 |
| **VERDICT (both E3 primaries)** | **E1/E5 split** | geometric maps elementary; the ℤ/16 **values** are external spectral inputs (Giambalvo/KT/ABP + Remark A.16 Adams + HKT p.28 AHSS) ⟹ 2nd independent confirmation of Substrate G+S |

**Kernel-verified in-tree facts (reconciliation §2):** `col4_height_eq_four` (`axioms:[]`), `rp4_dataBordismTied_equiv_zmod16` (std axioms, L2), `omega4PinPlusGMTied_equiv_zmod16_via_kt_of_grade0` (std axioms, L3), `GMrelation`/`SpinCharSurfaceData.gm`, `pinPlus_zmod16_of_smith_les` (abstract transport), `DataBordismGrp` = genuine `Bordism`-witness scaffold, `order_exact_sixteen_of_surfaceABK` (pure ℤ/16 arithmetic).

**Kernel-checked NO-GOs (never re-derive — read `docs/dev-loops/SETTLED_FORKS.md` before any impossibility reasoning):** `lattice_arf_bridge_refuted` (σ/8≡Arf FALSE; Rokhlin mod-16 irreducibly geometric → `nogo_lattice_arf_not_sigma8`), `synthetic-grade-ker-bot-nogo` (free-grade ker=⊥ FALSE → fix = GM carrier, not a better proof).

## 4. Worktree pointers (what to pull, where to build) — verified 2026-07-04

Base: **main @ `df10209b`**. Slots: `SK_EFT_Hawking/.claude/worktrees/wt{1,2,3}/lean`, servers `mcp__lean-lsp-wt{1,2,3}__*`.

- **wt1 (`worktree-wt1` @ `b3956505`) — HOLDS USABLE SUBSTRATE FOR E1/E3. DO NOT RESET.** 4 unmerged commits (`b537bcea`, `bbb7fc0d`, `34648eb5`, `b3956505`) add **7 new Lean files (842 lines)** of relative-PD / PD-with-boundary machinery:
  - `SingularCSCVanishAbove.lean`, `SingularCSCVanishAboveGeom.lean` — compactly-supported cohomology top-degree vanishing `Hᵏ_c(W)`
  - `SingularRelCohomVanishAbove.lean` — relative cohomology vanishing above
  - `SingularSubHomSumEnd.lean` — subhom sum / MV-end
  - `SingularOpenDualityMonotoneUnion.lean` — monotone-union stability of the open-duality maps (the W-relative cofinality core)
  - `PinPlusFloorCollapse.lean` — conditional `ker(abkGrade)=⊥` behind a tracked PD foundation (the disclosed injectivity skeleton — feeds E3/E4)
  - **PULL-IN PROCEDURE (E1's first brick):** wt1's base is 583 commits behind main → these are candidates, NOT a blind merge. Cherry-pick the 4 commits onto a branch off main (`git cherry-pick b537bcea bbb7fc0d 34648eb5 b3956505`), `lake build` the 7 files; if green + `lean_verify` clean, merge as E1's PD-with-boundary foundation. If APIs drifted, port the theorem statements (they are NEW files, so conflicts are import/signature-level, not content). **Never `/reset-slot 1` until these are harvested** (the guard will refuse anyway — unmerged commits).
- **wt2 (`worktree-wt2` @ `1bb9867c`) — no unique substrate (behind main; its tips are already merged). FREE SLOT** → `/reset-slot 2` to main, assign to a worker.
- **wt3 (`worktree-wt3` @ `1f44da1d`) — no unique substrate (on main's history). FREE SLOT** → `/reset-slot 3` to main, assign to a worker.

## 5. Parallelization plan (multi-agent)

Concurrency cap **≤2 concurrent `lean-worker` slots** (3+ ENFILE the file table — `feedback_parallel_slot_concurrency_enfile`); lead builds on main.

- **Lane L (lead, main):** E1 Substrate-G foundation — the shared critical path. First: harvest+validate the wt1 PD substrate (§4), then extend toward char-surface + surgery/handle/Novikov primitives.
- **Lane A (wt slot, START NOW — fully independent):** E5 Substrate-S spectral (ABP/Adams tower). Zero dependency on E1–E4, so it runs from day 1 in parallel. First: audit the Phase 5q.D `Ext_{A(1)}` shelf + the `spin_bordism_iso_Z` circularity guard.
- **Lane B (wt slot, after E1 provides shared primitives):** E2 Rokhlin `gm` (Taylor/Klug) — independent of E3.
- **Lane C (rotates onto a slot after E1):** E3 Smith map + exactness (DDK⁺/HKT) — independent of E2.
- E4 (assembly) is lead-work once E2+E3 land. Merge each slot FF-only into main; re-run the full gate per wave.

## 6. Current state & how to start (executing-agent bootstrap)

1. Read THIS map → your effort's `E<n>_*/LAB_NOTEBOOK_INDEX.md` (FRONTIER + CHECKLIST + DECISIONS) → the effort's verified source (§3) **directly** (never via summary).
2. `docs/dev-loops/SETTLED_FORKS.md` before any impossibility reasoning; the two NO-GOs (§3) are binding.
3. Live repo state: `scripts/repo_state_probe.py` (sorry/commit); counts via `update_counts.py` (never `rm …hash`).
4. Build MCP-first (lean_goal → lean_multi_attempt → write → repeat); commit GREEN kernel-pure increments every ~5–6 bricks; **never push**.

**State as of 2026-07-04:** infrastructure just laid; no Option-A Lean written yet. main @ `df10209b`. The disclosed-form L3 predecessor is archived at `_archive/` (its verified-blueprint history distributed into E2/E3). E1 first brick = harvest the wt1 PD substrate; E5 startable immediately in parallel.
