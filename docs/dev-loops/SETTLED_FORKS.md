# SETTLED FORKS — NEVER RE-DERIVE

The **negative half** of the Live-Anchor split (spec `LIVE_ANCHOR_REDESIGN_SPEC.md`, Move 2):
dead / banned / superseded routes that no *code* artifact records, so the loop keeps
re-deriving them across compactions (System-2 finding `compaction-summary-quality`; the harvest
repeatedly catches the loop re-opening a settled fork or re-deriving a committed engine).

**This is a MANDATED READ** (FIRST_ACTION): grep this register BEFORE any "this is impossible /
needs a banned route / let me re-derive whether X works" reasoning. `repo_state_probe.py` surfaces
the count + IDs as a pointer; the *reasons* live here.

**Schema** (one `## <route-id>` block per fork):
- `verdict`: `dead` | `banned` | `superseded`
- `tier`: `automatic` | `agent-reviewed` | `human-reviewed` (governance; mirrors System-2)
- `authored_by`: `kernel-no-go` | `coach` | `harvest` | `debrief`
- `killed_by`: the commit / kernel-check / decision that settled it
- `reason`: one line — why; what it would have needed
- `memory`: `[[note-slug]]` cross-link to project memory
- `created_ts` (REQUIRED) · `reviewed_ts` (set when `/debrief` reviews/modifies)

**Authoring & governance (ruling 2026-06-24):** a **kernel-checked no-go settles a fork
decisively** (`authored_by: kernel-no-go`, tier `automatic` — the kernel is the authority, so the
loop MAY record these mid-run). The **coach** may author/influence (`agent-reviewed`); the harvest
may *propose* (`automatic`). **`/debrief`** is the human review/modify layer (promote tier, edit,
retire) — no entry is immutable. Every entry carries datetime metadata.

> Seeded 2026-06-24 from the existing `Lit-Search/Phase-5qF/L2/LAB_NOTEBOOK_INDEX.md` register +
> project memory. The forks below are RECORDS of prior settled decisions; do not re-litigate them.

---

## routeC-snake-mv-ses
- verdict: banned
- tier: human-reviewed
- authored_by: debrief
- killed_by: user ruling (goal marker `20260617T231250` SETTLED LOCKS: "B<->C thrashed for DAYS — NON-NEGOTIABLE")
- reason: the snake / MV-SES + SnakeInput route is a multi-wave rebuild kept ONLY as a last-resort fallback; never re-open, re-cost, or re-litigate Route B vs C.
- memory: [[project-L2-routes-B-C-compaction-prep-2026-06-22]]
- created_ts: 2026-06-22T00:00:00Z
- reviewed_ts: 2026-06-24T00:00:00Z

## homology-class-square-lift
- verdict: dead
- tier: agent-reviewed
- authored_by: coach
- killed_by: reverted 2026-06-22 (needs the false `hmem`; stay at CHAIN-pairing altitude, never lift to the homology-CLASS square)
- reason: lifting the connecting square to the homology-class level requires a membership fact (`hmem`) that is false at cover level; the close stays whnf-dodged at chain-pairing altitude with the z_seam ∃-bound.
- memory: [[project-L2-routes-B-C-compaction-prep-2026-06-22]]
- created_ts: 2026-06-22T00:00:00Z
- reviewed_ts: 2026-06-24T00:00:00Z

## kronecker_cap_chainIncl_eq_rcap_chainIncl-MatchLHS83
- verdict: dead
- tier: agent-reviewed
- authored_by: coach
- killed_by: FALSE-POSITIVE confirmed (lean_multi_attempt empty-goals ≠ an in-file close; verify with lean_diagnostic / lake build)
- reason: `kronecker_cap_chainIncl_eq_rcap_chainIncl` (MatchLHS:83) appears to close under multi_attempt but does NOT close in-file — do not re-attempt it as a real close path.
- memory: [[project-L2-routes-B-C-compaction-prep-2026-06-22]]
- created_ts: 2026-06-22T00:00:00Z
- reviewed_ts: 2026-06-24T00:00:00Z

## mfd-equals-H1-dead-end
- verdict: dead
- tier: automatic
- authored_by: kernel-no-go
- killed_by: kernel-checked `dataBordism_two_torsion_of_revStr_trivial` (Phase 5q.F)
- reason: the `Mfd := H¹` construction is a kernel-checked dead-end; do not re-attempt it.
- memory: [[project-phase5qF-strict-retirement]]
- created_ts: 2026-06-15T00:00:00Z
- reviewed_ts: 2026-06-24T00:00:00Z

## cap-sigmaR-connecting-needs-banned-formula
- verdict: superseded
- tier: human-reviewed
- authored_by: coach
- killed_by: committed engine `cap_coboundary_cochainSplit_eq` / `_subdiv` (a3f217e1 / 2f58618c, kernel-pure)
- reason: the recurring WORRY that "cap σR-connecting needs the banned `relCohomMvConnecting_eq` formula / non-degeneracy, so it's dead" is FALSE — the committed engine proves it GAP-FREE (only `cap_relCochains_subspaceChains_eq_zero` + `cap_leibniz` + ℤ/2, NEVER the formula). Coach-resolved 4×; a recurring re-seed. NEVER re-derive; NEVER reach for `relCohomMvConnecting_eq`.
- memory: [[project-L2-sigmaR-connecting-resolved-2026-06-23]]
- created_ts: 2026-06-23T00:00:00Z
- reviewed_ts: 2026-06-24T00:00:00Z

## kronecker-altitude-respine
- verdict: banned
- tier: human-reviewed
- authored_by: coach
- killed_by: reverts `a79f1912` (of_hcup_linked re-seed → cap-altitude `8cb87e5c`) + `3ea6b739` (kronecker_pd_fold_fund / `_of_crossRealization` re-seed, ~15 commits `ae6a1210`→`ac415397` → cap-altitude `ccdd0aef`); user + coach (2nd dispatch) goldfish-reseed ruling
- reason: re-spining the L2 close to the KRONECKER ALTITUDE (the `_of_crossRealization` / `kronecker_pd_fold_fund` / `of_hcup_linked`-as-spine family) is THE dominant 5q.F spiral — started 3×, hard-reverted 2×, each time framed as a "whnf-dodge breakthrough" (that framing is the re-seed tell). The L2 close SPINE stays at CAP altitude (cap-Leibniz); the σR side joins via the pairing adjunction `relKroneckerH_relCohomMvConnecting` as a SUB-step (Fact A), never as the spine. The ban is on the ALTITUDE, not on any single lemma name (kronecker sub-lemmas inside the Fact-A step are fine). The tactical cap-altitude whnf is a SYMPTOM, dodged AT cap altitude (def-head-match), never by re-spining. Verify present state by ROUTE/ALTITUDE, not "commit present."
- memory: [[project-L2-kronecker-reseed-reverted-2026-06-24]]
- created_ts: 2026-06-24T00:00:00Z
- reviewed_ts: 2026-06-24T00:00:00Z

## L2-hident-exact-equality-dead
- verdict: dead-end (kernel-level)
- tier: self-derived (turn 52, 2026-06-25)
- killed_by: `cap_homology_singularSd_iterate` (SingularCapHomologySubdiv:28) = cap-Sd-shift is HOMOLOGY-level (up-to-boundary), not exact
- reason: closing the L2 KEY via `connecting_square_close_cocycle_fund` (or `connecting_square_close`) forces `hident` as an
  EXACT chain equality `chainIncl seam + chainIncl pd = cap g_rep ∂fund`. But the cover-split of `∂fund_∩` is available ONLY
  via subdivision (`exists_cover_fine_subdivision`, Sdʲ), introducing a non-zero boundary slack `∂(cap g_rep · subdiv-homotopy ∂fund)`
  that the exact equality cannot absorb (seam/pd are un-subdivided + fixed). The S2 cleaner-witness route is a DEAD END for L2.
  ✅ USE the COACH-LOCKED ∈-boundaries route (NC:1465-1468): `realize_chainBoundary_cap_mem_boundaries` on `W = cap(cochainSplit
  g_rep)(F)` (F = cover-V-projection) + the two facts (χ-term via the engine `cap_coboundary_cochainSplit_eq`, seam-term) — the slack
  lives IN the boundary so no exact-cancellation needed. This is the engine/realize route the coaching block named all along.
- created_ts: 2026-06-25T00:00:00Z

## synthetic-grade-ker-bot-nogo
- **Date/goal:** 2026-07-03, 5q.G G3-4/G4-2 (goal 20260702T184323).
- **The fork:** prove `ker(abkFaithfulGrade) = ⊥` UNCONDITIONALLY for the synthetic-grade faithful
  datum (`Mfd s := {g : PinPlusGrade // PinPlusCert I s}`, grade free in the subtype) via
  surjectivity + a provable `card ≤ 16` cap.
- **Kernel-checked verdict: NO-GO.** For ANY datum whose grade is free per-manifold, a grade-`0`
  structure on a certified non-null-bordant manifold (`ℝP⁴`: `w₂ = 0`, `[ℝP⁴] ≠ 0 ∈ Ω₄^O`) is a
  kernel class not bordant to `(∅, 0)` — every `IsDataBordant` chain preserves the grade AND needs
  underlying unoriented bordisms, which for `ℝP⁴ → ∅` do not exist. So `ker = ⊥` (and `card ≤ 16`)
  is FALSE for the free-grade datum; making it true requires the grade to be TIED to the structure
  (the Dirac-η/ABK invariant *of a Pin⁺ structure*), whose formalization needs the Mathlib-absent
  frame-bundle/Pin⁺-structure foundation, and the cap is then AHSS convergence (Anderson–Brown–
  Peterson 1969) — the same absences already documented in `PinPlusTangentialData` §2/§5b.
- **Resolution (SHIPPED, `PinPlusFaithfulData.lean` §3):** (a) UNCONDITIONAL
  `dataBordismFaithful_quotient_abk_equiv_zmod16` (first-iso on the faithful carrier — the residual
  kernel is now the *certified* floor, strictly sharper in meaning than pinPlusData's `Ω^O` floor);
  (b) the ONE disclosed Prop = `Finite` + `Nat.card ≤ 16` of the faithful carrier, under which
  `abkFaithfulGrade_bijective_of_cap` / `abkFaithfulGrade_ker_eq_bot_of_cap` /
  `dataBordismFaithful_equiv_zmod16_of_cap` deliver the full-carrier `≃+ ℤ/16` — every OTHER
  Landmark field (datum, w₂-selection, revStr-nontriviality, surjectivity) now PROVEN, not disclosed.
- **Discharge plan for the residual Prop (two-part decomposition — corrected 2026-07-03 after
  user review; the original "infeasible, revisit on substrate shift" framing was a
  hypothesis-based descope and is retracted):**
  1. **The structure-tied grade (BUILDABLE ARC — not blocked):** model a Pin⁺ structure as
     Kirby–Taylor data the current tower already expresses — the `H¹(M;ℤ/2)`-torsor of structures
     over the `w₂ = 0` certificate (both in-tree), with the grade DEFINED through the
     characteristic-surface quadratic enhancement + the Brown machinery (`Z4Quadratic`, `brown`,
     `reduce16to8`, the PD/Wu tower for characteristic-surface data). This kills the ℝP⁴ witness
     (grade 0 becomes unpopulatable — the enhancement forces odd β) and upgrades `faithfulGenerator`
     to a geometric class. A multi-wave arc of the same shape this project has repeatedly closed.
  2. **The `card ≤ 16` completeness (the irreducible input):** even with tied grades, `ker = ⊥`
     needs "η(σ)=0 ⟹ (M,σ) bounds" = ABK-completeness = the Anderson–Brown–Peterson spectral
     fact; formalizing it means an AHSS fragment for this filtration (Mathlib has SS basics, no
     bordism AHSS). A phase-scale program in its own right — SCOPE IT AS SUCH if attempted;
     until then it is the single disclosed Prop, with `col4_height_eq_four` as its decidable
     Ext-chart input.
- **DO NOT re-attempt** the unconditional `ker = ⊥` on ANY free-grade datum; the ℝP⁴ witness kills
  every such design. Any future attempt must FIRST tie grades to structures.

## phase6BB-physlib-pin-bump-B-vs-C
- verdict: superseded
- tier: human-reviewed
- authored_by: coach
- **UPDATE 2026-06-29 (USER-AUTHORIZED, supersedes the `banned` verdict below):** user said "I'm open to bump". Investigation found PhysLib's QM tree splits across the v4.30.0 bump (#1130): the **molecular-Hamiltonian substrate** (`SpaceDQuantumSystem` + `kinetic`/`potential`/`hamiltonianOperator`, `momentumSqOperator`, `𝓜`) landed at **#1120 (`085dab8f`) on Mathlib v4.29.1 = OUR pin**, while the **spectral theory** (regularity/defect/surjectivity) landed at #1141+ on Mathlib **v4.30.0**. So: BUMP to **#1120** (085dab8f) — gains the molecular substrate, **NO Mathlib bump**, StatMech + QuantumInfo APIs unchanged #1081..#1120 (empty diffs → existing consumers unaffected); do NOT pull the spectral theory (v4.30.0 = forbidden project-wide bump). The earlier autonomous "banned" was correct ABSENT user sign-off; with sign-off + the v4.29.1-safe target, the bump is the right call. NOTE: required removing the contaminated `.lake/packages/Physlib` (untracked version-skew files) + fresh re-clone at #1120 (contamination = 0 after). **Phase-6BB still builds its OWN Kato–Rellich self-adjointness in-tree** (the 11 C-minimal lemmas) — #1120 gives the molecular OBJECT, not the spectral theory; the C-minimal work is NOT mooted, the bump complements it (molecular instantiation + W2–W4 foundation).
- killed_by: coach ruling (goal `20260629T154332`, substrate-routing escalation) — Route B is a STANDING "no", not a user-only call
- reason: 6BB W1's PhysLib QM/spectral substrate does not compile at our pin (SpectralTheory/Basic.lean `Or.casesOn` drift; DDimensions/Basic.lean mid-refactor missing identifiers). **Route B (bump the shared PhysLib pin) is pre-decided OFF autonomously** — forbidden by (a) the in-repo lakefile warning "Do NOT advance to a higher physlib commit", (b) the pin is shared with the parallel public-repo agent (`feedback_parallel_agent_git_hygiene`), (c) safe-by-default-on-shared-infra-doubt (`feedback_targeted_ambition_and_private_default`). It is NOT an external-value/risk-budget user call. **Route B2** (vendored `.lake` patch) is killed by the goal's "lake build green for everyone" AC (gitignored = non-reproducible). **Route = C**: build the minimal in-tree self-adjointness substrate on Mathlib `LinearPMap`, scoped to exactly what the chosen W1 architecture consumes (a defect/range self-adjointness criterion for the abstract Kato–Rellich), NOT a blanket ~1000-line spectral rebuild. If even that criterion is Mathlib-absent, it becomes ONE scoped disclosed tracked-Prop (PD-2; gates the W1 apex) — never a self-discharging/vacuous statement, never an axiom. Do NOT re-litigate B-vs-C across compactions.
- created_ts: 2026-06-29T00:00:00Z

## L2-crux-delta-phi-bounds-never-in-UcapV
- verdict: dead-end (derivation-level, term-by-term exhaustion)
- tier: automatic
- authored_by: kernel-no-go (derivation verified against committed engine statements, 2026-07-03 17th push)
- killed_by: the excision-gap constraint (L2 notebook 14th push) + the (χ)+Brick-D expansion audit (17th push)
- reason: routing the fact-(i) CRUX (`∂(cap g fB) + cap g bF ∈ ∂C(U∩V)`) through cap-δφ expansions of
  the fund-compat CANNOT close — every δφ-family bound lands in C(U∪V) (K-term), C(X) (η-term; the
  fund-compat rel-homology is structurally ambient), or C(infCompactᶜ) (a₂-term via Brick C), and the
  seam side has no matching partners, so nothing cancels into the required C(U∩V)-bound. The correct
  direction is the coach-locked W-shape (exhibit the crux-sum as ∂ of explicitly-C(U∩V) chains:
  W₀ = cap g (Sd^jF φ₂), W₁ = cap φ (Sd^jF φ₂), Brick-B T-bounds on aF/bF) and/or the DR's
  "on-the-nose chain identity once both sides are cover-small" (compatible single-subdivision choices).
  Do NOT re-attempt δφ-routing of the crux.
- memory: (L2 notebook 17th push, Lit-Search/Phase-5qF/L2/LAB_NOTEBOOK.md)
- created_ts: 2026-07-03T00:00:00Z

## synthetic-smith-map-to-tied-carrier
- verdict: dead
- tier: automatic
- authored_by: kernel-no-go (construction-level, verified against smithDataHom + GMTiedStr.htie, 2026-07-03)
- killed_by: the `htie` constraint of `GMTiedStr` (`reduce16to2 grade16 = swTotalNe s`) vs `swTotalNe emptySM = 0`
- reason: the `smithDataHom` shortcut (map every neighbor class `[M,σ]` to `[emptySM, (σ,0)]`, transporting
  the grade synthetically) CANNOT build the Smith map into the 5q.H TIED carrier `pinPlusGMTiedData`. The
  odd generator (grade 1) would need `GMTiedStr emptySM` with `grade16=1`, but `htie` forces
  `reduce16to2 1 = 1 = swTotalNe emptySM = 0` — contradiction. The geometric TIE that makes `ker=⊥`
  possible (defeating `synthetic-grade-ker-bot-nogo`) SIMULTANEOUSLY blocks any synthetic emptySM Smith
  map: an odd grade requires a real w₁⁴=1 manifold (ℝP⁴ / the Mathlib-absent `PD(a)` zero-locus), not
  emptySM. The genuine geometric Smith map into the tied carrier IS the deep §9.3 geometric input; there is
  no synthetic shortcut. Do NOT re-attempt an emptySM-based `smithGMTiedHom`.
- memory: [[nogo_lattice_arf_not_sigma8]]
- created_ts: 2026-07-03T00:00:00Z

## 5qH-injectivity-routes-all-equal-one-completeness-prop
- verdict: superseded (route-choice is MOOT — kernel-checked equivalence)
- tier: automatic
- authored_by: kernel-no-go (equivalence proven in-tree, `PinPlusGMWitness.spin_range_ge_of_grade0_inj` +
  `omega4PinPlusGMTied_equiv_zmod16_via_kt_of_grade0`, 2026-07-04)
- killed_by: the proven implication `hbound (grade-0 ⟹ 0) ⟹ hle (KT ⊇ inclusion)` + the existing
  `grade0_bounds_of_thom` (`hthom ⟹ hbound`); both kernel-pure
- reason: the three 5q.H injectivity routes — **Thom** (`hthom`: SW-trivial Pin⁺ 4-mfd bounds), **KT §5**
  (`hle`: `ker(reduce16to8∘abkGMTied16) ⊆ (n↦n•g8).range`), **Smith-LES** (`smith_inflow_z16`: `Ω₆^{Pin⁻}≅ℤ/16`)
  — are PROVABLY the SAME single node: all reduce to `hbound = grade-0-injectivity` on the tied carrier (KT ⊇
  follows from `hbound` via grade∈{0,8}+`g8`-coset; Thom gives `hbound` via `grade0_bounds_of_thom`; the tied
  carrier's `htie`+cert make grade-0 ⟺ SW-trivial). So DO NOT route-shop among them or re-derive "which route
  is closer" — they are apex-equivalent, the reduction is CANONICAL. The terminal node `hbound`/`hthom` = Thom
  generation / the relative fundamental class `[W,∂W]` + surgery = the genuine Mathlib-absent research-grade
  wall (NOT `16∣σ` Rokhlin alone — that is necessary but strictly weaker than the completeness `hbound` needs).
- UPDATE 2026-07-06 (user-directed re-anchor; DIRECT read of KT-LMS §5 pp.216–218 + `Lit-Search/Phase-5qH/
  KT_LMS_Section5_completeness_proof_extracted.md`): the surgery wall above is now NAMED concretely, and it is
  GEOMETRIC — consistent with this fork's "`[W,∂W]` + surgery" line, and correcting the *separate* "spectral
  ABP tower / no elementary substitute" framing that the atlas ranking + reconciliation §0-B carried. KT §5
  proves `Ω₄^{Pin⁺}≅ℤ/16` via the exact sequence `0 → ℤ/2 → Ω₄^{Pin⁺} → ℤ/8 → 0`: the `ℤ/8` is `Ω₂^{Pin⁻}`
  (Brown/Gauss, DONE in-tree); the kernel is the image of `Ω₄^{Spin}`, `≤ ℤ/2` by Lemma 5.3 (double-cover
  `÷32` signature). So **`card ≤ 16 = 2×8` is assembled FROM BELOW** — the only deep input is **`Ω₄^{Spin}≅ℤ`
  (gen. Kummer)** + the geometric Smith map `[∩w₁²]` (E3) + Lemma 5.3, with Rokhlin `16∣σ` supplied by E2's GM
  formula at `F=∅`. **NO ABP `Ω₆^{Pin⁻}≅ℤ/16`, NO Adams tower.** The `α`/`ψ` index invariant is OFF the
  critical path (the project's `surjective-onto-ℤ/16` is standalone from the Gauss-sum + δ-cap, so the
  non-split extension is automatic; index theory drops out — verified in-tree, `PinPlusGMWitness` cap chain).
  This does NOT re-open the settled route-equivalence above (the injectivity Props stay apex-equivalent to
  `hbound`); it re-anchors the DISCHARGE TARGET onto the cheapest Substrate-S form — `Ω₄^{Spin}≅ℤ` (KT route,
  reuses E1/E2/E3) rather than `smith_inflow_z16` (`Ω₆^{Pin⁻}`, the wired-but-harder spectral form that only
  ranks atlas-keystone because the downstream Smith-LES transport is what's wired). `smith_inflow_z16` is
  DEMOTED: an alternative route, not the required keystone. Formalizability of `Ω₄^{Spin}≅ℤ` = live
  deep-research (scout dispatched 2026-07-06). The reconciliation §0-B "no elementary substitute" verdict was
  scout-sourced about the SPECTRAL computations and never verified for the `Ω₄^{Spin}` surgery route (the
  scout's own C5 flag) — do NOT treat "the completeness requires the ABP tower" as settled.
- UPDATE 2026-07-06b (deep-research on `Ω₄^{Spin}≅ℤ` returned + lead-vetted → `Lit-Search/Phase-5qH/
  Omega4Spin_Z_formalization_route_20260706.md`): the finest-grain wall is NAMED — `σ=0` spin ⟹ even form
  `≅ n·H` (Milnor–Husemoller even-indefinite classification — *formalizable lattice algebra, reuses E1's
  intersection form*) ⟹ `n(S²×S²)` ⟹ **bounds a spin 5-manifold by 3-handle attachment** (the one
  Mathlib-absent manifold-topology step; matches this fork's memory `project_5qH_geometric_floor_terminal`).
  Confirmed SURGERY, not Adams/AHSS (Kirby–Taylor survey arXiv:math/9803101; FKV arXiv:2012.02004). Mathlib
  has definitional `SingularManifold` scaffolding (`Mathlib/Geometry/Manifold/Bordism.lean`, no group/relation
  yet) to build on. **CAVEAT (lead-corrected a scout over-claim): there is NO Rokhlin-only shortcut around the
  full `Ω₄^{Spin}≅ℤ`** — the "`|image| ≤ 2` from Rokhlin + first-iso-theorem" idea needs Lemma 5.3's `⟸`
  direction (`32∣σ ⟹ Pin⁺-bounds`), which itself uses "K3 generates `Ω₄^{Spin}`" = the full iso. Do NOT
  re-chase that shortcut. `Ω₄^{Spin}≅ℤ` stays the one deep input; its Lean-tractability (surgery step vs the
  spectral tower it replaces) is the open judgment call.
- **⚠ CORRECTION 2026-07-21 (atlas-integrity repair, wt3 — verified against the Lean, not the prose):** the
  wording above ("PROVABLY the SAME single node", "apex-equivalent", "the reduction is CANONICAL") **overstates
  what is proved and must not be cited as a kernel-checked equivalence.** What is actually in the kernel is
  **three ONE-WAY implications**, all stated on `pinPlusGMTiedData (k := 0)`:
  `hthom ⟹ hbound` (`UnorientedThomCapstone.grade0_bounds_of_thom`),
  `hbound ⟹ hle` (`PinPlusGMWitness.spin_range_ge_of_grade0_inj`), and
  `hbound ⟹` the old-carrier iso (`PinPlusGMWitness.omega4PinPlusGMTied_equiv_zmod16_via_kt_of_grade0`).
  So `hbound` is **SUFFICIENT** to feed those old capstones. **NOT proved anywhere in-tree:** any reverse
  implication (`hle ⟹ hbound`, `hbound ⟹ hthom`); **any** theorem relating the Smith leg
  (`smith_inflow_z16` / `SmithInflow` / `Ω₆^{Pin⁻}`) to `hbound` in either direction — the Smith leg of the
  "three routes" claim has **zero** backing; that the routes agree on the **faithful** carrier; or that any
  node is **unavoidable**. Separately, all three implications live on the carrier that
  `NonHausdorffBordismCollapse` later **vacated** — there `hbound` is an *unconditional theorem*
  (`grade0_eq_zero_of_nonHausdorff`, zero geometric input) and `mk p = mk q ↔ grade16 p = grade16 q`
  (`dataBordismGMTied_mk_eq_iff_grade16_eq`). So the *surviving* settled content is: **route-shopping on the
  old tied carrier is moot because that carrier is dead**, not because the routes were shown equivalent. The
  `KERNEL_NOGO_REGISTRY` entry `5qH-injectivity-routes-apex-equivalent` now carries this as an explicit
  `scope_limit` (rendered into `KernelNoGos.lean`); the fork-id retains the legacy wording and is **not** a
  claim. Nothing here licenses "the node is unavoidable, therefore we must pay for it."
- memory: [[project_5qH_geometric_floor_terminal]]
- created_ts: 2026-07-04T00:00:00Z

## 5qH-capstone-regularity-level-k0-vs-k1-unbridged (2026-07-21, wt3 atlas-integrity repair — KERNEL-BACKED fence; registry entry pending an extraction refresh)
- **verdict:** OPEN RESIDUAL — **the roadmap's leg-2 hard constraint is currently violated by the assembly
  of record** · **tier:** automatic · **authored_by:** atlas-integrity audit (lead-dispatched; every
  citation below verified in-tree, not taken from prose)
- **⚠ SEVERITY (determined 2026-07-21, escalated by the lead mid-audit).**
  `Phase5qH_LiteratureGradeUnconditional_Roadmap.md` §2 leg 2 promotes to a **hard constraint**: the
  carrier must be smooth, `k ≥ 1`, because "at `k = 0` the honest group is topological Pin⁺ bordism
  `≅ ℤ/2 ⊕ ℤ/8` (Kirby–Siebenmann; E₈), i.e. the **WRONG group** … the C⁰ fork must never be silently
  conflated with the ℤ/16 target." §2 also warns a carrier missing any leg produces
  "**true-but-vacuous completeness statements**." The lead asked whether the in-tree `k := 0` is (a) an
  index unrelated to smoothness, or (b) a genuine C⁰ carrier. **The answer, settled in source, is (b) —
  and it is sharper than the roadmap's phrasing.**
- **The determination (kernel-checked, `SKEFTHawking/PinPlusRegularityFence.lean`).**
  `CharPairWProviderPerOp`'s binder is `(k : WithTop ℕ∞)` (`PinPlusCharPairBorTethered.lean:142-143`) —
  Mathlib's **smoothness exponent**, the same `k` fed to `SingularManifold X k I`, whose
  `[isManifold : IsManifold I k M]` instance field (`Mathlib/Geometry/Manifold/Bordism.lean:120`)
  is what carries regularity. At `k = 0` that field is **not weak — it is FREE**: Mathlib proves
  `contDiffGroupoid 0 I = continuousGroupoid H` (`IsManifold/Basic.lean:694`) and registers the
  **unconditional** `instance : IsManifold I 0 M` (ibid.:860) for *every* charted space. Two kernel-pure
  theorems record this: `isManifoldZero_free` (the binder is free for any charted space) and
  `singularManifoldZero_ofTopological` (a compact boundaryless charted space over
  `EuclideanSpace ℝ (Fin 4)` yields an element of `SingularManifold PUnit 0 (𝓡 4)` with **no
  smoothness hypothesis in its binder list**). Both `{propext, Classical.choice, Quot.sound}`.
- **Consequence.** `PinPlusKTAssemblyResiduals.residualProv : CharPairWProviderPerOp (𝓡 4) 0` puts the
  assembly of record on `pinPlusCharPairData residualProv : T2TangentialData PUnit 0 (𝓡 4)`, i.e. over
  **compact boundaryless charted topological 4-manifolds, zero differentiability**. That is exactly the
  C⁰ fork the roadmap forbids conflating with the ℤ/16 target. **Every ℤ/16 statement currently proved on
  that carrier must be quoted with "`k = 0` / topological category" attached.**
- **What is NOT claimed (do not overstate this fence).** The assembly's conclusion is **not refuted** —
  it is *uninterpreted* pending a regularity fix. And the **stronger** form is deliberately NOT built: no
  in-tree *separating witness* (a concrete element of `SingularManifold PUnit 0 (𝓡 4)` admitting no
  `IsManifold (𝓡 4) 1` structure — an atlas with homeomorphic but non-`C¹` transitions) exists yet. That
  witness is the honest next brick; it would upgrade this from "the binder is free" to "the categories
  provably differ in-tree".
- **Registry status.** This IS kernel-encodable (false statement: "the `k := 0` instantiation keeps the
  char-pair carrier in the smooth category / the `k` binder carries regularity at `0`"; backing:
  `isManifoldZero_free` + `singularManifoldZero_ofTopological`). It is **not yet a
  `KERNEL_NOGO_REGISTRY` entry** only because `lean_deps.json` is stale (its regen lock was held by
  another slot), and `nogo_substrate_integrity` hard-fails on backing theorems absent from that cache.
  **Encode it in the same turn as the next extraction refresh** — the entry is drafted in the wt3
  handoff report.
- **The gap.** The standing goal requires a **smooth `k ≥ 1`** carrier —
  `docs/dev-loops/Phase5qH/HANDOFF_16_CONVERGENCE.md:31-37` states the target as "a genuine
  bordism-of-manifolds substrate (T2 carrier, **smooth k ≥ 1 data**, structure-extension bordism relation
  with the Brown/ABK invariant *computed*, not posited)". But the **canonical provider actually consumed by
  the authoritative KT assembly is declared at `k := 0`**:
  `PinPlusKTAssemblyResiduals.residualProv : CharPairWProviderPerOp (𝓡 4) 0` (lines 65-72), and the
  end-to-end conditional's conclusion is consequently an iso on `pinPlusCharPairData residualProv` — i.e. on
  the `k = 0` carrier.
- **What is missing.** **No declaration in-tree proves the resulting bordism groups equivalent**, or
  transports a `k = 0` result to a `k ≥ 1` carrier. `T2TangentialBordism.lean:20-30` explicitly labels the
  `k = 0` topological-vs-smooth relationship a **"record, not proven here"** (the Kirby–Siebenmann / E₈
  concern: at `k = 0` this is *topological* bordism, where KS breaks the ℤ/16 — the same warning appears in
  `KERNEL_NOGO_REGISTRY["nonhausdorff-bordism-collapse"]`: "even T2 at k=0 is TOPOLOGICAL bordism (KS breaks
  ℤ/16); literature-grade needs the SMOOTH (k=∞) + T2 carrier").
- **Why prose and not a registry entry** (per ADR-007 N-B / the encode-on-settle discrimination): this is a
  *statement-shape / route* fact — a **gap between two stated targets**, with **no false statement and no
  backing refutation theorem**. It is not provably-false, so it is not kernel-encodable. It becomes a
  registry entry only if someone proves a `k = 0` ⟹ `k ≥ 1` transport is *impossible* as shaped.
- **Standing obligation (do not let this rot).** Any claim that Phase 5q.H has landed "the Kirby–Taylor
  `Ω₄^{Pin⁺} ≅ ℤ/16` on a faithful carrier" **must** state its regularity level explicitly. Closing it needs
  ONE of: (a) a proved transport `k = 0 ⟹ k ≥ 1` for these carriers; (b) re-declaring `residualProv` and the
  assembly at `k ≥ 1` and re-proving the row; or (c) an explicit, signed-off narrowing of the handoff target
  to `k = 0` **with** the Kirby–Siebenmann caveat carried into every downstream claim. Until one of the three
  lands, the honest phrasing is "**on the `k = 0` tethered char-pair carrier**", never an unqualified
  "faithful smooth carrier".
- **✅ RESOLVED BY ROUTE (b) — 2026-07-21, wt3 (the regularity lift). Route (a) was never available:**
  `PinPlusRegularitySeparation.no_generic_zero_to_one_transport` refutes generic `C⁰ ⟹ C¹`, and
  `PinPlusRegularitySeparationCarrier.exists_carrier_element_not_smooth` shows the object classes
  genuinely differ. So the lift had to be a **re-declaration**, and it is done:
  * `PinPlusKTAssemblyResiduals.residualProvK (k)` — the canonical provider at **every** `k`
    (`nonempty_charPairWProviderPerOp` was always `{k}`-generic; `k := 0` was a *choice*).
    `residualProv = residualProvK 0`, type unchanged.
  * `kt_equiv_zmod16_of_residuals_ofKRS {k}` — the regularity-generic assembly core;
    `kt_equiv_zmod16_of_residuals_ofAmbientRow {k}` — the same with the KRS leaf at the
    `AmbientSurgeryDatum` row; `kt_equiv_zmod16_of_residuals_smooth` /
    `rokhlin_sixteen_of_residuals_smooth` — **the `k = ⊤` headline** (`Nat.card … = 16` in the
    smooth category). All `{propext, Classical.choice, Quot.sound}`.
  * The smooth carrier is **unconditionally non-vacuous**: `charPairBrown_surjective_smooth` and
    `rp4_ne_zero_smooth`, off the `Cω` ℝP⁴ witness `RP4CharPairWitness.rp4CharPairK ⊤`
    (`RP4Manifold.isManifold_rp4` and `RP2Manifold.isManifold_rp2` are `Cω`;
    `RP2EquatorialInclusion.contMDiff_embRP2` is `k`-generic).
  * **Conservative, not a walk-back:** `kt_equiv_zmod16_of_residuals` and
    `rokhlin_sixteen_of_residuals` keep their exact `k = 0` statements and are now corollaries; the
    generic KRS leaf is a *weaker* hypothesis than the `k = 0` `KRSResidualRow` supply.
- **⚠ THE HONEST RESIDUE — what is still C⁰-only (named, do not paper over).** The KT surgery-trace
  *constructed supplier* of the KRS leaf is genuinely C⁰-only, at the statement level:
  `SurgeryFoundation.SmoothSurgeryChartDatum.ofC0` (sets `D.k := 0`, "the whole smoothness/weld stack
  is free"), `SingularSurgeryChartsConcrete.ambientTraceBordism_concrete` (its
  `he_smooth : ContMDiff … 0 e := contMDiff_zero_iff.mpr he_cont` — smoothness IS continuity there),
  and everything typed on them: `ktHandleAttachment`, `SeamCollarDatum`, `SurgeredEndDatum`,
  `ambientTraceBordism_capstone(_ofSurgeredEnd)`, `capstoneB`, `KRSResidualRow`, plus the four modules
  `PinPlusTraceCapstone{Inhabit,MembraneWeld,SupplyMV,ResidualRow}` (deliberately byte-identical to
  main) and `PinPlusResidualGate` / `PinPlusCharPairTetherGate`. To make the KRS leaf smooth one must
  build a **smooth handle attachment** (corner smoothing on the glued 5-dim trace + a genuinely `C^k`
  boundary embedding) — Mathlib-absent, a phase-scale brick, and the honest open content of the
  smooth lift. Until it lands, the smooth headline takes its KRS leaf at `AmbientSurgeryDatum`, where
  the `Bordism`'s `IsManifold … k` / `ContMDiff … k` fields carry the regularity for real.
- created_ts: 2026-07-21T00:00:00Z · reviewed_ts: 2026-07-21T00:00:00Z

## 5qH-fg-ek-over-Z-blocked (2026-07-12, arm-2 — KERNEL-REGISTERED same-day; scout-verified vs primaries)
**Encode-on-settle upgrade (same turn-chain):** now a `KERNEL_NOGO_REGISTRY` entry backed by
`SKEFTHawking.FGDualityNoGo.dual_blowup_not_finite` + `not_finite_baerSpecker` (the ℤ-dual blow-up:
Dual ℤ (ℕ →₀ ℤ) ≅ the Baer–Specker group, uncountable/non-f.g. — kernel-pure). The FULL Specker
self-dual counterexample ((⊕ℤ)⊕ℤ^ℕ; needs slenderness of ℤ) is literature-verified, formalization queued.
**BANNED route:** deriving `intH2_basis` FG at general M via a ℤ-analog of the mod-2 Erdős–Kaplansky
self-duality forcing (`SingularUCFinite` pattern). PROVABLY BLOCKED: `A = (⊕ℤ) ⊕ ℤ^ℕ` is self-dual
(Specker) and not f.g. — PD (H²≅H₂) + UCT-duality over ℤ cannot force finite generation. The countable
rescue (ℵ₁-freeness of ℤ^ℕ) is circular (countability of H₂ needs ANR tech). Minimal published FG route =
Borsuk-ENR (FNOP 1910.07372 Cor 3.18) — community-scale. **Project path: witness-level `kron`/`B` data.**
Verdict file: `Lit-Search/Phase-5qH/FG_via_PD_duality_forcing_verdict_20260712.md`.

## 5qH-orient-normalized-vs-chartAt-pinned-generators (2026-07-12 arm-2 round 6 — route ban, prose; INDEPENDENCE, not falsity — NOT kernel-encodable)
**BANNED route:** any `orient ≡ 1`-normalised statement against `chartAt`-pinned integral local
generators on Mathlib's sphere instance (e.g. the round-5 freeze `Sphere4ChartBallsOriented`, or any
`IntOrientationData` demanding the constant `+1` pinned section). **CHOICE-SENSITIVE:** the pinned
generator at `y` routes through `stereographic' n (-y)` → `OrthonormalBasis.fromOrthogonalSpanSingleton`
→ `stdOrthonormalBasis` = an `irreducible_def` over `Classical.choose` — a per-point arbitrary basis with
NO cross-point interface (verified at pin 4.29.1: PiL2.lean:1063,1148; Instances/Sphere.lean:336-356).
Both coherent and incoherent global sign patterns model Lean's axioms ⟹ the statement is INDEPENDENT —
no discharge can ever land (and no refutation either — hence prose, not registry). The mod-2 tower was
immune (unique generator); this is ℤ-only. **The fix that works (shipped same round):** the
choice-ABSORBING section — define `orient z := iso_z(ρ_z g)` recording the choice pattern, and eliminate
the normalisation binder from the consuming chain (it enters only via `E g = 1`, absorbed by sign
conjugation — the primed chain in `SixteenDvdOrientSectionInt`). See
`SphereFourOrientationDataInt.lean` + the zero-binder firing `SphereWitnessFiringUncondInt`.

## nonhausdorff-bordism-collapse (2026-07-13, arm-2 — KERNEL-REGISTERED same-day; found by Fable, VERIFIED by lead)
- **verdict:** dead (kernel-checked) · **tier:** automatic · **authored_by:** kernel-no-go
- **killed_by:** `SKEFTHawking.NonHausdorffBordismCollapse.bordismGrp_subsingleton` + `bordismGrp_rp4_eq_zero` + `dataBordismGMTied_mk_eq_iff_grade16_eq` (main `9e9ef129`, all `{propext, Classical.choice, Quot.sound}`; found by the wide-latitude Fable `hbound` attack, independently re-verified by the lead via source read + `lean_verify`).
- **The fork:** the in-tree `Bordism` relation (`BordismGroup.lean:37-42`) is a faithful bordism theory usable to state/discharge a completeness/injectivity/bounding Prop.
- **Kernel verdict: NO-GO (DEGENERATE).** `Bordism.W` is required compact/charted/`IsManifold` but **NOT Hausdorff**, so the non-Hausdorff bug-eyed interval `B` (`[0,1]` w/ doubled origin — compact, real-analytic, 3 boundary points) makes `W = s.M × B` an admissible bordism `(s⊔s)⊔s → ∅` for EVERY closed `s`; with the in-tree 2-torsion (`3x=0 ∧ 2x=0 ⟹ x=0`), `BordismGrp X 0 I` is the TRIVIAL group (`[ℝP⁴]=0`, a falsifier — false for genuine unoriented bordism), and `DataBordismGrp mk p = mk q ↔ grade16 equal` (no geometric content). ⇒ `hbound` and every `DataBordismGrp`-quantified Prop is VACUOUS.
- **BLAST RADIUS:** Freeze B `SphereProductBounds := DataBordismGrp.mk ξ R.s2s2 = 0` (grade-0 = FREE) — `trivialSpherePresentation_freezeB` was discharged vacuously (2026-07-13 session); likely also the `omega4PinPlusGMTied_equiv_zmod16` door iso + hg door re-expressions. **NOT vacuous (genuine, stands):** E1 integral topology, the K3 LATTICE (`k3Form`), E2 Rokhlin algebra, the D³/S²×D³ manifold atlas, the Milnor–Husemoller lattice lemmas.
- **THE FIX (shipped `T2TangentialBordism.lean` + lead-re-verified):** require `[t2W : T2Space W]`; honest relation `IsT2DataBordant`, carrier `pinPlusGMTiedT2Data`, `abkGMTied16T2_surjective` **NON-vacuous** (surjects onto `ZMod 16` via `ℝP⁴→odd` — INCOMPATIBLE with collapse; lead re-verified `{propext, Classical.choice, Quot.sound}`). Real keystone re-anchors to `hboundT2 : ∀ x, abkGMTied16T2 x = 0 → x = 0` (OPEN, binder, no axiom) — `omega4PinPlusGMTiedT2_equiv_zmod16_of_grade0_bounds`.
- **⚠ DEEPER (prose, not kernel-encodable):** even T2 at `k=0` is TOPOLOGICAL bordism (KS classes break ℤ/16 — the E₈-manifold has a grade-0 tied structure but doesn't bound TOP). Literature-grade `Ω₄^{Pin⁺}≅ℤ/16` is the **SMOOTH** group ⟹ the genuine target needs the SMOOTH (`k=∞`) + T2 carrier. Endorsed route = the from-below `Ω₄^{Spin}≅ℤ` surgery (fork `5qH-injectivity-routes-...` UPDATE 2026-07-06b) on Mathlib's `SingularManifold` scaffolding.
- **DO NOT** state any completeness/injectivity/bounding Prop over the T2-less `Bordism`/`DataBordismGrp` relation — it is vacuous. Use the T2 (and ultimately smooth) carrier.
- **memory:** `[[project_5qH_nonhausdorff_substrate_bug]]` · **created_ts:** 2026-07-13

## comp-twist-doubling-incompatible
- verdict: dead
- tier: agent-reviewed
- authored_by: kernel-no-go (Fable vacuity attack, W-A definition gate)
- killed_by: kernel-checked `PinPlusCompTorsorNoGo.no_comp_twist_of_doubling_rigid` (+ `not_doubling_rigid_of_comp_twist`, `no_uniform_comp_twist_of_cylinder_rigid`)
- reason: an H¹-coordinate `comp` field with reversal twist `comp ↦ comp + w₁`, anchored by a restriction-compatibility Bor, is JOINTLY UNINSTANTIABLE with the TangentialData ops — `negBor` on the doubling cylinder forces the end-comps equal (both inclusions homotopic), and the uniformly-twisted variant dies on `cylBor`. Any v2 twist datum must evade these theorems' hypotheses (per-boundary-component collar/co-orientation + w₁(W)-corrected compat), or the comp field must be dropped (KT §5 carries the odd bit in the w₁-dual 3-manifold V / ψ, not an H¹ coordinate).
- memory: [[project_5qH_nonhausdorff_substrate_bug]]
- created_ts: 2026-07-13T00:00:00Z
- reviewed_ts: 2026-07-13T00:00:00Z

## membrane-level-nonhausdorff-collapse
- verdict: dead
- tier: agent-reviewed
- authored_by: kernel-no-go (Fable vacuity attack, W-A definition gate)
- killed_by: kernel-checked `PinPlusCompTorsorNoGo.qLevelTripleMembrane_not_t2`
- reason: the bug-eyed collapse is DIMENSION-GENERIC — a T2-less manifold-typed witness datum inside a carrier/relation (membrane Q, surface Σ, any auxiliary manifold field) admits compact non-Hausdorff instances (`qLevelTripleMembrane`: three boundary copies of Σ), making Taylor-Thm-1.1-style extension conditions toothless and breaking bordism-invariance of computed invariants. RULE: every manifold-typed datum carries its OWN T2 + compactness + charted certificate; the ambient W-level T2 fence does not propagate.
- memory: [[project_5qH_nonhausdorff_substrate_bug]]
- created_ts: 2026-07-13T00:00:00Z
- reviewed_ts: 2026-07-13T00:00:00Z

## taylor-leg-end-convention-trap
- verdict: dead
- tier: agent-reviewed
- authored_by: kernel-no-go (Fable re-gate round 2, W-A definition gate)
- killed_by: kernel-checked `PinPlusTaylorConventionNoGo.no_plain_end_pairing_of_cylinder` (+ `not_cylinder_plain_pairing_of_odd_value`, `not_cylinder_bor_of_invariant_ne`)
- reason: two of the three readings of the Taylor extension leg die through the HONEST T2 cylinder — plain-joint-sum forces 2q=0 on the anti-diagonal (kills odd enhancements; cylBor totality fails on the ℝP² witness), σ-side-only is vacuous on cylinders (Bor relates arbitrary structures; Brown/abk8 ill-defined). The correct form negates the τ-END: q_σ ⊕ (neg q_τ) vanishes on ker(H₁(∂Q)→H₁(Q)). Self-tests on negBor alone CANNOT discriminate the readings (both doubling copies sit on one end) — cylBor is the discriminating op; test extension conditions against cylBor first.
- memory: [[project_5qH_nonhausdorff_substrate_bug]]
- created_ts: 2026-07-13T00:00:00Z
- reviewed_ts: 2026-07-13T00:00:00Z

## free-membrane-kernel-kills-nonsplit
- verdict: dead
- tier: agent-reviewed
- authored_by: kernel-no-go (Fable vacuity gate round 3, W-D)
- killed_by: kernel-checked `PinPlusKTVacuityGateWD.ktKernelRep_eq_zero` (+ `ktNonSplit_false`, `kt_binders_unsatisfiable`)
- reason: with the membrane kernel L a FREE field (geometric Q deferred), the un-reversed double σ⊔σ bounds the plain doubling cylinder for any metabolic Lagrangian of q⊕q (brown ∈ {0,4}); the e₈-graph Lagrangian kills 8•[ℝP⁴] for every provider — the KT non-split bit is FALSE on the as-built carrier and the W-D binder pair is jointly unsatisfiable. Round-3 of the deferred-tie pattern. FIX: Bor carries the certified membrane with L computed (the frozen v4 item-2/3 spec); acceptance = the honest anti-diagonal cylinder kernel excludes the e₈ graph. Never open discharge waves against binders whose carrier ties are deferred.
- memory: [[project_5qH_nonhausdorff_substrate_bug]]
- created_ts: 2026-07-13T00:00:00Z
- reviewed_ts: 2026-07-13T00:00:00Z

## capstone-binary-partition-detection-uninhabitable (2026-07-16, arm: close-out)
- kind: route ban (kernel-encodable core deferred — needs the boundary-face local-homology lemma formalized first; see NOTE)
- banned: inhabiting `CapstoneRelFundPartitionDatum` / driving the connected capstone's `hasClass` through ANY binary complementary set partition {U, Uᶜ} (`capstone_hasClass_of_partition` consumption on the CONNECTED trace).
- killed_by: the #156 wall analysis (structural, not proof-difficulty): at a seam point x (healed W-interior, `boundary_weldedInterval`), the closed piece's summand restricts through H₅(sub U, sub U∖{x'}) at a BOUNDARY-FACE point of the manifold-with-boundary sub U ≅ M×I — which vanishes in every degree — so `restrictBd β x = 0 ≠ (gen x hx).symm 1` for EVERY αU. Symmetric under swapping which piece is closed. General: any binary complementary partition of a CONNECTED W has a closed piece whose frontier contains W-interior points; detection fails there.
- scope: the partition/clopen-split engines (`hasRelFundClass_of_partition`, `_clopen_split`, `_finite_clopen_partition`) remain VALID for their disconnected-cylinder uses (clopen pieces, no interior frontier) — the ban is ONLY their application to the connected capstone.
- fix (the live route): genuine RELATIVE COVER-MV GLUING — W = A ∪ B open (A = cyl∪collar, B = handle∪collar, A∩B ≃ the collar; the seam interior to BOTH), per-piece classes agreeing on the overlap, glued via the relative cover-MV sum-exactness H₅(A,S∩A) ⊕ H₅(B,S∩B) → H₅(W,S) → H₄(A∩B,…) — which is NOT yet in-tree (SingularRelativeMV has only the deleted-variable triad). Fable-scale construction; dispatched as the follow-up.
- banked: `SingularRelativeDisjointUnionDetectInterior.lean` (interior-point detection for closed pieces — pins the failure to exactly the frontier).
- NOTE (encode-on-settle): the kernel-encodable core = "boundary-face local homology vanishes ⟹ hdetU(seam) false"; formalizing the boundary-local-homology lemma is itself a task — when it lands, promote this ban to KERNEL_NOGO_REGISTRY.
- memory: [[project_5qH_nonhausdorff_substrate_bug]]
- created_ts: 2026-07-16T00:00:00Z
- reviewed_ts: 2026-07-16T00:00:00Z

## capstone-pair-class-sum-routes-uninhabitable (2026-07-16, arm: close-out — the #159 refinement of the binary-partition ban)
- kind: route ban refinement (same genus as capstone-binary-partition-detection-uninhabitable)
- banned: ANY route of the shape "sum of excisionMap-pushforwards of per-piece PAIR classes" for the connected capstone's [W,∂W] — closed pieces (H₅ rel a PROPER part of the piece boundary vanishes — the seam face is missing) AND open pieces (compact chain support ⟹ no class detects everywhere on a noncompact piece), with any multiplicity bookkeeping. Also explains the 3-open-set double-count probe's failure (dead for a second, independent reason).
- fix (REALIZED, in-tree): the CHAIN-LEVEL gluing — RelCoverGlueData (SingularRelativeCoverMV.lean): core-supported chains whose seam boundary terms cancel mod 2 IN THE SUM; hasRelFundClass_of_glueData + the core detections (SingularSurgeryCoreDetect.lean). Categorically distinct from the banned shapes: detection is never demanded at a closed piece's frontier.
- memory: [[project_5qH_nonhausdorff_substrate_bug]]
- created_ts: 2026-07-16T00:00:00Z
- reviewed_ts: 2026-07-16T00:00:00Z

## capstone-choose-representative-corrector-uninhabitable (2026-07-16, arm: close-out — #178 architecture verdict)
- kind: architecture verdict (prose — unprovable-not-refutable, hence NOT kernel-encodable)
- banned: inhabiting the corrector against the OPAQUE .choose-based capstoneCylChain (the fixed-representative hasClass_ofCorrector entry): its top face is an uncontrolled artifact — no constructible disk chain can cancel it simplex-wise; corrector facts (1)+(2) jointly force the literal mod-2 seam-face cancellation, unreachable for opaque representatives.
- fix (REALIZED): route (iii) — the CONTROLLED cylinder representative (the named crossChain z prism chain; PinPlusTraceCapstoneSeamTransfer.lean) + the transfer datum (the top-face/disk-boundary splits + the literal shared-face transfer) ⟹ hbd CONSTRUCTED (hbd_ofTransfer); hasClass = {z, the disk triple, the transfer datum, hdetAB} (hasClass_ofTransfer(Corrector)).
- memory: [[project_5qH_nonhausdorff_substrate_bug]]
- created_ts: 2026-07-16T00:00:00Z
- reviewed_ts: 2026-07-16T00:00:00Z

## freeze-atoms-not-composable-from-sigma-trace (2026-07-16, arm: close-out — #200 triage verdict)
- kind: compositional gap (prose — a true non-implication established by proof inspection, NOT a false statement, hence NOT kernel-encodable)
- banned: re-attempting "HandleTradeCobordism / HyperbolicBase / the S²×S² bounding bordism compose from the landed Lane-B surgery trace." They do NOT: Lane B (AmbientSurgeryDatum / PinPlusKTSurgeryTrace) performs ambient surgery on the characteristic surface Σ — the ENHANCEMENT-rank axis (p.2.n, drops by exactly 2, ambientSurgeryDatum_pos_rank forces 0 < n) — while the Freeze-A/B atoms are E1 INTERSECTION-FORM b₂-axis surgery (trading a hyperbolic pair H for [S²×S²] on the 4-manifold's 2-cycles). Orthogonal geometric axes; handleTradeCobordism_residual_is_traceBor is rfl-documentation (names the residual, constructs nothing). Also: RankZeroCollapseDatum (#199) shares NO bounding-datum core with HyperbolicBase (different carrier / different rank notion / different target) — do not wire one from the other's Prop-shape.
- the honest floor (recorded #200): the phase's E1 geometric leaves terminate at exactly three manifold-surgery primitives a future E1 foundation must build — (1) one raw handle-trade cobordism, (2) one rank-0 nullbordism, (3) one S²×S² bounding bordism (S²×S² = ∂(S²×D³); the frozen SphereDiskSmoothData package needs the concrete slot + Dⁿ-instance/change-of-model transport) — all consumed at terminal grain by kt_equiv_zmod16_of_residuals_freezeAtoms.
- memory: [[project_5qH_nonhausdorff_substrate_bug]]
- created_ts: 2026-07-16T00:00:00Z
- reviewed_ts: 2026-07-16T00:00:00Z

## hBbord-reduced-to-coboundary-wadm (2026-07-16, arm: close-out — #203 maximal reduction)
- kind: missing-construction isolation (prose — a gap, not a refutation; NOT kernel-encodable)
- record: hBbord (the S²×S² bounding bordism on the spin carrier) is NOT dischargeable outright in current in-tree machinery — but the #200 framing ("gated behind the Mathlib-absent closed-ball atlas") is SUPERSEDED: the closed-ball Dⁿ IsManifold + J5 change-of-model transport are BANKED (SphereDiskFreezeB/J5), and the entire membrane/Taylor-leg/Lagrangian/tether apparatus COLLAPSES on spinEmptyData by construction (Σ=∅; the #171 empty-source machinery). The kernel-pure reduction isDataBordant_empty_of_wadm strips hBbord to THE SOLE NAMED ATOM `SphereProdCoboundaryWAdm prov p` = ∃ a T2 S²×D³-type coboundary b with Nonempty (WAdmPinned b) — the substrate-pinned Lefschetz–Wu w₂=0 tower on the 5-manifold-with-boundary (rel-PD + Steenrod; the op-provider supplies WAdmPinned only for the cylinder/doubling/mapCylinder/add family). Do NOT re-attempt hBbord through the membrane/atlas layers — they are done; the ONLY remaining content is the coboundary WAdmPinned.
- consumed by: kt_equiv_zmod16_of_residuals_freezeAtoms_ofCoboundary (PinPlusKTSphereProdBordism.lean).
- SHARPENED (#206, PinPlusKTSphereProdWAdm.lean): the coboundary WAdmPinned residual is now exactly {a T2 coboundary b · RelFundClassDatum D ([W,∂W] ∈ H₅) · Subsingleton H¹(W;ℤ/2) · Subsingleton H⁴(W,∂W;ℤ/2) · the pinned (2,3) datum P23 (H²(W)≅H³(W,∂W) perfect cup pairing) · wuClass P23 = 0}. The (1,4) Wu leg is SETTLED-FREE (vacuous via the subsingletons — degenerateP14); hwu ⟺ v₂ = 0. Consumed by kt_equiv_zmod16_of_residuals_freezeAtoms_ofDegenerate14. Do not re-derive the (1,4) leg.
- memory: [[project_5qH_nonhausdorff_substrate_bug]]
- created_ts: 2026-07-16T00:00:00Z
- reviewed_ts: 2026-07-16T00:00:00Z

## seam-transfer-open-support-uninhabitable — THE #210 ADJUDICATION (2026-07-17, lead-direct; SUPERSEDES the three "machinery gap" verdicts)
- kind: kernel refutation (fork 22, KERNEL_NOGO_REGISTRY; backings in PinPlusTraceSeamTransferNoGo.lean)
- SUPERSEDES: the #198/#204/#207 prose verdicts "the closed-S support barrier is NOT kernel-false — a machinery gap; it holds for a genuine surgery collar." That intuition was WRONG for the as-shipped shape: htransfer + open-complement hwOut force BOTH top-face split pieces to be CYCLES (seam-supported + off-seam-supported), and a fundamental class cannot so decompose when the regions are H₄-null. The CapstoneSeamTransfer/Seam route to hasClass is dead AS SHIPPED — do NOT re-attempt cSeam construction against the open-support shape at any depth.
- THE REPAIR ANALYSIS (the #210 design record — read before building the replacement):
  1. The naive interior-repair (hwOut over `topface ∖ interior(range φ)`) escapes the refutation BUT is NOT engine-compatible: the #189 subdivision engine's attached piece lands in an OPEN U₁ ⊇ A (spills outside A), while htransfer still forces wAtt ⊆ A exactly.
  2. THE ENGINE-COMPATIBLE SHAPE = the COLLAR-PAIR split: a shrunk closed core K ⊂ int(A); wAtt supported in the CLOSED A (delivered by U₁ := int A — int A ⊆ A, no spill), wOut supported in topface ∖ K (delivered by U₂ := topface ∖ K). The forcing then only pins ∂wAtt = ∂wOut into the collar annulus A ∖ K — no contradiction. #198's exact-hvOut machinery serves the sphere side unchanged (sphere∖S ⊆ sphere∖K').
  3. BUT the collar-pair split alone does NOT restore hbd: ∂(glued) ∈ C(∂W) needs the literal seam cancellation which fails for independent chains — the honest entry is the CORRECTOR (`hasClass_ofTransferCorrector`, #178's crossChain/MV-partition machinery): the corrector p absorbs the seam mismatch; the collar-pair splits feed hagree/hpS.
  4. Any replacement structure is a NEW consumption shape — GATE-PENDING before consumption (rounds 11–13 discipline; the #204 anti-fakes must transfer: a genuine attachment must force nonzero seam content).
- consumed by: nothing (the dead shape's consumers hasClass_ofTransfer/hbd_ofTransfer remain TRUE but vacuous on genuine inputs; no soundness issue — the T-input is simply unsuppliable).
- memory: [[project_5qH_nonhausdorff_substrate_bug]]
- created_ts: 2026-07-17T00:00:00Z
- reviewed_ts: 2026-07-17T00:00:00Z

## sigma-tower-inhabitation-adds-no-strength (backed by REGISTERED kernel no-gos) — don't invest #209 for row closure (2026-07-17, lead — TWICE-CORRECTED after operator skepticism; see the ⚠ block)
- verdict: effort-caution / route-guidance (genuine σ-tower inhabitation adds ZERO statement strength for the row; NOT falsity, NOT "orphaned/dead code"). The KERNEL fact (carrier fakeable) is REGISTERED (below); this prose entry is only the downstream route consequence.
- tier: agent-reviewed
- authored_by: lead (post-compact code trace + registry verification at `936de9ca`)
- killed_by (REGISTERED kernel no-gos — NOT a fresh lead observation): the fakeability is the registered fork **`novikov-geometric-tower-carrier-conclusion-fakeable`** (round 13, `KERNEL_NOGO_REGISTRY`), backed by `PinPlusRoundThirteenGate.{novikovGeometricPairLESDataOfRealPairLES, nonempty_novikovGeometricPairLESData_iff_realPairLES, …_iff_sig_eq, …_diag}` (lean_verify 2026-07-17: axioms `{propext, Classical.choice, Quot.sound}`), + the round-12 sibling **`novikov-substrate-synthetic-inhabitation`** (`PinPlusResidualGate.*`). Both are fence forks; `nogo_substrate_integrity` green. The carrier `NovikovGeometricPairLESData Bd` is populated from a SYNTHETIC `NovikovRealPairLES` with ZERO bordism geometry; the σ-tie gives `Nonempty (…) ↔ σ(A)=σ(B)`.
- ⚠ TWO CORRECTIONS (both my own over-claims, both caught by operator skepticism, same failure mode): (1) my FIRST framing ("ORPHANED — nothing references it — validated") was a grep-scope error — the tower carrier IS referenced by the round-12/13 GATES. (2) My SECOND framing (committed `409ebb37`) called the fakeability "a post-compact lead judgment, NOT a kernel no-go, NOT pre-recorded" — ALSO WRONG, and again asserted without checking the registry: the fakeability IS a REGISTERED kernel no-go (the two forks above) and WAS pre-recorded (rounds 12/13, pre-compact). This PROSE entry is ONLY the downstream ROUTE-GUIDANCE consequence — legitimately prose per encode-on-settle — resting on those REGISTERED kernel forks as its backing.
- reason (corrected):
  Genuine inhabitation of `GenuineBoundingWTower` (via `Bw`/`Br` for the 5-dim W, or the ℝ-Prop reductions) adds NO strength because **round 13 already gate-proved the carrier it feeds is conclusion-fakeable** (a synthetic Lagrangian populates `NovikovGeometricPairLESData` with zero geometry). Separately, the row's actual σ-content does NOT route through the tower: `SpinPresentationRow.hdvd` (Rokhlin `16∣σ`) is a POSITED FIELD (per-carrier residual, the E2 stack), `hker` routes via `KTSharpnessSupply` (`kerPhiSubDoubles_of_row_of_supply`), `hg` via the K3 form. So inhabiting the tower discharges no row atom AND doesn't discharge the posited `hdvd` (that's Rokhlin, not signature-cobordism-invariance). NET: don't spend effort inhabiting the σ-tower for the 16-convergence goal.
  NOT claimed: the tower is "dead code" (it is gate-referenced, round-13-audited infra) or kernel-false. The σ-descent is a TRUE conditional result; it is simply a fakeable carrier that the row closure doesn't need.
- memory: [[project_5qH_nonhausdorff_substrate_bug]]
- created_ts: 2026-07-17T00:00:00Z
- reviewed_ts: 2026-07-17T00:00:00Z

## hBbord-relFund — the cross-of-fundamental-classes KEYSTONE IS BUILT (cylinder); hBbord = a disk-factor ADAPTATION (2026-07-17, lead — CORRECTED, supersedes wt3's "research wall")
- verdict: route-map (hBbord's relFund is a TEMPLATED ADAPTATION of proven machinery, NOT open research; wt3's wall was a scope miss)
- tier: agent-reviewed
- authored_by: lead (deep scope of the cylinder tower at `9f81a5ad`, correcting the earlier over-pessimistic entry + wt3's wall)
- killed_by: `cylFundClassCandidate_restricts_disc` + `hasRelFundClass_cylGen_components` + `cylinderRelFundClassDatum_of_components` (all BUILT, unconditional)
- ⚠ CORRECTION: the earlier read ("hBbord bottoms at an OPEN relative cross-product; research-level") was WRONG — it trusted a STALE cylinder docstring (`PoincareLefschetzRelFundClassCylinder.lean:31` "the exact missing tool is a relative cross-product") and wt3's S²×D³-only scope. The relative-cross-product keystone IS BUILT:
  * `SingularRelativeCrossProduct.crossH : Hₚ(M) → Hₚ₊₁(M×I, ∂)` — the cross MAP (exists).
  * `PoincareLefschetzRelFundClassCylinderCross.cylFundClassCandidate := [M] × [I,∂I]` — the honest product witness.
  * `PinPlusCylComponentClsIdentDisc.cylFundClassCandidate_restricts_disc : RestrictsToRelGen … cylFundClassCandidate` — **the cross of fundamental classes RESTRICTS to the interior local generators** (via `crossHloc_mLocalClass_ne_zero` local-Künneth + `crossHloc_map_naturality`). THE KEYSTONE, PROVEN.
  * `hasRelFundClass_cylGen_components` = the assembled `HasRelFundClass` for the cylinder; `cylinderRelFundClassDatum_of_components` builds the datum UNCONDITIONALLY. **Track 2's cylinder relFund is DONE, not open.**
  * `SingularRelativeHomotopyInvariance` = the mod-2 pair homotopy invariance (piece 2), also BUILT (docstring "only integral in-tree" is stale too).
- THE REAL hBbord GAP: `S²×D³` is NOT a closed-`M`×`I` cylinder (D³≠I; `S²×D³ ≅ cyl(S²×D²)` has a with-BOUNDARY base, so the closed-M cylinder keystone doesn't apply verbatim). hBbord needs the analogous witness `[S²] × [D³, ∂D³]` and its `RestrictsToRelGen` — an ADAPTATION of the proven cylinder template to a DISK factor (cross with D³ not I). The local-Künneth core (`crossHloc_mLocalClass_ne_zero`) is dimension-generic and should transfer; the global cross (`crossH` via `graphHom`/`prismOp` over I) is interval-specific and is the piece to re-build for the disk factor (or a general absolute⊗relative cross `H(M)⊗H(N,∂N)→H(M×N,M×∂N)`). The banked D³/D⁵ relFund (`PinPlusTraceDiskCorePair`) supplies `[D³,∂D³]`.
- BANKED GREEN (reusable): wt1 `sphereProdCoboundaryBordism`; wt2 `Subsingleton (Homology SphereDisk 1/4)` + `SingularProdContractible`; wt3 `sphereDisk_homology_four/five_eq_zero`, `betaClass_ne_zero`, `injective_boundary_to_diskFactorSet`.
- STATUS: task #213 — implementing the disk-factor adaptation (lead, main-line).
- memory: [[project_5qH_nonhausdorff_substrate_bug]]
- created_ts: 2026-07-17T00:00:00Z
- reviewed_ts: 2026-07-17T00:00:00Z

## metric-vs-chart-radius-coverage (2026-07-20, K4′′ packaging — ROUTE FACT, prose-only, not kernel-refutable)
On `TorusFour` with ρ = 1/2 chart-ball excisions, a METRIC-ball interior region (`openPunctured`, metric radius 1/2) does NOT overlap-cover T⁴° with the ROUND chart-radius collar band `[1/2, 3/4)`: a point with all four per-factor chart-coords ≈ 1/2 has metric (sup) distance ≈ 0.495 but round chart-radius ≈ 1.0 — in T⁴°, covered by neither family. Any interior/collar chartAt dispatch on the punctured torus must use the CHART-radius interior region (`KummerBoundaryChart.interiorSet`, round closed balls of chart-radius 5/8, overlap band [1/2, 5/8]; covering = `punctured_covered`). Do not re-introduce the metric-ball interior region in covering arguments. Same lesson applies to any future excision family: keep the interior region and the collar band in the SAME radial coordinate.

## 2026-07-20 · hcolD one-sphere/3-handle route — UNSOUND WITHOUT A FRAMING THEOREM (route caution, prose)

The proposed universal "kill each characteristic 2-sphere by one index-3 D³×D² handle" route for the
rank-0 collapse is NOT available as stated: rank 0 + the carrier's `hchar` tie do NOT force the
sphere's normal Euler number to vanish (`hchar` sees only the mod-2 characteristic class; the oriented
GM congruence `σ ≡ F·F + 2β (mod 16)` constrains only the TOTAL self-intersection, and its transfer
to the nonorientable Pin⁺ carrier is unverified). Any hcolD/SectorIsGeometric construction via a
single-sphere handle MUST carry an explicit framing hypothesis or use the global
characteristic-bordism (KT) route. Source: the 2026-07-20 vetted codex hcolD dossier
(`codex_hcolD_route.md`, risks 2/6), demand-narrowing lead-verified in-tree
(`nonempty_ktSpinPresentationDatum_of_row` consumes only `SectorIsGeometric`;
`kt_equiv_zmod16_of_residuals_sector` now exposes the weakest form).

## 2026-07-21 — K7 seam-cover interior hypothesis (KERNEL no-go) + the δ₁ fence

- **`k7-seam-cover-interior-fails` (KERNEL-REFUTED, registry-backed):** the K7 opener's `K7SeamCoverHyp` (interiors of the un-thickened closed weld pieces cover K3) is FALSE — `k7SeamCoverHyp_false` (KummerK7SeamCoverNoGo). A seam point is interior to neither piece. The UNIQUE route is the collar-thickened cover (`qThick`, `k7_hcov` — discharged). Do not aim any worker at "discharge K7SeamCoverHyp".
- **δ₁ fence (route caution, prose):** in the K7 degree-2 window, the MV connecting map δ₁ over H₁(collar) = (ℤ/2)¹⁶ is GENUINELY NONZERO for the true K3 (the Kummer lattice has 2-power index in H₂). Do NOT dispatch "prove δ₁ = 0" — the correct target is the δ₁-image/extension analysis (the cokernel-exponent-2 window `k7H2_two_smul_mem_range` is the honest bound already landed).

## 2026-07-21 — Gram atoms: a literal matrix EQUALITY is the wrong target (route fact, prose; kernel-CHARACTERIZED)

**`SphereProdGramPin` is RETIRED, not proved — and it is independent of the in-tree data, not merely
unproven.** The abbrev asks for the literal `interMatrix fc B = sphereProdFormDatum` on the computed
basis. The exact computed-basis Gram is now kernel-checked
(`SphereProdGramPinRetire.sphereProd_interMatrix_computed_eq`):

    interMatrix fc sphereProdIntH2Basis = !![-(2·s·u·ε), u·ε; u·ε, 0]

with `s = (sphereProdCohomTwoEquivInt (alphaOf xS)).2`, `u = topSphereIsoInt 1 deltaSnd`, `ε` the E–Z
cross value. Hence (`sphereProdGramPin_iff`) the pin holds **iff `s = 0 ∧ u·ε = 1`**, and BOTH conjuncts
are unavailable:

1. **`s = 0` is CHOICE-DEPENDENT — the stronger obstruction.** `deltaGen` is an `Exists.choose` section
   pinned only modulo `sumInto`, and `fst_* sumInto ≠ 0` (`sumInto_prodFst`). Replacing
   `deltaGen ↦ deltaGen + k·sumInto 1` shifts `s` by `k` and the (0,0) entry by `−2kuε`. So the pin is
   **independent of the in-tree data**. Note this kills the old hope that normalizing the cross value to
   literally `1` would suffice — even a normalized `ε` leaves the diagonal free.
2. **`u·ε = 1`** — the orientation/sign gap; both are pinned only as units.

**The content the pin stood in for IS in tree and unconditional:**
`SphereProdBasisIdInt.sphereProd_interMatrix_intCongr_hyp` proves `II(S²×S²) ≅ Hyp` *itself* — sharp,
no hypotheses — via the MV cup–Stokes peel (`SphereProdHemiUnitInt.hcross_pm`) plus the basis-ID
(`crossFamily_basis_intCongr`). Every consumer's conclusion is **congruence-invariant**
(`∃ N, IsHyperbolicForm N ∧ IntCongr M N` by transitivity; `IsEvenUnimodular` via the pre-existing
`IntCongr.isEvenUnimodular`; likewise `latticeSig` and the `2 ∣ σ/8` binder), so the congruence
supersedes the equality. Hypothesis-free replacements:
`SphereProdGramPinRetire.sphereProd_s2s2_{hyp,evenUnimodular,latticeSig,htopo}'`.

**THE GENERAL RULE (applies to every future Gram atom, incl. the K3/T⁴ one):** state Gram targets as
`IntCongr … <form>`, never as a literal matrix equality on a chosen basis. The extra content of an
equality over a congruence is basis normalization, not geometry, and it is generically unreachable
whenever any basis vector comes from a choice. `KummerK3Base` §K8 already targets `IntCongr … k3Form`
— that is the correct shape; keep it. Do not dispatch a worker at "prove the literal Gram equality".

---

## k6b-seam-chart-stays-on-RP3-x-interval — ROUTE DECISION (2026-07-21, lead)

**Not a no-go — a settled architecture choice. Do not re-litigate; do not silently refactor.**

The wt2 worker that closed transition classes (3,3) and (2,1) surfaced, without acting on it, an
architectural option for the K6′b weld atlas: rebuild the **seam chart** on *E-fiber `w`-coordinates*
with `‖w‖ ∈ (1/2, 9/8)` (E half `‖w‖ ≤ 1`, Q half above), instead of the current
`ℝP³ × (−1/8, 1/2)` presentation. The payoff is real: class **(1,3) would become definitionally
trivial** (identical coordinates to the E-interior charts), leaving only the Q-side gluing as
genuine work — one hard transition class instead of two.

**DECISION: keep the `ℝP³ × interval` architecture. Finish the mechanical descent.** Reasons:

1. **The current route is unblocked.** The worker's own words: "No obstruction encountered — just
   unbuilt." The hard analytic kernel is already built and kernel-pure — `contDiffOn_seamSection0`
   (`KummerSeamSection.lean:124`), `bdryMap_seamPoint0` (:151), resting on `phaseSqrt_sq` (:38) —
   a smooth local right inverse of the chart-0 boundary map. What remains for (1,3)/(2,3) is the
   chart-1 and annulus analogues plus descent through `mkRP3` into `rp3Chart` (composable with
   `contDiffOn_reprStereo`): **bulk, not depth.**
2. **The refactor would invalidate banked, just-landed work.** `seamCompNbhd`, the openness/covering
   arguments behind it, `isOpen_cover_three_families`, and `disjoint_seamCompNbhd` — the last of
   which was *proved in the same block that proposed the refactor*. Trading finished mechanical work
   for re-derivation of landed results is the wrong direction of risk.
3. **Both routes reach the identical theorem** (`IsManifold (𝓡 4) KummerK3`), so correctness does not
   discriminate; the tiebreak is risk, and the refactor carries strictly more.

**If the mechanical descent turns out to hide a real obstruction** (as opposed to bulk), that is new
information and this decision should be revisited *at that point* — reopen it with the obstruction
named, not on the general appeal of fewer hard classes. Until then, a worker that proposes the
`w`-coordinate rebuild should be pointed here.

---

## k7-b2-single-threshold-excision-corner — ROUTE FACT (2026-07-21, prose by design)

**Not a no-go, and deliberately NOT a `KERNEL_NOGO_REGISTRY` entry.** The wt3 worker that proved
(C0) outright identified this and correctly declined to propose a registry entry: it says one
*excision hypothesis is unavailable*, not that a *statement is false*. Registry entries are for
provably-false statements with a refutation/forcing theorem; this is a route constraint. Prose is
the right home. (The discrimination itself is worth copying — not every settled obstacle is
kernel-encodable, and mis-filing a route fact as a refutation inflates the negative frontier.)

**The fact.** In the `b₂ = 22` chart-1 excision, excising `H₂(splitBOpen r, outerE; ℤ)` down to the
chart-1 pair with a **single** threshold **fails**: the corner where `‖base‖ = r` meets
`fiberNorm = 1/2` is not interior to `outerE` inside `splitBOpen r`, so the excision hypothesis
cannot be met.

**The fix, now kernel-checked** (`KummerSplitBChart1ExcisionInt.splitBOpen_chart1_cover` :124, with
the forcing step `openBaseE_inter_splitBOpen_subset` :97): use **two thresholds `r' < r`**. Retain
`chartNbhd1 r' ∩ splitBOpen r` — ⚠ note `chartNbhd1 r' ⊄ splitBOpen r`, so the intersection is
required; the earlier prose formulation that retained `chartNbhd1 r'` alone was imprecise. The
load-bearing set identity is `splitBOpen r ∖ chartNbhd1 r' = outerE ∩ deepChart0 r'`, every point of
which has an open neighbourhood meeting `splitBOpen r` only inside `outerE`. Corner gone.

**Housekeeping debt this created:** `KummerSplitBCoreVanishInt` now supersedes part of
`KummerChartNbhdInt` — `relHomologyInt_splitBOpen_eq_zero_of_chart0` and `outerECyclic_of_chart_local`
are dead weight (harmless, still green, still building). Prune when the b₂ lane closes, not before —
they are cheap to keep and removing them mid-lane risks churn.

---

## collar-pair-surgered-end-range-has-no-degrees-of-freedom — ROUTE FACT (2026-07-21, prose by design)

**Not a no-go — a statement that a *hypothesis is unavailable*, not that a statement is false. Prose
is the right home** (same discrimination as `k7-b2-single-threshold-excision-corner`).

`SurgeredEndDatum.bdry` is an **equality**, so `range eM' = ∂W ∖ range ktSourceEnd` exactly — there is
no slack in it. `bd_datum_indep` shows `∂W` is `rfl`-equal across data, hence `range_eM'_datum_indep`
and `seamPreimage_datum_indep`: **all `SurgeredEndDatum`s have the SAME `eM'` range**, and the
residual holds for one iff it holds for all.

**Consequence — never dispatch this:** "construct a `SurgeredEndDatum` whose `eM'` covers the seam
annulus." There is nothing to construct; the datum has no degrees of freedom here. The residual's
truth is a fact about the chart-determined `∂W` (boundary-floor territory), not about datum choice.

---

## collar-pair-coarse-core-does-not-relax-the-disk-side — ROUTE FACT (2026-07-21, prose by design)

**Not a no-go.** Records a *failed relaxation attempt*, so that it is not re-attempted.

The End row's `houtH` support is `sphere ∖ ↑''seamCore`, which is **weaker** than `sphere ∖ S`
(`seamCore ⊆ S`), and it is tempting to read that extra room as relaxing the disk side. It does not.
The extra room lies **inside `S`**, whereas the closed-`S` barrier concerns simplices in `U ∖ S` —
**outside** `S`. Room inside `S` cannot host a simplex outside it.

**Scope: this does not close `hctrlH`.** (What *does* close it is unrelated — see the entry below:
the row's remainder is demanded off the builder-chosen core `K`, and that is a genuinely different,
*open*-complement condition, not a coarsening of the closed-`S` one.)

Also settled in the same lane, and equally not to be retried:
* the **representative-subdivision dodge** does not reach `hctrlH`. At `μ = 0` the cylinder side
  loses nothing (one subdivides the *representative*), but the disk side does — `diskDetectChain` is
  fixed.

---

## collar-pair-closed-seam-attached-collar-bridge-is-FALSE — KERNEL NO-GO (2026-07-21)

⚠ **Kernel-checkable — this entry is a POINTER. The registry is the home of record**
(`KERNEL_NOGO_REGISTRY` in `src/core/constants.py`, filed by the atlas/registry owner). Recorded here
only because the fork was settled in the collar-pair lane and readers arrive here first.

**Refutation theorem:** `SKEFTHawking.PinPlusTraceSeamCollarBridgeNoGo.collar_bridge_refuted`
(`lean/SKEFTHawking/PinPlusTraceSeamCollarBridgeNoGo.lean`), kernel-pure
`{propext, Classical.choice, Quot.sound}`.

**False statement:** `PinPlusTraceSeamResidualNarrow.ClosedSeamAttachedCollarBridge S a` — for a
closed seam `S ⊆ D⁵` and an attached chain `a` supported in an open neighbourhood's sphere-part,
`∃ cSeam corr, a = mapChain (ambIncl S) cSeam + corr ∧ corr ∈ subspaceChains (sphere ∖ S)`.

**Why it is false.** `attachedBridge_iff_support_dichotomy` (same module) shows the atom is EXACTLY
"no support simplex of `a` straddles `S`" — a purely combinatorial condition on the free `ℤ/2`-module
basis, with **no collar content whatsoever**. The "collar deformation-retraction" reading in
`PinPlusTraceSeamResidualNarrow` §3 is wrong: a retraction gives homotopy/homology invariance, never
the chain-level EQUALITY the atom demands. `collar_bridge_refuted` then exhibits a closed nonempty
`S = {e₀} ⊆ sphere`, `U = univ` (satisfying the engine's own cover hypothesis
`sphere ⊆ U ∪ Sᶜ` verbatim), and a single great-circle 4-simplex chain running from `e₀` into the
sphere, for which the atom fails.

**Do NOT re-attempt** any of: a collar retraction supplying it; a homotopy/prism argument; more
subdivision (the atom carries no subdivision hypothesis, and the engine's `a` is post-subdivision by
construction). No proof can exist at the stated generality.

**Scope — this kills the ATOM, not the collar-pair row.** `CollarPairBuild.hctrlH`/`houtH` never
asked for the `sphere ∖ S` support; they ask for `sphere ∖ (Subtype.val '' K)`, off the
*builder-chosen shrunk closed core* `K ⊂ int A` — an **open** complement, exactly the open-cover
engine's granularity. That pair is now SUPPLIED, bridge-free:
`PinPlusTraceCapstoneCollarPairHandle.exists_ctrlHandle_split_offCore`. The bridge was a needlessly
strong reduction of `#212 item d`, not the row's actual obligation.

---

## `collar-pair-cCore-co-adaptation-is-not-on-the-hasClass-path` (route fact — CLOSED, lead-traced 2026-07-21)

**Do NOT build the shared-`cCore` co-adaptation.** The `codex_212_collarpair_design.md` dossier sizes
it at 450–800 LOC and calls it the hardest item ("Opus, hardest"); the bridge-free `hctrlH` producer
left its residue apparently sitting on `hctrlC`. It is not an obligation of the `#212` row.

**Traced in the Lean by the lead** (not taken from a worker report):
`PinPlusTraceCapstoneCollarPairMatch.lean` gives the full chain to the capstone —
`CollarPairGeomEnd`(4 obligations) → `CollarPairSeamRow`(3) → `CollarPairCoreRow`(2) → `hasClass` —
with `CollarPairSeamRow.toHasClass` (:336, via `toCorrectorT`) and `CollarPairCoreRow.toHasClass`
(:609, firing `capstone_hasClass_ofCoreChains` directly) both producing the EXACT
`CapstoneAmbientSupply.hasClass` field type that `CollarPairGeomEnd.toHasClass`
(`PinPlusTraceCapstoneCollarPairEnd.lean:419`) produced before. **No link in that chain mentions the
co-adaptation.** The live floor is `CollarPairCoreRow`'s `hbd` + `hdetAB` at the canonical
`cHa := diskDetectChain` (where `hcHa`/`hdetHa` are discharged by banked `diskDetectChain_hc`/`_hdet`).

**Scope.** This kills the *co-adaptation build*, not the row. Also note the anti-fake guard survives
as a theorem, `CollarPairCoreRow.qGen_ne_zero_of_seamCore_nonempty` — a consequence of the two
obligations under nonempty `seamCore`, not an added assumption. An inhabiter is still well advised to
carry `hseamHit`: `seamMatch_mem_of_seamCore_empty` shows the *seam-row* obligation is free at
`seamCore = ∅` (that configuration is exactly what `hseamHit` excludes).

**Tooling note that produced a false alarm here:** `lean_local_search "CollarPairCoreRow"` returns the
structure ONLY — it does not surface namespaced members like `.toHasClass`. Do not read a one-hit
`lean_local_search` as a reference check; use `lean_references` or read the module.

---

## `kummer-16-plus-6-geometric-block-is-not-a-basis` (route fact — planning, lead-traced 2026-07-21)

**A K3 Gram plan of the shape "tabulate the 16 exceptional + 6 descended-torus classes and stop" cannot
work.** Those 22 classes span a PROPER finite-index sublattice of `H₂(K3;ℤ)`; the Kummer half-sums are
mandatory. Elementary reason, self-contained: their Gram has `|det| ≠ 1`, while `H₂(K3;ℤ)` is unimodular
of rank 22 (`k3Form_isEvenUnimodular`, transported by `IntCongr.isEvenUnimodular`).

⚠ **NUMERICAL CORRECTION 2026-07-28 (lead-verified at page level against the primary — the earlier
numbers here were WRONG).** This entry used to say the Gram is `⟨−2⟩¹⁶ ⊕ 3H` with `|det| = 2¹⁶` and
index `2⁸`. The **descended** torus block is *scaled by 2*: `π : Ã → Km(A)` is a degree-2 quotient and
`ι*` is the identity on `H²(A;ℤ)`, so `π_*` doubles the form. Verbatim, Garbagnati–Sarti
(arXiv:1305.3514) **Lemma 2.5, p. 5**: *"π_{A*}(U^{⊕3}) = π_{A*}(H²(A,ℤ)^{ι*}) = H²(A,ℤ)^{ι*}(2) =
U^{⊕3}(2)"*; and immediately after it, **p. 5**: *"The lattice U(2)^{⊕3} ⊕ ⟨−2⟩^{⊕16} has index 2¹¹ in
Λ_{K3} ≃ U^{⊕3} ⊕ E₈(−1)^{⊕2}."* So:

| quantity | correct value |
|---|---|
| Gram of the 16+6 | `⟨−2⟩¹⁶ ⊕ 3H(2)`, `\|det\| = 2¹⁶·4³ = 2²²` |
| index of their span in `H₂(K3;ℤ)` | **`2¹¹`** (= `2⁵ · 2⁶`), **not `2⁸`** |
| `[K : Π]`, `K` = Kummer lattice | `2⁵` (GS Prop. 2.2, p. 4: `disc K = 2⁶` ⟹ `2¹⁶/2⁶ = 2¹⁰ = (2⁵)²`) |
| `[H₂(K3;ℤ) : K ⊕ π_*H₂(T)]` | `2⁶` (GS Rem. 2.3(4), p. 4: `A_K ≅ (ℤ/2)⁶`) |

⚠ Also corrected: the half-sums adjoined to get `K` are indexed by affine **HYPERPLANES** (dim 3, 8
points; GS Rem. 2.3(1), p. 4 — *"there are 30 classes of this kind"*), **not** by affine subspaces of
dimension ≥ 2. The dim-2 half-sums are **not** in `K`: GS Rem. 2.3(7), p. 4 says the six `V_{i,j}`
half-sums *"generate the discriminant group of the Kummer lattice"*, i.e. they live in `K^∨/K`. (This
is Nikulin's even-set theorem: a disjoint set of rational curves that is a double-cover branch locus
has exactly 8 or 16 members.) Corpus note with the full provenance:
`Lit-Search/Phase-5qH/Kummer-lattice-index-and-scaling.md`.

**The fork's CONCLUSION is unaffected** — the 22 classes are still not a basis and the half-sums are
still mandatory. Only the two numbers moved.

**Correct target instead:** choose a cap-dual cohomology family for a genuine rank-22 generating set
(geometric classes **plus** the half-sums), tabulate `⟨·,·⟩` via
`IntersectionMatrixBasisChange.interMatrix_capDual`, exhibit the unimodular congruence to `k3Form`,
then apply `KummerK3E1Package.kummerK3_hk3_of_geometric_basis`. No basis-normalisation obligation on
top, because `interMatrix_intCongr_of_rank_eq` makes the packaged basis's anonymity free.

**Citation correction (lead-traced).** A worker report attributed this to
`KummerPairHalving.pairCokerEquiv` / `pairCoker_card = 2¹⁶`. Those live in
`KummerPairTubeSeparation`, **and they state something else**: `pairCoker_card :
Nat.card (PairH2 ⧸ LinearMap.range pairProj) = 2 ^ 16` is the cokernel of the *relative pair*
`H₂(ESub, CollarInE; ℤ)`, not the index of the 16+6 span inside `H₂(K3;ℤ)`. Do not cite it for this.

**Status: planning fact, NOT kernel-encodable yet.** The determinant argument needs the 16+6 Gram
computed in-tree, which has not been done. Nothing here is a refuted Prop, so there is no
`KERNEL_NOGO_REGISTRY` entry — prose only, by the ADR-007 route-fact/refutation discrimination.

## hker-opener-supplyGeo-is-non-reducing
- `verdict`: `banned`
- `tier`: `agent-reviewed`
- `authored_by`: `kernel-no-go`
- **⬆ UPGRADED 2026-07-27 (operator catch): this is now KERNEL-ENCODED, not prose-only.** Registry fork
  `hker-opener-supplyGeo-is-non-reducing`, backing
  `SKEFTHawking.PinPlusKTHkerAmbPinGate.nonempty_ktSharpnessSupplyGeo_iff_hfwd`
  (`Nonempty (KTSharpnessSupplyGeo prov R) ↔ hfwd`). The prose below is the operational dispatch ban;
  the FACT is fenced in Lean.
- `killed_by`: lead trace 2026-07-27 against the FROZEN ROUND-12 SPEC item 1
  (`PinPlusResidualGate.lean:107-110`) + kernel fork
  `dual-spin-opened-construction-conclusion-fakeable` (registry #19)
- `reason`: **Do NOT dispatch `hker` as "inhabit `KTSharpnessSupplyGeo` and fire
  `kerPhiSubDoubles_of_row_of_supplyGeo`".** That theorem is TRUE but NON-REDUCING: its input is
  conclusion-strength. `KTSharpnessSupplyGeo.amb : ∀ x, Φ x = 0 → TopCat`
  (`PinPlusKTDualSpinSubmanifold.lean:148`) is a **FREE `TopCat` field** — the docstring says
  "intended value `TopCat.of b.W`", i.e. intent, not enforcement. Round-12 spec 1 binds exactly this:
  a `KTSharpnessSupplyConstr`/`KTSharpnessSupplyGeo` claim is construction progress ONLY IF `amb x hx`
  is the tethered witness's `TopCat.of b.W` and `Vspace`/`ιV`/`edge` are the genuine `w₁(W)`-dual data
  — "**checked by DATA INSPECTION; the statement shape is conclusion-strength (G12-1) and can never
  enforce this**". Kernel backing: `nonempty_dualSpinConstruction_iff_thirtytwo_dvd`,
  `nonempty_ktSharpnessSupplyConstr_iff_hfwd`, `spinOfSigMul16_sig` (the σ-onto engine realizes a
  genuine `SmoothSpinManifold4` for every multiple of 16, so on an unpinned ambient the whole opened
  supply ⟺ the `hfwd` conclusion). **So `hker` is not "unstarted with an opener available" — the
  opener does not open anything.** The real work is (1) an `amb`-PINNED supply shape that makes the
  exploit type-level unavailable rather than leaving it to permanent data inspection, then (2) the
  genuine `w₁(W)`-dual spin submanifold `V ⊂ W` (smooth transversality, Mathlib-absent).
  ⚠ Method note for the lead: a `grep` for consumers of `KTSharpnessSupplyGeo` initially suggested
  "no gate coverage"; that was WRONG — `PinPlusResidualGate.lean:107` names it explicitly. Read the
  gate spec, never grep-conclude coverage (`feedback_no_grep_scoped_directionshift_claims`).
- `memory`: `[[project_5qH_nonhausdorff_substrate_bug]]`
- `created_ts`: 2026-07-27
- `status_update_2026_07_27b`: **The `V` side of item (2)'s prerequisite is now built; items (1) and
  (2) themselves are NOT.** `PinPlusKTDualSpinDerived` (main `c1142672` + `6dc13d7b`) replaces the
  free `SmoothSpinManifold4` lattice with one DERIVED from `Vspace`'s own integral homology
  (`IntOrientation` + `IntH2Basis` + `IntPoincareDuality`), and proves the resulting datum forces
  `|σ(M)| ≤ 2·b₂(V)` on an actual space — so the fork-31 witness class (`PEmpty`/`PUnit` carriers
  with a bolted-on lattice) is kernel-excluded (`derived_excludes_fork31_witness_class`). The
  re-based supply `KTSharpnessSupplyDerived` still carries a FREE `amb : ∀ x hx, TopCat`, so
  **item (1) — the `amb` pin — is untouched and remains owed**, and item (2) — the genuine
  `w₁(W)`-duality certificate — is untouched. ⚠ Do NOT read the derived interface as making the
  lane reducing: whether the derived supply is still equivalent to `hfwd` is OPEN (it turns on the
  missing `w₁` tie), and that openness is deliberately NOT encoded as a no-go — proving it would
  need a realization construction (a closed 4-manifold with an `IntPoincareDuality` datum of every
  signature in `16ℤ`) the project does not have. Prose only; not `KERNEL_NOGO_REGISTRY` (Inv #17).

## `kummer-degree-3-smith-walk-parity-flip` (route caution — LEAD-VERIFIED in the Lean, 2026-07-27)

**Do NOT attempt the degree-3 analogue of the Smith walk that produced `H₂(Q;ℤ) ≅ ℤ⁶`.** It is not
merely unbuilt; the engine's key hypothesis is FALSE one degree up.

- The degree-1/2 walk (`KummerQuotientH2Solve`) runs `inclBH_one_injective` (:102) → `deltaIII 1 = 0`
  (:114) → `projH 2` surjective (:121). Its engine is `X_H1_fixed_eq_zero`: on `H₁(T⁴°;ℤ)` a
  `τ`-FIXED class is zero — i.e. `τ_* = −1`.
- One degree up the parity flips: `τ(x) = −x` on `T⁴` gives `τ_* = (−1)² = +1` on `H₂`. The tree
  encodes exactly this asymmetry — the degree-2 lemma is `X_H2_anti_eq_zero` (ANTI-fixed ⟹ zero,
  used by `projH_two_injective` :127), and there is **no** `X_H2_fixed_eq_zero`, because on `H₂`
  every class is fixed. **Lead-verified by reading both proofs, not by grep.**
- Consequence: `inclBH 2` is not injective by that route, `deltaIII 2` need not vanish, and
  **`projH 3` is not surjective**. Consistent with `two_smul_mem_range_mapInt_qmkC`
  (`KummerK3H3SeamWindow.lean:382`), which gives only `2·Hₙ₊₁(Q;ℤ) ⊆ im p_*` — the doubled classes.
- ⚠ Prose only, NOT `KERNEL_NOGO_REGISTRY`: what is verified is that *this engine* does not lift, not
  that `projH 3` is provably non-surjective as a kernel-checked false statement (Inv #17). Do not
  cite it as a kernel no-go. The wt2 round aborted this route before building on it.

## `thickA-is-not-puncturedTorus` (carrier fact — LEAD-VERIFIED, 2026-07-27)

`thickA` and `puncturedTorus` are **different carriers**, and a prior revision of
`HANDOFF_16_CONVERGENCE.md` conflated them (corrected same day). Verified in the tree:
- `thickA = (⋃ c ∈ fixedSet, halfBall c)ᶜ` — `KummerPunctureBalls.lean:244`, HALF-radius balls
  (`halfBall c = centeredChartParam c '' halfD4o`, :121).
- `puncturedTorus = excisedBallsᶜ` — `KummerPuncturedTorus.lean:432`, FULL-radius balls
  (`chartBall c = centeredChartParam c '' {t | sqNorm t < excisionRadius ^ 2}`, :420).

So `KummerPunctureH3Mod2.thickA_H3_twoTorsionFree` is literally a statement about `thickA`, **not**
syntactically about `PTtop`.

### ⚠ CORRECTION 2026-07-27 (same day) — the second half of this entry was WRONG. Lead error.

The entry originally continued: *"the route to the Q side has TWO gaps (`thickA → PTtop`, then
`PTtop → Q`) … They are very plausibly homotopy equivalent, but that equivalence is NOT in tree —
build it or route around it, do not assume it."* **That is false**, was flagged by the wt2 worker,
and is now **lead-verified in the source**:

`SKEFTHawking.KummerPuncturedMV.puncIncl_mapInt_bijective` (`KummerPuncturedMV.lean:329`; section
header at `:304` reads "`T⁴° ↪ thickA` is a homotopy equivalence") proves
`Function.Bijective (Homology.mapInt puncInclC (n+1))` for **all** `n`. It is **constructed**, not
assumed — from the glued radial deformation retraction `puncFlow` (`puncRetrC :312`,
`thickHtpyC :317`) via `Homology.mapInt_bijective_of_homotopyEquiv`. **Gap 1 was already closed in
tree.** Consequence, now landed as `KummerQuotientH3Descent.punctureH3_twoTorsionFree`:
**`H₃(T⁴°;ℤ)` is 2-torsion-free, UNCONDITIONALLY**, plus the reusable bridge
`punctureThickHEquiv (n) : H_{n+1}(T⁴°;ℤ) ≃ₗ[ℤ] H_{n+1}(thickA;ℤ)`.

**What survives:** the set-distinctness (the two carriers really are different complements) — that
half was verified and is correct, and it does mean the two names are not interchangeable.
**What does not:** there is **ONE** gap to the Q side, not two. It is the descent along the FREE
ℤ/2 quotient `T⁴° → Q`, which remains genuinely open (free quotients CREATE 2-torsion:
H₁(S³)=0 vs H₁(ℝP³)=ℤ/2); the only unconditional covering bridge is
`two_smul_mem_range_mapInt_qmkC`.

**Process note (the lesson, not the fact).** The lead verified the *definitions* (radii differ →
different sets, correct) and then asserted the *consequence* (therefore an open gap) without
checking for a bridge. That is the `feedback_no_grep_scoped_directionshift_claims` failure mode one
level up: checking a definition is not checking the consumers. Before writing "X is not in tree",
search for the bridge (`lean_local_search` on the map/iso name), not just the two objects.

## `kummer-h3-even-descent-is-non-reducing-and-likely-false` (2026-07-27, arm: orientInput)
- `kind`: route ban — **two independent reasons**, one unconditional and one conditional.
- `banned`: consuming the EVEN descent form `(ED) : im p_* ⊆ 2·im qSeamCoord3` as an input to
  `orientInput`. Do NOT dispatch "prove even descent".
- **REASON 1 (unconditional, and the decisive one): it is NON-REDUCING.**
  `KummerQuotientH3EvenDescent.evenTwoSaturated_iff_surjective` — modulo 2-torsion-freeness of
  `H₃(Q;ℤ)`, the even-saturation the criterion actually consumes is **equivalent to
  `Function.Surjective qSeamCoord3`**, i.e. to its own conclusion. Same shape as fork 32
  (`hker-opener-supplyGeo-is-non-reducing`): supplying the input is exactly as hard as assuming the
  target. Lead-verified by reading the proof (a clean two-way argument on the 2-torsion hypothesis).
  `evenDescent_iff_surjective_and_rangeTwoDivisible` locates the split: (ED) = the conclusion
  (surjectivity) **plus** pure excess (`im p_* ⊆ 2·H₃(Q;ℤ)`).
- **REASON 2 (CONDITIONAL — this is why the entry is prose, not `KERNEL_NOGO_REGISTRY`): (ED) is
  expected FALSE.** `not_evenDescent_of_seamNormOddity` refutes it from two named Props,
  `SeamKernelEvenlyConstant` (implied by the tree's own already-open "im ∂₃ is the diagonal
  ℤ ⊆ ℤ¹⁶", `KummerPunctureH3.lean:89-96`) and `SeamNormOddity` (the slab fact — only its parity
  half is new; the containment half is banked as `NormLandsInSeam`). The informal driver: the
  boundary-`S³`↦twice-`ℝP³` fact controls only the **boundary-generated** sublattice of
  `H₃(T⁴°;ℤ) ≅ ℤ¹⁹ = ℤ¹⁵(boundary) ⊕ ℤ⁴(bulk)`; the bulk 3-subtori give `p_*[T³] =` a sum over an
  **8-element** subset of seam classes, a 0/1 vector that is neither `0` nor `𝟙` mod 2. Index check:
  `[H₃(Q) : 2·H₃(Q)] = 2¹⁵` but `[H₃(Q) : im p_*] = 2¹¹`, so `im p_* ⊋ 2·H₃(Q)` outright.
  ⚠ **Constructing `SeamNormOddity` would promote this to `KERNEL_NOGO_REGISTRY`** (Inv #17); until
  then the refutation is conditional and stays here.
- `scope / what survives`: the **WEAK** form `im p_* ⊆ im qSeamCoord3`
  (`KummerK3H3SeamWindow.twoTorsionFree_iff_qSeamCoord3_surjective_of_descent`) is UNAFFECTED and is
  the form to consume — it is satisfied by exactly the eight-fold seam sums that kill (ED). Nothing
  about `H₃(K3;ℤ) = 0` is lost by dropping (ED).
- `side-effects banked`: **`H₃(Q;ℤ) ≅ ℤ¹⁵` is free**, so the parallel 2-torsion-freeness target is
  true and untouched; and the boundary-`S³` lattice of `T⁴°` is **exactly**
  `ker (H₃(T⁴°;ℤ) → H₃(T⁴;ℤ))` with free `ℤ⁴` quotient (`ptSeam3`,
  `range_ptSeam3_eq_ker_mapInt_inclXC`, `punctureH3ModSeamEquivFin4`, `not_surjective_ptSeam3`) —
  the kernel-checked localization of the overreach.
- ⚠ **CONSUMER DEBT (lead, open):** `KummerQuotientTransferSequence.lean:236` and `:247`
  (`h3K3_eq_zero_of_top_vanishing_of_evenDescent`,
  `nonempty_intOrientation_of_top_vanishing_of_evenDescent`) take (ED) as a hypothesis and are
  therefore conditioned on something expected false — not unsound, but useless as written. They need
  weak-form twins. Do not delete them; ADD the twins (remediate by building, not by walking back).
- `memory`: `[[project_5qH_nonhausdorff_substrate_bug]]`
- `created_ts`: 2026-07-27

## `k3-orientation-needs-an-integral-geometric-input-not-mod-2` (2026-07-27, arm: close-out — wt1 round 2)
- `kind`: route ban (prose — a structural observation about proof strategies, NOT a false in-Lean
  statement, hence NOT `KERNEL_NOGO_REGISTRY`-eligible).
- `banned`: attempting to close `H₄(K3;ℤ) ≠ 0` — equivalently `Nonempty (IntOrientation KummerK3)`,
  equivalently `ker qSeamCoord3 ≠ ⊥` — by any purely **mod-2 / algebraic** argument in the degree-4
  window. **A closed NON-ORIENTABLE 4-manifold satisfies every mod-2 constraint available there**, so
  no amount of ℤ/2 bookkeeping can separate the orientable case. A **geometric integral input is
  structurally required**, and the cheapest one in tree is T⁴-orientability
  (`det(τ = −id) = +1` in even dimension ⟹ `Q = T⁴°/τ` orientable).
- `status of the lane`: `orientInput` is **REPLACED, NOT DISCHARGED**, and the replacement is
  **lossless** — `nonempty_intOrientation_iff_ker_ne_bot : Nonempty (IntOrientation KummerK3) ↔
  LinearMap.ker qSeamCoord3 ≠ ⊥` is a genuine `↔` (lead-verified: no hypotheses in the statement),
  because both side conditions of the ambient-generic criterion
  `nonempty_intOrientation_iff_nontrivial_h4` are unconditional in tree (`k3_h4_free`,
  `instPreconnectedKummerK3`). The residual moved from a **2-saturation** statement to a single
  **existential**: one nonzero `v ∈ ℤ¹⁶` with `qSeamCoord3 v = 0`.
- `what is proved unconditionally` (the exact mirror, on the double cover):
  `KummerPunctureSeamRelation.exists_nonzero_seam_relation : ∃ v : EIndex → ℤ, v ≠ 0 ∧
  thickSeamCoord3 v = 0` and `ker_thickSeamCoord3_ne_bot` — the sixteen boundary `S³` classes of
  `T⁴°` ARE ℤ-linearly dependent. Lead-verified kernel-pure and binder-free.
- ⚠ **THE ONE REMAINING SPAN — a transport, not a computation.** Intertwine
  `KummerPunctureH3.interH3EquivEIndex` (T⁴° side) with `KummerK7MVAssembly.interH3EquivInt` (K3
  side) across the free ℤ/2 covering `T⁴° → Q`. The geometry already lines up numerically
  (`excisionRadius = 1/2`; `chartSphere c = centeredChartParam c '' {sqNorm = 1/4}`; `ann4 =
  {1/16 ≤ sqNorm ≤ 1/4}` retracts to `sphHalf = {‖w‖ = 1/2}`, so `chartSphere c` **is** the outer
  face of `annPiece c`) — **but no Lean lemma states it**, and `KummerQuotientTransferInt`'s
  `transferChainInt` has **no naturality lemma for inclusions of subspaces**. That is the whole span.
  The degree-2 defect is NOT an obstacle: once transport exists, `2 • qSeamCoord3 v = 0` upgrades to
  `qSeamCoord3 v = 0` for free via the banked unconditional `h3Q_twoTorsionFree`.
- ⚠ **Retraction of an earlier claim (wt1's own, and I had propagated it):** "mod-2 top-homology
  uniqueness `H₄(M;ℤ/2) ≅ ℤ/2` is NOT in tree" was **WRONG**. It IS in tree —
  `SingularFundamentalClassExist.localDegree_bijective` + `homologyTopEquivZMod2` (a different file
  from the `SingularFundamentalClass.lean` that was checked). No new span was needed; only the
  `PreconnectedSpace` instance, which wt1 then built. *Lesson: a "not in tree" verdict from one file
  is not a verdict about the tree — search by declaration, not by filename.*
- `memory`: `[[project_5qH_nonhausdorff_substrate_bug]]`
- `created_ts`: 2026-07-27

## `do-not-redefine-bordism-on-collared-representatives` (2026-07-27, arm: close-out — LEAD DECISION)
- `kind`: scope/policy decision (prose — a route choice, not a false statement).
- `context`: wt2 surfaced a genuine lead-level scope call while scoping bordism gluing. Since arc A
  (the collar neighbourhood theorem) is Mathlib-grade, an alternative is to **redefine
  `IsT2DataBordant` on COLLARED bordisms**, packaging the collar as data. Gluing would then be
  constructible from `SingularSurgerySeamCollar.WeldedCollarModel`-style double collars, and
  "mathematically it is the same relation" by the collar theorem.
- ⛔ **DECISION: DO NOT DO THIS.** Taken by the lead after diligence; not escalated, because one
  option is clearly better on correctness grounds.
- **Why (the decisive argument):** without the collar theorem in Lean, the collared relation is
  a priori **strictly finer** than plain bordism — `Collared → Bordant` is easy, `Bordant → Collared`
  is exactly the missing theorem. A finer relation gives a **LARGER quotient**. So
  `T2DataBordismGrp` built on it could be a *different, bigger* group, and proving `≅ ℤ/16` about it
  would be proving something about the wrong object — precisely the failure the goal's FAITHFUL-carrier
  condition exists to prevent, and the exact shape of the `k = 0` fence ("at `k = 0` the honest group
  is the wrong one"). It also makes **injectivity strictly harder** (Brown = 0 must now yield a
  *collared* bordism), while surjectivity stays easy since our witnesses have explicit collars — a
  tell-tale sign the change buys convenience by moving the difficulty rather than removing it.
- Secondary: it is walk-back-shaped — changing the definition so the claim goes through. Standing
  policy (`feedback_remediation_build_dont_walkback`) is to build the substrate that makes the claim
  true, or prove it cannot be built; never redefine as the fix.
- ✅ **DO INSTEAD — the third option, which is cheaper than either and costs no faithfulness.**
  wt2's `SeamGlueChart` **types the wall exactly**: `Bordism.ofSeamGlueChart` already assembles the
  composite from 8 generically-constructed fields, leaving exactly four (`chartW`, `mfdW`,
  `he_smooth`, `he_boundary`). **Inhabit `SeamGlueChart` for the CONCRETE families actually in play**
  (cylinder, surgery trace, sphere-product coboundary) rather than proving the general collar theorem.
  This is the project's established and repeatedly-successful pattern — the Kummer weld's `IsManifold`
  came from ~15 modules of concrete atlas work, not a generic engine — and it leaves the relation, and
  therefore the group, untouched.
- ⚠ **AMENDED 2026-07-27 (operator steer).** The **rejection of the collared-relation redefinition
  above STANDS** — it rests on faithfulness (finer relation ⟹ larger quotient ⟹ possibly the wrong
  group), which nothing here touches. **What is corrected is the OTHER half of my reasoning:** I
  part-justified "concrete families *instead of* the general collar theorem" on the grounds that the
  general theorem is Mathlib-grade and Mathlib lacks both it and boundary-is-a-submanifold. **That is
  a COST input, not a closure.** This project builds Mathlib-grade infrastructure routinely and
  upstreams later; Mathlib's own `Geometry/Manifold/Bordism.lean` *names* this exact gap, so the
  collar neighbourhood theorem is an absent-but-true theorem blocking a real result — a legitimate
  build target and a genuinely upstreamable one. ("Route closed" is reserved for a kernel-checked
  no-go or a proved impossibility.)
  ✅ **Both arcs are AUTHORIZED IN PARALLEL, not in sequence:** the concrete `SeamGlueChart`
  inhabitation (fast unblock of `hker` for the families in play) **and** the general collar
  neighbourhood theorem (the reusable, upstreamable asset that makes `Transitive (IsT2DataBordant)`
  general and `T2DataBordismGrp` a genuine quotient by an equivalence relation). Neither blocks the
  other; the concrete one is not a substitute the general one must wait behind.
- `related`: `KERNEL_NOGO_REGISTRY['hker-single-witness-extraction-is-equivalent-to-gluing']` (the
  extraction is EQUIVALENT to gluing, so no shortcut exists) and task **#312**.
- `memory`: `[[project_5qH_nonhausdorff_substrate_bug]]`
- `created_ts`: 2026-07-27

## `arc-b-glueBor-needs-end-reparametrisation-too` (2026-07-27, arm: close-out — wt2)
- `kind`: interface-gap record (prose — a missing field, not a false statement; NOT registry-eligible).
- **The finding.** Arc B of bordism gluing (transporting the tethered `ξ.Bor` across a weld) was
  believed to need one new `TangentialData` field, `glueBor`. It needs **two**, and this is visible
  already at the EMPTY seam, which had been expected free: `addBor` yields
  `Bor (b₁.add b₂) (sumStr σ emptyStr) (sumStr emptyStr τ)` — endpoints `p.sum emptySM` and
  `emptySM.sum r`, **not** `p` and `r`. Closing that needs `Bor` transported along the **unitor
  diffeomorphism of the ENDS**, and `TangentialData` has **no boundary-reparametrisation field**
  either. So the arc-B debt is `glueBor` **plus** an end-reparametrisation transport.
- `consequence`: both are breaking changes to every `TangentialData` instance in tree. **Not
  authorized**; surface before any attempt. Arc B remains gated on arc A regardless.
- `related`: `KERNEL_NOGO_REGISTRY['hker-single-witness-extraction-is-equivalent-to-gluing']`;
  `do-not-redefine-bordism-on-collared-representatives`; task **#312**.
- `created_ts`: 2026-07-27

## `surgery-trace-is-not-a-seamglue-composition` (2026-07-27, arm: close-out — wt2, LEAD ERROR)
- `kind`: scope correction (prose). ⚠ **This corrects a target I set.**
- **What I got wrong.** I briefed the surgery trace as target #2 for `SeamGlueChart` inhabitation,
  calling it "the closest thing in tree to a collar and why I picked this route". The collar-MODEL
  half of that was right; the CARRIER half was wrong. `HandleAttachment`
  (`SingularSurgeryFoundation.lean:211–223`) welds along `S : Set Ha` — the closed attaching region
  `Sʳ × D^{n−r}`, a **proper subset** of the handle — whereas `glueCarrier b₁ b₂` welds along an
  **entire boundary component** (all of `q.M`). Lead-verified: I read the structure myself.
- **Consequence:** the surgery trace is **not a composition of two bordisms** and cannot be typed as
  `SeamGlueChart b₁ b₂` at all — it is not blocked by any field, it is outside the structure's domain.
  Typing it needs a different pushout notion. Do not re-dispatch it as a `SeamGlueChart` family.
- **Also corrected:** target #3 (`S²×D³`) is *partially covered already* — as a coboundary its other
  end is `∅`, so composing it IS the empty-seam family, which is now discharged. Only gluing it along
  the full `S²×S²` boundary is the collar case.
- `lesson`: "closest thing in tree to X" is a claim about a MODEL; before making it a build target,
  check the CARRIER the target structure actually quantifies over.
- `created_ts`: 2026-07-27

## `collar-no-cheap-route-around-the-boundary-flow` (2026-07-27, arm: close-out — wt3)
- `kind`: route ban (prose — two structural findings, neither a false in-Lean statement).
- **Context.** The collar neighbourhood theorem is the wall for `hker` arc A (`SeamGlueChart`'s four
  residual fields). wt3 built prerequisite (1) — **`isManifold_boundary`, Mathlib's own explicit TODO
  at `IsManifold/InteriorBoundary.lean:66`, discharged for the bordism model `I.prod (𝓡∂ 1)`** — plus
  `contMDiff_boundary_val` (the inclusion `∂W ↪ W` is `C^n`, i.e. the submanifold content). Both
  lead-verified kernel-pure and NON-VACUOUS (`prodIcc_boundary_nonempty_isManifold` exhibits a witness
  with a genuinely **nonempty** boundary).
- ⛔ **BANNED ROUTE 1 — the boundaryless-enlargement dodge.** Do NOT try to sidestep the
  boundary-flow gap by enlarging `W` to a boundaryless `W⁺ = W ∪_∂ (∂W × (−1,0])` and flowing there
  with Mathlib's interior-point integral-curve theorem. **It is circular:** constructing `W⁺` means
  building charts at a seam, which IS the `SeamGlueChart` problem. It is a mildly easier instance
  (one side is a product) but the same shape, so it cannot be the tool that solves the general case.
- ⛔ **BANNED ROUTE 2 — local collars in place of a global one.** Local product structures chosen
  independently near each boundary point are **not `C^k`-compatible with each other across the seam**.
  That incompatibility is precisely why the classical proof needs a coherent GLOBAL collar built from
  a single vector field. Do not dispatch "just get local collars, that's enough for seam charts."
- **The honest remaining inventory** (wt3, verified against the pinned Mathlib source, not memory):
  - **(1) boundary-is-a-submanifold — DONE** (above).
  - **(2) partitions of unity — present but `C^∞`-ONLY.** ⚠ Corrects the assumption in my brief:
    Mathlib's machinery does **not** require boundarylessness, so manifolds-with-boundary are fine;
    the obstruction is *regularity*. `SmoothPartitionOfUnity` is valued in `C^∞⟮I, M; 𝓘(ℝ), ℝ⟯` and
    `SmoothBumpFunction`'s smoothness lemmas sit under `[IsManifold I ∞ M]`. A finite-`k` partition of
    unity does not exist in the library. Since we are k-generic by fence, this is a real cost line —
    moderate, self-contained, and separately upstreamable (the standard bump is `C^∞` in a chart,
    hence `C^k` on a `C^k` manifold).
  - **(3) uniform-time flow OUT OF a boundary point — the dominant gap, and Mathlib's own open TODO.**
    `exists_isMIntegralCurveAt_of_contMDiffAt` requires `I.IsInteriorPoint x₀`, and every result in
    `IntegralCurve/UniformTime.lean` carries `[BoundarylessManifold I M]`.
    `IntegralCurve/ExistUnique.lean`'s header says so outright ("the case where the integral curve may
    lie on the boundary … we leave it as a TODO … See Theorem 9.34, Lee. May require submanifolds").
    Closing it needs Picard–Lindelöf on `Ici 0` in the model half-space, then the manifold-level
    statement.
- `upstreamable` (per the standing "Mathlib lacks X is COST not CLOSURE" pre-decision): the leg-1
  general `ModelWithCorners` block is upstreamable today; leg-2/3/5 as "boundary is a submanifold for
  `I.prod (𝓡∂ 1)`", directly addressing the named TODO; the finite-regularity partition of unity as an
  independent third PR. The module has **no dependence on the bordism stack** — upstreaming is a file
  move, by construction.
- `memory`: `[[project_5qH_nonhausdorff_substrate_bug]]`
- `created_ts`: 2026-07-27

## `hphig-from-hcyc-is-circular` (2026-07-27, arm: close-out — wt2; LEAD BRIEF ERROR)
- `kind`: circular-reduction ban (prose — both arrows are true theorems; the *composition* proves
  nothing, so there is no false statement to kernel-encode).
- ⛔ **BANNED:** discharging `hΦg` by way of `{hcyc, h2}` and
  `spinForgetPhi_g_eq_ktKernelRep_of_cyclic`. **`SpinImageCyclic` is a bare `def … : Prop` whose ONLY
  route, `PinPlusKTKernelSpinRoute.spinImageCyclic_of_presentation` (`:315`), itself takes
  `(hΦg : Φ (mk ξ g) = ktKernelRep prov)` as an explicit hypothesis** (lead-verified: I read line 320).
  So `{hcyc,h2} ⟹ hΦg` composed with `hΦg ⟹ hcyc` is a strict circle.
- ⚠ **This was MY brief.** I instructed wt2 that if `hcyc`/`h2` were discharged then `hΦg` follows and
  to "land that wiring and say so plainly." A compliant worker would have shipped a **false
  discharge**. wt2 verified first and caught it. → new checklist item 4 in `PRE_DECISIONS.md`:
  *when a brief says X follows from Y via arrow A, open A and confirm A's own hypotheses do not
  contain X.*
- **Also corrected:** task #197 (`PinPlusKTBinderDischarge.lean`) is a **REDUCTION, not a discharge** —
  its own header says so, and all three of its theorems still take `hcyc`/`hΦg`/`hk` as hypotheses.
  Neither `SpinImageCyclic prov` nor `ktKernelRep + ktKernelRep = 0` is proved for the live provider.
  Do not read a completed task title as a discharge.
- ✅ **The non-circular route, BUILT:** drop `hΦg` from `spinImageCyclic_of_presentation` (it is used
  only to rewrite `Φ[g]` into `k₀` at the last line) and the sector is cyclic **on `Φ[g]` itself`.
  Then `k₀` brown-kernel (banked) → `hKRS` puts it in the sector → `k₀ = n • Φ[g]` → `Φ[g]` 2-torsion
  via `spinForgetPhi_add_self` (enhancement-tied, so `dataBordism_two_torsion_of_revStr_trivial` is
  NOT reproduced) → `k₀ = 0 ∨ k₀ = Φ[g]` → `KTNonSplit` kills the first.
- **Consequence — `hΦg` IS `KTNonSplit`** (`phiG_eq_ktKernelRep_iff_ktNonSplit`): closing `hΦg` is
  neither easier nor harder than closing `8·[ℝP⁴] ≠ 0`.
- ⚠ **REFUTABILITY POSTURE (do not treat `hΦg`/`KTNonSplit` as safe):**
  `PinPlusCharPairTetherGate.ktKernelRep_eq_zero_of_tethered_double` and
  `PinPlusCharPairFlipGate.ktKernelRep_eq_zero_of_realization` make `k₀ = 0` derivable from open
  geometric witnesses — the latter **refutes `KTNonSplitU` outright on the flipped/untethered
  carrier**. Since `hΦg ⟺ KTNonSplit`, `hΦg` inherits exactly that posture: a live open bit that
  could go either way, not a formality.
- `created_ts`: 2026-07-27

## `OPEN-RISK-collar-may-cap-below-the-flagship-k-top` (2026-07-27, arm: close-out — LEAD, UNVERIFIED)
- `kind`: ⚠ **OPEN RISK, not a finding.** Filed so it is not lost; the verification is OWED.
- **The observation.** wt3's finite-regularity partition of unity is stated at `{n : ℕ∞}` throughout,
  and its scope note is that **analytic bump functions do not exist — excluded by mathematics, not by
  a formalization gap** (`ContDiffBump.contDiff` is itself `{n : ℕ∞}`). But `ℕ∞`'s top is `∞` (C^∞),
  whereas this project's manifold regularity is **`WithTop ℕ∞`**, whose `⊤` sits *strictly above*
  `(⊤ : ℕ∞) = ∞`. The goal's flagship instantiates at `residualProvK ⊤`
  (`PinPlusKTAssemblyResiduals.lean:70`, `:196`).
- **The risk, stated precisely.** IF `⊤ : WithTop ℕ∞` is the analytic level, THEN the collar
  neighbourhood theorem — which needs a partition of unity for the inward field — **cannot be proved
  at `k = ⊤`**, so the `hker`-via-gluing route would cap at `k ≤ ∞` and would NOT serve the flagship.
  Note this affects nothing already landed: no shipped theorem depends on a collar yet.
- ⚠ **NOT VERIFIED BY ME.** I grepped Mathlib's `IsManifold/Basic.lean` for the analytic groupoid and
  got nothing — which settles **nothing** (a failed grep is not evidence; see `PRE_DECISIONS.md`
  "verify with the kernel, not grep"). Do not act on this entry as though it were established.
- **What would settle it** (cheap, do it before any further collar investment):
  1. `lean_hover_info` on `IsManifold` / read Mathlib's regularity convention — does `WithTop ℕ∞`'s `⊤`
     select `analyticGroupoid`, and is `(∞ : WithTop ℕ∞) < ⊤`?
  2. If yes: check whether the *bordism relation at `k = ⊤`* genuinely requires an analytic collar, or
     whether an `∞`-collar suffices because the relation only asks for *some* manifold-with-boundary.
     ⚠ Do NOT assume the second — a Cω-to-C^∞ slide is exactly the shape of
     `k0-to-k1-transport-refuted`, and the goal forbids transporting across regularity levels.
  3. If the ceiling is real, the honest options are: state the collar/`hker` discharge at `k ≤ ∞` and
     declare the flagship at `∞` rather than `⊤` (a **goal-condition change — operator call**), or
     find a collar construction that avoids partitions of unity.
- `created_ts`: 2026-07-27

## `stablenegrank16-rank18-forces-spinor-genus-restate-at-rank20` (2026-07-27, arm: close-out — wt1)
- `kind`: route ban + restatement (prose — the rank-18 statement is **TRUE**, merely not elementarily
  provable, so there is nothing false to kernel-encode).
- ⛔ **BANNED:** attempting Wall's characteristic-vector transitivity / `UnitCancellation` **at the
  rank-18 phrasing of `StableNegRank16`** (one hyperbolic plane, `σ = −16`). **Kernel-checked reason:**
  `inertia_of_rank18_sig_neg16` proves that lattice has inertia **(1, 17)** — it *is* the Lorentzian
  even unimodular `II_{1,17} ≅ U ⊕ E₈(−1)²`. That is precisely where `2U` cannot split off for
  numerical reasons, **Eichler's criterion does not apply**, and every published proof routes through
  Eichler's **spinor genus / strong approximation** (Borcherds, *The Leech lattice and other lattices*,
  arXiv:math/9911195 Thm 3.9.1 — primary source verified by wt1). Mathlib has no genus theory, so this
  phrasing is not reachable.
- ✅ **THE FIX, AND IT COSTS NOTHING: restate at RANK 20 (two hyperbolic planes).**
  `inertia_of_rank20_sig_neg16` gives inertia **(2, 18)** — `min ≥ 2`, inside Eichler's elementary
  regime. `StableNegRank16Two` + `hk3_of_stable16_two` lift the rank-20 stabilization through **one**
  peeled `H` instead of the rank-18 one through two, and land **the same** `IntCongr M k3Form`
  (lead-verified: I read both inertia theorems and the target, and checked the arithmetic independently
  — rank 18: sum 18, diff −16 ⟹ (1,17); rank 20: sum 20, diff −16 ⟹ (2,18)).
- ⚠ **MY BRIEF ERROR (second instance of the same checklist item).** I told wt1 the target was
  "**Elementary — reflections only. Not genty theory**", asserting as fact a characterization I had
  inherited from wt1's own earlier report. It was false at the rank I named. → `PRE_DECISIONS.md`
  item 5 widened from "never inherit an ESTIMATE" to "never inherit an estimate **or a
  characterization**" — a claim about the mathematical *nature* of a target is a route claim.
  **The cheap check that would have caught it: compute the inertia.**
- **Progress banked at the corrected rank:** the Eichler transvection is built explicitly
  (`eichler`, `eichler_isometry`, `eichler_isUnit_det`; integrality costs exactly the parity of
  `x·M·x`, which is the even/odd dividing line for this route), and **Eichler's criterion STEP 2 is
  DISCHARGED** (`exists_isometry_map_of_perp_hyp` — three explicit transvections; the proof makes
  visible that `w·w = w'·w'` is exactly what kills the middle arrow's leftover `f`-coefficient).
  `unitExtend_intCongr_of_evenUnimodular` reduces the whole brick to **cancelling the `⟨1⟩`**, off the
  now-unconditional `odd_indefinite_intCongr_unconditional`.
- **Remaining = Eichler STEP 1 only** (normalize `w'` ⊥ `⟨e,f⟩`): the
  `SO⁺(U ⊕ U₁) ≅ (SL₂ℤ × SL₂ℤ)/±` reduction, a 2×2 Smith normal form driven by four transvections
  whose action on the pairing quadruple wt1 wrote out explicitly; plus the `2U` splitting of the
  rank-20 `A` (two applications of the banked `even_unimodular_indefinite_split_congr`, indefinite at
  ranks 20 and 18 since `|σ| = 16 < 18`), the `w·w' ≡ 1 (mod 4)` sign normalization, and block
  extraction. **None of that needs genus theory.**
- ⛔ **Two dead ends closed so they are not re-walked:** (i) a one-step reflection descent on
  `c = w·w'` is **FALSE** — counterexample `c = 17`, `a = 6a₀` with `a₀·a₀ = −2`: the shifts live in
  `24ℤ` but must hit `−18` or `−16`. (ii) There is **no** general lemma "∃ isotropic `u ∈ A` with
  `u·a = ±1`" — it fails as soon as `div(a) > 1`.
- `created_ts`: 2026-07-27

## `planereduction-axis-gcd-divisibility-refuted` (2026-07-28, arm: close-out — LEAD-VERIFIED, numerical)

**Status: route caution on a PROOF STRATEGY (not kernel-encoded — the counterexample is a numerical
chain, and encoding it in Lean costs more than it saves).**

- ⛔ **Do NOT try to prove `AxisReturnBound` (or the `PlaneReduction` outer recursion) by
  strengthening the axis measure from `<` to DIVISIBILITY.** The tempting simplification is to carry
  `gcd(γ₂,δ₂) ∣ gcd(γ₁,δ₁)` between successive `β = 0` axis visits, which would make the induction
  fall out immediately. **It is FALSE.**
- **Witnesses** (lead's own simulation of the exact in-tree move set, with the conserved quantity
  `αβ + γδ` and `gcd(α,β,γ,δ)` asserted at every step): out of 600 adversarially constructed hard
  axis states (`e = gcd(γ,δ) ∈ {4..72}` chosen so `e ∤ α`), **strict `<` holds with ZERO
  violations**, but divisibility fails **7** times —
  `(5, 0, 24, 30)` visits axis gcds `[6, 4]` and `4 ∤ 6`; also `(58,0,240,300) ↦ [60,8]`,
  `(40,0,192,240) ↦ [48,32]`, `(30,0,144,180) ↦ [36,24]`, `(29,0,240,336) ↦ [48,8,3,1]`.
- **Consequence for the open work:** the measure genuinely is an inequality, so the descent
  induction must **carry a bound** through its rounds rather than re-derive a divisibility chain at
  the end. That is exactly what `AxisReturnBound` (`PlaneReductionDescent.lean` §6c) states, and why
  it is stated as a named Prop rather than proved in passing.
- **Also do not retry the naive monotonicity route:** `gcd(γ,δ)` is not monotone under a single
  descent round either — `γ = 2, δ = 3, β = 5` sends `gcd 1 → 2` whenever `3 + qα` is even.

## `gm-empty-surface-specialization-is-circular` (2026-07-27, arm: close-out — LEAD-VERIFIED)

**Status: route caution + inventory fact. Binding on every future `hdvd` / Rokhlin dispatch.**

> ⚠️ **AMENDED 2026-07-27 (same day) — the ROUTE CAUTION BELOW STANDS, but the REASON stated for it
> was WRONG, and the wrongness matters because it would mis-gate future candidates.**
>
> I originally wrote that the defect is the **biconditional** between the layer's hypothesis and
> `16 ∣ σ` at the spin locus. `GMTripleLayer.triple_layer_forcing` (wt2, and I re-derived both
> directions myself before accepting it) proves that criterion is **unsatisfiable**: *any* predicate
> `P` on the invariant triple `(σ, F·F, 2β)` that follows from Guillou–Marin and suffices for Rokhlin
> at spin satisfies `P (σ,0,0) ↔ 16 ∣ σ` — **including the true Guillou–Marin theorem**. Judging a
> candidate layer by "is it biconditional with the conclusion at spin?" therefore rejects everything,
> the real theorem included. `no_triple_layer_escapes_the_biconditional` states this as a no-go on
> the whole design space; both are registered under
> `KERNEL_NOGO_REGISTRY['gm-triple-level-layer-is-decided-by-sigma-alone']`.
>
> **The correct criterion is INTENSIONAL: what DATA is the hypothesis a predicate on?** A layer
> predicated on a pin⁻ class and a surface is admissible; one predicated on σ-arithmetic is not.
> The admissible in-tree form is `PinTorsor.gmrelation_shift_iff` — a predicate on the pin⁻ class
> `w`, with both attacks recorded as theorems (`no_pin_structure_realizes_gm_at_zero`,
> `gm_layer_depends_on_pin_class`, the latter holding at `w = 0` and failing at `w = 1` on the SAME
> triple, which a σ-arithmetic Prop provably cannot do).
>
> **What still stands, unchanged:** do not build `SpinCharSurfaceData` at the empty surface and call
> `hdvd` discharged. That datum is a predicate on σ-arithmetic, so it fails the intensional test —
> the practical ban is correct, only its justification is restated here.

- ⛔ **Do NOT try to obtain `hdvd` (`∀ x, 16 ∣ R.sig x`, the atlas KEYSTONE
  `hyp:rokhlin_sigma_mod_16`, gating impact 11) by specializing the Guillou–Marin / Freedman–Kirby
  congruence to the EMPTY characteristic surface.** For a spin manifold the characteristic surface is
  dual to `w₂ = 0`, so `FdotF = 0` and `Q.brown = 0`, and `GMrelation σ 0 Q` **degenerates to
  `16 ∣ σ` itself**. The specialization *is* the conclusion. Lead-verified against `GMrelation`'s
  definition; the blueprint says the same independently ("at `F = ∅` the surface nodes
  `[G1][G2][Q1][Q2]` are VACUOUS; only `[FK]`-at-∅ remains — that single congruence IS the node").
- ⚠ **`SpinCharSurfaceData` is a PACKAGING of Rokhlin, not a proof of it.** Its `gm` field is the
  genuine input; `SpinCharSurfaceData.rokhlin` (`GMRokhlinDischarge.lean:103`) consumes it. Building a
  `SpinCharSurfaceData` for a carrier element with an empty surface therefore discharges nothing —
  a compliant worker would ship a circular `hdvd`.
- 📋 **Inventory, lead-verified by grepping EVERY `GMrelation` occurrence in the tree:** every in-tree
  producer proves `GMrelation 0 0 C.Q` — the **null-bordant / metabolic** leg only
  (`CharSurfaceMembrane.lean:343`, `CharSurfaceBounding.lean:123`,
  `CharSurfaceNormalShadow.lean:210/233/245`, `CharSurfaceRealization.lean:199`). Each takes a
  `Bounding` datum, i.e. the manifold bounds, where `σ = 0` holds trivially by bordism-invariance.
  **There is NO supplier at general σ.**
- ✅ **What IS built:** the wire *from* GM-at-general-σ *to* `16 ∣ σ` —
  `CharSurfaceRokhlinAssembly.sixteen_dvd_sig_of_gm_realization` (:109) takes `hgm : GMrelation σ 0 C.Q`
  plus four leaves `{KernelClassesEmbedded, KernelCirclesBound, MembraneSpinKill, KernelLagrangianForB}`,
  and `topo_of_bounded_charSurface` (:125) carries it to `SmoothSpinManifold4.topo`. So the missing
  piece is **exactly `hgm`**.
- ⛔ **The tethered carrier does not supply it either** (checked before briefing):
  `CharPairStrBundled` carries `surf`/`emb`/`embSmooth`/`embInj`/`surfClass`/`basis`/`hpolar`/`hchar`
  — **no field relating σ to the Brown invariant**.
- ⛔ **No algebraic shortcut exists**: `lattice_arf_bridge_refuted` (kernel no-go) kills
  `σ/8 ≡ Arf(q̄) mod 2`; E₈ is even unimodular with `σ/8 = 1` and is not smoothly realizable, so the
  lattice provably cannot see this node. It is irreducibly smooth-topological — confirmed, not a
  magnitude judgment.
- **Route of record:** blueprint `Lit-Search/Phase-5qH/Rokhlin_16_sigma_elementary_blueprint_20260703.md`
  Route A ([FK]/Matsumoto, Arf form), with the Kervaire–Milnor sphere bridge as a candidate lighter
  target — ⚠ "cleanest" is the blueprint's characterization and is **NOT** lead-verified; per
  `PRE_DECISIONS.md` item 5 it must be tested, not inherited.
- `created_ts`: 2026-07-27

## `k3-gram-must-not-use-pdInput-of-gram` (2026-07-27, arm: close-out — LEAD-VERIFIED)

**Status: circularity fence on the K3 Gram lane. Binding.**

- The welded Kummer K3's E1 residual ledger is down to **one** obligation
  (`KummerK3E1FromGram.nonempty_kummerK3E1Atoms_of_gram` :61): the Gram congruence
  `∀ o, ∃ C hC, IntCongr (reindex (interMatrix [K3]_o C)) k3Form`. `h1Free` is unconditional
  (`free_h1K3_uncond`), `orientInput` is retired as a gate
  (`nonempty_intOrientation_kummerK3_uncond`), and `pdInput` is derived **from** the Gram.
- ⛔ **Therefore, on the lattice-classification route to the Gram (via `hk3_of_stable16_two`), you may
  NOT use `KummerK3PoincareDuality.kummerK3_pdInput_of_gram` to supply unimodularity** — that theorem
  takes the Gram as its hypothesis, so `Gram ⟹ pdInput ⟹ Gram` is a strict circle. Genuine integral
  Poincaré duality on the welded carrier is required. (`PRE_DECISIONS.md` item 4: open the arrow and
  check its own hypothesis list. I opened it; this one contains the target.)
- ✅ The route itself is sound: `hk3_of_stable16_two` needs `IsEvenUnimodular` + `latticeSig = -16` on
  the rank-22 form, plus `StableNegRank16Two` (wt1's Eichler STEP 1 lane). Nothing in
  `even_unimodular_indefinite_split_congr`'s hypothesis list (`{IsEvenUnimodular, 0 < sigPos,
  0 < sigNeg}`) contains the target — lead-verified, so that arrow is safe.
- ⛔ **The definite-classification shortcut is DEAD**: you cannot instead split `2U` off and classify
  the negative-definite rank-16 residual, because there are **two** classes
  (`−E₈ ⊕ −E₈` and `−D₁₆⁺`). Absorbing that distinction is precisely the content of the
  `2U`-stabilization, which is why cancellation/Eichler is irreducible here.
- `created_ts`: 2026-07-27

## 6ea-interval-restricted-gaussian-lower-tail
- verdict: banned
- tier: agent-reviewed
- authored_by: coach
- killed_by: Phase 6EA Stage-2 statement freeze §3.2 (UNKNOWN-2 resolution), lead sign-off 2026-07-27
- reason: `Q z ≥ ½ − z/√(2π)` (and the variant `½(1 − z/√(2π))`) is TRUE but VACUOUS — its RHS goes negative for `z > √(2π)/2 ≈ 1.2533`, i.e. across the entire range any consumer operates in (`z ≳ 2`). It is therefore not kernel-refutable and gets no backing theorem; it is banned on uselessness, not falsity. The shipped replacement is `gaussianTail_ge_window` (`c·φ(z+c) ≤ Q z`, global in `z`, parametric in `c`, no side condition), with `gaussianTail_birnbaum` as the sharp form — both now on main in `Detection/GaussianThreshold.lean`. If a proof attempt starts reconstructing the interval-restricted rational as the headline lower tail, stop.
- memory: [[project_vectorC_public_6E_series]]
- created_ts: 2026-07-28T00:00:00Z

## 6ea-optimalhypothesisrate-quantum-seam
- verdict: dead
- tier: agent-reviewed
- authored_by: coach
- killed_by: Phase 6EA Stage-2 statement freeze §4 (UNKNOWN-3 resolution), after reading PhysLib `QuantumInfo.ResourceTheory.HypothesisTesting` in full (568 lines)
- reason: TYPE-LEVEL IMPOSSIBLE, two independent ways. (i) `OptimalHypothesisRate ρ ε S` takes `ρ : MState d` with `[Fintype d]`, and PhysLib's classical embedding `MState.ofClassical` takes `ProbDistribution α` with `[Fintype α]` — Poisson lives on ℕ, which is not a `Fintype`, so it cannot be an argument to either. (ii) `OptimalHypothesisRate` is the *asymmetric* Neyman–Pearson value (min Type-II at Type-I ≤ ε), whereas the 6EA floor bounds the *symmetric* Bayes/Le Cam average error at equal priors — calling one a specialization of the other is a category error, so any such theorem would be false or vacuous. Not kernel-encodable (a typing/functional fact, not a false proposition). The seam instead routes through the `Fin 2` pushforward as a diagonal restriction of the project's own proven FvdG. COROLLARY: 6EA Wave 3 must NOT be described as "the first project consumption of `HypothesisTesting`" in any D12-facing text unless that consumption actually happens.
- memory: [[project_vectorC_public_6E_series]]
- created_ts: 2026-07-28T00:00:00Z

## 6eb-enbw-convention-falsifier-shape
- verdict: banned
- tier: agent-reviewed
- authored_by: coach
- killed_by: Phase 6EB Wave 1 (`Detection/FilterFloors.lean`, merged `4378cc01`) — worker finding, lead-confirmed
- reason: a dimensional/convention falsifier phrased as "the one-sided vs two-sided PSD convention is wrong" is VACUOUS over any composed variance, because the product `S₀ · ENBW` is convention-INVARIANT (a physical variance must be). The only detectable error is *MIXING* the two — one-sided PSD against two-sided ENBW — which is a clean factor of 2. Any 6EB/6EC/6EE falsifier in this family must target a MIXED pairing. Detectability is already encoded as `enbw_oneSided_ne_twoSided` (the two normalizations provably disagree on the boxcar at every `T > 0`); build on it rather than restating it.
- memory: [[project_vectorC_public_6E_series]]
- created_ts: 2026-07-28T00:00:00Z

## 6eb-unsigned-matched-saturation-characterization
- verdict: dead
- tier: agent-reviewed
- authored_by: kernel-no-go
- killed_by: Phase 6EB Wave 3 (`Detection/MatchedFilter.lean`, 2026-07-29) — kernel-checked, lead-derived
- reason: matched-filter saturation phrased WITHOUT a sign condition — "`filteredSNR = matchedBudget` iff `h` is a.e. *some* scalar multiple of the template" — is **FALSE**, not merely lossy. Witness `h = −s` (`c = −1`): it satisfies the unsigned membership condition and **saturates Cauchy–Schwarz in magnitude**, yet realizes `−matchedBudget`. The deflection-to-noise ratio is *signed* (numerator `∫₀ᵀ h·s`, denominator the positive `√(V h)`) while C–S equality only controls `|∫ h·s|`; the anti-matched filter is the extremal **minimizer**. Refuted flatly by `unsigned_saturation_characterization_false`, with `filteredSNR_neg_matched_eq_neg_budget` as the computed witness — see `KERNEL_NOGO_REGISTRY['unsigned_matched_saturation_characterization']`. SCOPE: this does **not** weaken the shipped `filteredSNR_eq_budget_iff` (which carries `∃ c, 0 < c ∧ …` and is correct), nor `filteredSNR_le_matchedBudget` (true for `h = −s`, trivially). The refutation is **class-restricted** (corrected 2026-07-29 after adversarial review): it quantifies over `IsAdmissibleFilter T s h`, because refuting the unrestricted `∀ h` does *not* refute the class-restricted statement a consumer would write — `¬(∀h, P h)` does not imply `¬(∀h ∈ class, P h)`.
- **⚠ CONSUMER TRAP for 6EC/6EE — this bullet's earlier wording was FALSE and is retracted (2026-07-29).** It previously said that in the **power** SNR `(∫h·s)²/V h` "the sign drops out and the unsigned characterization *is* correct there". The sign does drop out; **`c = 0` does not**. The **zero filter** satisfies the unsigned membership condition at `c = 0` and realizes power SNR `0`, not `matchedBudget²` — so the sign-free power statement still needs `∃ c ≠ 0`. Not a pathological corner here: `c = 0` is exactly a **vanishing-responsivity readout chain**, the branch both `Electrothermal.ETFModel.responsivityETF` and `Detection.nepOfOutput` disclose. Both halves are now kernel-backed instead of prose — `power_unsigned_characterization_false` (the `c = 0` refutation; needs no whiteness binder, since the zero filter defeats the claim for *any* variance functional) and `powerSNR_smul_eq_budget_sq` (the correct `c ≠ 0` form). Do not transport the corrected power-domain statement back into the amplitude domain — that remains the shape this fork bans.
- memory: [[project_vectorC_public_6E_series]]
- created_ts: 2026-07-29T00:00:00Z
