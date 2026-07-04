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
- memory: [[project_5qH_geometric_floor_terminal]]
- created_ts: 2026-07-04T00:00:00Z
