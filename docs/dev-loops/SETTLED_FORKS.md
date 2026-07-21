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
- memory: [[project_5qH_geometric_floor_terminal]]
- created_ts: 2026-07-04T00:00:00Z

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
