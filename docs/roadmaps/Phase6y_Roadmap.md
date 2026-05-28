# Phase 6y: SU(d > 2) Substrate Extension + Full Multi-Qubit Solovay-Kitaev (Academic Completeness)

## Technical Roadmap — May 2026

*Prepared 2026-05-26 PM, following the Phase 6x lift/shift retrospective audit.*

**Trigger condition:** Phase 6x completes at the *lift/shift* interpretation level (per the updated Phase 6x Roadmap and the Phase 6x retrospective): T-A1 ships as "1Q-rotations-compiled-via-Phase-6u-Clifford+T + MS-as-primitive"; T-A2 ships at the CCZ-alphabet-substrate level only; the SU(d > 2) extension and the full multi-qubit Solovay-Kitaev compilation are *explicitly deferred* to Phase 6y. Phase 6y picks up the substantive SU(d) substrate work that the Phase 6x lift/shift framing deferred.

**Headline goal:** Generalize the Phase 6u SU(2)-targeted quantitative Solovay-Kitaev substrate to arbitrary `d ≥ 2`, enabling **kernel-verified compilation of arbitrary unitaries in SU(d)** for d-dimensional gate sets. Validate at three instances: (1) trapped-ion native gates at SU(4) (Mølmer-Sørensen + 1Q with the full 2-qubit Hilbert-space target); (2) Clifford+CCZ at SU(8) (3-qubit full compilation, not just CCZ-as-primitive); (3) generic SU(d) instance for documentation purposes. Ship Mathlib-PR-quality SU(d) Cartan substrate as community-citizenship deliverable.

**Predecessor work assumed clean:**
- Phase 6x lift/shift closure (T-A1 1Q-compiled-with-MS-primitive + T-A2 CCZ-substrate-only) — ships first.
- Phase 6u generic SU(2)-targeted substrate (Waves 1-6 + Wave 4b) — the SU(2) baseline being generalized.
- M.1 (`SKEFTHawking.MatrixBCHCubic.bch_order_2_cubic_thm`) — the underlying lemma is already generic over `{d : ℕ}` matrix dimension (`Matrix (Fin d) (Fin d) ℂ`). Phase 6x completion ships the `Matrix m m ℂ` reindex generalization + de-privatization at `Matrix.BCH.bchOrder2Cubic`. Phase 6y Track S can begin against the `(Fin d)`-indexed lemma since the `m : Type*` generalization is mechanical reindexing; Phase 6y consumers should use whichever form (Fin-indexed or m-indexed) is available when Track S sub-waves ship.

**Project rule applied:** No new project-local axioms (Pipeline Invariant #15 RESPECTED). No `maxHeartbeats` overrides in proof bodies (Invariant #10). The SU(d) extension work is multi-session and *substrate-heavy*; each track scopes the Mathlib-upstream option from Stage 1.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY PHASE 6y WAVE WORK:**
>
> 1. **Mandatory project bootstrap** per workspace `CLAUDE.md` Mandatory References list.
> 2. **Read this roadmap + the Phase 6x retrospective** (`docs/stakeholder/Phase6x_Implications.md`, `docs/stakeholder/Phase6x_Strategic_Positioning.md`) to understand WHY Phase 6y exists as a separate phase rather than as Phase 6x completion. The TLDR: Phase 6x's lift/shift framing yielded substantial substrate work to Phase 6y; this roadmap picks up that work.
> 3. **Read `Phase6u_Roadmap.md` end-to-end** — Phase 6y generalizes the Phase 6u SU(2)-targeted Generic substrate to SU(d). Familiarity with `GenericSU2GeneratingSet`, `GenericClosureDenseWitness`, `GenericSolovayKitaevRecursion`, `dnStepFG_su2`, `CartanFinalStep_SU2_v4` is mandatory.
> 4. **Critical substrate — read source directly:**
>    - **`SKEFTHawking.MatrixBCHCubic.bch_order_2_cubic_thm`** — already generic over `{d : ℕ}` matrix dimension; the load-bearing analytic substrate for SU(d) Cartan extension.
>    - **`SKEFTHawking.FKLW.CartanSubstrate.CartanFinalStep_SU2_v4`** (SU(2) version) and the discharge in `SU2BCHBracketClosure.lean::CartanFinalStep_SU2_v4_holds` — the SU(2) template the SU(d) ship generalizes.
>    - **`SKEFTHawking.FKLW.OneParameterSubgroupSU2.SU2_nhd_one_covered_by_exp_ts`** — the SU(2) local diffeomorphism that needs SU(d) generalization via IFT.
>    - **Mathlib's `NormedSpace.exp`, `HasStrictFDerivAt.exp`, `IsCompact.elim_finite_subcover`** — the upstream substrate the SU(d) ship composes on.
> 5. **Do not delegate substantive theorem proving to subagents** for the load-bearing SU(d) substrate extension sub-waves. MCP loop default; Aristotle is fallback. Background agents OK for Mathlib-API search + composition work.
> 6. **No PM / time estimates anywhere** — by user direction.
> 7. **Pivot rule re-clarified per the Phase 6x retrospective:** Invariant #15's "no project-local axioms" rule applies ONLY when an axiom is genuinely required (substrate missing from Mathlib4 AND no constructive path exists). It does NOT apply when work is substantial-but-doable. The Phase 6x retrospective explicitly catalogued this conflation as a failure mode; Phase 6y consumers should ship substantively across multiple sessions rather than yielding on "substantial work" grounds.

---

## Track catalog

Four primary tracks, organized by substrate dependency (highest-substrate-first; each later track consumes the prior):

  - **Track S** (SU(d > 2) substrate extension, lift Phase 6u to arbitrary dimension): **highest priority + load-bearing**. All downstream tracks depend on this.
  - **Track M-S** (Mathlib upstream of SU(d) substrate): runs in parallel with Track S; community-citizenship for the substrate.
  - **Track T-A1′** (full SU(4) trapped-ion compilation; "academic completeness" T-A1): consumes Track S, generalizes from the Phase 6x lift/shift T-A1.
  - **Track T-A2′** (full SU(8) Clifford+CCZ compilation; "academic completeness" T-A2): consumes Track S, generalizes from the Phase 6x T-A2 CCZ-matrix substrate.

**Status legend** (matches prior phases):
- ✅ **SHIPPED** — Lean / numerical deliverables committed and kernel-verified.
- 🟡 **IN-PROGRESS** — partial deliverables shipped.
- 📝 **WORKING DOC** — Stage-1 substrate-analysis or audit draft only.
- ⏳ **NOT STARTED**.

| Track | Codename | Status | Bundle absorption |
|---|---|---|---|
| **Track S** | SU(d > 2) substrate extension (the Phase 6u Generic substrate generalized to arbitrary d). The largest single deliverable: generalize `GenericSU2GeneratingSet` (carrier ρ_hom into SU(2) → ρ_hom into SU(d)), `CartanFinalStep_SU2_v4` → `CartanFinalStep_SUd_v4`, `dnStepFG_su2` → `dnStepFG_sud`, `Y_h` Lipschitz d-dependent. | ⏳ NOT STARTED | I1 substrate + D4 §9.8 multi-alphabet showcase extension |
| **Track M-S** | Mathlib upstream contributions extracting the SU(d) substrate from the project's Phase 6y ship to Mathlib4-PR-quality. Two anchors: (M-S.1) Generic Cartan v4 density-from-witness at SU(d); (M-S.2) `NormedSpace.exp` strict-F-derivative at zero for Lie subalgebras + the local diffeomorphism corollary. | ⏳ NOT STARTED | (Mathlib4 upstream; no project-bundle absorption) |
| **Track T-A1′** | Full SU(4) trapped-ion compilation (academic completeness): compile arbitrary `U ∈ SU(4)` via the Phase 6y SU(d) extension; MS(θ) + 1Q rotations no longer treated as primitives but compiled into the discrete alphabet. Consumes Track S; supersedes the Phase 6x T-A1 lift/shift ship as the "full" T-A1. | ⏳ NOT STARTED | D4 §9.8 multi-alphabet showcase + E1 cross-bridge |
| **Track T-A2′** | Full SU(8) Clifford+CCZ compilation (academic completeness): compile arbitrary `U ∈ SU(8)` via the Phase 6y SU(d) extension; CCZ no longer treated as primitive but compiled. Consumes Track S; supersedes the Phase 6x T-A2 CCZ-matrix-substrate ship. | ⏳ NOT STARTED | D4 §9.8 + fault-tolerant-architecture cross-bridge |

**Track dependencies:**
- Track S is the keystone; all others consume it.
- Track M-S can begin in parallel with Track S (extracting Mathlib-PR-quality presentations as Track S sub-waves ship).
- Track T-A1′ and Track T-A2′ are independent once Track S ships; can run in parallel.

---

## Track S detail — SU(d > 2) substrate extension

### Goal

Generalize the Phase 6u alphabet-agnostic quantitative Solovay-Kitaev substrate from SU(2)-targeted to SU(d)-targeted for arbitrary `d ≥ 2`. The shipped substrate enables **kernel-verified compilation of arbitrary unitaries in SU(d)** at any `d`, with error and length bounds at the same algorithmic compile level — the same shape as the Phase 6u SU(2) headline but at arbitrary dimension.

### Sub-wave decomposition

**S.1 — `GenericSUdGeneratingSet`** (~100-200 LoC). Generalize the `GeneratingSet` structure: replace `ρ_hom : W →* specialUnitaryGroup (Fin 2) ℂ` with `ρ_hom : W →* specialUnitaryGroup (Fin d) ℂ` for arbitrary d (parametrized at the structure level or via subtype). All downstream lemmas thread d through.

**S.2 — `CartanFinalStep_SUd_v4`** (~400-700 LoC; the biggest single piece). Generalize Phase 6p's `CartanFinalStep_SU2_v4` to SU(d). Conceptually:
  - Two ℝ-LI tangent flow lines in `𝔰𝔲(d)` (dimension `d² − 1`) ⟹ closed subgroup = ⊤.
  - For d = 2 (3-dim algebra), 2 LI tangents + 1 bracket = 3 = dim 𝔰𝔲(2). For d ≥ 3, the spanning argument requires more tangents OR a Lie-closure argument (the iterated brackets of 2 generic LI tangents span 𝔰𝔲(d) for any compact simple Lie group).
  - The local diffeomorphism `𝔰𝔲(d) → SU(d)` near identity via IFT on `expMap`. Mathlib4 v4.29.1 has the IFT (`HasStrictFDerivAt.toOpenPartialHomeomorph`) and the matrix `NormedSpace.exp` derivative at zero (`HasStrictFDerivAt.exp_zero`); composition gives the local diffeomorphism.
  - The open-subgroup-containing-identity-interior → ⊤ argument generalizes directly.

**S.3 — `dnStepFG_sud`** (~200-400 LoC). Generalize Phase 6t's Dawson-Nielsen balanced-commutator decomposition from SU(2) to SU(d). The SU(2) version uses Bloch-sphere parametrization; the SU(d) version uses the general `𝔰𝔲(d)` balanced-commutator existence theorem (which IS in the Aharonov-Arad lineage and SHOULD be generalizable).

**S.4 — `Y_h` Lipschitz d-dependent** (~150-300 LoC). The matrix-log Lipschitz constant in Phase 6u is π/2 (SU(2)-Bloch-specific). For SU(d), the constant depends on d via the operator-norm bound of the matrix exponential's inverse near the identity. Generalize.

**S.5 — Generic SU(d) discharge** (~300-500 LoC). The Phase 6u Wave 4b 800-LoC discharge generalized to SU(d) — uses S.1-S.4 above plus the existing `bch_order_2_cubic_thm` (already generic over d).

**S.6 — `solovayKitaev_dawson_nielsen_quantitative_generic_sud_strict_constructive_tight`** (~50-100 LoC). Wave 6's bundled-strict generic headline at SU(d).

### Aggregate Track S effort

~1,200-2,200 LoC across 5-8 sessions. The biggest single piece is S.2 (Cartan v4 at SU(d)); the others are mechanical generalizations.

### Audience

Mathlib4 working groups (Lie theory, matrix exponentials), formal-methods quantum-computing researchers (the SU(d) substrate is a one-time investment that unlocks all higher-dimensional gate-set Solovay-Kitaev ships).

### Risk

MEDIUM. The conceptual content is established (Phase 6u SU(2) version + the SU(d) generalization is standard Lie theory). The risk is in the LoE — the multi-session investment is real. No axioms required; no exotic substrate; just substantial composition.

---

## Track M-S detail — Mathlib upstream of SU(d) substrate

### Goal

Extract the Phase 6y Track S substrate as Mathlib-PR-quality contributions, generalizing the M.2 SU(2) presentation (Phase 6x) to the full SU(d) substrate.

### Sub-wave decomposition

**M-S.1 — Mathlib `Matrix.SpecialUnitary.Cartan.finalStepVd`** (~200-400 LoC). The SU(d) Cartan v4 density-from-witness as a Mathlib-conventional namespace entry. Builds on M.2 (which documented the SU(d) extension plan but shipped only SU(2)).

**M-S.2 — Mathlib `Matrix.expMap_isLocalHomeomorph_zero`** (~150-300 LoC). The general local diffeomorphism property of the matrix exponential at zero (the load-bearing substrate for both the SU(d) Cartan classification and the Phase 6u SU(2) ship). Mathlib4 v4.29.1 has the pieces (IFT + matrix exp derivative); the assembled local-homeomorphism statement is missing.

### Aggregate Track M-S effort

~350-700 LoC. Submission-step work + Mathlib reviewer iteration.

### Audience

Mathlib4 community (Lie theory, matrix exponentials, topological groups).

### Risk

LOW. Both M-S.1 and M-S.2 are well-understood mathematically. Submission-step costs are standard.

---

## Track T-A1′ detail — Full SU(4) trapped-ion compilation

### Goal

Generalize the Phase 6x T-A1 lift/shift ship (1Q-compiled + MS-primitive) to the **full SU(4) compilation**: arbitrary `U ∈ SU(4)` compiled via the Phase 6y SU(d) substrate at d = 4. MS(θ) and 1Q rotations are both in the discrete alphabet; the compiler decomposes any 2-qubit unitary.

### Sub-wave decomposition

**T-A1′.1 — `trappedIonGeneratingSetSU4`** (~100-200 LoC). The SU(4)-targeted `GeneratingSet` instance consuming Track S's `GenericSUdGeneratingSet` at d = 4. Generators: MS(θ) at rational-π/N grid + 1Q rotations on each ion at rational-π/N grid.

**T-A1′.2 — Closure-density witness at SU(4)** (~300-500 LoC). The MS(θ) + 1Q rotations alphabet generates a dense subset of SU(4); discharge via the Phase 6y SU(d) Cartan v4 substrate. (The mathematical content is well-known; the formalization is straightforward composition of Track S substrate.)

**T-A1′.{3,4,5} — ε₀-net + calibration + bundled-strict headline** (~200-400 LoC). Standard alphabet instantiation per Phase 6u T-S template, now at SU(4).

### Aggregate Track T-A1′ effort

~600-1,100 LoC across 2-4 sessions (assuming Track S substrate ships first).

### Audience

Industry quantum-compiler teams (Quantinuum, IonQ, AQT), trapped-ion-architecture-research community.

### Risk

LOW after Track S ships. The conceptual content is standard.

---

## Track T-A2′ detail — Full SU(8) Clifford+CCZ compilation

### Goal

Generalize the Phase 6x T-A2 CCZ-matrix-substrate ship to the **full SU(8) compilation**: arbitrary `U ∈ SU(8)` compiled via the Phase 6y SU(d) substrate at d = 8. CCZ is in the discrete alphabet (not primitive); the compiler decomposes any 3-qubit unitary using Clifford + CCZ generators.

### Sub-wave decomposition

**T-A2′.1 — `cliffordCCZGeneratingSetSU8`** (~100-200 LoC). The SU(8)-targeted `GeneratingSet` instance. Generators: per-qubit Hadamard (3 generators), CCZ (1 generator). The discrete alphabet has 4 generators; the closure is dense in SU(8).

**T-A2′.2 — Closure-density witness at SU(8)** (~400-700 LoC). Substantive — the Clifford+CCZ alphabet is known universal for SU(2^n) for any n, but the per-n density witness is non-trivial.

**T-A2′.{3,4,5} — ε₀-net + calibration + bundled-strict headline** (~200-400 LoC).

### Aggregate Track T-A2′ effort

~700-1,300 LoC across 3-5 sessions.

### Audience

Fault-tolerant-architecture researchers (Litinski, O'Gorman, Babbush, Beverland), magic-state-distillation researchers.

### Risk

MEDIUM. The closure-density witness at SU(8) for the Clifford+CCZ alphabet is the trickiest piece; literature on this (Aaronson-Gottesman 2004 and follow-ons) is well-developed but the Lean formalization is new.

---

## Cross-cutting work

### Adversarial-review checkpoints

Per `BUNDLE_LIFT_PROCEDURE.md` Stage 13 hard gate, each Phase 6y track gets its own checkpoint:

  - **CP-S** — after Track S (SU(d) substrate extension).
  - **CP-M-S** — after Track M-S Mathlib upstream PRs file / in-project PR-quality ships.
  - **CP-T-A1′** — after Track T-A1′ ships.
  - **CP-T-A2′** — after Track T-A2′ ships.

### Pipeline Invariants

- **#10 (no `maxHeartbeats`)**: RESPECTED. Phase 6u W4b pattern applies — top-level numerical helpers, not heartbeat-budget overrides.
- **#15 (no new axioms)**: RESPECTED. Phase 6y's substantive content does NOT require axioms; the SU(d) extension composes from Mathlib4 v4.29.1 primitives. The Phase 6x retrospective explicitly cautioned against conflating "substantial work" with "needs axiom"; Phase 6y consumers ship substantively across multiple sessions rather than yielding on "substantial work" grounds.

### M.4 length-conjunct inheritance (Phase 6x → Phase 6y)

The Phase 6x completion ship adds the concrete-word length-bound conjunct
`(compile U ε).toWord.length ≤ <polylog bound>` to all bundled-strict
headlines (CT, RR5, RR7, T-A1 lift/shift). **All Phase 6y bundled-strict
headlines (Track S.6 generic SU(d), Track T-A1′.5 full SU(4), Track
T-A2′.5 full SU(8)) inherit this conjunct shape** — i.e., each per-track
T-X.5 headline statement includes both the error bound `‖compile U ε - U‖ ≤ ε`
AND the concrete-word length conjunct. This is the explicit guardrail
against anti-pattern #4 (substrate-only-shipped vs headline-integrated)
identified in the Phase 6x retrospective.

---

## Cross-references

- **Phase 6x roadmap** (`docs/roadmaps/Phase6x_Roadmap.md`) — Phase 6x lift/shift completion ships first; Phase 6y picks up the deferred SU(d) extension work.
- **Phase 6x Implications** (`docs/stakeholder/Phase6x_Implications.md`) + **Strategic Positioning** (`docs/stakeholder/Phase6x_Strategic_Positioning.md`) — Phase 6x retrospective explains WHY Phase 6y exists as a separate phase.
- **Phase 6u roadmap** (`docs/roadmaps/Phase6u_Roadmap.md`) — the SU(2)-targeted Generic substrate being generalized.
- **Phase 6u Generic substrate**: `lean/SKEFTHawking/FKLW/Generic*.lean` (7 files) — the alphabet-agnostic chain Phase 6y generalizes to SU(d).
- **Mathlib4 v4.29.1 substrate**: `Mathlib.Analysis.NormedSpace.MatrixExponential`, `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`, `Mathlib.LinearAlgebra.UnitaryGroup` — the substrate Phase 6y composes on.
- **Phase 6x M.1 PR** (`lean/SKEFTHawking/MatrixBCHCubicMathlibPR.lean`) — the BCH cubic estimate, already generic over d, ready for use in Phase 6y Track S.
- **Phase 6x M.2 documentation** (`lean/SKEFTHawking/CartanFinalStepSUdMathlibPR.lean`) — the SU(d) extension plan documented in Phase 6x; Phase 6y Track S.2 ships the substantive proof.

---

## Wave 1 — Multi-session execution tracker (started 2026-05-27)

Per [[feedback-multi-session-wave-pattern]] (`memory/feedback_multi_session_wave_pattern.md`): Phase 6y is genuinely multi-session work. Wave 1 is the keystone Track S substrate + downstream T-X′ instantiations. Sessions ship per-AC-item substantively, with each session producing build-clean Lean modules + per-session memory.

### Wave 1 Status block

Phase 6y Wave 1: **IN PROGRESS** (Sessions 1-51 of N shipped 2026-05-27; **38 commits, ~4925 LoC kernel-only**; build clean 8830 jobs throughout).

- **AC items substantively shipped (UNCONDITIONAL)**: S.1, S.2 (S.2g UNCONDITIONAL), **S.3 d≥3 PROPER (Sessions 14-39, keystone `symmetric_balanced_commutator_hermitian_unconditional` Session 33)**, S.4 (explicit K=2), S.5 (UNCONDITIONAL), T-X′.1, T-X′.3 (F#5 algorithmic ε-net), T-A1′.4, T-A2′.4 calibration.
- **AC items partially shipped (substrate + 2 of 4 substantive ingredient discharges)**: S.6 cascade substrate + 2 of 4 substantive ingredients discharged:
  - **(1) `ExpIsud_det_eq_one_predicate` discharge ✓** (Session 49, spectral decomposition path; SU(d) analog of SU(2) `DetExpZeroOnSu2_SU2_discharged` ~2300 LoC)
  - **(2) `SkLevelPolylog_sud_spec` discharge ✓** (Session 48, K-parametric lift of SU(2) ~110 LoC `skLevel_polylog_spec`)
  - **(3) `skLength_sud` closed-form substrate ✓** (Session 51; substantive recursion-discharge + polylog asymptotic discharge remain)
  - **(4) `SkApproxCSuperQuadraticBound_generic_sud` discharge ✗** (analog of SU(2) ~981 LoC `SkApproxCSuperQuadraticBound_generic_holds`, multi-session)
- **AC items conditional/partial**: T-X′.2 (tracked-Prop framework + cascade UNCONDITIONAL from witness), M-S.1/2 (alias-only — per F#3, ALIAS-ONLY NOT ACCEPTANCE; substantive Mathlib-PR extraction pending).
- **AC items NOT YET shipped**: S.6/T-X′.5 polylog UNCONDITIONAL bundled-strict headlines (cascade-ready via Session 50's `skHeadline_FreeGroup_SUd_cascade_2ingredient`; require remaining 2 ingredient discharges + per-alphabet baseFinder), T-X′.2 substantive density witnesses (Brylinski-Brylinski SU(4) + Aaronson-Gottesman SU(8) — multi-session each), M-S substantive Mathlib-PR extraction, Stage-13 fresh-context adversarial review.

### Sessions 14-51 inventory (per-session map)

  - **Sessions 14-39** (Track S.3 keystone substrate chain): 27 modules in `lean/SKEFTHawking/FKLW/GenericSUd*.lean` building up to the keystone `symmetric_balanced_commutator_hermitian_unconditional` (Session 33) + predicate-form lifts + norm bridge + bounded form + index + usage examples + loose predicate.
  - **Session 41** (`GenericSUdDnStepFG.lean`): SU(d) Dawson-Nielsen step composing keystone.
  - **Session 42** (`GenericSUdExpIsuD.lean`): SU(d) exp coercion (det-conditional) + `ExpIsud_det_eq_one_predicate`.
  - **Session 43** (`GenericSUdSkApproxC.lean`): SU(d) SK recursion engine.
  - **Session 44** (`GenericSUdSkApproxCBound.lean`): super-quad bound predicate.
  - **Session 45** (`GenericSUdSkHeadlineCascade.lean`): F#4-compliant cascade composition.
  - **Session 46** (`GenericSUdSkLevelPolylog.lean`): polylog level chooser + spec predicate.
  - **Session 47** (`GenericSUdSkCascadeIndex.lean`): cascade INDEX documenting 4 substantive ingredients.
  - **Session 48** (`GenericSUdSkLevelPolylogSpec.lean`): **SUBSTANTIVE polylog level spec discharge** (ingredient 2).
  - **Session 49** (`GenericSUdExpIsuDDetDischarge.lean`): **SUBSTANTIVE det predicate discharge** (ingredient 1).
  - **Session 50** (`GenericSUdSkHeadlineCascade2Ingredient.lean`): refined 2-ingredient cascade leveraging Sessions 48 + 49.
  - **Session 51** (`GenericSUdSkLength.lean`): word-length closed-form substrate (ingredient 4 foundation).

### Remaining substantive work (post Session 51)

  1. **Super-quad bound discharge** (`SkApproxCSuperQuadraticBound_generic_sud K ε₀_sud gs baseFinder h_det_pred`) — analog of SU(2) Phase 6u Wave 4b ~981 LoC `SkApproxCSuperQuadraticBound_generic_holds`. Multi-session.
  2. **Length-bound recursion discharge** — proves `wordLength (skApproxC_generic_sud ... n U) ≤ skLength_sud baseCase decompCost n` (relating actual recursion word length to Session 51's closed-form).
  3. **`SkLengthPolylogBound_sud` substantive discharge** — asymptotic analysis of `skLength_sud (skLevel_polylog_sud K ε) ≤ c · (log(1/ε))^polylogExponent` (similar to SU(2) `skLength_at_skLevel_polylog_le` proof).
  4. **Per-alphabet baseFinder + ε-net** at SU(4)/SU(8) for T-A1′.5 / T-A2′.5 headlines.
  5. **T-X′.2 substantive density witnesses**: Brylinski-Brylinski 2002 (SU(4) trapped-ion entangler universality) + Aaronson-Gottesman 2004 (Clifford+CCZ at SU(8)). Multi-session each.
  6. **M-S.1/M-S.2 substantive Mathlib-PR extraction** (de-privatize + Mathlib-namespace + generic-type + docstrings + examples; per F#3 alias-only NOT acceptance).
  7. **Stage-13 fresh-context adversarial review pass** — CLOSURE gate; dispatched ONLY after ALL items above ship.

### Wave 1 Plan (per-session)

**Session 1 (SHIPPED 2026-05-27 — commits `c054842` → `de1c2c1`)**:
- Substrate ships at 8790 jobs clean, 0 axioms, 0 sorries. See `memory/project_phase6y_session_2026_05_27_shipped.md`.

**Sessions 2-13 (SHIPPED 2026-05-27)** — early S.3 d≥3 substrate buildup (σ-block primitives, conjugation invariance, partial discharges); see session memory.

**Sessions 14-39 (SHIPPED 2026-05-27 — Track S.3 d≥3 PROPER keystone chain)** — 27 modules building up to the keystone `symmetric_balanced_commutator_hermitian_unconditional` (Session 33) for ANY Hermitian-traceless H at SU(d) via spectral decomposition + symmetric F=αG construction with cross-term pair-swap cancellation. Plus predicate-form lifts (Sessions 34-35) + norm bridge (Session 36) + bounded form (Session 37) + index (Session 38) + usage examples (Session 39) + loose predicate (Session 40).

**Sessions 41-47 (SHIPPED 2026-05-27 — Track S.6 cascade substrate chain)**:
- Session 41: `dnStepFG_sud` (SU(d) DN step composing keystone)
- Session 42: `expIsud_conditional` (SU(d) exp coercion, det-conditional)
- Session 43: `skApproxC_generic_sud` (SU(d) SK recursion engine)
- Session 44: `SkApproxCSuperQuadraticBound_generic_sud` predicate
- Session 45: `skHeadline_FreeGroup_SUd_cascade` (F#4-compliant cascade composition)
- Session 46: `skLevel_polylog_sud` + spec predicate
- Session 47: Cascade INDEX (`GenericSUdSkCascadeIndex.lean`) documenting 4 substantive ingredients

**Sessions 48-51 (SHIPPED 2026-05-27 — Track S.6 substantive ingredient discharges, 2 of 4)**:
- **Session 48** (`09a939a`): **SUBSTANTIVE polylog level spec discharge** — `skLevel_polylog_sud_spec_holds` given calibration `K² · 2·ε₀_sud ≤ 1/4`.
- **Session 49** (`64c7e64`): **SUBSTANTIVE det predicate discharge** — `expIsud_det_eq_one_predicate_holds` via spectral decomposition + Matrix.exp_conj + Matrix.exp_diagonal + Matrix.det_diagonal + Pi.exp_def + Complex.exp_sum.
- **Session 50** (`4c3c4b7`): refined 2-ingredient cascade leveraging Sessions 48 + 49.
- **Session 51** (`a0594ef`): `skLength_sud` closed-form word-length substrate.

**Sessions 52-54 (SHIPPED 2026-05-27 — additional Track S.6 + per-alphabet substrate)**:
- **Session 52** (`27bd7f7`): UNCONDITIONAL `expIsud` at SU(d≥2) composing Sessions 42 + 49 (removes det-hypothesis).
- **Session 53** (`68934bc`): **SUBSTANTIVE length-bound recursion discharge** at SU(d), parametric wordLength. Lifts Phase 6x SU(2) proof mechanically.
- **Session 54** (`9389f38`): per-alphabet length-bound specializations at SU(4) trapped-ion + SU(8) Clifford+CCZ via `FreeGroup.norm_mul_le` + `FreeGroup.norm_inv_eq`.

**Sessions 55+ (PENDING) — remaining substantive ingredients**:
- Super-quad bound discharge (`SkApproxCSuperQuadraticBound_generic_sud`) — analog of SU(2) ~1236 LoC structure per Explore-agent intel; mechanically liftable (alphabet-agnostic via MonoidHom abstractions). Multi-session.
- Polylog asymptotic for length bound (`SkLengthPolylogBound_sud` discharge) — exponent mismatch with headline form's `log 5 / log 2`; needs sharper recursion analysis OR exponent revision.
- Per-alphabet length-bounded baseFinder construction at SU(4)/SU(8) — uses constructive ε-net substrate already shipped (`GenericSUdConstructiveEpsilonNet.lean`).
- T-X′.2 substantive density witnesses: Brylinski-Brylinski 2002 (SU(4)) + Aaronson-Gottesman 2004 (SU(8)). Each multi-session.
- Stage-13 fresh-context adversarial review (CLOSURE gate) — dispatched ONLY after all substantive items ship.

**Cumulative tally (Sessions 14-54)**: **41 commits, ~5310 LoC kernel-only**. Build clean 8833 jobs.

**Sessions 55-59 (SHIPPED 2026-05-27 — cascade closure substrate)**:
- **Session 55** (`109d31e`): length-bounded baseFinder discharge from constructive ε-net.
- **Session 56** (`6a9d011`): END-TO-END cascade `skHeadline_FreeGroup_SUd_cascade_final` reducing SU(d) headline to ONLY 2 substantive ingredients (D)+(B).
- **Session 57** (`4fdf4ba`): per-alphabet T-A1′.5 cascade-final at SU(4) trapped-ion → reduces T-A1′.5 to (D)+(B) at SU(4).
- **Session 58** (`7cf36fb`): per-alphabet T-A2′.5 cascade-final at SU(8) Clifford+CCZ → reduces T-A2′.5 to (D)+(B) at SU(8).
- **Session 59** (`da76a9a`): Phase 6y CASCADE CLOSURE STATUS INDEX (documentation, downstream + Stage-13 prep).

**Updated cumulative tally (Sessions 14-59)**: **46 commits + 2 docs syncs, ~6000 LoC kernel-only**. Build clean 8838 jobs.

**Sessions 70-82 (SHIPPED 2026-05-27 — F/G-norm bound chain for the (B) ingredient)**:
The F-norm bound `‖F‖ ≤ K_F·√(θ/2)` (the hardest sub-piece of the (B) super-quad
bound) is now FULLY discharged at the dnStep level via an explicit assembly chain:
- **Session 69** (`0ba7310`): bounded-form (F,G) at dnStep level (`‖F‖ ≤ (n+2)²·‖F_inner‖`).
- **Session 70** (`bc3fb0c`): σ_y/σ_x-block sum linftyOp norm bound (`‖∑γσ_y‖ ≤ ∑|γ|`).
- **Session 71** (`1777fb5`): permutation-conjugation linftyOp norm preservation.
- **Session 72** (`9253a01`): γ-sum algebraic decomposition (`∑√(θ·b/2) ≤ √(θ/2)·card·√B`).
- **Session 73** (`7207cad`): Hermitian eigenvalue ≤ linftyOp norm (Gershgorin).
- **Session 74** (`35dc0cc`): partial-sum arithmetic bound.
- **Sessions 75-78** (`babff73`/`a8a3c31`/`44166ec`/`23c51c2`): composed F_inner norm bound,
  γ-sum-of-abs capstone, bounded symmetric diagonal discharge, permMatrixAsUnitary conj bridge.
- **Session 79** (`a93ba94`): bounded FULL diagonal discharge `symmetric_balanced_commutator_diagonal_real_full_bounded` (threads S77+S78 through eigenvalue-sort conjugation).
- **Session 80** (`ef0e88e`): explicit-∑√ bounded Hermitian discharge `symmetric_balanced_commutator_hermitian_via_spectral_bounded_explicit` (re-threads S37 with S79 → `‖F‖ ≤ (n+2)²·∑√(θ·b'_p/2)`).
- **Session 81** (`b468965`): CONCRETE `K_F·√(θ/2)` bounded keystone `symmetric_balanced_commutator_hermitian_unconditional_bounded` (composes S80 + Gershgorin + γ-sum → `‖F‖ ≤ (n+2)²·(n+1)·√(n+2)·√(θ/2)` for ‖H‖≤1).
- **Session 82** (`60eb1fa`): RE-WIRED `dnStepFG_sud` to extract (F,G) from the bounded keystone (S81) + DISCHARGED `DnStepFG_sud_F/G_norm_bound_predicate` at `K_F = (n+2)²·(n+1)·√(n+2)`. Field projections preserved → all 8 downstream consumers unaffected (full build clean 8849 jobs).

**Session 83 (SHIPPED 2026-05-27 — `7f1bba8`)**: dnStepFG_sud structural extraction lemmas (`GenericSUdDnStepFGCommutator.lean`): `dnStepFG_sud_commutator_identity_valid` (`[F,G] = -matrixLog (n+2) Δ.val` in the valid branch) + `dnStepFG_sud_invalid_F_G_zero` (F=G=0 outside the regime). Refactored dnStepFG_sud's norm proof into named lemma `normalize_smul_norm_le_one`. Full build clean 8850 jobs.

**Sessions 84-87 (SHIPPED 2026-05-27 — `3d6f854`/`b10ceaf`/`65df43a`/`fcea8f6`)**: ALL super-quad per-step ingredients + MonoidHom abstractions: S84 `dnStepFG_sud_exp_neg_comm_eq_Delta` (exp(-[F,G])=Δ); S85 `expIsud_norm_sub_one_le` + inverse (≤ δ·exp δ, exact inverse via expIsud_inv_val_eq_exp_neg); S86 `dnStepFG_sud_gC_minus_Delta_norm_le_cubic` (≤320·δ³); S87 `ρ_hom_sud_mul/inv/groupCommutator_val` MonoidHom abstractions. `groupCommutator_stability_nearIdentity` already dimension-generic.

**Sessions 88-89 (SHIPPED 2026-05-27 — `3e8b5bb`/`ae1ebb9`)**: S88 CALIBRATION UNBLOCK — `K_compose_sud` bumped `1024·d^4 → 1024·d^16` (per-step K_proof ≈ 320·d^13 from cubic+telescoping; all K-parametric dependents rebuild unchanged, confirming the calibration architecture). S89 super-quad main-induction BASE CASE `skApproxC_generic_sud_zero_error_bound` (level-0 ≤ 2·ε₀) in new `GenericSUdSuperQuadInduction.lean`.

**Updated cumulative tally (Sessions 14-103)**: **~90 commits, ~9300 LoC kernel-only**. Build clean 8345 jobs. 🎯 S102 (B) DISCHARGED + S103 fed (B) into S.6 cascade → headline now conditional on (D)+regime+length only. Remaining: (D-SU4)/(D-SU8) density witnesses + regime/length discharge + UNCONDITIONAL headlines + M-S extraction + Stage-13. 🎯 S102 = (B) SUPER-QUAD BOUND DISCHARGED (SkApproxCSuperQuadraticBound_generic_sud_holds). The hardest (B) ingredient DONE; remaining: feed (B) into S.6 cascade + (D-SU4)/(D-SU8) density witnesses + M-S extraction + Stage-13. 🎯 S101 SINGLE-STEP VALID-BRANCH BOUND (skApproxC_sud_succ_super_quad_valid) integrates ALL (B) substrate. ONLY the Nat.rec wrap (with per-level regime establishment) remains for (B). S96 stability-through-Vn + S97-S99 numeric chain (THE arithmetic core: 334d^16 ≤ 1024d^16) + S100 F/G-norm-in-√ε. Remaining (B): final valid-branch integration (regime establishment via existential δ_lipschitz + matrixLog-in-su-d guards) + Nat.rec wrap. S93 cubic-term-through-Vn + S94 stability-term wrapper + S95 combine assembly: inductive-step telescoping ASSEMBLED; only numeric chain + Nat.rec wrap remain for (B). S91 = stability M-bound + poly F/G-norms; S92 = composition identity (inductive-step structural core). Remaining (B): telescoping core + numeric chain + Nat.rec wrap (carrying regime hypothesis). S90 = K_F polynomial bound (numeric-chain prep). EXISTENTIAL-REGIME finding: main-induction discharge carries explicit `2d·(2ε₀_sud) < δ_lipschitz(d)` regime hypothesis (S60 H-norm is existential-δ; honest, discharged downstream by fine ε-net).

**Sessions 104-108 (SHIPPED 2026-05-27/28 — regime-discharge substrate chain)**: the
**regime hypothesis** `h_regime` is the last conditional carried by the S.6 cascade
(alongside (D) density + length-polylog). These sessions build it toward an
unconditional discharge:
- **S104** (`GenericSUdRegimeGuards.lean`): `negI_smul_isHermitian_of_isSkewHermitian`
  + `negI_matrixLog_isHermitian_traceless_on_nhd_one` — `H = (-i)·log Δ` is
  Hermitian-traceless on a nbhd of 1.
- **S105**: `negI_matrixLog_herm_traceless_on_residual_nhd` — same on the residual
  `V⁻¹U` form.
- **S106**: `regime_thetabound_herm_traceless_on_residual_nhd` — adds the Lipschitz
  θ-bound `‖H‖ ≤ 2(n+2)‖V−U‖`.
- **S107** (`4c0ab56`): `regime_predicate_on_residual_nhd` — the **5-conjunct regime
  predicate** (θ-bound ∧ ‖H‖≤1 ∧ Herm ∧ traceless ∧ Δ∈target) on a residual nbhd
  `∃ δ>0, ∀ V U, ‖V−U‖<δ → …`, composing S106 + the ‖H‖≤1 derivation + target
  membership via `residual_norm_le_d_mul` + `expAmbientPartialHomeo_target_mem_nhds_one`.
- **S108** (`9a06ffa`): **DROPPED the `0 < ‖H‖` conjunct** from the super-quad chain
  (S84/S86/cubic_term/S101/S102/S103). This fixes a real defect — `h_regime` was
  UNIVERSALLY FALSE at `V = U` (where `H = 0`), so it could never be discharged
  unconditionally on the calibration ball. S84 now case-splits internally: at `H=0`
  the target round-trip forces `Δ=1`, the DN step gives `F=G=0`, and `exp(-[0,0])=1=Δ`.
  The cascade's `h_regime` now matches the exact 5-conjunct shape S107 proves.

**⚠️ Regime concrete-radius gap (the genuine remaining blocker)**: S107 gives the
regime predicate on a residual neighborhood of **existential radius** (`matrixLog` is
the IFT local inverse `(expAmbientPartialHomeo).symm`, whose `.target` is an
existential open set from `HasStrictFDerivAt.toOpenPartialHomeomorph`). The cascade's
`h_regime` needs it on the **calibration ball** `‖V−U‖ ≤ 2·ε₀_sud`. Bridging requires
a **concrete-radius matrix logarithm** (the Mercator power series
`log(1+X)=Σ(-1)^{k+1}X^k/k`, convergent for `‖X‖<1` with a *named* radius) replacing
the IFT `matrixLog`, plus its Lipschitz tail bound — a genuine multi-session
Mathlib-gap substrate (Mathlib has no Banach-algebra log with a known radius). The
existential radius cannot be made quantitative (no nameable lower bound), so no choice
of `K`/`ε₀` closes it; only a concrete construction does.

**Truly remaining substantive work (post S108 — (B) is DISCHARGED; 4 named items + 1 review)**:
  0. **(B) Super-quad MAIN INDUCTION discharge ✓ DONE** (S102 `SkApproxCSuperQuadraticBound_generic_sud_holds`, fed to the cascade by S103). Calibration resolved by S88 (`K_compose_sud = 1024·d^16`). No longer a blocker.
  1. **Regime concrete-radius substrate** (the closest-to-done headline blocker) — replace the IFT `matrixLog` with a concrete-radius Mercator power-series matrix log to bridge S107's existential-radius regime predicate to the calibration ball `‖V−U‖ ≤ 2·ε₀_sud`. **Brick 1 SHIPPED (S109, `e37ad01`, `GenericSUdMatrixMercatorLog.lean`)**: `matrixMercatorLog X = ∑'(-1)^n/(n+1)•X^(n+1)` with named-radius convergence (`summable_matrixMercatorLog` for `‖X‖<1`) + explicit bound `‖·‖ ≤ ‖X‖/(1−‖X‖)` + concrete-radius K=2 Lipschitz `‖·‖ ≤ 2‖X‖` on `‖X‖≤1/2`. **Brick 2a SHIPPED (S110, `de322c9`)**: `matrixMercatorLog_commute_self` (`Commute X (matrixMercatorLog X)`) + `matrixMercatorLog_commute_one_add` — the commutation the round-trip's exp-path derivative needs. **Remaining bricks**: (2) exp/log round-trip `exp(matrixMercatorLog X) = 1 + X` on the ball; (3) agreement `matrixMercatorLog (Δ−1) = matrixLog d Δ` for `Δ` near 1 (via local exp injectivity), discharging the regime θ-bound + `Δ∈target` on the concrete ball. After all three, `h_regime` discharges UNCONDITIONALLY and S.6/T-X′.5 reduce to (D)+length only.

  **⚠️ Brick 2 (round-trip) — KEY OBSTRUCTION + EXECUTABLE PLAN (for the next dedicated session)**: Mathlib's clean exp-derivative `hasFDerivAt_exp` (`NormedSpace.exp x • 1` at `x`) requires **`NormedCommRing 𝔸`** — the matrix algebra `Matrix (Fin d) (Fin d) ℂ` is **non-commutative**, so it does NOT apply directly (the non-commutative `d/dt exp(A(t))` is the integral `∫₀¹ exp(sA)·A'·exp((1−s)A) ds`, simplifying to `exp(A)·A'` ONLY when `A,A'` commute — which is why S110's commutation was shipped first). **Recommended route**: the derivative argument `f(t) = exp(−matrixMercatorLog(t•X))·(1 + t•X)`, `f'(t)=0`, `f(0)=1` ⟹ `f(1)=1`, restricted to the **commutative closed subalgebra `A_X` generated by `X`** (where `matrixMercatorLog(t•X)`, its derivative `X·(1+t•X)⁻¹` via Neumann, and `1+t•X` all live and pairwise commute), so `hasFDerivAt_exp` applies inside `A_X`. **Enabling Mathlib lemmas identified**: `hasFDerivAt_exp` (commutative exp deriv — applies INSIDE `A_X` only), `mul_neg_geom_series (x) (‖x‖<1) : (1−x)·∑'xⁿ = 1` + `Summable.one_sub_mul_tsum_pow`/`.tsum_pow_mul_one_sub` (Neumann inverse — **already off-the-shelf for the matrix algebra, do NOT re-derive**; gives `(1+t•X)⁻¹ = ∑(−t•X)ⁿ` for the log-derivative), `NormedRing.inverse_one_sub` + `hasFPowerSeriesOnBall_inverse_one_sub`, `HasFPowerSeriesOnBall.hasFDerivAt` (term-by-term differentiation of `matrixMercatorLog(t•X)`). The two HARD crux steps with no off-the-shelf lemma: (iii) `HasDerivAt (fun t => matrixMercatorLog (t•X)) (X·(1+t•X)⁻¹) t` (term-by-term differentiation of the log power series), and (iv) `HasDerivAt (fun t => exp(A(t))) (exp(A(t))·A'(t)) t` for commuting `A,A'` (the commutative-subalgebra exp-path derivative — `hasFDerivAt_exp` needs `NormedCommRing`). Substantial multi-lemma analytic substrate — a dedicated session.

  **⚠️⚠️ Crux (iii) ROOT-CAUSE finding (Sessions 112-113 attempts — instance-pollution diamond)**: the per-term derivative `HasDerivAt (fun s : ℝ => c_n • ((↑s:ℂ)•X)^(n+1)) (((-1)^n·(↑s)^n) • X^(n+1)) s` is mathematically clean (coefficient `(n+1)·c_n = (-1)^n` collapses; assemble via `Complex.ofRealCLM.hasDerivAt` + `HasDerivAt.pow` + `HasDerivAt.smul_const`). **THE DEEP BLOCKER (diagnosed via `lean_run_code`)**: `Matrix.linftyOpNormedAddCommGroup` (a *local instance* the whole file needs for `‖·‖`) supplies its OWN `AddCommGroup` and hence its own ℝ-module path (`NormedSpace.complexToReal`-derived, `inst.toModule`), which is a **NON-DEFEQ diamond** with the standard `Matrix.addCommGroup`/Pi ℝ-module that the goal and the `Complex.ofRealCLM`/`smul_const` calculus machinery resolve to. Concretely: `smul_const`'s output `HasDerivAt` lands in `linftyOpNormedAddCommGroup.toAddCommGroup`+`inst2.toModule`, but the goal (post-`rw`) sits in `Matrix.addCommGroup`+default `module` — `exact` fails with a genuine type mismatch, and the surfaced "`IsScalarTower ℝ ℂ (Matrix ℂ)` not synthesized" is a *symptom* of `smul_const` searching the tower over the wrong module path. **This is instance pollution specific to doing CALCULUS (ℝ-module + norm together) on `Matrix ℂ` under the linftyOp norm** — bare `inferInstance` finds each instance, but `smul_const` mixes the two module diamonds. **✅ RESOLVED (Session 112, `ec55dbb`)**: option (c) — bundle the ℂ-smul into a continuous ℝ-linear map `g : ℂ →L[ℝ] Matrix ℂ`, `g z = z • X^(n+1)` (`(id ℂ).smulRight (X^(n+1)) |>.restrictScalars ℝ`), and differentiate via `g.hasFDerivAt.comp_hasDerivAt` — sidesteps `smul_const` and the module diamond entirely. `hasDerivAt_matrixMercatorLog_term` SHIPPED (per-term derivative `d/dt[c_n•((↑t)•X)^(n+1)] = ((-1)^n·(↑t)^n)•X^(n+1)`, kernel-only). **✅ CRUX (iii) COMPLETE (Sessions 113-114, `78f93bb`/`61a02bd`)**: `summable_matrixMercatorLog_deriv_series` + `tsum_matrixMercatorLog_deriv_eq` (`∑' ((-1)^n(↑t)^n)•X^(n+1) = (1+(↑t)•X)⁻¹·X` via `geom_series_eq_inverse`) + `hasDerivAt_matrixMercatorLog_path` (`d/dt[matrixMercatorLog((↑t)•X)] = (1+(↑t)•X)⁻¹·X` for `|t|·‖X‖<1`, assembled via `hasDerivAt_tsum_of_isPreconnected` on `ball 0 R`, `|t|<R<1/‖X‖`). **✅ CRUX (iv) COMPLETE (Session 115, `df209e7`)**: `hasDerivAt_exp_path` — `d/dt[exp(A t)] = exp(A t₀)·A'` for a commuting path, built from `exp_add_of_commute` + `hasStrictFDerivAt_exp_zero` (~20 LoC; Mathlib lacks the non-commutative general version). **Remaining brick 2 (ONLY the round-trip assembly left)**: apply crux iv with `A t = −matrixMercatorLog((↑t)•X)` (values pairwise commute via `matrixMercatorLog_commute_mercatorLog`, S111) + crux iii (`hasDerivAt_matrixMercatorLog_path`) to show `f(t)=exp(−mLog(t•X))·(1+t•X)` has `f'(t)=0` on `[0,1]` (via product rule + commutation; the bracket `−exp(...)·(1+tX)⁻¹·X·(1+tX) + exp(...)·X = 0` since everything commutes) and `f(0)=1` ⟹ `f≡1` (`is_const_of_deriv_eq_zero` / MVT) ⟹ `exp(matrixMercatorLog X)=1+X`. Then brick 3 (agreement `matrixMercatorLog(Δ−1)=matrixLog d Δ` via local exp injectivity + concrete ball ⊆ target). **Historical re-scope options (now moot for crux iii, but relevant if crux iv hits the same diamond — it won't, same CLM fix applies)**: (a) reconcile the diamond — prove `linftyOpNormedAddCommGroup.toAddCommGroup`'s ℝ-module is defeq/`Subsingleton`-equal to the standard one and force one path via `@`-explicit instances or `convert ... using 1` + `AddCommGroup`-congruence (painful but local); (b) **PIVOT to a non-derivative round-trip proof** (Cauchy product of the exp/log series, or the dense-diagonalizable + continuity route) that avoids ℝ-module calculus entirely — likely the cleaner path given the diamond; (c) prove the round-trip in a norm whose `NormedAddCommGroup` shares the standard Matrix `AddCommGroup` (e.g. a Pi/Frobenius norm) then transfer the equation (norm-independent) back. The mathematical skeleton (Neumann `(1+t•X)⁻¹` off-the-shelf; `hasDerivAt_tsum_of_isPreconnected` on `ball 0 (1/‖X‖)`) is unchanged once the module path is settled.
  2. **(D-SU4) Density witness at SU(4) trapped-ion** — Brylinski-Brylinski 2002 entangler universality. Multi-session entangler-theoretic content.
  3. **(D-SU8) Density witness at SU(8) Clifford+CCZ** — Aaronson-Gottesman 2004 Clifford-stabilizer lineage. Multi-session.
  4. **Length-bound polylog exponent caveat** — headline form's `log 5 / log 2` exponent revision OR sharper recursion analysis.
  5. **Stage-13 fresh-context adversarial review pass** — CLOSURE gate; dispatched ONLY after items 1-4 ship (i.e. once the UNCONDITIONAL S.6/T-X′.5 headlines exist).

### Wave 1 References

- **Roadmap**: this file (Phase 6y) + Phase 6x retrospective (`docs/stakeholder/Phase6x_Implications.md`).
- **SU(2) Phase 6u/6t substrate**: `lean/SKEFTHawking/FKLW/SU2BalancedCommutator.lean::balanced_commutator_general_axis_lie_traceless` (the d=2 model for S.3); `lean/SKEFTHawking/FKLW/CliffordTV4WitnessUnconditional.lean` (Phase 6u substantive density discharge model).
- **Phase 6y substrate in flight**: `lean/SKEFTHawking/FKLW/Generic*.lean` (~25 files); `lean/SKEFTHawking/FKLW/TrappedIonSU4*.lean` (~6 files); `lean/SKEFTHawking/FKLW/CliffordCCZSU8*.lean` (~6 files).
- **Spawn-task chips queued** (one-click resumption per session): S.3 d≥3 Aharonov-Arad; T-X′.2 substantive density; M-S Mathlib-PR extraction.

### Wave 1 Session-handoff contract

Per [[feedback-multi-session-wave-pattern]]: when picking up Wave 1, FIRST:
1. Read this §"Wave 1" block end-to-end.
2. Read the latest session memory (`project_phase6y_session_*.md` — most recent date).
3. Verify the latest committed Lean module(s) compile (`lake build` from `lean/`).
4. Proceed to next-session PENDING items (per §"Wave 1 Plan" above).
5. Each session ships build-clean modules + per-session memory entry.

The stop hook from the controlling `/goal` is the **session-end indicator**, NOT a "keep grinding" signal — when it fires, save per-session memory, commit, end the session cleanly. A new session in fresh context picks up the next Wave 1 item per the handoff contract.

