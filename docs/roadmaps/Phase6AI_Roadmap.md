# Phase 6AI — Constructive diamond-norm optimal witness (MOONSHOT D, public)

**Status:** PLANNED (opened 2026-06-02). Public-only. The arc's last analytic frontier — but
**reframed**: the primary target is a *constructive* optimal-witness extractor, not the abstract
`diamondDist = dual-optimum` equality.

**Why constructive, not abstract.** The directly-useful object is: *given any channel pair, produce
the dual witness `W*` that achieves the diamond distance* (so the exact value is `‖Tr₂ W*‖_∞` for an
explicit `W*`). This is strictly better than the abstract equality on BOTH axes — (i) more reachable,
because it sidesteps general conic duality entirely (it's an explicit construction + the already-shipped
weak-dual bound, not a Slater/minimax/Fenchel argument), and (ii) more usable, because a downstream
numeric routine can run the construction and the Lean theorem backs the exact value. The abstract
equality `diamondDist_eq_choiSDP` then follows as a corollary (an attained witness ⟹ primal=dual).

**The fence we are attacking.** 6AF/6AG proved BOTH one-sided bounds of the Watrous Choi sandwich and
the weak-dual witness bound `diamondDist_le_dual_witness` (any feasible dual witness ⟹ upper bound).
What remains is the EQUALITY: `diamondDist(Φ₁,Φ₂) = inf{ ‖Tr₂ W‖_∞ : W ⪰ 0, W ⪰ J(Φ₁)−J(Φ₂) }`
(strong duality). The earlier fan-out fenced this on "Mathlib pin has no zero-gap SDP / Slater /
minimax / Fenchel." **But that fence is about *imported general* conic duality — the project's track
record is that such fences fall to constructive routes.** We already have, constructively:
- **Attainment** (`exists_diamondDist_eq`): the primal `sSup` is a genuine max.
- **Per-channel exact strong duality**: `diamondDist_dephasing_eq`, `diamondDist_depolarizing_eq` were
  proven by exhibiting an OPTIMAL dual witness matching the primal lower bound — i.e. strong duality
  ALREADY holds by explicit construction for those channels.

**Thesis:** strong duality for the diamond norm may be provable WITHOUT general conic duality, by an
explicit primal-optimizer → dual-witness construction (Watrous's constructive proof: from the optimal
input `ρ*` and the structure of `(Φ⊗id)`, build the matching witness `W*` with `‖Tr₂ W*‖ =
diamondDist`). The whole point of a moonshot is to find out if the constructive route exists.

**Invariants:** kernel-pure; **NO new project-local axiom without explicit user sign-off** — if the
proof appears to need an SDP-duality axiom, STOP and present the recommendation. Fence-discipline: any
NEW sub-fence requires interactive lean4 scouting + a grep/`lean_local_search`-verified written
blocker, never a hand-wave.

---

## Wave 6AI.0 — Mathlib scouting (interactive lean4 skill, NOT deep research)

Map, via `lean_local_search`/`lean_leansearch`/`lean_loogle`/`lean_state_search`, exactly what the
pinned Mathlib (v4.29.1) provides toward strong duality:
- minimax / `inf_iSup` ↔ `iSup_inf` swaps, von Neumann minimax, Sion;
- conic / LP / SDP duality, `Convex`/`ConvexCone` separation, Hahn–Banach separation in fin-dim;
- Lagrangian / Fenchel conjugate / biconjugate; KKT.
Output: a written table of "present / absent / partially-present" with exact lemma names. This decides
which of Waves 6AI.1 vs 6AI.2 is viable. **Gate:** if NOTHING usable is present and the constructive
route (6AI.2) also stalls after a genuine attempt, FENCE with the verified table and stop — do not
ship an axiom.

## Wave 6AI.1 — Abstract route (if minimax/separation substrate exists)
If Mathlib has fin-dim Hahn–Banach separation (`geometric_hahn_banach_*`) or a usable minimax, build:
weak duality (have it) + a separating-hyperplane argument that the duality gap is zero for this
specific SDP (the feasible sets are compact + the Slater point `W = (‖C‖+1)·1` is strictly feasible).
Headline `diamondDist_eq_choiSDP`.

## Wave 6AI.2 — Constructive route (Watrous primal→dual witness; PRIMARY)
Generalize the per-channel exact constructions. From the attained optimal input `ρ*` (and its
purification / the spectral data of `(Φ₁⊗id − Φ₂⊗id)ρ*`), construct the optimal witness `W*`
explicitly and prove `‖Tr₂ W*‖_∞ = diamondDist`. Sub-bricks:
- characterize the primal optimizer's Choi/marginal structure;
- build `W*` from the positive part of the optimal Hermitian difference (the dephasing/depolarizing
  witnesses `γ·vvᵀ`, `(2p/3)P₊` are the templates — generalize the pattern);
- prove the matching `le_antisymm` against `diamondDist_le_dual_witness`.

## Wave 6AI.3 — Consolidation
`diamondDist_eq_choiSDP` headline; re-express the named-channel exacts as corollaries; D6 §6 +
preprint update ("the last QI analytic frontier closed / honestly fenced"); Stage-13.

---

## Phase exit (two acceptable outcomes, per quality standard)
EITHER (a) `diamondDist_eq_choiSDP` PROVEN kernel-pure (no new axiom) — the frontier closed; OR
(b) a genuinely-blocked FENCE with an interactive-lean4-verified written blocker (exact missing
Mathlib lemmas) + a documented argument that no constructive route is feasible at this pin, presented
to the user. NO axiom shipped without explicit sign-off. Counts/docs/memory synced either way.

---

## OUTCOME (2026-06-02, autonomous /goal) — general constructive witness SHIPPED; strong-duality equality ROUTE MAPPED (continuation, not fenced)

**Wave 6AI.0 scout (interactive lean4 on Mathlib v4.29.1).** PRESENT: geometric Hahn–Banach
separation (`geometric_hahn_banach_compact_closed`, `RCLike.geometric_hahn_banach_*`,
`geometric_hahn_banach_point_closed`), cone separation `ProperCone.hyperplane_separation`,
`ProperCone.innerDual` + bipolar `ProperCone.innerDual_innerDual`, order-theoretic saddle point
`isSaddlePointOn_value` + easy minimax `iSup₂_iInf₂_le_iInf₂_iSup₂` (Mathlib.Order.SaddlePoint),
Krein–Milman. **ABSENT** (verified — searched leansearch/loogle/local): analytic Sion / von Neumann
minimax for concave–convex real functions; Fenchel conjugate biconjugate duality theorem; any conic /
SDP / LP strong-duality (Slater zero-gap) theorem; KKT. ⟹ both abstract routes (6AI.1 minimax,
Fenchel) lack a ready theorem; raw-Hahn–Banach zero-gap assembly for the operator-norm-objective LMI
is multi-week.

**SHIPPED (Wave 6AI.2, constructive, the reachable toehold):** `DiamondNormWitness.lean` (root-imported,
kernel-pure) — `diamondDist_le_ptrace2_posPart`: for ANY channel pair, the positive part
`C₊ = (J(Φ₁)−J(Φ₂))₊` is an explicit dual-feasible witness (`posPart_choiDiff_sub_posSemidef`:
`C₊ − C = C₋ ⪰ 0`), giving the general constructive upper bound `diamondDist ≤ ‖Tr₂ C₊‖`. Helper
`posPart_sub_self_eq_negPart` (general `C₊ − M = C₋`, via `sub_sub_cancel` to dodge the
proof-dependent-motive `rw`). Generalizes `diamondDist_le_choi_opNorm` and unifies the per-channel
optimal witnesses (it IS `C₊` for the covariant Pauli/dephasing/depolarizing family; loose for
amplitude damping whose worst-case input is a product state, not max-entangled).

**ROUTE MAPPED — strong-duality EQUALITY is an in-progress continuation, NOT a fence (Explore fan-out
2026-06-02).** The general equality `diamondDist = inf{‖Tr₂ W‖ : W ⪰ 0, W ⪰ C}` IS reachable at this
pin. Mathlib ships genuine conic strong duality: `ProperCone.hyperplane_separation` /
`ProperCone.relative_hyperplane_separation` / `hyperplane_separation_of_notMem` (`Cone/InnerDual.lean`)
= the Farkas / cone-image strong-duality equivalence; bipolar `innerDual_innerDual`;
`geometric_hahn_banach_compact_closed` (`LocallyConvex/Separation.lean`). The ONLY concrete missing
object is a **real Frobenius `InnerProductSpace ℝ` on self-adjoint matrices** (`⟪A,B⟫ = re (A·B).trace`);
Mathlib's matrix inner products are ℂ-valued + PSD-weighted (private), so this one instance must be
built (`InnerProductSpace.ofCore` on `selfAdjoint (Matrix (Fin d) (Fin d) ℂ)`, which already carries
the ℝ-module `selfAdjoint.instModule…`). NO Sion minimax / Fenchel needed (absent but unused).

**Brick sequence (continuation):**
1. ✅ **DONE (2026-06-03, commit `f1b08b69`, `SelfAdjointInnerProduct.lean`, kernel-pure, root-imported,
   full build 9048 jobs no instance pollution):** `selfAdjointInnerProductSpace :
   InnerProductSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ))`, `⟪A,B⟫ = Re tr(A·B)`, via
   `InnerProductSpace.ofCore` (Core fields: symmetry=`trace_mul_comm`; nonneg/definite=
   `posSemidef_conjTranspose_mul_self`+`PosSemidef.trace_eq_zero_iff`+`conjTranspose_mul_self_eq_zero`;
   `selfAdjoint_inner_eq` computes by `rfl`). The SDP linchpin — cone-duality engine now applies.
2. `ProperCone.positive ℝ E` for the PSD cone; closedness from finite-dim PSD-closed conditions.
3. Slater point `W₀ = (‖C‖+1)·1` (PosDef, strictly dominates `C`).
4. Compactness of `S_R = {W ⪰ 0, W ⪰ C, ‖W‖ ≤ R}` via `Metric.isCompact_of_isClosed_isBounded`
   (finite-dim ProperSpace) ⇒ dual inf ATTAINED (`IsCompact.exists_isMinOn`).
5. `hyperplane_separation` on the primal-optimal point ⇒ separating functional = optimal primal
   density (via `InnerProductSpace.toDual`); complementary slackness `⟪W*−C, Y⟫ = 0` ⇒
   `g(W*) = diamondDist`. Headline `diamondDist_eq_choiSDP`.
The constructive `C₊` upper bound + per-channel covariant exact strong duality are already shipped;
this continuation closes the general equality. NO axiom.

### Continuation progress (2026-06-03, autonomous /goal "complete 6AI without fencing")
- ✅ **`≤` direction DONE** (`4ca541e9`, `DiamondSDP.lean`): `choiDualValue` def + `diamondDist_le_choiDualValue` (weak duality).
- ✅ **Dual-attainment foundational lemmas DONE** (`a8d7a291`, `DiamondSDPAttainment.lean`, kernel-pure,
  root-imported): `trace_ptrace2` (`tr(Tr₂ W) = tr W`); `dualObjective_trace_bound`
  (PSD `W ⇒ Re tr W ≤ card·‖Tr₂ W‖`, the boundedness seed — composes `traceNorm_posSemidef` +
  shipped `traceNorm_le_card_mul_l2opNorm`).
- ✅ **op≤trace bridge + boundedness DONE** (`70f1b453`, `DiamondSDPAttainment.lean`): `opNorm_le_of_mul_conjTranspose_le_sq`
  (`‖K‖ ≤ c` from `c²•1 − K·Kᴴ ⪰ 0`; generalized the `c=1` EuclideanLin `opNorm_le_one`, 🔑 tail coercion fix
  `show ((c^2:ℝ):ℂ) = RCLike.ofReal (c^2) from rfl` bridges Complex.ofReal→RCLike.ofReal so
  `RCLike.re_ofReal_mul` fires) → `l2opNorm_le_traceNorm_psd` (`‖W‖ ≤ traceNorm W` for PSD W, via CFC Loewner
  `W·W ⪯ (traceNorm W)²•1` using `isHermitian_mul_self_eq_cfc_sq`+`cfc_const`+`cfc_sub`+`cfc_posSemidef` and
  `IsHermitian.trace_eq_sum_eigenvalues`+`Finset.single_le_sum` for eigenvalue ≤ trace) → `l2opNorm_bound_of_dual_feasible`
  (PSD dual witness with `‖Tr₂ W‖ ≤ B` has `‖W‖ ≤ card·B`).
- ✅ **DUAL ATTAINMENT DONE** (`e164ea96`): `isClosed_posSemidef` (PSD set closed, mirrors `isClosed_isDensityOperator`) +
  `continuous_ptrace2` → **`exists_choiDualValue_eq`**: the dual sublevel `{W⪰0, W⪰C, ‖Tr₂ W‖ ≤ ‖Tr₂ C₊‖}` is compact
  (`Metric.isCompact_of_isClosed_isBounded`), the continuous objective `‖Tr₂ ·‖` attains its min there via
  `IsCompact.exists_isMinOn`, and that min = `choiDualValue` (inf over all feasible). Gives an EXPLICIT optimal dual
  witness `W*` with `‖Tr₂ W*‖ = choiDualValue`. 🔑 the `L2Operator`-scoped-instance topology cooperates with the
  Frobenius-proved closedness lemmas (finite-dim, no instance pollution).
- ✅ **R3 helper DONE** (`0bd63b5f`): `inMarginal_le_one` (`1 − inMarginal ρ ⪰ 0` for `IsDensityOperator ρ`,
  via `l2opNorm_le_traceNorm_psd` ⟹ `‖inMarginal ρ‖ ≤ tr = 1` + `cfc(1−x)`). Feeds dual feasibility.

### FINAL BRICK fully mapped (zero-gap `≥`, opus design-agent + weak-dual-chain analysis 2026-06-03)
**Route decision: A (constructive Watrous primal→dual witness), NOT B (abstract cone).** Route B verified-blocked at
pin: NO PSD-matrix `ProperCone` / NO `PartialOrder (selfAdjoint (Matrix …))` in Mathlib, and `ProperCone.map` is a
*topological closure* so `relative_hyperplane_separation` gives feasibility only up-to-closure (residual closed-image
gap). Route A reuses the already-proven primal analysis.

**The weak-dual chain (`diamondDist_le_dual_witness`, DiamondNormDual.lean:174-185) IS the map.** For attained `ρ*`
(`exists_diamondDist_eq`), `T = (Φ₁⊗id−Φ₂⊗id)ρ*`, `P = posProj T`:
`diamondDist = eigPosSum T = Re tr(C·M(P,ρ*)) ≤ Re tr(W·M(P,ρ*)) ≤ Re tr(W·M(1,ρ*)) = Re tr(Tr₂W·inMarginal ρ*) ≤ ‖Tr₂W‖·tr(inMarginal ρ*) = ‖Tr₂W‖`
(`M = choiContraction`). The `≥` needs a feasible `W*` making ALL THREE `≤` tight:
  (i) `tr((W*−C)·M(P,ρ*)) = 0` (complementary slackness, `W*−C⪰0 ⟂ M(P,ρ*)⪰0`);
  (ii) `tr(W*·M(1−P,ρ*)) = 0`; (iii) Hölder tight: `Tr₂W*` aligns with `inMarginal ρ*` (scalar on its support).
Then `‖Tr₂ W*‖ = diamondDist` ⟹ `csInf_le` ⟹ `choiDualValue ≤ diamondDist` ⟹ `le_antisymm` ⟹ **`diamondDist_eq_choiSDP`**.
- Brick 0 (csInf reduction), 1 (extract ρ*/P, transcribe primal-value identity), 6 (assemble): ROUTINE.
- Brick 3 (`W*⪰0`), 5 (objective `≤ diamondDist`): MODERATE. R3 (`inMarginal_le_one`): DONE.
### ⚡ BLOCKER PINPOINTED (prototyping agent, 2026-06-03) — topology instance diamond, not "multi-week"
**Avenue 1 (explicit `W*`) is a general dead-end** (verified): no closed-form `W*(ρ*,P,C)` satisfies the 3
complementary-slackness conditions for non-covariant channels; the per-channel witnesses exploit Pauli-covariance
(`ptrace2 W = c·1` scalar). General `≥` genuinely needs conic strong duality (avenue 2/3).
**Avenues 2/3 (Hahn–Banach / ProperCone) are reachable — Mathlib HAS the engine** (`ProperCone.relative_hyperplane_separation`
= Farkas, `geometric_hahn_banach_compact_closed`, both verified present) — **blocked ONLY by a topology instance diamond:**
`selfAdjoint (Matrix ι ι ℂ)` carries TWO non-defeq topologies — `instTopologicalSpaceSubtype` (global default) vs the
metric topology from `selfAdjointNormedAddCommGroup` (`InnerProductSpace.ofCore`). `rfl` fails between them ⟹
`ContinuousSMul ℝ` / `CompleteSpace` / `LocallyConvexSpace` (all REQUIRED by the separation lemmas) fail to synthesize.
`FiniteDimensional ℝ` IS provable but doesn't repair the diamond; `local instance` / type-alias `def` don't override the
subtype topology (all verified by the agent in `lean_run_code`).
**FIX (the linchpin brick) — single-topology carrier.** Either (a) `EuclideanSpace ℝ (Fin d)` (d = real-dim = card²)
via a `LinearIsometryEquiv` from the Hermitian matrices [all instances verified clean; transport PSD cone + `ptrace2` +
`W↦W−C` = medium-high index bookkeeping], OR (b) a single-field `structure SAW where val : selfAdjoint …` [verified no
leaking topology; re-derive AddCommGroup/Module ℝ/Core = medium mechanical]. **Then:** PSD-as-`ProperCone ℝ E`
(`ProperCone = ClosedSubmodule {0≤·}`; build from `isClosed_posSemidef`) → encode dual feasibility as a cone-image
membership → `relative_hyperplane_separation`, handling `ProperCone.map`=closure via finite-dim closed-image
(`isClosed_posSemidef` + the `DiamondSDPAttainment` compactness). **Several-hundred-line multi-brick build, NO fence, NO axiom.**
- ✅ SHIPPED (`8d524ba0`): `choiDualValue_le_of_witness` — reduces the whole `≥` to one feasible-witness existence (`csInf_le`).
- ✅✅ **LINCHPIN SOLVED (`9fef193d`): the topology diamond is gone.** `HermCarrier ι` (`HermitianCarrier.lean`) — a fresh
  one-field `structure` wrapping `selfAdjoint (Matrix ι ι ℂ)`, with AddCommGroup/Module ℝ transported via `equivSA`
  and the Frobenius `InnerProductSpace ℝ` via `ofCore`. Because it's a FRESH type (no `instTopologicalSpaceSubtype`),
  `ofCore` gives the only topology, so **`ContinuousSMul ℝ` + `LocallyConvexSpace ℝ` resolve** (verified by in-file
  `example`s); `CompleteSpace` follows from `FiniteDimensional` (next). 🔑 smul_left needs `Matrix.smul_apply`+`Finset.mul_sum`
  (the ℝ-on-ℂ `Matrix.trace_smul` rw doesn't match the Module-smul instance); `definite` via `equivSA.injective`+`zero_toSA`.
  This is the brick that collapsed the design agent's "multi-week" — the blocker was a fixable instance diamond, not missing math.
- ✅ `FiniteDimensional ℝ (HermCarrier ι)` (`266e670d`, `Module.Finite.of_injective`, import `Mathlib.LinearAlgebra.Complex.FiniteDimensional`) ⟹ `CompleteSpace`. All 3 engine instances resolve.
- ✅✅ **PSD ProperCone DONE (`6417c24e`, `DiamondSDPCone.lean`):** `psdProperCone : ProperCone ℝ (HermCarrier ι)` (`toMatₗ`+`continuous_toMat` finite-dim continuity; `isClosed_psdCarrierCone` via shipped `isClosed_posSemidef`; `psdCarrierCone` pointed-cone; `convex_psdSet`). Import `Mathlib.Analysis.Convex.Cone.Dual` (ProperCone + `hyperplane_separation`). **ROUTE (a) geometric Hahn–Banach confirmed** over (b) `relative_hyperplane_separation` — `ProperCone.map`=closure ⟹ cone-image closedness obligation (cone images NOT closed in general even finite-dim); route (a) separates the closed PSD set from a compact set, no image cone.
- ✅ VERIFIED-COMPILING (prototyping agent, integrate when reached): separation→Riesz skeleton (`geometric_hahn_banach_compact_closed` + `InnerProductSpace.toDual` on the carrier) + the conditional headline glue `diamondDist_eq_choiSDP (hwit) := le_antisymm (diamondDist_le_choiDualValue …) (choiDualValue_le_of_witness hwit)`.
- 🔴 **REMAINING = the Watrous complementary-slackness analytic core (sub-lemmas 3+4, NO Mathlib gap, NO axiom):**
  (3) `primal_value_eq : (C * choiContraction (posProj T*) ρ*).trace.re = diamondDist` (transcribe `DiamondNormDual.lean:174-185` chain in reverse, from `exists_diamondDist_eq` + `eigPosSum_eq_re_trace_posProj` + `trace_mul_krausMap_sub`) — moderate;
  (4) gap ⇒ separate the primal-optimum carrier-lift from the dual-feasible objective-sublevel `t` (closed+convex via `convex_psdSet`+`continuous_ptrace2`) via `geometric_hahn_banach_compact_closed`; the separating vector `v⪰0` + complementary slackness (reuse `re_trace_mul_le_of_loewner` for tightness) ⟹ a feasible `W` with `‖ptrace2 W‖ ≤ diamondDist`, contradicting `δ<choiDualValue` — the genuine SDP-duality content, multi-session but UNBLOCKED.
  THEN `choiDualValue_le_of_witness` → `le_antisymm` → **`diamondDist_eq_choiSDP`**. All scaffolding (carrier, cone, separation skeleton, both attainments, weak-dual, glue) shipped + verified.
- (history) Bricks 2 (define `W*`) + 4 (`W*−C⪰0` + tightness) = the deep crux. `W* = C₊` works ONLY for Pauli-covariant
  (max-entangled `ρ*`); GENERAL non-covariant (amp-damp: product-state `ρ*`) needs the `ρ*`-aligned witness — the
  genuine Watrous §3.3.2 dual-optimal construction (per-channel exacts in `NamedChannelDiamondExact.lean` are the
  validation templates). NOT a Mathlib gap — genuine QI-math derivation. The single hardest piece; all surrounding
  infra (weak-dual ≤, InnerProductSpace, both attainments, op≤trace, R3) is in place. NO fence, NO axiom.
- (superseded) NEXT concrete brick (brick 4a): `l2opNorm_le_traceNorm` for PSD `W` (`‖W‖_{L2op} ≤ traceNorm W`,
  i.e. max eigenvalue ≤ trace) — the bridge bounding `‖W‖` itself in the AMBIENT L2-op metric (the
  shipped `frobenius_le_traceNorm` is in the *Frobenius* instance, won't unify under `L2Operator` open).
  ROUTE: `W ⪯ (tr W)•1` (PSD eigenvalues ≤ trace) ⇒ generalize the 6AJ EuclideanLin
  `opNorm_le_one_of_mul_conjTranspose_le_one` pattern to `opNorm_le_of_loewner_smul_one`. ⚠️ EuclideanLin
  CLM route (the whnf-wall-avoiding one), not the CStarAlgebra CFC instance (200k-heartbeat whnf wall).
  THEN: closedness of `{W⪰0, W⪰C}` (PSD conditions closed) + `‖Tr₂·‖≤B` sublevel bounded (via brick 4a +
  `dualObjective_trace_bound`) ⇒ `Metric.isCompact_of_isClosed_isBounded` ⇒ `IsCompact.exists_isMinOn`
  of continuous `W↦‖Tr₂ W‖` ⇒ dual inf ATTAINED. THEN brick 5 (Hahn–Banach separation +
  complementary slackness) = the larger creative core ⇒ `≥` direction ⇒ `le_antisymm` headline.
- **HONEST SCOPE:** the `≥` direction is Watrous diamond-SDP strong duality — a large multi-increment
  bespoke build (attainment + separation). Infrastructure (brick 1 InnerProductSpace) + `≤` + attainment
  foundations are committed kernel-pure; the separation/complementary-slackness core remains. NOT fenced
  (reachable, no axiom); NOT the holding antipattern (continuous committed increments).

## OUTCOME UPDATE (2026-06-03, autonomous /goal) — 4 Farkas bricks SHIPPED + DECISIVE negative finding
New file `DiamondSDPDuality.lean`, kernel-pure, root-imported:
- brick A `mem_innerDual_psdProperCone` (`e019b7a6`): PSD-cone Frobenius **self-duality** (rank-1 `vvᴴ`
  test + `posSemidef_iff_dotProduct_mulVec` + Mathlib Hermitian-reality `im_star_dotProduct_mulVec_self`;
  `trace_mul_nonneg` for `←`). Import `Mathlib.Analysis.Convex.Cone.InnerDual`.
- brick B `trace_ptrace2_mul` (`cf4c1821`): `Tr₂` adjoint identity `tr(Tr₂W·Y)=tr(W·(Y⊗ₖ1))`.
- brick C′ `re_trace_mul_le_l2opNorm_ptrace2_mul_trace` (`d0e39ad2`): primal-side weak duality
  `Re tr(C·X) ≤ ‖Tr₂W‖·Re tr σ` for `X⪯σ⊗1`.
- brick C″ `choiContraction_le_inMarginal_kron_one` (`80334e4f`): primal feasibility `M(Q,ρ)⪯inMarginal(ρ)⊗1`.

⚠️⚠️ **DECISIVE FINDING (verified):** the line-197 plan — naive conic Farkas on the DUAL-feasibility
system `{W⪰0,W⪰C,‖Tr₂W‖≤δ}`, "gap ⇒ sublevel empty ⇒ separate" — is a **DEAD-END for the `≥`
direction**: it only RE-PROVES WEAK duality. The Farkas separator `(ρ̃⪰0,Y₂⪰0,ρ̃⪯Y₂⊗1,
Re tr(Cρ̃)>δ·tr Y₂)` is bounded by brick C′ as `Re tr(Cρ̃) ≤ choiDualValue·tr Y₂`, and
`choiDualValue ≥ diamondDist = δ`, so there is NO contradiction (it is consistent with the gap).
STRIKE the line-197/line-64-handoff "separation of the dual-sublevel" route.

🔴 **CORRECT ROUTES (genuine Watrous strong-duality content; no Mathlib gap, no axiom, harder):**
- (a) prove the diamond-SDP **primal value = diamondDist**, primal `= sup{Re tr(C·X): X⪰0, ∃σ density,
  X⪯σ⊗1}`. `≥`: brick C″ + `traceDist_eq_re_trace_choiContraction_posProj` (M(P*,ρ*) feasible,
  value = traceDist). `≤` (THE HARD HALF, true analytic content): every feasible X has
  `Re tr(C·X) ≤ diamondDist` — needs Watrous "pure-input suffices" / construct input ρ from X;
  NOT the elementary chain (that gives choiDualValue). Then primal = choiDualValue via correct
  primal/dual SDP separation.
- (b) complementary-slackness: explicit optimal dual `W*` from attained `(ρ*,P*)` (`exists_diamondDist_eq`)
  with `‖Tr₂W*‖=diamondDist`, then `choiDualValue_le_of_witness`. Watrous explicit witness = literature.
- **Deep-research dispatched:** `Lit-Search/tasks/DR_6AI_diamond_SDP_strong_duality.md` (explicit `W*`
  formula and/or the `primal ≤ diamondDist` construction). Resumption prompt:
  `~/.claude/.../memory/next_session_6AI_full_delivery_goal.md` (CORRECTED to reflect this finding).
Bricks A/B/C′/C″ feed routes (a)/(b) regardless and are committed kernel-pure infrastructure.

## OUTCOME UPDATE 2 (2026-06-03) — DEEP RESEARCH LANDED; explicit-witness route confirmed (route b)
DR note: `Lit-Search/Phase-6AI/Strong Duality for the Diamond-Norm SDP- A Constructive,
Formalization-Ready Note.md` (read directly). **Decisive: NO Slater/Sion/conic-closure needed.**
The headline closes by EXPLICIT optimal-witness construction:
- **W\*** (DR D1, **must verify by direct calculation — DR's closed form is internally muddled on
  `C` vs the contracted Choi `(√ρ*⊗1)C(√ρ*⊗1)`, and is explicitly flagged "verify, do not cite"**):
  `W* = (√ρ*⊗1)·Π*·C·Π*·(√ρ*⊗1)`, `Π*` = positive spectral projector of `(√ρ*⊗1)C(√ρ*⊗1)`,
  `ρ*` = optimal input (`exists_diamondDist_eq`). Prove `W*⪰0`, `W*⪰C` (claim `W*−C=(T_proj)₋⪰0`),
  `‖Tr₂W*‖ ≤ diamondDist` ⟹ `diamondDist_eq_choiSDP_of_witness` (SHIPPED `122da9a9`) closes it.
- **Staged plan (DR §Recommendations):** S1 SDP primitives (✅ `ptrace2_choiDiff_eq_zero`,
  `ptrace2_choiMatrix_krausMap` `1d58d63d`; remaining: vec-J purification identity D2
  `(Φ⊗id)(ψ_σ)=(1⊗√σ)J(Φ)(1⊗√σ)` — the linchpin) → S2 weak duality (✅) → S3 `primal ≤ diamondDist`
  (F5 analytic half: Schur `X=(√σ⊗1)K(√σ⊗1)`,`‖K‖≤1` + Hölder, via `Matrix.PosSemidef.schur_complement`
  + shipped `traceNorm_mul_le`) → S4 construct `W*`/`Π*` (`Matrix.IsHermitian.spectralTheorem`, select
  `λ>0`) → S5 attainment `‖Tr₂W*‖≤diamondDist` (DR-flagged hardest) → S6 `le_antisymm`.
- **DR decision-thresholds:** if S3 > ~1500 lines, consider Bhatia Schur-lemma as axiom (USER SIGN-OFF
  REQUIRED); if S5 intractable, alternative route via max-output-fidelity SDP (1207.5726 §2.3 Thm 5).
- Convention swap `σ:X⊗Y→Y⊗X` (one `Matrix.reindex`/`swap_kronecker` lemma) is the single conversion point.
- **⚠️ The earlier naive dual-Farkas route is a confirmed DEAD-END (reproves only weak duality) — STRUCK.**
  S3 alone does NOT close the headline; the witness (S4+S5) is the headline-critical core (via the
  shipped conditional `diamondDist_eq_choiSDP_of_witness`).

## OUTCOME UPDATE 3 (2026-06-03) — CORRECTED W* derived (DR formula was wrong); substrate shipped
Working the DR "verify-by-calc, do not cite" caveat: the DR's `W* = (√σ⊗1)Π*CΠ*(√σ⊗1)` is WRONG
(fails `W*⪰C`). **Derived correct form** (for PosDef `σ`, `M := contractedChoi = (√σ⊗1)C(√σ⊗1)`,
Jordan–Hahn `M = M₊ − M₋`):
```
    W* = (√σ⁻¹ ⊗ 1) · M₊ · (√σ⁻¹ ⊗ 1)        [M₊ = posPart M ; note σ⁻¹, NOT √σ]
```
- `W*⪰0`: conjugation of PSD `M₊` by Hermitian `(√σ⁻¹⊗1)` (`PosSemidef.mul_mul_conjTranspose_same`).
- `W*⪰C`: since `C = (√σ⁻¹⊗1)·M·(√σ⁻¹⊗1)` (from `M=(√σ⊗1)C(√σ⊗1)` + `(√σ⁻¹⊗1)(√σ⊗1)=1`),
  `W*−C = (√σ⁻¹⊗1)·(M₊−M)·(√σ⁻¹⊗1) = (√σ⁻¹⊗1)·M₋·(√σ⁻¹⊗1) ⪰ 0` (`posPart_sub_self_eq_negPart`).
- `‖Tr₂W*‖ ≤ diamondDist` (S5, hardest): `Tr₂W* = √σ⁻¹·(Tr₂ M₊)·√σ⁻¹`; bound via `tr(σ·Tr₂W*) =
  tr(M₊) = diamondDist` (CS3) + the operator-norm-from-trace step.
SHIPPED substrate: `contractedChoi` + `contractedChoi_isHermitian` (`a5648909`); `Π* := posProj
(contractedChoi_isHermitian …)`. NEEDS: σ PosDef ⟹ `psdSqrt` is a unit (`isUnit_psdSqrt`) for `√σ⁻¹`;
the `(√σ⁻¹⊗1)(√σ⊗1)=1` cancellation; then `W*⪰0`/`W*⪰C` are short. ⚠️ σ non-invertible (DR D4) needs
a `+ε·1` limiting argument or the pure-input reduction — the remaining wrinkle. CONVENTION: our
`diamondDist` sups over doubled-space ρ; `σ` is the single-factor input — the ρ↔σ bridge
(pure-input-suffices, Watrous Thm 3.53) is the other prerequisite for the S5 diamondDist connection.

## OUTCOME UPDATE 4 (2026-06-03) — STAGE 4 COMPLETE (witness dual-feasible); STAGE 5 underway
Shipped (kernel-pure, `DiamondSDPDuality.lean`):
- `diamondWitness` def + `diamondWitness_posSemidef` (**W*⪰0**, `21bce19e`) + `diamondWitness_sub_posSemidef`
  (**W*⪰C** for PosDef σ, `70393737`). **Stage 4 (witness dual-feasibility) DONE.**
- `ptrace2_kron_one_conj` (`Tr₂((A⊗1)Z(A⊗1))=A(Tr₂Z)A`, `8ca2a147`) ⟹ `Tr₂W* = √σ⁻¹(Tr₂M₊)√σ⁻¹`.
- `trace_contractedChoi_eq_zero` (**tr M = 0**, `557cee2a`) ⟹ `tr(M₊)=½‖M‖₁` (M Hermitian+traceless).
REMAINING for headline (Stage 5 + convention, the hardest analytic stretch; all mapped, no conceptual
unknown):
- (S5a) `tr(M₊) = ½‖M‖₁`: from `tr M = 0` + `posPart` trace identity `tr(posPart hM) = ½(‖M‖₁ + tr M)`
  (need/derive this posPart-trace lemma).
- (S5b) `½‖M‖₁ = traceDist` at the σ-purification input: the **vec-J identity** (DR D2,
  `(Φ⊗id)(ψ_σ)=(1⊗√σ)J(Φ)(1⊗√σ)`) relating `M=(√σ⊗1)C(√σ⊗1)` to the output difference — needs
  `maxEntangled`/`omegaVec` purification machinery (in `DiamondNormChoi.lean`).
- (S5c) **operator-norm** attainment `‖Tr₂W*‖ ≤ diamondDist` (NOT just the trace bound): via CS3
  (ρ* on top eigenspace of Tr₂W*) — the optimal-input eigenvector argument.
- (Conv) pure-input-suffices (Watrous Thm 3.53: optimal ρ* purifiable) + non-invertible-σ `+ε·1` limit.
Then `‖Tr₂W*‖ ≤ diamondDist` feeds `diamondWitness_posSemidef`+`diamondWitness_sub_posSemidef` into the
shipped `diamondDist_eq_choiSDP_of_witness` ⟹ headline.

## OUTCOME UPDATE 5 (2026-06-03) — S5b core shipped; pure-input-suffices NOT needed (de-risk)
- Shipped `trace_posPart_eq_half_traceNorm` (S5a, `5b6c9f18`: `tr(M₊)=½‖M‖₁` for traceless Herm) +
  `krausMap_tensorKraus_conj_kron_one` (S5b core, `b45b5574`: `(Φ⊗id)((1⊗A)ρ(1⊗A))=(1⊗A)(Φ⊗id)(ρ)(1⊗A)`).
- 🔑 **KEY DE-RISK:** **pure-input-suffices (Watrous Thm 3.53) is NOT needed.** The σ-weighted
  maximally-entangled state `ψ_σ ψ_σ* = (1⊗√σ)·(ωωᴴ)·(1⊗√σ)` (normalized) IS a valid doubled-space
  density, so `traceDist(ψ_σ) ≤ diamondDist` is *direct* via `le_diamondDist` — no optimal-input-is-pure
  reduction required.
- **S5b-combine (tractable, few bricks):** `krausMap_tensorKraus_conj_kron_one` (A=√σ) + the shipped
  `krausMap_tensorKraus_omegaVec` (ω↔Choi swap) ⟹ output difference at `ψ_σ` = `(1⊗√σ)·(C swap)·(1⊗√σ)`;
  then `traceNorm_submatrix_equiv` (trace-norm swap-invariance, shipped) ⟹ `‖that‖₁ = ‖(√σ⊗1)C(√σ⊗1)‖₁
  = ‖M‖₁`; and `½‖output diff‖₁ = traceDist(ψ_σ) ≤ diamondDist` (`le_diamondDist`, needs ψ_σ normalized
  density). ⟹ `tr(M₊) = ½‖M‖₁ ≤ diamondDist` for ALL σ.
- **S5c (the one genuinely hard piece left):** the **operator-norm** attainment `‖Tr₂W*(σ)‖ ≤ diamondDist`
  (vs the trace bound `tr(M₊) ≤ diamondDist`). `Tr₂W* = √σ⁻¹(Tr₂M₊)√σ⁻¹` — need its top eigenvalue ≤
  diamondDist, which holds at the OPTIMAL σ via CS3 (the optimal input on the top eigenspace). This is
  the Watrous optimality step; no Mathlib gap, but the real analytic core that still needs construction.
- Non-invertible-σ `+ε·1` limit (DR D4) folds into S5c's optimal-σ handling.

## OUTCOME UPDATE 6 (2026-06-03) — S5b COMPLETE; S5c reduced to a single operator inequality
S5b-finish SHIPPED (`0fb7b30f`): `trace_posPart_contractedChoi_le_diamondDist` —
`tr(M₊) ≤ diamondDist` for ALL input densities `σ` (ρ_σ density + σ-weighted ω↔Choi + trace-norm
swap + tr M=0 + S5a). Supporting bricks: `isDensityOperator_weighted_omega`, `krausMap_tensorKraus_
weighted_omega`, `traceNorm_kron_one_conj_swap`, `kron_one_submatrix_prodComm`, `contractedChoi_
submatrix_swap`. Witness Tr₂ formula SHIPPED (`44c8fb3f`): `ptrace2_diamondWitness :
Tr₂ W* = √σ⁻¹·(Tr₂ M₊)·√σ⁻¹`.
**S5c now reduces (congruence by √σ) to a SINGLE operator inequality:**
```
    ‖Tr₂ W*(σ)‖ ≤ diamondDist   ⟺   Tr₂(posPart M) ⪯ diamondDist · σ      (M = (√σ⊗1)C(√σ⊗1))
```
because `√σ⁻¹·(diamondDist·σ − Tr₂M₊)·√σ⁻¹ = diamondDist·1 − Tr₂W*` and congruence preserves PSD.
Reduction plumbing (concrete, next): `l2opNorm_le_of_loewner` (PSD `A ⪯ c·1 ⟹ ‖A‖≤c`, CFC route:
`c²·1−A² = cfc(c²−x²)`, eigenvalues in `[0,c]`) + the congruence step.
🔴 **THE IRREDUCIBLE KERNEL — `Tr₂(posPart M) ⪯ diamondDist·σ` at the OPTIMAL `σ*`** — is the
genuine Watrous first-order-optimality content (the DR's "hardest single step"). The weighted-average
`tr(σ*·Tr₂W*) = tr(M₊) ≤ diamondDist` is shipped (S5b); upgrading to the operator inequality needs:
`σ*` maximizes `traceDist` over densities ⟹ no eigenvector of `Tr₂W*` exceeds `diamondDist` (else
perturb the input toward it, contradicting maximality). Needs the variational/perturbation argument on
the attained `ρ*` (`exists_diamondDist_eq`). This is the SOLE remaining mathematical content; all
construction + feasibility + the trace bound are done (~24 kernel-pure increments this arc).

## OUTCOME UPDATE 7 (2026-06-03) — 6AI REDUCED TO ONE VARIATIONAL INEQUALITY (everything else SHIPPED)
S5c plumbing SHIPPED (kernel-pure): `l2opNorm_le_of_loewner` (`242ae029`: PSD `A⪯c·1 ⟹ ‖A‖≤c` via
`c²·1−A² = c·(c·1−A)+√A·(c·1−A)·√A`, no eigenvalues/cfc-commute) + `opNorm_ptrace2_diamondWitness_le`
(`9cfa3dd5`: `‖Tr₂W*‖≤d` from `Tr₂M₊ ⪯ d·σ` via √σ⁻¹-congruence).
**HEADLINE-MODULO-KERNEL SHIPPED** (`f82ec77b`): `diamondDist_eq_choiSDP_of_loewner` —
`diamondDist = choiDualValue` follows from a SINGLE hypothesis:
```
    ∃ σ : Matrix (Fin n)(Fin n) ℂ, ∃ hσ : σ.PosDef,
      ((diamondDist K₁ K₂ : ℂ)•σ − Tr₂(posPart (contractedChoi … (choiDiff_isHermitian K₁ K₂)))).PosSemidef
```
(assembles `diamondWitness_posSemidef` + `diamondWitness_sub_posSemidef` + `opNorm_ptrace2_diamondWitness_le`
+ `diamondDist_eq_choiSDP_of_witness`). **~29 kernel-pure increments this arc; the ENTIRE explicit-witness
construction + both feasibility conditions + the trace bound + all reductions are DONE.**
🔴 **THE SOLE REMAINING KERNEL:** discharge that hypothesis — exhibit the optimal PosDef `σ*` with
`Tr₂(posPart M(σ*)) ⪯ diamondDist·σ*`. This is the Watrous first-order-optimality fact: `σ*` maximizes
`tr(posPart M(σ)) = traceDist(ρ_σ)` over densities (the trace bound `tr(M₊)≤diamondDist` is shipped
∀σ), and the maximality upgrades to the operator inequality. Needs first-order/perturbation machinery on
the attained `ρ*` (`exists_diamondDist_eq`) — genuinely substantial (matrix-function differentiation /
envelope; non-smooth posPart, √σ; Mathlib matrix-derivative support is limited). Plus the non-invertible-σ
`+ε·1` limit (DR D4). This is the multi-session analytic frontier; everything around it is proven.

## OUTCOME UPDATE 8 (2026-06-03) — BOTH DR SHORTCUTS REFUTED; KERNEL CONFIRMED AS THE CONIC-DUALITY CORE
Second DR returned (`Lit-Search/Phase-6AI/Operator-Inequality Lemma for the Diamond-Norm SDP-
Formalization-Ready Note.md`). Its headline recommendation — "Route 1 with **σ = 1_X/dim(X)**, no
ε-regularization, cleanest proof; (★) holds for EVERY PosDef σ" — is **MATHEMATICALLY FALSE**. With
σ = 1/d the kernel collapses to `Tr₂(posPart C) ⪯ diamondDist·1` (since √σ = (1/√d)1 ⟹ M = C/d ⟹
posPart M = posPart C/d). But `posPart C` is itself a *dual-feasible* witness (`posPart C ⪰ 0`,
`posPart C ⪰ C`), so weak duality forces `‖Tr₂(posPart C)‖ ≥ diamondDist`; equality would require
`posPart C` to be dual-OPTIMAL, which is generically false.
**Numerical refutation (verified):** Φ₁ = id, Φ₂ = reset-to-|0⟩ (asymmetric pair) on a qubit gives
`eig(C) = {−1, −0.618, 0, 1.618}`, `Tr₂(posPart C) = diag(0.447, 1.171)`, so
`‖Tr₂(posPart C)‖ = 1.171 > 1 = diamondDist(id, reset)`. (★) at σ = 1/d is FALSE. ⇒ never transcribe it.
The DR's §2 derivation (Steps 1–5) is itself CORRECT but presupposes a dual-optimal `W^♯` attaining
`‖Tr₂ W^♯‖ = diamondDist` — i.e. it assumes strong duality (the hard direction) to prove (★). The DR's
own finding #2 concedes this: the un-conjugated `H = Tr₂((1⊗P*)C) ⪯ diamondDist·1` (derivative-free,
non-circular, TRUE) does NOT bridge to the √σ-conjugated (★) "without the same complementary-slackness
identity Route 1 was trying to avoid." The first DR's explicit `W*` formula was also wrong (corrected to
`diamondWitness` earlier this arc). **Both DRs failed to crack the kernel.**

**First-principles verdict (confirmed against the actual primal infra `DiamondNormSup`/`DiamondNormAttainment`):**
- The genuinely NON-CIRCULAR, derivative-free handle that IS reachable: for the FIXED optimal output
  projector `Q*`, the *adjoint-channel* operator `G = Δ*(Q*)` (Δ = (Φ₁−Φ₂)⊗id) satisfies
  `G ⪯ diamondDist·1` on the doubled space, because `tr(Gρ) = tr(Q*·Δρ) ≤ traceDist ≤ diamondDist` for
  every density ρ (linear in ρ — no √σ, no derivative; closes via the shipped
  `posSemidef_smul_one_sub_of_quadratic_le`). **But G lives on X⊗X′ and is NOT σ-conjugated; bridging it to
  (★)'s `Tr₂(posPart M(σ*)) ⪯ diamondDist·σ*` on X requires the stationarity/complementary-slackness
  EQUALITY at the optimum** — which is precisely the conic-duality content.
- Key bridge identity (shipped infra): `Δ(ρ_σ) = M(σ).submatrix(swap)` via
  `krausMap_tensorKraus_weighted_omega` + `contractedChoi_submatrix_swap`; this is why the TRACE bound
  `tr(posPart M(σ)) ≤ diamondDist ∀σ` (`trace_posPart_contractedChoi_le_diamondDist`) was provable. The
  trace→operator upgrade is the irreducible step.
- **Mathlib v4.29.1 genuinely lacks** every tool that would discharge it: Sion/von-Neumann minimax,
  Fenchel/conic strong duality, zero-gap SDP, and the matrix-square-root Fréchet derivative
  (Sylvester-equation form) needed for the envelope/perturbation route. This MATCHES the project's
  repeated prior fence findings (memory: "primal=dual Choi-SDP equality — conic duality absent";
  "Mathlib NO minimax/Fenchel/Slater/zero-gap-SDP/Bauer"). The 6AI explicit-witness arc successfully
  reduced the ENTIRE strong-duality theorem to this ONE inequality and proved everything else kernel-pure
  — a real achievement — but the final inequality is the irreducible conic-duality core, not a transcription.

## OUTCOME UPDATE 9 (2026-06-03) — ROUTE RECOVERED: conic Farkas IS in Mathlib v4.29.1; pivot off the (★) path
**Context-loss correction (user-prompted "from one lemma to multi-week usually means lost context").** The
`diamondWitness`/(★) reduction was a DEAD-END SIDE-PATH, not the intended route. The (★) operator inequality
at a single PosDef σ is genuinely unsatisfiable for singular-optimum channels (id-vs-reset: optimal σ* =
|1⟩⟨1| is rank-1; (★) violated at every PosDef σ), so `diamondDist_eq_choiSDP_of_loewner` can't be
discharged — but that capstone was never needed.
**THE INTENDED ROUTE (written in the codebase's own docstrings, `primalSDPValue` / `dual_infeasible_of_lt_choiDualValue`):**
`diamondDist = choiDualValue` via the SDP-value chain
`choiDualValue ≤ primalSDPValue ≤ diamondDist ≤ choiDualValue`:
- **Piece 2** `choiDualValue ≤ primalSDPValue` — conic Farkas / theorem-of-alternatives. Dual sublevel
  empty at δ<choiDualValue (shipped `dual_infeasible_of_lt_choiDualValue`) ⟹ primal-feasible X with
  Re tr(C·X) ≥ δ ⟹ primalSDPValue ≥ δ; sup over δ ⟹ piece 2.
- **Piece 3** `primalSDPValue ≤ diamondDist` — Watrous primal→operational reduction (each SDP-feasible
  X gives an operational distinguishability ≤ diamondDist).
- Shipped weak directions: `diamondDist_le_choiDualValue` (W1), `primalSDPValue_le_choiDualValue` (W2).
**🟢 BLOCKER CLEARED:** Mathlib v4.29.1 HAS `ProperCone.hyperplane_separation`,
`hyperplane_separation_point`, and `relative_hyperplane_separation` (Farkas for proper cones, via
Hahn–Banach) in `Mathlib/Analysis/Convex/Cone/{Dual,InnerDual}.lean`. The PSD proper cone
(`psdProperCone`), its self-duality (`mem_innerDual_psdProperCone`), and Slater
(`exists_dual_strictly_feasible`) are ALREADY shipped. The prior "conic duality absent" memory is STALE
for this pin. **Numerically VERIFIED** (cvxpy, three asymmetric pairs incl. singular-optimum id-vs-reset):
`primalSDPValue = choiDualValue = diamondDist` exactly (1.0 / 0.5 / 0.6). Route is tractable
Mathlib-style work, in scope for the goal loop. NO axiom, NO fence. Building pieces 2 + 3.

## OUTCOME UPDATE 10 (2026-06-03) — PIECE 3 SHIPPED (`primalSDPValue ≤ diamondDist`), kernel-pure
4 new kernel-pure lemmas in `DiamondSDPDuality.lean` (commits after `2bf696cf`):
- `re_trace_mul_le_trace_posPart` — Helstrom bound `Re tr(M·Q) ≤ tr(M₊)` for `0⪯Q⪯1`.
- `re_trace_choiDiff_mul_le_diamondDist_of_posDef` — per-point bound at PosDef σ via `√σ⁻¹`-conjugation
  `X=(√σ⊗1)Q′(√σ⊗1)` (`0⪯Q′⪯1`) → `Re tr(C·X)=Re tr(M(σ)·Q′) ≤ tr(M(σ)₊) ≤ diamondDist` (shipped trace bound).
- `re_trace_choiDiff_mul_le_diamondDist` — general density σ via `(1−ε)`-perturbation
  `(σ_ε,X_ε)=((1−ε)σ+(ε/n)1,(1−ε)X)` PosDef-feasible, algebraic `ε₀=(t−d)/(2t)` conclusion (no limits).
- `primalSDPValue_le_diamondDist` — `csSup_le` over the feasible set. **PIECE 3 = DONE.**
Uses ℂ-cast scalars for `PosDef.smul`/`PosSemidef.smul` (ℝ-smul lacks `PosSMulMono ℝ ℂ` instance).
**Remaining: PIECE 2** `choiDualValue ≤ primalSDPValue` (conic Farkas / theorem-of-alternatives) — the
hard brick. Plan: `∀ δ < choiDualValue, δ ≤ primalSDPValue` (then `le_of_forall_lt`-style). Per
`dual_infeasible_of_lt_choiDualValue` (shipped): δ<choiDualValue ⟹ the dual sublevel system
{W⪰0, W⪰C, δ1−Tr₂W⪰0, δ1+Tr₂W⪰0} is infeasible. Encode this as a PSD-product-cone feasibility and
apply `ProperCone.hyperplane_separation` / `relative_hyperplane_separation` to extract a primal
certificate `(X,σ)` with `Re tr(C·X) ≥ δ`. Mathlib has Farkas but NOT packaged cone-program duality,
so the SDP-alternatives reduction is built by hand (the substantial brick). Then assemble headline:
`choiDualValue ≤ primalSDPValue ≤ diamondDist ≤ choiDualValue`.

### PIECE 2 — executable separation design (scaffolding already in `DiamondSDPCone.lean`: `psdProperCone`, `dualFeasSublevel`+closedness, `convex_psdSet`, `traceDist_eq_re_trace_choiContraction_posProj`; tool `geometric_hahn_banach_compact_closed`)
Target `choiDualValue ≤ diamondDist`. Suffices `∀ δ, diamondDist < δ → choiDualValue ≤ δ`; show
∃ feasible `W` (`W⪰0,W⪰C`) with `‖Tr₂W‖≤δ` (⟹ `csInf_le`). By contradiction (dual infeasible at δ):
1. `A := {Tr₂W : W⪰0 ∧ W⪰C} ⊆ Herm(X)` convex+closed; `Bδ := {M:‖M‖≤δ}` compact convex; `A∩Bδ=∅`.
2. Separate (`geometric_hahn_banach_compact_closed`, Frobenius functional `M↦Re tr(Y·M)` on HermCarrier):
   ∃ Hermitian `Y`, `u<v`, `Re tr(Y·M)<u` ∀M∈Bδ, `Re tr(Y·Tr₂W)>v` ∀ feasible W.
3. `sup_{‖M‖≤δ} Re tr(Y·M) = δ·‖Y‖₁` (BUILD dual-norm identity) ⟹ `δ‖Y‖₁ ≤ u`.
4. `Re tr(Y·Tr₂W)=Re tr((Y⊗1)·W)` (`trace_ptrace2_mul`); over feasible W reassemble `Y`(rescale/sign)
   into a primal pt with `Re tr(C·X) > δ` via `traceDist_eq_re_trace_choiContraction_posProj` +
   `choiContraction_posSemidef` + `choiContraction_le_inMarginal_kron_one`; contradict piece 3
   (`primalSDPValue ≤ diamondDist < δ`).
Sub-bricks (kernel-pure, standalone): (i) A convex+closed; (ii) op-norm ball compact convex;
(iii) `sup Re tr(Y·M) over ‖M‖≤δ = δ‖Y‖₁`; (iv) separation→`Y`; (v) `Y`→primal pt + value bound;
(vi) `choiDualValue ≤ diamondDist`; (vii) `le_antisymm` ⟹ unconditional `diamondDist_eq_choiSDP`.
OPTIONAL by-product (NOT on critical path): `diamondDist ≤ primalSDPValue` via `exists_diamondDist_eq`
+ choiContraction feasibility ⟹ `primalSDPValue = diamondDist`.

## OUTCOME UPDATE 11 (2026-06-03) — piece-2 reassembly bricks shipped; refined (cleaner) separation design
Shipped kernel-pure (commits after `05e91026`): `primalSDPValue_eq_diamondDist` (= via piece 3 +
`diamondDist_le_primalSDPValue` attainment); and the piece-2 reassembly chain:
`kron_sqrtInv_conj_kron_self` (`(√σ⁻¹⊗1)(σ⊗1)(√σ⁻¹⊗1)=1`), `trace_kron_one_mul_diamondWitness`
(`tr((σ⊗1)·W*)=tr(M₊)`, the saddle-value identity, `W*=diamondWitness` is the optimal dual witness
against its own input), `re_trace_kron_one_mul_diamondWitness_le` (`Re tr((σ⊗1)·W*) ≤ diamondDist`).
**Sion minimax is NOT in Mathlib v4.29.1** (checked) ⇒ raw Hahn–Banach (route a) confirmed.
**REFINED separation design (cleaner than Update-10's; no full dual-norm identity needed):** to show
`choiDualValue ≤ diamondDist`, by_contra `diamondDist < δ < choiDualValue`; `dual_infeasible_…` ⟹
`S ∩ ballδ = ∅` where `S := {Tr₂W : W⪰0∧W⪰C} ⊆ HermCarrier(Fin n)`, `ballδ := {M : ‖M‖≤δ}`.
`geometric_hahn_banach_compact_closed` (s=ballδ COMPACT, t=S CLOSED) ⟹ functional `φ`, `u<v`,
`φ<u` on ballδ, `φ>v` on S. Riesz (`InnerProductSpace.toDual`) ⟹ Hermitian `Y`, `φ(M)=Re tr(Y·M)`.
- BALL side: plug `M = δ•(1:HermCarrier)` (‖1‖=1) ⟹ `δ·tr Y ≤ u` (NO dual-norm identity; just M=δ1).
- S side: `Y⪰0` (else `W=C+t·P`, `t→∞`, `Re tr((Y⊗1)W)→−∞` contradicts `>v`). For `σ=Y/tr Y`
  (PosDef case) `W₀=diamondWitness σ` is feasible (shipped feasibility), `Tr₂W₀∈S`, and
  `φ(Tr₂W₀)=Re tr(Y·Tr₂W₀)=tr Y·Re tr((σ⊗1)W₀)=tr Y·tr(M₊)≤tr Y·diamondDist` (SHIPPED
  `re_trace_kron_one_mul_diamondWitness_le` + `trace_ptrace2_mul`). Singular `Y/tr Y`: `(1−ε)`-perturb
  `σ_ε` (as in piece 3) ⟹ `≤ tr Y·diamondDist/(1−ε)`, `ε→0`. Then `δ·tr Y ≤ u < v < tr Y·diamondDist`
  ⟹ `δ < diamondDist`, contradiction. ⟹ `choiDualValue ≤ diamondDist`.
REMAINING piece-2 sub-bricks (need `HermitianCarrier.lean` API): `S` as HermCarrier set + convex +
closed (Tr₂ continuous/linear, feasible set closed); `ballδ` compact convex; Hahn–Banach + Riesz→`Y`;
`Y⪰0` from the S-lower-bound (explicit `t`); assemble. Then headline `diamondDist_eq_choiSDP` by
`le_antisymm` (W1 `diamondDist_le_choiDualValue` + this). Reassembly VALUE bricks are DONE; the
HermCarrier separation plumbing is the remaining build.

## OUTCOME UPDATE 12 (2026-06-03) — separation crux identified + compactness lever found
The separation core's genuine subtlety: `{W : W⪰0, W⪰C}` is UNBOUNDED, so naive "separate the empty
sublevel" doesn't apply. LEVER: the codebase already ships `exists_choiDualValue_eq` (dual inf ATTAINED)
via `dualObjective_trace_bound` (`tr W ≤ card·‖Tr₂W‖`); with `W⪰0 ⟹ ‖W‖ ≤ tr W`, the set
`dualFeasSublevel C δ` (`W⪰0, W⪰C, ‖Tr₂W‖≤δ`) is BOUNDED hence COMPACT (closedness already shipped:
`isClosed_dualFeasSublevel`). So the dual optimum `W^♯` EXISTS with `‖Tr₂W^♯‖ = choiDualValue`.
**Cleanest finish (avoids the empty-set separation entirely):** with `W^♯` the attained dual optimum,
the headline `choiDualValue ≤ diamondDist` reduces to `‖Tr₂W^♯‖ ≤ diamondDist`. Two viable closes:
(A) complementary slackness at `W^♯` against the attained primal optimum `ρ*` (`exists_diamondDist_eq`)
+ the saddle-value bricks just shipped; (B) the value-function/separation argument with the COMPACT
`dualFeasSublevel` as the compact set in `geometric_hahn_banach_compact_closed`. Next-turn focus: pick
(A) or (B), build the HermCarrier separation/CS plumbing (S-image or `W^♯`-CS), assemble headline.
STATE: route fully recovered; piece 3 + `primalSDPValue=diamondDist` + all reassembly VALUE bricks
SHIPPED kernel-pure; only the separation/CS plumbing remains (≈100–150 LoC, well-scoped).
