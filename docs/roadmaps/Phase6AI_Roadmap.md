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
