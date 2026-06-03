# Phase 6AI — Strong-duality SDP equality for the diamond norm (MOONSHOT D, public)

**Status:** PLANNED (opened 2026-06-02). Public-only. The arc's last analytic frontier: prove the
**primal = dual** equality for the diamond distance, closing the Watrous SDP characterization that
6AF/6AG left as the sole documented-deferred item.

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
