# Phase 5q.T `/goal` prompts (split — run Part 1 first, then Part 2)

Two self-contained <4k-char `/goal` prompts for completing Phase 5q.T (Ext Substantiation).
Part 2 consumes the real `Ext` that Part 1 builds, so run Part 1 first. T1 is already DONE
(A1ExtSubstantive.lean). See docs/roadmaps/Phase5qT_ExtSubstantiation_Roadmap.md for full context.

---

## Part 1 — T2 (genuine ring) + T3 (real `Ext` via `isoExt`) + T5 proxy-detector

GOAL: Phase 5q.T Part 1 — make the A(1) Ext computation a theorem about Mathlib's REAL
`Ext` functor (not a `cols/8` arithmetic proxy): waves T2 (genuine ring) + T3 (real Ext via
isoExt) + the independent T5 proxy-detector guard rail. T1 is DONE (A1ExtSubstantive.lean);
T4 change-of-rings + paper/registry integration = Part 2, run AFTER this. PUBLIC repo. Read
docs/roadmaps/Phase5qT_ExtSubstantiation_Roadmap.md + its entry-state table FIRST.

HARD INVARIANTS: axioms exactly {propext, Classical.choice, Quot.sound}; NO new
project-local `axiom`; NO `native_decide`; NO `sorry`; NO maxHeartbeats in proof bodies
(decompose into `have` sub-lemmas; maxRecDepth bumps OK); never weaken statements to pass.
Parallel agent shares `main`: stage ONLY your own paths (never add -A/-a/.), never push.
Dev loop = lean-lsp MCP (lean_goal → lean_multi_attempt → write); lean_verify each module.

T2 — A(1) genuine `Ring`/`Algebra (ZMod 2)` (extend A1Ring.lean or new A1Algebra.lean).
  Define `A1` as a NEWTYPE over `Fin 8 → ZMod 2` (dodge the Pi mul diamond), Milnor basis
  e₀..e₇. Multiplication from the EXISTING A1Ring `L0..L7` left-regular-rep matrices
  (`Lₐ·e_b` columns = sum-valued products); do NOT use SteenrodA1.a1_mul (Adem basis,
  Option-valued, can't represent sums). Ring + Algebra axioms by `decide`. Augmentation
  `A1 →ₐ[ZMod 2] ZMod 2` (project e₀). Prove the rep `A1 →ₐ Matrix (Fin 8)(Fin 8)(ZMod 2)`
  (eᵢ↦Lᵢ) is a FAITHFUL algebra hom — ties T2 to A1Resolution's differentials. Risk low-med.

T3 — Real `Ext^n_{A(1)}(F₂,F₂)` via `ProjectiveResolution.isoExt` (new A1ExtReal.lean).
  Build a `ProjectiveResolution` of F₂ over A1 from the resolution matrices; prove
  `Module.finrank (ZMod 2) ((Ext .. n).obj ..) = rₙ` (r=1,2,2,2,3,4). Steps: ModuleCat A1
  wrappers for free Pₙ + differentials as A1-linear maps; free⟹projective; the 5
  ProjectiveResolution fields incl. quasiIso (port A1Resolution ker-card/RREF rank facts to
  homology vanishing of the augmented complex); matrix-rank→finrank helper; isoExt +
  minimality ⟹ dimension. Mathlib: CategoryTheory/Abelian/Ext.lean (`Ext R C n`,
  `ProjectiveResolution.isoExt`); homology is noncomputable. Risk medium.

T5-detector (independent guard — land it here, it guards the exact class T1 fixed): extend
  scripts/build_graph.py `_PLACEHOLDER_BODY_PATTERNS` (or new ProxyMarker) to flag
  `decide`/`norm_num` bodies whose STATEMENT is a closed arithmetic identity (a/b=c, a+b=c)
  on a theorem whose NAME/docstring claims a structural quantity (*_dim,*Ext*,rank,finrank)
  — the gap that let `ext_dim_n` through. Add a validate.py check. (T5 docstring/bundle/
  registry integration is in Part 2, after T4.)

CLOSURE (Part 1): validate.py (incl. the new check), file-gate + `lake build` of the new
modules + ExtractDeps, lean_verify axiom-purity on the new ring + Ext theorems,
update_counts.py + Inventory + roadmap status table (T2/T3 → COMPLETE, detector landed).
Leave T4/H2 + paper/registry integration for Part 2. Topological H1/H3/H4 (ko/Adams/ABP) are
OUT OF SCOPE (Phase 5q.B territory) — don't touch.

/goal autonomous mode: the stop hook is a GO signal. Ship the next substantive increment
each turn, kernel-pure, across compacts, until T2 + T3 + detector are done. Never
"hold"/"await direction"/"next session".

---

## Part 2 — T4 (change-of-rings H2) + T5 integration + closure

GOAL: Phase 5q.T Part 2 — discharge change-of-rings H2 for REAL (T4) and finish T5
integration (docstrings, bundles, counts, registry), then close out the wave. PREREQUISITE:
Part 1 (T2 genuine A1 Ring/Algebra + T3 real `Ext^n_{A(1)}(F₂,F₂)` via
`ProjectiveResolution.isoExt`) MUST be landed first — this wave consumes that real `Ext`.
T1 is DONE (A1ExtSubstantive.lean). PUBLIC repo. Read
docs/roadmaps/Phase5qT_ExtSubstantiation_Roadmap.md + its entry-state table FIRST.

HARD INVARIANTS: axioms exactly {propext, Classical.choice, Quot.sound}; NO new
project-local `axiom`; NO `native_decide`; NO `sorry`; NO maxHeartbeats in proof bodies
(decompose into `have` sub-lemmas; maxRecDepth bumps OK); never weaken statements to pass.
Parallel agent shares `main`: stage ONLY your own paths (never add -A/-a/.), never push.
Dev loop = lean-lsp MCP (lean_goal → lean_multi_attempt → write); lean_verify each module.

T4 — Genuine change-of-rings, discharge H2 (rewrite ChangeOfRings.lean). REPLACE the
  placeholders `h2_discharged : True := trivial` and `hom_tensor_adjunction_dim :
  rank = rank := rfl` with a real proof of `Ext^n_A(A ⊗_{A(1)} F₂, F₂) ≅
  Ext^n_{A(1)}(F₂,F₂)` (Shapiro / Hom-tensor adjunction). A(1) and A are NONCOMMUTATIVE →
  use Mathlib's general-ring `restrictCoextendScalarsAdj` (restrictScalars ⊣ coextendScalars,
  [Ring R][Ring S]), NOT the CommRing-only `extendRestrictScalarsAdj`. The generation chain
  needs only the DIMENSION EQUALITY at each n (lighter than the full natural iso). If full
  generality balloons, ship the explicit Ext-dimension theorem about the concrete A//A(1)
  module — NEVER a True/rfl placeholder. Update H2 in ExtBordismBridge.lean to consume the
  real result. Risk med-high (Mathlib lacks Shapiro; small upstreamable lemmas may be needed).

T5-integration (the non-detector half; the detector landed in Part 1):
  - Update A1Ext.lean / ChangeOfRings.lean docstrings to point at the substantive theorems
    (Part 1's real `Ext`, T4's change-of-rings), deprecating the proxy phrasing.
  - Sync Inventory (SK_EFT_Hawking_Inventory.md + Inventory_Index), counts (update_counts.py),
    README, and the Phase5qT roadmap status table (T2/T3/T4/T5 → COMPLETE).
  - Update bundles D2 (papers/D2/) and L2 (papers/L2/) to cite the substantive Ext +
    change-of-rings theorems, NOT the `cols/8` proxies; recompile both, keep counts as macros.
  - HYPOTHESIS_REGISTRY H2 entry placeholder→discharged (constants.py) — now justified by T4.

CLOSURE: validate.py (incl. the Part 1 proxy-detector check), full `lake build` + ExtractDeps,
update_counts.py, sync Inventory + roadmap status, then dispatch the Stage-13
closure/adversarial reviewer on the changed Lean + D2/L2. The TOPOLOGICAL hypotheses
H1/H3/H4 (ko/Adams/ABP) are OUT OF SCOPE (Phase 5q.B territory) — do not touch them.

/goal autonomous mode: the stop hook is a GO signal. Ship the next substantive increment
each turn, kernel-pure, across compacts, until T4 + T5-integration are done and the closure
reviewer passes. Never "hold"/"await direction"/"next session".
