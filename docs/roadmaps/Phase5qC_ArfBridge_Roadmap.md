# Phase 5q.C: Arf-bridge hardening — refactor the Rokhlin topological residue to its irreducible core

> # ⛔ NO-GO (2026-06-13): THE PHASE-1 ARF BRIDGE IS MATHEMATICALLY FALSE — DO NOT RUN THE PHASE-1 `/goal`
> The target bridge **`σ/8 ≡ Arf(q̄) (mod 2)`** (q̄ = `redQuad` on `L/2L`) is **FALSE**. `Arf(redQuad)` is
> **identically 0** on every even unimodular lattice: the discriminant form `L*/L` is trivial for unimodular
> `L`, so the finite Arf / Gauss-sum apparatus on `L/2L` sees only `σ mod 8`, never the mod-16 factor. Concrete
> refutation: **E₈ has `gaussSum = +16`, `#zeros = 136 = 2⁷+2³ ⟹ Arf(q̄) = 0`, but `σ(E₈)/8 = 1`** — so
> `0 = Arf(q̄) ≠ σ/8 = 1`. The bridge would force `arfOfForm E₈ = 1`; the truth is `arfOfForm E₈ = 0`.
> **Proved in `lean/SKEFTHawking/RokhlinArfNoGo.lean`** (`arfOfForm_e8lit_eq_zero`,
> `lattice_arf_bridge_refuted`, `redQuad_neg_eq`).
>
> **Root error:** conflating the *lattice* `Arf(redQuad)` with the *geometric* Guillou–Marin Arf of a smoothly
> embedded **characteristic surface** in the 4-manifold (Freedman–Kirby `σ ≡ Σ·Σ + 8·Arf(M,Σ) mod 16`). Those
> are different invariants; the geometric one is genuinely topological and is NOT what `redQuad` computes. The
> false identity came from an internally self-contradictory deep-research note.
>
> **Consequence:** Waves C.1–C.4 below and the Phase-1 `/goal` prompt (L151–188) are **VOID**. The irreducible
> Rokhlin residual **stays `topo : 2 ∣ σ/8`** (the geometric Atiyah–Singer / Freedman–Kirby input), carried as
> the tracked hypothesis per [ADR-003](../adrs/ADR-003-rokhlin-leg-discharge-and-deferred-topological-frontiers.md);
> it is NOT relocatable to a lattice `Arf=0`. `8 ∣ σ` (van der Blij, `eight_dvd_latticeSig`) remains TRUE and
> unconditional. See the no-go memory + ADR-003. **NEVER delete the `redQuad`/`gaussSum` machinery — it is
> correct; only this σ-bridge claim is wrong.**

## Technical Roadmap — June 2026

*Created 2026-06-08. Follows Phase 5q.B (unconditional `16 ∣ σ` via the classification route). Governed by
[ADR-003](../adrs/ADR-003-rokhlin-leg-discharge-and-deferred-topological-frontiers.md). PUBLIC repo. No new
axioms; kernel-pure `{propext, Classical.choice, Quot.sound}`; no `native_decide`; no `maxHeartbeats` in proof
bodies. North star: correctness over expedience; make the one irreducible hypothesis as small and transparent
as mathematically possible.*

---

## STATUS 2026-06-13 — ⛔ VOID: Phase-1 bridge REFUTED (see top banner)

**⛔ The Phase-1 plan in this STATUS block is a NO-GO.** `arfOfForm` is identically 0 on even unimodular
lattices, so the bridge `σ/8 ≡ Arf(q̄) mod 2` is FALSE (refuted in `RokhlinArfNoGo.lean`). The `/goal` below
must NOT be run. The residual stays `topo : 2 ∣ σ/8` (geometric). The remainder of this STATUS block is
retained for provenance only and is superseded by the top banner.

**This is THE authoritative roadmap for the Rokhlin `topo` discharge.** The 2026-06-13 substrate-weakness
reconciliation ranks it **#1** (score 92, the flagship — `docs/audits/SUBSTRATE_WEAKNESS_LIVE_BOARD_2026-06-13.md`
§B1). Entry-state **re-verified on disk 2026-06-13**: `EvenLattice.redQuad` + `redQuad_refines_redBilin` /
`redQuad_add` / `redQuad_zero` and `Arf.gaussSum_genus_g` all **PRESENT**; **`arfOfForm` does NOT yet exist →
C.1–C.4 are UNSTARTED.** The Phase-1 `/goal` below is ready to run as-is.

**Honesty (corrects the 5q.B header).** The 5q.B roadmap header reads "16∣σ UNCONDITIONAL" — that is
**OVERSTATED**. `8∣σ` is proven outright; `16∣σ` consumes `SmoothSpinManifold4.topo : 2∣σ/8`. This wave
RELOCATES that to `topo' : Arf(q̄)=0` (the genuine smooth-spin input) **and PROVES the bridge** — it does NOT
make `16∣σ` unconditional (mathematically impossible — E₈). Endpoint = *"16∣σ proven GIVEN Arf(q̄)=0."*

**Ecosystem re-check 2026-06-13** (fresh re-run of the ADR-003 Decision-#7 two-layer watch over the
leanprover-community org — 83 active repos): **nothing to pull in for this wave.** We already have `batteries` +
the full standard dep set (transitively via Mathlib) + `Physlib` direct. **Existence checks done by SEMANTIC
search** (lean4-skill `leansearch`/`loogle`/`leanfinder`, NOT grep — per `feedback_lean_semantic_search_over_grep`;
a tree-`grep "Arf"` returns only `line`**`arF`**`orm`/`Ch`**`arF`**`un` substring noise): **no Arf invariant**
anywhere (Mathlib pin v4.29.1 AND current master via leansearch/loogle, `sphere-eversion`, `physlib`); **no
Brown/Milgram Gauss-Milgram** (Mathlib's `NumberTheory.GaussSum` is the multiplicative-character sum, a different
object); **manifold spin structure absent** (only algebraic `CliffordAlgebra.spinGroup`); **cup-product / Poincaré
duality / intersection form / Stiefel-Whitney / Pontryagin / Chern / Witt-group all absent** (only the
`VectorBundle` foundation + the `PoincareConjecture` *statement*). So our hand-built `ArfInvariant.lean` is
necessary and Phase 1 is top-row in-repo assembly. **Reusable Mathlib substrate that DOES exist** (already used
by 5q.B/5q.C): `QuadraticForm.{sigPos,sigNeg}`, `equivalent_weightedSumSquares*` (diagonalization),
`QuadraticMap.discr`, `QuadraticForm.toDualProd` (hyperbolic `Q⊕(−Q)`), `CliffordAlgebra.{EquivEven,spinGroup}`.
**Phase-2 load-bearing bricks STILL ABSENT** → **deferral UNCHANGED, do NOT vendor**. Trajectory/warming
(gh master-tree, watch-don't-vendor): master added `QuadraticForm/{Signature,Radical,Basis}.lean` +
`QuadraticModuleCat/*`, `AlgebraicTopology/EilenbergSteenrod.lean` (cohomology AXIOMS), `Sites/SheafCohomology/*`,
`Manifold/PoincareConjecture.lean` (a STATEMENT, not duality). The sister doc
`Phase5qB_RokhlinTopoDischarge_Plan.md` is now a pointer here (this is the single source of truth).

---

## Why this wave exists

After Phase 5q.B, `SmoothSpinManifold4.rokhlin : 16 ∣ σ` is kernel-pure, consuming only `even_unimod` (Wu,
topological) and `topo : 2 ∣ latticeSig form / 8` (the irreducible smooth-topological residue). Per ADR-003:
`16 ∣ σ ⟺ (8 ∣ σ) ∧ (2 ∣ σ/8)`; we proved `8 ∣ σ`; `2 ∣ σ/8` is irreducible (the theorem is *false*
algebraically — E₈, σ=8 — so a smooth-category input is mathematically required and cannot be removed).

~~This wave does the **maximal honest hardening short of the geometric frontier**: it proves the algebraic
identity `σ/8 ≡ Arf(q̄) (mod 2)` and refactors the residual hypothesis from the opaque arithmetic form
`2 ∣ σ/8` into `Arf(q̄) = 0` — the genuine Arf invariant of the form's mod-2 quadratic refinement, tied to the
already-built `ArfInvariant.lean`. Same logical strength; far more transparent; connected to machinery.~~
**⛔ FALSE (2026-06-13).** This paragraph is the root error. `σ/8 ≡ Arf(q̄) (mod 2)` does NOT hold: `Arf(q̄)`
(the lattice Arf of `redQuad` on `L/2L`) is identically 0 on every even unimodular lattice, whereas `σ/8` is
not (E₈: `Arf=0`, `σ/8=1`). The two are *not* the same logical strength — the lattice Arf carries no mod-16
information. The residual `2 ∣ σ/8` is irreducibly **geometric** (Guillou–Marin Arf on a characteristic
surface), not a lattice invariant. See top banner + `RokhlinArfNoGo.lean`.

**Why this is tractable now (top-row, days — see ADR-003 LOE table).** It needs *no new Mathlib foundation*.
The classification existence (`E₈^a ⊕ (−E₈)^b ⊕ Hᶜ`) is already proven (Phase 5q.B `[HM]`+`[Θ]`); σ-additivity
is in `RokhlinClassification`; Arf-additivity is `Arf.gaussSum_genus_g` (`ArfInvariant.lean`); the generator
Arf-values are finite `decide`. The whole bridge is an assembly of in-repo bricks.

**Entry-state ground truth (verified 2026-06-08 via lean-lsp local search):**
- `SKEFTHawking.Arf.arf` (abbrev) + `Arf.gaussSum_genus_g`, `Arf.arf_democratic`, `Arf.arf_surjective` —
  `ArfInvariant.lean`. The genus-`g` Arf Gauss sum gives `2^g·(−1)^{∑Arf}` ⟹ Arf is additive over `⊕`.
- `SKEFTHawking.EvenLattice.redQuad` (def, the mod-2 refinement q̄) + `redQuad_refines_redBilin`
  (`q̄` refines `b̄`), `redQuad_add`, `redQuad_zero` — `EvenLatticeForm.lean`.
- `SmoothSpinManifold4.{rank, form, even_unimod, topo}` — `SpinRokhlinInterface.lean`; `topo` is the field to
  refactor. `latticeSig`, `latticeSig_of_posDef/negDef`, classification calculus — present.

---

## Phase 1 — the Arf bridge  [⛔ VOID — REFUTED 2026-06-13; DO NOT RUN]

> **⛔ Waves C.1–C.4 below are VOID.** The capstone they build to — `latticeSig_div_eight_modTwo_eq_arf`
> (`σ/8 ≡ arfOfForm M mod 2`) — is FALSE (`arfOfForm` is identically 0 on even unimodular lattices; E₈ gives
> `arf=0`, `σ/8=1`). Refuted in `RokhlinArfNoGo.lean`. Retained below for provenance; do NOT execute.

### Wave C.1 — Arf invariant of `redQuad` as a genus structure
Connect `EvenLattice.redQuad form` to the `Arf.arf` genus/refinement structure (`Arf.arf` is currently stated
on an abstract `IsRefinement`; instantiate it on `redQuad`, using `redQuad_refines_redBilin` for the
refinement law and unimodularity ⟹ `b̄` nondegenerate for the symplectic structure). Output: a well-defined
`arfOfForm (M) : ZMod 2` for even unimodular `M`, `= Arf.arf` of the refinement of `redBilin M`.

### Wave C.2 — Arf values on the generators  [⛔ VALUES WRONG — VOID]
~~`arfOfForm E₈ = 1`, `arfOfForm (−E₈) = 1`, `arfOfForm H = 0`.~~ **⛔ FALSE (2026-06-13).** The correct
finite-F₂ computation is **`arfOfForm E₈ = 0`** (and `arfOfForm (−E₈) = 0`, `arfOfForm H = 0`) — the lattice
Arf of `redQuad` is identically 0 on every even unimodular lattice (E₈: `gaussSum = +16`, `#zeros = 136 ⟹
Arf = 0`; proved `arfOfForm_e8lit_eq_zero` in `RokhlinArfNoGo.lean`). The "`= 1`" values are exactly what the
false bridge below would have required, and are the tell that the bridge is wrong (`σ(E₈)/8 = 1 ≠ 0`).

### Wave C.3 — Arf additivity + the bridge `σ/8 ≡ Arf(q̄) (mod 2)`  [⛔ BRIDGE FALSE — VOID]
- `arfOfForm (A ⊕ B) = arfOfForm A + arfOfForm B` (mod 2), via `Arf.gaussSum_genus_g` / `gaussSum_orthogonal`
  applied to the block structure (the orthogonal-sum refinement is the sum of refinements). *(Additivity itself
  is fine, but with all generator values = 0 it only yields `arfOfForm M = 0` for every even unimodular M.)*
- ~~**`latticeSig_div_eight_modTwo_eq_arf`** (even unimodular `M`): `(latticeSig M / 8 : ℤ) ≡ arfOfForm M (mod 2)`.
  Proof: classification `M ≅ E₈^a ⊕ (−E₈)^b ⊕ Hᶜ` (Phase 5q.B existence) ⟹ `σ/8 = a − b` (σ-additivity,
  `RokhlinClassification`) and `arfOfForm M = a + b` (C.2 + C.3 additivity) ⟹ `a − b ≡ a + b (mod 2)`.~~
  **⛔ FALSE (2026-06-13).** The step "`arfOfForm M = a + b`" is wrong because the generator values are 0 (C.2
  above), giving `arfOfForm M = 0` for all even unimodular `M`, while `σ/8 = a − b` is generically nonzero (E₈:
  `a=1, b=0 ⟹ σ/8 = 1 ≠ 0`). So `(σ/8 mod 2) ≠ arfOfForm M` in general. Refuted: `lattice_arf_bridge_refuted`
  in `RokhlinArfNoGo.lean`.
  - **Scope note (covers the manifold application):** smooth spin 4-manifold forms are **indefinite**
    (Donaldson), so the `E₈^a ⊕ (−E₈)^b ⊕ Hᶜ` normal form (which Phase 5q.B established) suffices. The fully
    general *definite* case would additionally need the definite even-unimodular classification (E₈^a is not
    the only definite even unimodular form in rank ≥ 16: D₁₆⁺, Leech, …) — **not needed here**; if pursued for
    generality, prove `σ/8 ≡ Arf mod 2` is a congruence invariant directly (van der Blij), tracked separately.

### Wave C.4 — Refactor the interface + sync
- Replace `SmoothSpinManifold4.topo : 2 ∣ latticeSig form / 8` with **`topo' : arfOfForm form = 0`**
  (the sharp, transparent form). Re-prove `SmoothSpinManifold4.rokhlin` via `latticeSig_div_eight_modTwo_eq_arf`
  (`arf = 0` + `8 ∣ σ` ⟹ `2 ∣ σ/8` ⟹ `16 ∣ σ`). Keep a `topo`-form corollary for back-compat if any consumer
  needs it.
- Update `HYPOTHESIS_REGISTRY['rokhlin_sigma_mod_16']`: note the residual is now expressed as `Arf(q̄)=0`
  (the Freedman–Kirby Arf-vanishing), pointer to ADR-003 + Phase 5q.C; status stays `discharged` for `16∣σ`
  with the one tracked topological input named precisely.
- Update D2/L2 prose: the bordism leg's single tracked input is `Arf(q̄)=0` (smooth Freedman–Kirby vanishing),
  not an opaque `2∣σ/8`. Recompile; counts as macros. Stage-13 (claims + adversarial) on changed Lean + D2/L2.

**Stage gates:** lean-lsp loop per lemma; `lean_verify` axiom-purity on `latticeSig_div_eight_modTwo_eq_arf`
and the refactored `rokhlin`; `lake build` + ExtractDeps; `validate.py`; update_counts + Inventory + this
roadmap status; closure reviewer.

---

## Phase 2 — geometric discharge of `Arf(q̄) = 0` (FRONTIER, DEFERRED — spike-confirmed, see ADR-003)

Discharging `arfOfForm form = 0` *from an actual smooth spin 4-manifold* is the irreducible smooth-topology
content (Freedman–Kirby / Guillou–Marin, or Atiyah–Singer Â-even).

**Scouting spike RUN (2026-06-09):
[LegC_GeometricResidue_ScoutingSpike](../assessments/LegC_GeometricResidue_ScoutingSpike.md).** It did the
interface-first, fragment-by-fragment decomposition ADR-003 Decision #3 required, and concluded **DEFER on
evidence.** Resolved tiering (the prior "FK is middle-row" was an over-correction): a Leg-C route's band is set
by its slowest link, and **both routes are bottom-row at the capstone.** For the leaner FK route, by layer:
- *entry* — assemble a closed oriented smooth 4-manifold on `SmoothManifoldWithCorners`: **MIDDLE-ROW** ✓;
- *prerequisites* — singular **cohomology + cup product**, **Poincaré duality + fundamental class**, the
  **intersection form**, and (for evenness) a **manifold spin structure + Wu formula**: **BOTTOM-ROW** to build
  (Mathlib has singular *homology* only and an *algebraic* `spinGroup` only);
- *capstone* — the **Guillou–Marin congruence**: **BOTTOM-ROW, tier-2 — never formalized in any proof
  assistant.**

The spike's decisive finding: **no interface-first narrowing dodges constructing the form from the manifold**
(the algebraic shadow is already fully captured by Phase 1 here), so the geometric residue genuinely needs the
absent cohomology+PD layer. `topo'` is therefore the **permanent irreducible hypothesis** (honest by
mathematical necessity — E₈ is the algebraic counterexample), not a "pending-a-spike" placeholder.

**Re-trigger (per ADR-003, sharpened by the spike):** the gating brick is singular **cohomology cup product +
Poincaré duality / fundamental class** for closed manifolds (FK route). **Leading indicator (NEW):**
`AlgebraicTopology.singularHomologyFunctor` *already landed* in Mathlib v4.29.x — homology is the prerequisite
for the brick, so the brick is on the community trajectory; monitor `loogle "singularCohomology"`,
`loogle "cup"`, `leanfinder "Poincaré duality fundamental class"` periodically. Activate this phase when that
brick lands (then the residual build is spin-structure/Wu + the Guillou–Marin capstone), **or** when
Pontryagin/characteristic classes + a geometric Dirac operator land (AS fallback; watch `loogle "Pontryagin"`,
`loogle "Dirac"`, `leanfinder "A-hat genus"`), **or** when the project deliberately funds foundational
algebraic topology because a publication demands the *literal* smooth discharge. The wave plan (FK: assemble
form → spin-structure/Wu → Guillou–Marin ⟹ `Arf=0`) lives here so reactivation is execution, not re-planning.

---

## `/goal` prompt (Phase 1 — paste to run autonomously; <4k chars)  [⛔ VOID — DO NOT RUN]

> **⛔ DO NOT RUN THIS `/goal` (2026-06-13).** Its stated objective (`σ/8 ≡ Arf(q̄) mod 2`,
> `arfOfForm E₈ = 1`, refactor `topo → topo' : arfOfForm form = 0`) is mathematically FALSE — `arfOfForm` is
> identically 0 on even unimodular lattices, so `arfOfForm form = 0` is vacuous and does NOT capture `2 ∣ σ/8`.
> Refuted in `RokhlinArfNoGo.lean`. The whole prompt below is retained for provenance only.

GOAL: Execute Phase 5q.C Phase 1 — the Arf-bridge hardening. Prove `σ/8 ≡ Arf(q̄) (mod 2)` for even
unimodular forms and refactor the Rokhlin topological residue from `topo : 2 ∣ latticeSig form / 8` to
`topo' : arfOfForm form = 0`. PUBLIC repo. Read docs/roadmaps/Phase5qC_ArfBridge_Roadmap.md +
docs/adrs/ADR-003-*.md FIRST. Phase 2 (geometric `Arf=0`) is DEFERRED — do NOT open it.

HARD INVARIANTS: axioms exactly {propext, Classical.choice, Quot.sound}; NO new project-local `axiom`; NO
`native_decide`; NO `sorry`; NO maxHeartbeats in proof bodies (decompose into `have`; maxRecDepth OK); never
weaken statements to pass. Parallel agent shares `main`: stage ONLY your own paths (never add -A/-a/.), never
push. Dev loop = lean-lsp MCP (lean_goal → lean_multi_attempt → write); lean_verify each new theorem.

REUSE (verified in-repo, do NOT rebuild): `SKEFTHawking.Arf.arf` + `Arf.gaussSum_genus_g`/`arf_democratic`
(ArfInvariant.lean); `SKEFTHawking.EvenLattice.redQuad` + `redQuad_refines_redBilin`/`redQuad_add`
(EvenLatticeForm.lean); the classification existence + σ-additivity (RokhlinClassification / Phase 5q.B
RokhlinHMRankFour); `latticeSig` + `latticeSig_of_posDef/negDef` (LatticeSignature.lean);
`SmoothSpinManifold4` (SpinRokhlinInterface.lean).

WAVES:
C.1 — define `arfOfForm (M) : ZMod 2` for even unimodular M as `Arf.arf` of the refinement of `redBilin M`,
  using `redQuad_refines_redBilin` (refinement law) + unimodularity ⟹ `b̄` nondegenerate (symplectic).
C.2 — ⛔FALSE `arfOfForm E₈ = 1`, `arfOfForm (−E₈) = 1`, `arfOfForm H = 0` (finite `decide` / `arf_democratic`).
  [the true values are all 0 — see `arfOfForm_e8lit_eq_zero`, `RokhlinArfNoGo.lean`; this is why the goal is void.]
C.3 — `arfOfForm (A⊕B) = arfOfForm A + arfOfForm B` (via gaussSum_genus_g / orthogonal sum); then the
  capstone `latticeSig_div_eight_modTwo_eq_arf : even unimodular M → (latticeSig M/8 : ℤ) ≡ arfOfForm M [ZMOD 2]`
  from classification (σ/8 = a−b) + Arf-additivity (arf = a+b) + a−b ≡ a+b mod 2. Indefinite normal form
  suffices (Donaldson ⟹ smooth spin 4-mfld forms indefinite); do NOT chase the definite classification.
C.4 — refactor `SmoothSpinManifold4`: `topo` → `topo' : arfOfForm form = 0`; re-prove `rokhlin` via the
  bridge + proven `8∣σ`; keep a `2∣σ/8` corollary for back-compat. Update HYPOTHESIS_REGISTRY (residual named
  as Arf(q̄)=0, pointer to ADR-003), D2/L2 prose (single tracked input = Freedman–Kirby Arf-vanishing),
  recompile, counts-as-macros.

CLOSURE: lean_verify axiom-purity on the bridge + refactored `rokhlin`; `lake build` + ExtractDeps;
validate.py; update_counts + Inventory + this roadmap status; dispatch Stage-13 closure/adversarial reviewer on
changed Lean + D2/L2. Then STOP — Phase 2 is trigger-gated, not part of this goal.

/goal autonomous mode: the stop hook is a GO signal. Ship the next substantive increment each turn,
kernel-pure, until C.1–C.4 are done and the reviewer passes. Never "hold"/"await direction"/"next session".

---

*Phase 5q.C roadmap. Created 2026-06-08. Governed by ADR-003. Follows
[Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).*
