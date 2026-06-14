# Leg-C scouting spike — discharging the Rokhlin geometric residue `Arf(q̄) = 0` from a smooth spin 4-manifold

## Assessment (read-only; no Lean edits) — 2026-06-09

*Run per [ADR-003](../adrs/ADR-003-rokhlin-leg-discharge-and-deferred-topological-frontiers.md) Decision #3
("run a SCOUTING SPIKE before any defer/open decision"). This is the first-principles, interface-first
decomposition of the **leanest** route to discharge the one irreducible topological residue carried by
`SmoothSpinManifold4` — `topo'` (post-5qC: `arfOfForm form = 0`, equivalently `2 ∣ σ/8`). It converts
"Leg-C is hard" from an anchored guess into a fragment-level dependency graph, each link tagged
Mathlib/physlib-have-vs-build and velocity-row. PUBLIC repo; planning artifact only — no `.lean` touched, no
build run (safe alongside the concurrent 6AM/6AN public-side work).*

---

## 1. Purpose

ADR-003 self-corrected an overstatement ("can't be formalized") into "Leg-C-FK is middle-row, run a spike
first." The spike's job is to settle, **on evidence rather than on either prior**, which of three things is
true of the leanest Rokhlin discharge route:
- (a) it is a pure *encoding* problem on existing substrate (→ open it; middle-row), or
- (b) it has a genuine bottom-row capstone with no proof-assistant blueprint (→ defer, but with a precise,
  monitorable trigger), or
- (c) it is mathematically impossible (→ it is not; the hypothesis is *true* — it is Rokhlin's theorem).

**Verdict (full reasoning in §7):** (b). The deferral in ADR-003 / Phase5qC §Phase 2 is **earned on
evidence**, with the row-tiering tension resolved (the *capstone* is bottom-row; only the *entry layer* is
middle-row) and the trigger sharpened to a single named gating brick that **Mathlib is now actively building
toward** (singular homology is present in our v4.29.1 pin and the homology/bordism layers are maturing
upstream — a concrete leading indicator the spike surfaced; the ADR-003 first draft, written earlier this same
session *before* the spike, simply predates it — see §3d for the live-repo delta vs. master).

---

## 2. Method

Per memory `feedback_lean_semantic_search_over_grep`: presence/absence claims established with **semantic
search** (`lean_local_search`, `lean_leanfinder`), scope-calibrated, **not** grep. Searches ran on the
`lean-lsp-netrxn` server, whose project scope indexes **Mathlib + physlib + (private) together** — so a single
search answers "is X in Mathlib *or* physlib?" Calibration: `CliffordAlgebra` (Mathlib) and `LorentzGroup` /
`MState` (physlib) both resolve; `Spin`→only a `Hollom.SpinalMap` counterexample, confirming the index is warm
and absence results are real. Mathlib pin = v4.29.1.

---

## 3. Verified inventory (the evidence)

### 3a. Substrate that EXISTS (assemblable — these make the *entry* layer middle-row)

| Object | Decl / file (verified) | Use to a Rokhlin route |
|---|---|---|
| Smooth manifolds, diffeomorphism, spheres | `Geometry.Manifold.*`; `Mathlib.Geometry.Manifold.PoincareConjecture` (statement-only def `NonemptyDiffeomorphSphere`) | the 4-manifold object (FK-1, AS-1) |
| Vector bundles + tangent bundle | `Mathlib.Topology.VectorBundle.*` (`VectorBundleCore.vectorBundle`, Hom-bundles) | *foundation* for characteristic classes (AS-4) — classes themselves absent |
| Differential forms + exterior derivative | `Analysis/Calculus/DifferentialForm` (`extDeriv`, `extDeriv_extDeriv` = d²=0) | de Rham forms substrate (AS-4); cohomology assembly absent |
| Exterior / wedge algebra | `ExteriorAlgebra.gradedAlgebra` (graded), `ExteriorAlgebra` | wedge of forms; not yet a cohomology cup product |
| Clifford algebra + algebraic spin/pin groups | `CliffordAlgebra` (`…/CliffordAlgebra/Basic`); `spinGroup`, `pinGroup` (`…/SpinGroup.lean`) | algebra only — **not** manifold spin *structures* |
| Quadratic-form signature (Sylvester) | `QuadraticForm.sigPos/sigNeg` + `Equivalent.sigPos_eq` (`…/QuadraticForm/Signature`) | already the 5qB `latticeSig` substrate |
| **Singular homology** (NEW) | `AlgebraicTopology.singularHomologyFunctor` (`…/AlgebraicTopology/SingularHomology/Basic`) | **leading indicator**: the homology layer just landed; cohomology+cup+PD is the natural next community step |
| Elliptic-analysis flavor | `SchwartzMap.laplacianCLM`, iterated Fréchet derivative, Laplacian | *flavor* only; no Fredholm index / elliptic-operator index on manifolds |

### 3b. Load-bearing layer that is ABSENT (Mathlib *and* physlib)

| Missing object | Search evidence | Needed by |
|---|---|---|
| Singular **cohomology** + **cup product** / cohomology ring | `singularCohomology`→∅; `cup`→∅; leanfinder "cup product on singular cohomology"→only cochain-complex `CohomologyClass` | FK-3 (the gating brick) |
| **Poincaré duality** + **fundamental class** of a closed manifold | `Poincare`→∅; `fundamentalClass`→∅ | FK-4 (the gating brick) |
| **Intersection form** of a 4-manifold | `intersectionForm`→∅; `intersectionMatrix`→∅ | FK-5 |
| Manifold **spin/pin structures** (principal bundles) | `Spin`→only `Hollom.SpinalMap`; only *algebraic* `spinGroup`/`pinGroup` exist | FK-6, AS-1 |
| **Characteristic classes** (SW / Pontryagin / Chern / Euler) | `StiefelWhitney`→∅; `Pontryagin`→only `PontryaginDual` (group duality); `eulerClass`→∅; leanfinder → only `VectorBundle` substrate | FK-6 (Wu), AS-4 |
| **Characteristic surfaces** + **Guillou–Marin / Freedman–Kirby** congruence | leanfinder "Rokhlin/Arf characteristic surface/Guillou–Marin"→∅ (returns `PoincareConjecture`, the unrelated `ADEInequality.E8`, root-system forms) | FK-7 (the capstone) |
| **Dirac operator** + **index theorem** + **Â-genus** | `Dirac`→∅; leanfinder "Atiyah–Singer index"→only Schwartz/Laplacian analysis | AS-2…AS-5 |
| **Thom / cobordism / bordism** | `Thom`→∅; `Cobordism`→∅; `Bordism`→∅ | Leg-D / bordism route |

### 3c. physlib — answered definitively

physlib (HepLean/PhysLean) indexes as **Relativity** (`LorentzGroup`, real tensors), **Electromagnetism**, and
**QuantumInfo** (`MState`, entropy/DPI). The spin/Dirac/topology cluster searches above returned **zero**
physlib hits (the only matches were Mathlib's `CliffordAlgebra`, `PontryaginDual`, `singularHomology`). physlib
contributes **nothing** to Leg-C — confirming the ADR-003 disk inventory by a second, independent method.

### 3d. Live-repo delta — master vs. our pin (the "we're behind HEAD" check, `gh` 2026-06-09)

Our search above is scoped to our **pinned** Mathlib v4.29.1. Because upstream moves fast, the spike also
queried the **live repos** (`gh api .../git/trees/master`) to find foundations that have landed since our pin
and could be **vendored now / re-wired at the next bump**:

- **Mathlib master is `v4.31.0-rc2`** (we pin `v4.29.1` — ~2 minor versions behind). PhysLean master is `v4.30.0`.
- **NEW at Mathlib master, ABSENT in our pin** (real upstream motion on the relevant stack):
  - **`Mathlib/Geometry/Manifold/Bordism.lean`** (M. Rothgang) — **unoriented bordism theory, first brick.**
    Defines `SingularManifold X k I` (a closed `Cᵏ`-manifold + map `M → X`) with `refl`/`empty`/`sum`/`map`
    functoriality. The docstring states bordism *groups* + their abelian-group structure are **explicit future
    PRs.** So bordism has *started* upstream but Ω^Spin (let alone `Ω^Spin_4 ≅ ℤ`) is many PRs away
    (needs: bordism relation → groups → oriented → spin → computation).
  - **`SingularHomology/HomotopyInvariance(+TopCat)`** — homotopy invariance of singular homology (a major
    Eilenberg–Steenrod step, precursor to cohomology + cup product).
  - **`Algebra/Homology/SpectralSequence/{Basic,ComplexShape}`** — a *concrete* spectral-sequence layer atop
    the abstract `SpectralObject` machinery (relevant to a future Adams SS).
- **STILL ABSENT even at Mathlib master (v4.31):** singular **cohomology + cup product**, **Poincaré
  duality / fundamental class**, **characteristic classes** (SW/Pontryagin/Chern/Euler), Chern–Weil,
  intersection form, manifold **spin structures**, **Dirac/index/Â-genus**. (Name-collision false positives
  ruled out: `WhitneyEmbedding` = the embedding theorem, not Stiefel–Whitney; `EulerCharacteristic` = the
  homological alternating sum, not the Euler class.) So **both the FK and AS capstones' prerequisites remain
  un-shipped upstream** — the deferral verdict is unchanged by the live-repo check.
- **PhysLean master (v4.30):** the only topology-adjacent content is gauge **AnomalyCancellation** (SM/MSSM/BSM
  `ACCSystem`) — the *physics-premise* asset already noted, **not** the topological residue. Nothing for
  Leg-C/Leg-D, confirmed at HEAD.

**Vendoring assessment (now): premature, low payoff.** `Bordism.lean` is small (258 lines) but (a) only
delivers `SingularManifold` — *not load-bearing* for any 5q discharge yet (no bordism groups, no spin, no
computation), and (b) uses the **Lean 4.31 module system** (`module` / `public import`), so back-porting to our
v4.29.1 pin is non-trivial. The right posture is **vendor-and-rewire only when a *load-bearing* brick lands
upstream ahead of our official bump** — defined per leg as: **Leg-C** = cup-product cohomology **+** Poincaré
duality (both); **Leg-D** = oriented/spin bordism groups **+** a low-degree computation (or the Adams/ABP
stack). Until then, **watch, don't vendor.**

### 3e. Strategic assumption — plan for fast (super-linear) upstream growth

Mathlib/PhysLean are on a steep, AI/human-collaborative growth curve (e.g., bordism theory went from *absent*
to *started* between our pin and master). The 5q deferred-frontier posture is therefore built to **assume the
gating bricks arrive on a months-not-years horizon**, and to make adoption cheap when they do:
1. **Scheduled watch, not "someday":** re-run the `gh` master tree-grep (this §3d) at every pin-bump
   consideration and on a periodic cadence; the trigger declarations are named in ADR-003's Re-trigger table.
2. **Keep interfaces re-wire-ready:** `SmoothSpinManifold4` (one field `topo'`) and `HYPOTHESIS_REGISTRY` are
   the single swap points — when upstream ships the brick, discharge `topo'` and flip the registry entry; no
   architectural change. 5q.C's refactor to `arfOfForm = 0` deliberately minimizes this swap surface.
3. **Bias to vendor-and-rewire** over waiting for the official pin bump, *once a load-bearing brick lands*
   (per §3d criteria) — capturing the discharge early, then normalizing at the next bump.

---

## 4. The target, and why there is no interface-first dodge

> **⚠️ CORRECTION (2026-06-13) — this section conflates the LATTICE Arf with the GEOMETRIC Guillou–Marin Arf;
> the lattice statements below are FALSE.** The target `arfOfForm form = 0` (with `arfOfForm` = the Arf of
> `redQuad` on `L/2L`) is **NOT** the smoothness obstruction for `16∣σ`, and there is no lattice route to it:
> `arfOfForm` is **identically 0 on every even unimodular lattice** (E₈: `gaussSum = +16`,
> `#zeros = 136 = 2⁷+2³ ⟹ Arf = 0`, yet `σ(E₈)/8 = 1` is odd), because the discriminant form `L*/L` is trivial
> for unimodular `L`, so the lattice Arf/Gauss-sum apparatus sees only **σ mod 8**. The genuine geometric
> residue is `2 ∣ σ/8`, equivalently the vanishing of the **geometric** Guillou–Marin Arf on a smoothly
> embedded *characteristic surface* (the FK-7 congruence `σ − F·F ≡ 8·Arf(M,Σ) mod 16` below — which is TRUE
> and a *different object* than the lattice `arfOfForm`). The two were conflated by an internally
> self-contradictory deep-research note. Machine-checked refutation: `lean/SKEFTHawking/RokhlinArfNoGo.lean`
> (`arfOfForm_e8lit_eq_zero`, `lattice_arf_bridge_refuted`, `redQuad_neg_eq`). The §4 reasoning that "the form
> must be constructed from the manifold; there is no interface-first dodge; the defer is earned" is **still
> correct** — only the specific *target object* (`arfOfForm form = 0` as a lattice quantity, and the claim that
> E₈ has `arfOfForm = 1`) is wrong. Read "discharge `2 ∣ σ/8` geometrically" in place of "discharge
> `arfOfForm form = 0`."

Discharge `2 ∣ σ/8` (the geometric residue) **for a form that comes from an actual smooth spin 4-manifold**.
The substantive content is *constructing the intersection form from the manifold and proving the geometric
Guillou–Marin Arf (on a characteristic surface) vanishes*; it cannot be obtained by any **lattice-algebraic**
narrowing, because the lattice apparatus only ever reaches `σ mod 8` (van der Blij) — the E₈ counterexample
(`σ = 8`, `σ/8 = 1`) shows precisely that no lattice invariant of an even unimodular form distinguishes
`σ mod 16`. *(CORRECTION 2026-06-13: the original text here read "Discharge `arfOfForm form = 0` … for those it
is false: E₈ has `arfOfForm = 1`." That is wrong — E₈ has `arfOfForm = 0`; see banner above and
`RokhlinArfNoGo.lean`.)*

I explicitly looked for a leaner route (anti-wall discipline — decompose before asserting a wall):
- **The F=∅ / spin trick** (the null-homologous characteristic surface) collapses FK-8 to triviality but does
  **not** remove the need to *prove* the Guillou–Marin congruence (FK-7) or to *construct* the form (FK-2…5).
- **The algebraic shadow.** ~~(`σ ≡ 8·Arf mod 16`, van der Blij) is **already maximally captured** by Phase 5q.C
  Phase 1 (`latticeSig_div_eight_modTwo_eq_arf`).~~ **⚠️ CORRECTION 2026-06-13: this is FALSE.** There is no
  lattice identity `σ ≡ 8·Arf(q̄) mod 16` (with `q̄ = redQuad`): the *lattice* `Arf(redQuad)` is identically 0
  on every even unimodular lattice, so it determines only `σ mod 8` (the genuine van der Blij shadow), never the
  σ-mod-16 factor. The Phase 5q.C "Arf bridge" / `latticeSig_div_eight_modTwo_eq_arf` is **refuted** by
  `lean/SKEFTHawking/RokhlinArfNoGo.lean`. The correct algebraic shadow is just `8 ∣ σ` (van der Blij) — which
  *is* fully captured — and there is **no further algebraic content to extract** toward `σ mod 16`. The
  remaining factor of two is irreducibly geometric.
- **The bordism route** (σ is a spin-bordism invariant, `Ω^Spin_4 ≅ ℤ`) is Leg-D — a *different* bottom-row
  frontier (stable homotopy), and circular for Rokhlin.

Conclusion: every genuine discharge must construct the form from the manifold, which requires the
cohomology + Poincaré-duality layer (§3b). 5q.C is the floor of the interface-first narrowing; the geometric
residue genuinely needs the absent layer.

---

## 5. Route C-FK (Freedman–Kirby / Guillou–Marin) — fragment decomposition

The leanest classical route. Spin ⟹ take the characteristic surface `F = ∅`.

| # | Fragment | Needs | Status | Row |
|---|---|---|---|---|
| FK-1 | closed oriented smooth 4-manifold (structure) | assemble on `SmoothManifoldWithCorners` (compact, oriented, ∂=∅, dim 4) | substrate ✓ | **MIDDLE** (assembly) |
| FK-2 | `H₂(X;ℤ)`, `H²(X;ℤ)` | singular cohomology | homology ✓, cohomology ✗ | **BOTTOM** (build cohomology) |
| FK-3 | cup product → cohomology ring | the pairing `H²×H²→H⁴` | ✗ | **BOTTOM** — *gating brick*, no encoding blueprint |
| FK-4 | Poincaré duality + fundamental class | `H⁴(X)≅ℤ`, perfect pairing | ✗ | **BOTTOM** — *gating brick*, no encoding blueprint |
| FK-5 | intersection form = even unimodular | unimodular ⟸ FK-4; even ⟸ FK-6 | ✗ (depends FK-3,4,6) | **BOTTOM** |
| FK-6 | manifold spin structure + `w₂=0` ⟹ even (Wu) | spin *structure*, SW classes, Wu formula | ✗ (only algebraic `spinGroup`) | **BOTTOM** (parallel gap) |
| FK-7 | **Guillou–Marin congruence** `σ − F·F ≡ 8·Arf mod 16` | characteristic surfaces, Pin⁻ quadratic enhancement / Brown invariant, surgery-or-bordism argument | ✗ | **BOTTOM** — **the capstone wall; never formalized in any proof assistant** |
| FK-8 | spin ⟹ `F=∅` characteristic, `F·F=0`, `Arf=0` ⟹ `σ≡0 mod 16` | trivial once FK-1…7 exist | — | **TOP** (the easy finish) |

**Reading.** FK has a middle-row *entry* (FK-1) but two independent **bottom-row** sub-stacks on the critical
path: the cohomology/cup/PD/intersection-form layer (FK-2…5) and the spin-structure/Wu layer (FK-6), feeding
the **bottom-row capstone FK-7** which has *no encoding blueprint anywhere*. This is what makes the *capstone
row* bottom — the earlier "middle-row, just an encoding question" framing was an over-correction that applied
the *entry* row to the whole route.

---

## 6. Route C-AS (Atiyah–Singer / Â-genus) — fragment decomposition (the fallback)

| # | Fragment | Needs | Status | Row |
|---|---|---|---|---|
| AS-1 | Riemannian spin 4-manifold | metric (physlib GR / Mathlib inner-product, partial) + manifold spin *structure* | spin structure ✗ | **BOTTOM** |
| AS-2 | spinor bundle + geometric Dirac operator | associated bundle to spin structure; first-order elliptic op | ✗ (Clifford *algebra* only) | **BOTTOM** |
| AS-3 | Fredholm index of `D` | elliptic/Fredholm theory on manifolds | ✗ (Schwartz/Laplacian flavor only) | **BOTTOM** |
| AS-4 | Chern–Weil → Pontryagin → Hirzebruch signature theorem | connection/curvature→cohomology; `p₁`; `σ=⅓p₁` | ✗ | **BOTTOM** |
| AS-5 | **Atiyah–Singer index theorem** (`ind = ∫Â`) | the full theorem | ✗ | **BOTTOM (tier-2, generational)** — never formalized in any PA |
| AS-6 | `Â=−σ/8` + index even (quaternionic) ⟹ `16∣σ` | AS-4 + AS-5 + mod-2 index | ✗ | **BOTTOM** |

AS is **strictly deeper** than FK: its capstone (AS-5) is one of the deepest theorems in mathematics. It is the
documented fallback, **not** the recommendation.

---

## 7. Verdict — defer earned (evidence-based), tiering resolved, trigger sharpened

**(1) The hypothesis is TRUE and the carry is honest.** `Arf(q̄)=0` for smooth spin 4-manifolds *is* Rokhlin's
theorem (1952; reproven by Atiyah–Singer 1963 and Freedman–Kirby 1978). It is non-vacuous (E₈ violates it;
H/K3 satisfy it) and mathematically necessary (tier-1: a smooth-category input is required — E₈ and Freedman's
*topological* E₈-manifold are the counterexamples). We are not "flat wrong": we carry a true, irreducible fact.

**(2) Row-tiering tension RESOLVED.** The ADR-003 self-correction ("Leg-C-FK middle-row") and the dependency
table ("bottom") are both partly right and were conflating layers:
- **Entry layer (FK-1): MIDDLE-ROW** — assemblable on existing manifold substrate.
- **Prerequisite layer (FK-2…6): BOTTOM-ROW to build** — but the cohomology/cup/PD sub-stack is *actively
  developing in Mathlib* (singular homology just landed; see leading indicator below).
- **Capstone (FK-7 Guillou–Marin): BOTTOM-ROW, tier-2** — settled *mathematics*, but **no formalization
  blueprint in any proof assistant**. Our compression comes from transcribing an *encoding* blueprint; for
  FK-7 there is none, so velocity genuinely drops to the ~1–5× bottom-row band.

So the **capstone row is bottom** (the dependency table was right); the "middle-row" label correctly described
only the entry. The honest one-line tier is: *bottom-row capstone, middle-row entry, with a precisely-named
gating brick on a watchable community trajectory.*

**(3) No interface-first dodge exists** (§4) — the form must be built from the manifold, requiring the absent
cohomology+PD layer; the algebraic shadow (`8 ∣ σ`, van der Blij) is already fully captured by 5q.C. *(CORRECTION
2026-06-13: "algebraic shadow" here means only `8 ∣ σ` — the lattice apparatus captures nothing beyond it. The
once-claimed lattice bridge `σ ≡ 8·Arf(redQuad) mod 16` is FALSE; see the §4 banner and `RokhlinArfNoGo.lean`.)*
Anti-wall discipline satisfied: the wall was decomposed, not asserted.

**(4) Therefore: DEFER Leg-C-geometric — now on evidence, not on a reflex.** Opening it would mean building a
multi-foundation stack (cohomology ring + Poincaré duality + intersection form + spin structures + Wu) and then
a research-grade, never-formalized capstone (Guillou–Marin). Not warranted unless (a) a publication demands the
*literal* smooth discharge, or (b) the project elects to fund foundational algebraic topology as a standalone
Mathlib-landmark contribution. Neither holds today.

**(5) No pre-trigger down-payment beyond 5q.C is worthwhile.** Any "interface" we could add now without the
cohomology layer would merely re-axiomatize the residual at a different level (a new `Prop := True` pointer or a
new axiom — both worse than the current single tracked hypothesis). 5q.C Phase 1 is the maximal honest
hardening; do it, and stop there on the geometric side.

### The sharpened trigger + the NEW leading indicator

| | Pre-spike (ADR-003 draft) | Post-spike (this document) |
|---|---|---|
| Trigger granularity | "Mathlib ships algebraic topology / cup + PD" | **named gating brick:** singular **cohomology cup product** + **Poincaré duality / fundamental class** for closed oriented manifolds (FK-3 + FK-4). FK-6 (spin structure + Wu) and FK-7 (Guillou–Marin) are the *residual* build even after the brick lands. |
| Leading indicator | none | **`AlgebraicTopology.singularHomologyFunctor` landed in Mathlib v4.29.x.** Homology is the prerequisite for cohomology+cup+PD; its arrival is concrete evidence the gating brick is on the community roadmap. **Monitor** `loogle "singularCohomology"`, `loogle "cup"`, `leanfinder "Poincaré duality fundamental class"` periodically. |
| Verdict basis | "middle-row, cost unknown → spike first" | "bottom-row capstone, cost known to be multi-foundation → defer; reactivate when the brick lands or a publication forces it" |

---

## 8. What this spike changes vs. the pre-spike plan

1. **Confirms the absence list by semantic search** (both Mathlib and physlib) — the gaps are real; we are not
   grep-fooled and not "flat wrong" about either the gaps or the hypothesis's truth.
2. **Resolves the ADR-003 middle/bottom tension** (capstone bottom, entry middle) — §7(2).
3. **Sharpens the re-trigger** from "ships algebraic topology" to the named FK-3+FK-4 gating brick, and
   records the **singular-homology leading indicator** the ADR-003 pre-spike draft (same session) hadn't yet
   incorporated, plus the live-repo delta vs. master (§3d).
4. **Confirms physlib is irrelevant to Leg-C** — closes the user's explicit "anything in physlib?" question.
5. **Confirms no pre-trigger down-payment** beyond 5q.C — the geometric side is "do 5q.C, then wait for the
   brick," nothing in between.
6. **Leaves the recommendation:** proceed with 5q.C Phase 1 (top-row, now); keep Leg-C-geometric deferred with
   the sharpened trigger; Leg-D unchanged (its own bottom-row frontier, Phase5qD).

---

## 9. Cross-references

- [ADR-003](../adrs/ADR-003-rokhlin-leg-discharge-and-deferred-topological-frontiers.md) — master decision
  record; Decision #3 and the dependency/trigger tables are updated to cite this spike.
- [Phase5qC roadmap](../roadmaps/Phase5qC_ArfBridge_Roadmap.md) — §Phase 2 adopts this spike's verdict; Phase 1
  (the Arf bridge) is the recommended next build.
- [Phase5qD roadmap](../roadmaps/Phase5qD_AdamsABP_Frontier_Roadmap.md) — the bordism-route frontier (Leg-D),
  independent of Leg-C; same "defer + trigger" posture.
- [Route A/B assessment](GenerationConstraint_RouteA_vs_B_ImpactAssessment.md) — the cost-prediction precedent.

*Leg-C scouting spike. 2026-06-09. Read-only planning artifact. Governed by ADR-003. Follows
[Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).*
