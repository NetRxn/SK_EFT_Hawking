# ADR-003 — Rokhlin / `16 ∣ σ` leg: discharge posture and deferred topological frontiers

- **Status:** **ACCEPTED (2026-06-08); Leg-C scouting spike run + verdict folded in (2026-06-09).** `16 ∣ σ`
  is discharged unconditionally via Route B (the spectra-free classification route; landed in ~2 working days,
  see `Phase5qB` roadmap). This ADR records: (1) the permanent posture for the *irreducible* topological
  residue `2 ∣ σ/8`; (2) the decision to pursue **Phase 5q.C** (the Arf-bridge hardening) now; (3) the
  **Leg-C scouting spike** ([LegC_GeometricResidue_ScoutingSpike](../assessments/LegC_GeometricResidue_ScoutingSpike.md),
  2026-06-09) and its evidence-based conclusion to **defer** the two genuine topological frontiers — Leg
  C-geometric and Leg D (Adams/ABP) — as *documented, trigger-gated* frontiers rather than open or re-planned
  each time; (4) a velocity-grounded LOE convention; (5) the full remaining-work analysis, **including the
  parts judged infeasible-for-now**, so the analysis is not re-derived later.
- **Deciders:** John Roehm (project owner); investigation + draft by Claude.
- **Context source:** the 5q.B/5q.T coverage analysis (2026-06-08); a semantic-search inventory of Mathlib
  v4.29.1 (`leanfinder`/`leansearch`/`loogle`, scope-calibrated — NOT grep, per memory
  `feedback_lean_semantic_search_over_grep`); a direct inventory of `physlib` on disk; the
  **Leg-C scouting spike** (2026-06-09 — a second, independent semantic-search pass on the
  `lean-lsp-netrxn` server whose scope indexes Mathlib **and** physlib together,
  [LegC_GeometricResidue_ScoutingSpike](../assessments/LegC_GeometricResidue_ScoutingSpike.md)); the
  completion of Phase 5q.B; `HYPOTHESIS_REGISTRY` (`src/core/constants.py`).
- **Related:** [ADR-001](ADR-001-commring-qcyc5ext-roadmap.md), [ADR-002](ADR-002-native-decide-policy.md)
  (kernel-trust / `native_decide` posture; the velocity-compression caveat below sharpens its §"months→hours"
  observation); [Phase5qB roadmap](../roadmaps/Phase5qB_SpectraFreeSpinBordism_Roadmap.md);
  [Phase5qC roadmap](../roadmaps/Phase5qC_ArfBridge_Roadmap.md) (NEW; created with this ADR);
  [Phase5qT roadmap](../roadmaps/Phase5qT_ExtSubstantiation_Roadmap.md) (optional Wave T6 appended);
  [Phase5qD roadmap](../roadmaps/Phase5qD_AdamsABP_Frontier_Roadmap.md) (NEW; trigger-gated);
  [Route A/B assessment](../assessments/GenerationConstraint_RouteA_vs_B_ImpactAssessment.md)
  (**partially superseded on cost** — see Context); Pipeline Invariant #15 (no undocumented axioms).

---

## Context

### What is discharged, and what is not
`16 ∣ σ(M)` for closed smooth spin 4-manifolds (Rokhlin's theorem) is the fact consumed — historically as a
*hypothesis* — by `RokhlinBridge.sixteen_convergence_full`. As of Phase 5q.B it is a **kernel-pure theorem**
(`SmoothSpinManifold4.rokhlin`, axioms `{propext, Classical.choice, Quot.sound}`, no project-local axiom) via
the classification route: even-unimodular ⟹ (Hasse–Minkowski `[HM]` + theta-modularity `[Θ]`) ⟹ van der Blij
`8 ∣ σ`, composed with the topological factor `2 ∣ σ/8`.

The decomposition `16 ∣ σ ⟺ (8 ∣ σ) ∧ (2 ∣ σ/8)` is exact. We **proved `8 ∣ σ`** (the algebraic bulk). The
residual **`2 ∣ σ/8`** is carried as the `topo` field of `SmoothSpinManifold4`. Given the proven `8 ∣ σ`,
assuming `2 ∣ σ/8` is *logically equivalent* to assuming `16 ∣ σ` — so we did not reduce the logical strength
of the topological assumption; we **carved off and proved its algebraic half** and isolated the residual to
its most primitive form.

**Why `2 ∣ σ/8` is irreducible (not a Mathlib gap — a mathematical necessity).** `16 ∣ σ` is *false* for
general even unimodular forms — the E₈ form has σ=8, σ/8=1 (odd), and Freedman realized it as a *topological*
4-manifold. So `16 ∣ σ` is not a purely algebraic fact; any proof **must** detect smoothness, via gauge
theory (Dirac/Donaldson) or smooth embedded surfaces (Freedman–Kirby). No algebraic route — by Leg C *or*
Leg D — can eliminate this input. We have isolated it to the narrowest possible fact and carry it as a
**tracked hypothesis, not an axiom.**

A separate, parallel residue exists on the **Ext / Adams strand** (Phase 5q.T): the Ext-over-A(1) computation
is honest algebra, but the topological hypotheses **H1** (`H*(ko;𝔽₂) ≅ A//A(1)`), **H3** (Adams-SS collapse),
**H4** (ABP splitting) that would make it a *bordism* statement remain `Prop := True` pointers. These are
**not on the `16 ∣ σ` critical path** (Route B reaches `16 ∣ σ` without them) and H4 is **circular for
Rokhlin** (ABP historically uses Rokhlin-equivalent facts) — see `HYPOTHESIS_REGISTRY['spin_bordism_iso_Z'].circularity_note`.

### `physlib` offers nothing for either leg (inventoried on disk, 2026-06-08)
`physlib` (HepLean/PhysLean) is a physics library: GR metrics on Mathlib's manifold layer
(`PseudoRiemannian/Riemannian Defs`), quantum information (entropy/fidelity/`MState`), and **gauge anomaly
cancellation** (`Particles/.../RHN/AnomalyCancellation/*`, the `ACCSystem`). It has **zero algebraic/geometric
topology of manifolds** — no bordism, characteristic classes, index theory, Arf, Steenrod, or spectra
(`loogle`/grep diagnostic hits for "Arf"/"Dirac" were false positives: `BilinearForm`, Dirac-*delta*/QM).
Its one tangential asset (gauge anomaly cancellation, the *perturbative-triangle* anomaly) touches the
*physics-premise* side of the headline (`c₋ = 8N_f`), **not** the topological ℤ₁₆/framing anomaly, so it does
not help these legs. (It *is* relevant to other project work — QI for the quantum-network track, GR for the
upstream-disposition re-homing — but not here.)

### Mathlib has essentially nothing for either leg (semantic-verified, v4.29.1)
Verified with `leanfinder`/`leansearch`/`loogle` (full-Mathlib index, scope-calibrated against the known
`QuadraticForm.Real` family). **`loogle "Arf"` / `loogle "Bordism"` / `loogle "Steenrod"` → no results.**
Also absent: characteristic classes (Stiefel–Whitney/Pontryagin/Chern), cup-product cohomology, Poincaré
duality, Â-genus, Hirzebruch signature theorem, Dirac operator/index, ko/KO-theory, Thom spectra, spectra/
stable-homotopy category, Adams SS. **Two refinements vs. a naive grep:** (a) **differential forms are
PARTIAL** — `Analysis/Calculus/DifferentialForm` has `extDeriv` + `extDeriv_extDeriv` (d²=0), so the forms
substrate exists (de Rham *cohomology* assembly + Chern–Weil do not); (b) **vector bundles + tangent bundle
EXIST** (`Topology/VectorBundle`, `TangentSpace.vectorBundle`), so characteristic classes have a *foundation*
— the classes themselves don't. **Reusable & present:** `QuadraticForm.sigPos/sigNeg` (Sylvester), `Ext R C n`
+ `ProjectiveResolution`, and general homological-algebra spectral-sequence machinery (`SpectralObject`).

**Live-repo delta vs. our pin (added 2026-06-09 from the spike's `gh` master-tree check — the above is for our
pinned v4.29.1).** Mathlib **master is `v4.31.0-rc2`** (we are ~2 minors behind); PhysLean master is `v4.30.0`.
Since our pin, master has shipped (and we *don't yet have*): **`Geometry/Manifold/Bordism.lean`** (Rothgang —
`SingularManifold`, the first brick of *unoriented* bordism; bordism groups + abelian structure are stated
future PRs), **`SingularHomology/HomotopyInvariance`**, and a concrete **`Algebra/Homology/SpectralSequence`**
layer. **Still absent even at v4.31 master:** cup-product cohomology, Poincaré duality, characteristic classes,
Chern–Weil, intersection form, manifold spin structures, Dirac/index — so **neither leg's capstone
prerequisites have shipped upstream; the deferral verdict is unchanged.** But the *trajectory* is real
(bordism went absent→started between our pin and master), which sets the watch/vendoring posture in Decision #7
and the [spike §3d–3e](../assessments/LegC_GeometricResidue_ScoutingSpike.md).

### LOE convention (velocity-grounded — supersedes raw "person-year" framing)
The Route A/B assessment predicted Route B was "a serious multi-PY effort, not an order-of-magnitude
shortcut." **This was empirically falsified: Route B landed in ~2 working days.** Traditional pre-estimates
put the Route-B load-bearing path at ~1.5–2.5 PY (the assessment's "~10× smaller than Route A's 15–25 PY"),
and the *total built* (incl. exploratory theta/Poisson substrate) at ~2.75–6.5 PY. Demonstrated compression:
**~150–300×** (sanity: ~30k LOC / 2 days ≈ 15k LOC/day vs. a human's ~100 LOC/day of hard new formalization).

**The compression is strongly task-dependent — this is the operative fact for all LOE below:**

| Task row | Our compression vs. traditional PY | Examples |
|---|---|---|
| **Top** — algebraic / finite / decidable / **known-proof to transcribe** / decomposable | **~100–300×** (measured: 5q.B) | 5q.B, 5q.C, the 5q.T waves |
| **Middle** — new Mathlib *foundational design* (defining objects, typeclass/universe architecture) | **~5–20×** (extrapolated) | a deliberate characteristic-classes or spectra build |
| **Bottom** — genuine research frontier, **no formalization blueprint anywhere** | **~1–5×, high uncertainty** | Atiyah–Singer; full Adams/ABP from scratch |

When this ADR cites "10–25 PY," read it as **"this is a bottom-row task,"** not "divide by 200." We have
**measured** top-row velocity; middle/bottom rows are **extrapolations** — the real risk on the deferred
frontiers is less "slow" than "gated on foundations that don't exist regardless of speed."

#### Three tiers of "hard" — and a self-correction (added 2026-06-08 after review challenge)

The row table answers "how fast," but the *durable* question is "what kind of hard." Three tiers:
1. **Mathematical necessity** — binds everyone, always. *Some* smooth-category input is required for `16 ∣ σ`
   (E₈ / Freedman's topological E₈-manifold). This is real and is why `topo'` is carried.
2. **No *formalization* blueprint** — binds even us. The math is settled but the *proof-assistant encoding* is
   itself an open research question (e.g., the stable homotopy category; the analytic/topological index). An
   LLM's compression comes from transcribing a blueprint; here there is none, so velocity genuinely drops.
3. **Folklore "nobody's done it"** — does **NOT** bind us. Most un-formalized math is un-prioritized, not hard.
   The project's ~2-month record of "first ever formalized" results is direct evidence this inference is
   usually false. **This is where training-data priors cloud the estimate**, and where my "PY" numbers are
   least trustworthy.

**The test to apply (math blueprint AND Lean-encoding blueprint?):** 5q.B was "yes" (Serre/Poisson/van der
Blij — known proofs; the Lean *encoding* needed bounded middle-row design) ⟹ huge compression. A tier-2 task
is "no at the encoding level" ⟹ low compression.

**Self-correction logged, then resolved by the spike.** This ADR's first draft labeled *both* Leg-C routes
"bottom-row." The review challenge over-corrected that to "Leg-C-FK is middle-row." **The scouting spike
(2026-06-09) settled it on evidence, and the truth is layer-dependent:** the FK route's *entry* (assemble a
4-manifold on existing substrate) is middle-row, but its *prerequisite* layer (singular cohomology + cup
product + Poincaré duality + intersection form + manifold spin structure + Wu) is bottom-row to build, and its
*capstone* (the Guillou–Marin congruence) is **bottom-row, tier-2 — settled mathematics with NO formalization
blueprint in any proof assistant.** So the dependency table's "bottom" correctly described the *capstone*; the
"middle-row" label correctly described only the *entry*. The compression band is set by the slowest link, so
the route as a whole is bottom-row. Anti-wall discipline (decompose before asserting a wall *in either
direction*; cf. the 6AK arc where infeasibility was asserted wrongly 3×) was satisfied: the spike *decomposed*
the wall rather than asserting it, and the deferral below is now **evidence-based, not reflexive.** See
Decision #3 and [the spike](../assessments/LegC_GeometricResidue_ScoutingSpike.md).

---

## Decision

1. **`16 ∣ σ` stands discharged via Route B.** The residual `topo` (`2 ∣ σ/8`) is an **irreducible
   topological hypothesis, not an axiom**, and is the **permanent posture** unless a re-trigger (below) fires.
   This is correct and honest: the theorem is false without a smooth-category input, and `topo` is the
   narrowest such input.

2. **Pursue Phase 5q.C now (top-row, days).** Prove `σ/8 ≡ Arf(q̄) (mod 2)` from the *already-built*
   classification + Arf-additivity + generator Arf-values, then **refactor `topo : 2 ∣ σ/8` into
   `topo' : Arf(q̄) = 0`** — logically equivalent, but expressed as the Arf invariant of the form and tied to
   `ArfInvariant.lean`. This is the **maximal honest hardening** of the residual short of the geometric
   frontier: it makes the irreducible input transparent and machinery-connected. Roadmap: `Phase5qC`.

3. **Leg C-geometric: scouting spike RUN (2026-06-09) → DEFER, now evidence-based.** The spike
   ([LegC_GeometricResidue_ScoutingSpike](../assessments/LegC_GeometricResidue_ScoutingSpike.md)) did the
   first-principles, interface-first decomposition the prior draft demanded and reached three findings:
   (i) **no interface-first dodge exists** — the form must be *constructed from the manifold* (else E₈ is a
   counterexample), which requires the absent cohomology + Poincaré-duality layer; the algebraic shadow is
   already fully captured by 5q.C. (ii) **The row-tiering is layer-dependent**: FK *entry* middle-row, FK
   *prerequisites* bottom-row to build, FK *capstone* (Guillou–Marin) **bottom-row tier-2 — no proof-assistant
   blueprint anywhere**; the slowest link sets the band, so the route is bottom-row. (iii) **Therefore defer
   is earned** (not "cost unknown"): opening means a multi-foundation build plus a never-formalized capstone,
   warranted only if a publication demands the *literal* smooth discharge or the project funds foundational
   algebraic topology as a Mathlib-landmark. The Atiyah–Singer route is the deeper bottom-row fallback. `topo'`
   is carried as the **permanent irreducible hypothesis** (no longer "pending a spike"); the trigger-gated
   deferral in `Phase5qC` §"Phase 2" is the active posture. **NEW from the spike:** the trigger is sharpened to
   a single named gating brick (cup-product cohomology + Poincaré duality) and there is now a **leading
   indicator to monitor** — `AlgebraicTopology.singularHomologyFunctor` landed in Mathlib v4.29.x (see
   Re-trigger table).

4. **Pursue the optional Phase 5q.T Wave T6 only if the Ext-corroboration narrative is valued** (top-row,
   a session or two): build the full Steenrod algebra A + the `A//A(1)` module structure — the *algebraic*
   content of H1, **no spectra**. This strengthens the corroboration without touching the frontier. Appended
   to the `Phase5qT` roadmap; not on any critical path.

5. **Defer Leg D (Adams/ABP) as a documented, trigger-gated frontier.** It is **off the `16 ∣ σ` critical
   path** (Route B already delivers the fact), is a bottom-row build (spectra/Steenrod/Adams/Thom/ko from
   scratch), **and** H4 is circular for Rokhlin. Do **not** open it; documented in `Phase5qD` roadmap with
   triggers, so it is never re-planned from scratch.

6. **Report LOE in velocity rows, not raw PY** (the table above). Every future feasibility call on these
   frontiers must state which row the task is and whether the estimate is measured or extrapolated.

7. **Watch mechanism + vendoring posture + growth assumption** (sharpened by the 2026-06-09 spike). The
   deferred frontiers are gated on Mathlib/PhysLean growing specific foundations, and **we assume that growth is
   fast (super-linear, AI/human-collaborative)** — bordism went *absent→started* between our pin and master, so
   plan for gating bricks on a **months-not-years** horizon. Three mechanisms:
   - **Two-layer watch.** (i) Semantic search of *our pin* for trigger declarations (Re-trigger table); (ii)
     **a `gh` master-tree check** (`gh api repos/leanprover-community/mathlib4/git/trees/master?recursive=1`,
     and the same for `HEPLean/PhysLean`) at every pin-bump consideration and on a periodic cadence — because
     the gating brick can land at HEAD long before our pin moves. The spike's §3d is the template.
   - **Vendor-and-rewire (not "wait for the bump").** When a *load-bearing* brick lands at master ahead of our
     pin, vendor it and discharge early, normalizing at the next official bump. **Load-bearing** = **Leg-C:**
     cup-product cohomology **and** Poincaré duality; **Leg-D:** oriented/spin bordism *groups* **and** a
     low-degree computation (or the Adams/ABP stack). Sub-load-bearing bricks (e.g. master's current
     `SingularManifold`-only `Bordism.lean`, which also carries v4.31 module-system syntax) are **watch, don't
     vendor.**
   - **Re-wire-ready interfaces.** Keep the swap surface to `SmoothSpinManifold4.topo'` + `HYPOTHESIS_REGISTRY`
     (one field, one registry entry) so adoption is a discharge, not a refactor — 5q.C's `arfOfForm = 0`
     refactor exists partly to minimize this surface. A `validate.py` watch check MAY be added but is not
     required by this ADR.

---

## Full analysis of remaining work (including the parts judged infeasible-for-now)

This section is the durable record so the analysis is **not re-derived** each time the question resurfaces.

### Leg C-geometric — discharge `Arf(q̄) = 0` (equivalently `2 ∣ σ/8`) from a smooth spin 4-manifold

Two classical proof routes, **decomposed fragment-by-fragment in the 2026-06-09 spike**
([full tables there](../assessments/LegC_GeometricResidue_ScoutingSpike.md)). The spike's resolved tiering: a
Leg-C route's compression band is set by its *slowest link*, and **both routes are bottom-row at the capstone**
— C-FK's Guillou–Marin congruence and C-AS's index theorem each lack any proof-assistant encoding. C-FK is
nonetheless the **leaner** route (no Chern–Weil / index theory) and has a *middle-row entry*; C-AS is strictly
deeper (its capstone is generational).

**Route C-FK (Freedman–Kirby / Guillou–Marin) — leaner route; bottom-row capstone.** The Arf invariant of the
quadratic refinement on a characteristic surface equals `(σ − F·F)/8 mod 2`; for spin the characteristic
surface is null-homologous and the Arf vanishes. Fragment decomposition (spike §5), by layer:
- *entry (MIDDLE-ROW):* assemble a closed oriented smooth 4-manifold on `SmoothManifoldWithCorners` ✓;
- *prerequisites (BOTTOM-ROW to build):* singular **cohomology + cup product** (Mathlib has singular *homology*
  only — `singularHomologyFunctor`), **Poincaré duality + fundamental class**, the **intersection form** (cup
  pairing on `H²`), and — for evenness — a **manifold spin structure + the Wu formula** (Mathlib's "spin" is
  the *algebraic* `spinGroup` only);
- *capstone (BOTTOM-ROW, tier-2):* the **Guillou–Marin congruence** — settled mathematics, but **never
  formalized in any proof assistant; no encoding blueprint.** The spike confirmed there is *no* interface-first
  encoding that dodges constructing the form from the manifold (the algebraic shadow is already fully captured
  by 5q.C), so this layer is irreducibly bottom-row.

**Route C-AS (Atiyah–Singer / Â-genus).** `Â(M) = −σ/8 ∈ ℤ` (index of the Dirac operator ⟹ `8 ∣ σ`) and is
even by a mod-2-index / quaternionic argument (⟹ `16 ∣ σ`). Prerequisite stack (all ABSENT):
- **Chern–Weil theory** on the existing bundle+forms substrate (vector bundles ✓, `extDeriv` ✓, but no
  connections/curvature-to-cohomology) — *foundational design*;
- **Pontryagin classes** + the **Hirzebruch signature theorem** — *foundational*;
- a **geometric Dirac operator** on a spin manifold (Mathlib's "spin" is the *algebraic* `CliffordAlgebra.spinGroup`
  only) — *foundational*;
- the **Atiyah–Singer index theorem** — **never formalized in any proof assistant**; genuinely bottom-row
  (tier-2, no encoding blueprint). This route is the *fallback*, not the recommendation.

**LOE — and the action (post-spike).** Both routes are bottom-row at the capstone; C-AS is the deeper fallback.
C-FK, the leaner route, is **not "10+ PY of monolith" but a multi-foundation build**: a middle-row entry, a
bottom-row prerequisite stack (cohomology+cup+PD+intersection-form+spin-structure+Wu), and a bottom-row tier-2
capstone (Guillou–Marin) with no encoding blueprint. The spike's decisive finding is that **no interface-first
narrowing avoids that stack** (unlike Wave B3, which *could* narrow the *lattice* input to one field, the
*geometric* input here cannot be narrowed below "construct the form from the manifold"). So the honest call is
**defer — now earned on evidence**, with `topo'` carried as the **permanent irreducible hypothesis** and a
sharpened, monitorable trigger (Re-trigger table). The one genuinely new, actionable fact: **the gating brick
(cup-product cohomology + Poincaré duality) is on the Mathlib community trajectory** — singular *homology* just
landed — so reactivation may become "assemble + prove the capstone" rather than "build everything," and is
worth a periodic watch.

### Leg D — discharge H1 / H3 / H4 (make the Ext computation a bordism statement)

- **H1** (`H*(ko;𝔽₂) ≅ A//A(1)` as an A-module). *Algebraic half is top-row and tractable* (Wave T6: build A,
  state the `A//A(1)` module structure). *Topological half* (that this equals the cohomology of the real ko
  spectrum) needs the **ko spectrum** — bottom-row.
- **H3** (Adams-SS collapse). Needs the **Adams spectral sequence** as a topological device (the general
  `SpectralObject` machinery ✓ does **not** supply the Adams SS of a spectrum). Bottom-row.
- **H4** (ABP splitting `MSpin ≃ ko ∨ …`). Needs **Thom spectra + ko + stable homotopy category**. Bottom-row,
  **and circular for Rokhlin** — must route ABP through the Adams SS, not any Rokhlin-equivalent input.

**Strategic facts.** Leg D is **not needed for `16 ∣ σ`** (Route B delivers it), so its only payoff is
upgrading the Ext computation from "honest standalone algebra" to "connected to bordism." Given the bottom-row
cost (traditional 15–25 PY; the program's own booked figure) **and** the circularity, the core discharge is
**not worth opening**. The tractable adjacent (Wave T6, A//A(1) algebraic structure) is the only piece to
consider, and only for narrative strength.

### Prerequisite dependency summary

| Frontier | Hard prerequisites (all Mathlib-ABSENT) | Row of the capstone | On `16∣σ` path? | Circular? |
|---|---|---|---|---|
| Leg C-FK | cup product, Poincaré duality, intersection form, char surfaces, Guillou–Marin | bottom | yes (the residual) | no |
| Leg C-AS | Chern–Weil, Pontryagin, signature thm, geometric Dirac, **Atiyah–Singer** | bottom | yes (the residual) | no |
| Leg D | spectra, Steenrod A, Adams SS, Thom MSpin, ko | bottom | **no** | **H4 yes** |
| 5q.C (do now) | *none new* — reuses classification + `ArfInvariant.lean` | top | yes | no |
| 5q.T Wave T6 (optional) | full Steenrod A (algebraic) | top | no | no |

---

## Re-trigger conditions (when to reactivate a deferred frontier)

Each deferred frontier is gated on a foundation appearing. **Trigger = "Mathlib ships X" OR "we deliberately
fund the foundation Y."** Monitor via periodic semantic search for the named declarations.

| Frontier | Re-trigger: **Mathlib community ships** | Re-trigger: **we build** | Action on trigger |
|---|---|---|---|
| **Leg C-FK** | **gating brick:** singular cohomology **cup product** + **Poincaré duality / fundamental class** for closed manifolds. **Leading indicator (NEW, spike 2026-06-09):** `AlgebraicTopology.singularHomologyFunctor` *already landed* in v4.29.x — homology is the prerequisite for the brick, so the brick is on the community trajectory. Watch: `loogle "singularCohomology"`, `loogle "cup"`, `leanfinder "Poincaré duality fundamental class"` | a deliberate intersection-form + char-surface wave (bottom-row capstone = Guillou–Marin; only if a publication demands the *literal* smooth discharge, or to fund foundational alg-top as a Mathlib landmark) | open `Phase5qC` §Phase 2; assemble form → spin-structure/Wu → Guillou–Marin ⟹ `Arf(q̄)=0`; drop `topo'` |
| **Leg C-AS** | **Pontryagin/characteristic classes** (Chern–Weil) + a **geometric Dirac operator** (watch: `loogle "Pontryagin"`, `loogle "Dirac"`, `leanfinder "A-hat genus"`) | (not recommended — Atiyah–Singer is no-blueprint) | as above, via the Â-even route |
| **Leg D (H1/H3/H4)** | **spectra / stable homotopy category** + **Steenrod algebra** + **Adams SS** + **MSpin/ko** (watch: `loogle "Spectrum"`, `loogle "Steenrod"`, `loogle "Adams"`). **Warming (spike 2026-06-09):** master shipped `Geometry/Manifold/Bordism.lean` (`SingularManifold`, first brick) + a concrete `SpectralSequence` layer — *started, not load-bearing.* `gh`-watch `Geometry/Manifold/Bordism*` for bordism *groups* + spin | a deliberate stable-homotopy stack (bottom-row; only as a foundational-infrastructure ambition, **and** route ABP non-circularly) | open `Phase5qD`; discharge H1/H3/H4; wire the Ext-as-E₂ narrative as theorem |
| **5q.T Wave T6** | *no gate* — tractable now | full Steenrod A (top-row) | optional; strengthens H1's algebraic half |

If a trigger fires, the relevant roadmap already contains the wave plan — **no re-planning needed.** Triggers
are checked against **both** our pin *and* `gh` master (Decision #7) — a load-bearing brick at HEAD is itself a
trigger to **vendor-and-rewire** ahead of the official bump, not merely to wait. The Re-trigger "Mathlib
community ships" column is satisfied by a master landing, not only a pin bump.

---

## Consequences

**Positive.**
- The honest ceiling is on record: `16 ∣ σ` carries exactly **one** irreducible smooth-topological hypothesis,
  by mathematical necessity, and 5q.C makes it as small/transparent as possible (`Arf(q̄)=0`).
- The deferred frontiers are **planned, not re-litigated**: triggers + wave plans exist, so a future
  reactivation is execution, not re-analysis.
- LOE is now velocity-grounded; future estimates won't be mis-read (the Route-B "multi-PY" mis-prediction is
  the cautionary precedent, now corrected).
- `physlib` and Mathlib were inventoried with the *right tool* (semantic search), so absence claims are
  defensible, not grep-artifacts.

**Negative / accepted.**
- The D2/L2 bundles must continue to describe the bordism leg as "established by an independent spin-Rokhlin /
  classification proof" with one tracked topological input — **not** "by the Adams SS for ko" (that narrative
  stays motivational until Leg D, which we are not opening).
- The Ext-as-E₂-page story remains a true *narrative*, not a wired theorem, unless Wave T6 (+ eventually Leg D)
  is pursued.
- `2 ∣ σ/8` (post-5qC: `Arf(q̄)=0`) remains a hypothesis indefinitely. This is correct, but means "fully
  unconditional Rokhlin from nothing" is **not** claimed and must not be implied in any paper.

**Neutral.**
- None of this affects the `3 ∣ N_f` headline, which rests on the η/framing-anomaly physics premise
  (`modular_invariance_framing`) + SM content (`c₋ = 8N_f`) — untouched by any of these legs.

*ADR-003. Created 2026-06-08. Companion to Phase5qB/Phase5qC/Phase5qT/Phase5qD roadmaps.*
