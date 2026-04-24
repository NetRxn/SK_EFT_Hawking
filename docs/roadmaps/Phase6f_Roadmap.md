# Phase 6f: Classical GR Lean Infrastructure — Curvature, Einstein Tensor, Energy Conditions, Exact Solutions, ADM, Tetrad

## Technical Roadmap — April 2026

*Prepared 2026-04-24 | Derived from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §9. Classical-GR infrastructure in Lean that Phases 6e and 6g depend on. Mostly sits on top of Bonn's differential-geometry formalization and does not require condensate-side input. External Mathlib progress is the main risk.*

**Entry state (calibration, 2026-04-22 Inventory_Index snapshot):** 150 modules, 3300+ theorems, 0 sorry, 1 axiom. Classical-GR-relevant anchors: `KerrSchild.lean` (7, gravitational solutions scaffolding), existing tetrad infrastructure in `ADWMechanism.lean` and `TetradGapEquation.lean`. Mathlib: differential-geometry machinery as of 2026 — needs audit; Bonn diff-geom formalization referenced by strategy doc §9 as external dependency.

**Thesis.** Six waves of classical-GR infrastructure formalized in Lean: Riemann / Ricci curvature, Einstein tensor + Bianchi, energy conditions, exact solutions catalog, ADM 3+1 decomposition, tetrad (vierbein) formalism. Nearly all waves are Mathlib-PR candidates. This phase is the prerequisite backbone for Phases 6a.6 (positive mass theorem), 6e (nonlinear effective action), and 6g (global / nonperturbative GR). External Mathlib progress is the main schedule risk.

**Correctness-push framing.** 6f.3 (`EnergyConditions.lean`) is the correctness-push anchor: Phase 6e.4's `T_μν^emerg` must be checkable against these predicates, and NEC violation in ADW has direct cosmological consequences (supports DE without exotic matter; tension with standard BH theorems).

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, SK_EFT_Hawking_Inventory_Index
> 2. Read this roadmap for wave assignments
> 3. Read the source strategy document: [`Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md`](../../../Lit-Search/Phase-5z/Post-SK-EFT%20Research%20Program%20Strategy.md) §9 (6f), §4 (6a — context for 6a.6), §8 (6e — context for 6e.1/6e.4), §10 (6g — downstream dependency)
> 4. Wave-specific pre-reads (all waves): Mathlib current `Mathlib.Geometry.Manifold.*` namespace audit — identify existing differential-geometry / Riemannian-geometry infrastructure. Drop deep-research prompt `Lit-Search/Tasks/Phase6f_mathlib_gr_infrastructure_audit.md` before Wave 1 Stage 1 if unclear.
> 5. Bonn differential-geometry formalization (strategy doc §16 Open Q) — contact / coordinate? If not yet contacted, proceed independently with Mathlib-first approach; if contacted, align scope upstream.
> 6. Mathlib-PR strategy: every wave is a candidate Mathlib PR. Follow the Mathlib-categorical-PR guide in `Lit-Search/Phase-5h/Contributing categorical infrastructure to Mathlib4.md` adapted for differential-geometry contributions.
> 7. 6f waves are foundation-building; the correctness-push value comes via downstream consumers (6a.6, 6e, 6g). Do not demand correctness-push anchors inside 6f itself — it is infrastructure.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for Phase 6f:**
- Riemann `R^ρ_{σμν}`, Ricci `R_μν`, scalar `R` as typed Lean objects with standard identities
- Einstein tensor `G_μν = R_μν − ½ R g_μν` + second Bianchi `∇^μ G_μν = 0`
- Energy conditions: WEC, NEC, DEC, SEC as predicates on stress-energy
- Exact solutions catalog: Schwarzschild, Kerr, de Sitter, FLRW
- ADM 3+1 decomposition: lapse, shift, induced metric, extrinsic curvature, constraint equations
- Tetrad (vierbein) formalism on manifolds: frame-bundle section, spin connection, torsion, Einstein-Cartan action

**OUT OF SCOPE for 6f:**
- Full numerical-relativity machinery — simulation, not formalization (backlog)
- Covariant perturbation theory at nonlinear order — 6e territory
- Supersymmetric / higher-dimensional curvature — OOS by program framing
- Specific astrophysical solutions beyond the catalog (Kerr-Newman, charged solutions) — add as 6f.4 extensions if specifically needed

**External dependency:** If Bonn diff-geom team's formalization becomes available upstream, switch to import-based structure rather than in-house definitions. Decision per wave at Stage 1.

---

## Track A: Curvature Stack (6f.1, 6f.2)

### Wave 1 — `Curvature.lean` (6f.1) [Pipeline: Stages 1–8]

**Goal:** Riemann `R^ρ_{σμν}`, Ricci `R_μν`, scalar `R` as typed Lean objects with standard algebraic identities (antisymmetry, first Bianchi, Ricci symmetry).

**Prerequisites:** Mathlib current differential-geometry audit. If Bonn work is available, use it; otherwise build on Mathlib base.

**Module structure:**
- `lean/SKEFTHawking/Curvature.lean`
  - Riemann tensor `R^ρ_{σμν}(∇) : TensorField` from Levi-Civita connection ∇
  - Ricci tensor `R_{μν} = R^ρ_{μρν}`
  - Scalar curvature `R = g^{μν} R_{μν}`
  - Antisymmetry: `R_{ρσμν} = −R_{σρμν} = −R_{ρσνμ}`, symmetry: `R_{ρσμν} = R_{μνρσ}`
  - First Bianchi: `R^ρ_{[σμν]} = 0`
  - Ricci symmetry: `R_{μν} = R_{νμ}`
- Target ~12–16 theorems.

**Python side:** Minimal (Lean-side heavy).
- `src/classical_gr/curvature_numerical.py` — numerical curvature on test metrics (Minkowski, Schwarzschild) — validation against Lean

**Bridges:**
- Feeds 6f.2, 6f.3, 6f.4, 6f.5, 6f.6 (all downstream 6f waves)
- Feeds 6a.6 (positive mass theorem), 6e (nonlinear effective action), 6g (global GR)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_curvature.py`
- **Mathlib PR:** Curvature objects + core identities — coordinated with Mathlib maintainers
- Inventory update: +12–16 theorems, +1 Lean module, +1 Python script

**Estimated LOE:** 3–5 person-months
**Risk:** Medium. Dependent on Mathlib differential-geometry maturity. If Mathlib already has Riemann/Ricci, this becomes an import + specialization wave (~1 PM).

### Wave 2 — `EinsteinTensor.lean` (6f.2) [Pipeline: Stages 1–5]

**Goal:** `G_μν = R_μν − ½ R g_μν`; second Bianchi `∇^μ G_μν = 0` as theorem.

**Prerequisites:** Wave 1 complete.

**Module structure:**
- `lean/SKEFTHawking/EinsteinTensor.lean`
  - `G_μν` definition
  - Second Bianchi identity: `∇^μ G_μν = 0` theorem
  - Contracted Bianchi: `∇^μ R_μν = ½ ∇_ν R`
  - Trace theorem: `G^μ_μ = −R` in 4D
- Target ~6–8 theorems.

**Python side:** Minimal.

**Bridges:**
- Depends on Wave 1
- Feeds 6f.4 (exact solutions check), 6e.4 (nonlinear EFE), 6g (global GR)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_einstein_tensor.py`
- **Mathlib PR:** Einstein tensor + Bianchi
- Inventory update: +6–8 theorems, +1 Lean module

**Estimated LOE:** 2–4 person-months
**Risk:** Low–medium.

---

## Track B: Energy Conditions (6f.3)

### Wave 3 — `EnergyConditions.lean` (6f.3) [Pipeline: Stages 1–8]

**Goal:** Formal statements of weak, null, dominant, strong energy conditions as predicates on stress-energy. This is 6f's correctness-push anchor — enables NEC check on Phase 6e.4's `T_μν^emerg`.

**Prerequisites:** Waves 1, 2 complete.

**Module structure:**
- `lean/SKEFTHawking/EnergyConditions.lean`
  - Stress-energy tensor abstract type
  - WEC predicate: `∀ timelike u^μ, T_μν u^μ u^ν ≥ 0`
  - NEC predicate: `∀ null k^μ, T_μν k^μ k^ν ≥ 0`
  - DEC predicate: `∀ timelike u^μ, −T^μ_ν u^ν is future-pointing causal`
  - SEC predicate: `∀ timelike u^μ, (T_μν − ½ T g_μν) u^μ u^ν ≥ 0`
  - Implication theorems: `DEC ⇒ WEC`, `WEC ⇒ NEC`, etc.
  - **Correctness-push theorem (external to 6f, activated by 6e.4):** `ADW_T_emerg_satisfies_NEC` — open / activated when 6e.4 ships `T_μν^emerg` explicit form. If NEC is violated on ADW's emergent stress-energy, that regime becomes a targeted study (6g.2 Penrose singularity may not apply; DE support without exotic matter is permitted).
- Target ~8–10 theorems.

**Python side:**
- `src/classical_gr/energy_conditions.py` — numerical energy-condition checker on representative stress-energy tensors

**Bridges:**
- Depends on Waves 1, 2
- Feeds 6a.6 (positive mass under DEC), 6g.2 (Penrose singularity under NEC), 6g.4 (classical area theorem under NEC), 6e.4 (`T_μν^emerg` classification)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_energy_conditions.py`
- **Mathlib PR:** Energy conditions as predicates (possibly combined with 6f.1/6f.2 PR)
- Inventory update: +8–10 theorems, +1 Lean module, +1 Python script

**Estimated LOE:** 2–3 person-months
**Risk:** Low. Pure predicate definitions + implication theorems.

**Correctness-push anchor (activated downstream).** NEC on `T_μν^emerg` is the single most load-bearing check in the post-SK-EFT gravity program.

---

## Track C: Exact Solutions (6f.4)

### Wave 4 — `ExactSolutions.lean` (6f.4) [Pipeline: Stages 1–8]

**Goal:** Schwarzschild, Kerr, de Sitter, FLRW as explicit metrics satisfying vacuum / appropriate-source Einstein equations.

**Prerequisites:** Waves 1, 2 complete. `KerrSchild.lean` (existing) for Kerr-family scaffolding.

**Module structure:**
- `lean/SKEFTHawking/ExactSolutions.lean`
  - Schwarzschild metric + vacuum-EFE verification
  - Kerr metric (extending existing `KerrSchild.lean`) + vacuum-EFE verification
  - de Sitter metric + `Λ`-sourced EFE verification
  - FLRW metric (already referenced in 6a.4 `FLRWDynamics.lean`) — cross-reference or absorb
  - Horizon structure: Schwarzschild event horizon, Kerr inner/outer + ergosphere, de Sitter cosmological horizon
  - Killing vector fields
- Target ~14–18 theorems.

**Python side:**
- `src/classical_gr/exact_solutions.py` — numerical evaluators + Einstein-tensor verification on each solution

**Bridges:**
- Depends on Waves 1, 2
- Extends `KerrSchild.lean`
- Feeds 6g.6 (no-hair theorem), 6a.5 (BH thermodynamics on specific solutions)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_exact_solutions.py`
- **Mathlib PR:** Exact solutions catalog (possibly)
- Inventory update: +14–18 theorems, +1 Lean module, +1 Python script

**Estimated LOE:** 3–5 person-months
**Risk:** Medium. Kerr metric + horizon structure is the most technical subcomponent.

---

## Track D: ADM and Tetrad (6f.5, 6f.6)

### Wave 5 — `ADMFormalism.lean` (6f.5) [Pipeline: Stages 1–8]

**Goal:** Lapse, shift, induced metric, extrinsic curvature, Hamiltonian and momentum constraint equations. Required for 6g.5 (Cauchy problem).

**Prerequisites:** Waves 1, 2 complete. LeanMillenniumPrizeProblems PDE framework (external) as coordinated dependency — if unavailable, build inline.

**Module structure:**
- `lean/SKEFTHawking/ADMFormalism.lean`
  - Foliation of spacetime by spacelike hypersurfaces `Σ_t`
  - Lapse function `N`, shift vector `N^i`
  - Induced metric `γ_{ij}` on `Σ_t`
  - Extrinsic curvature `K_{ij}`
  - Hamiltonian constraint: `^(3)R + K² − K_{ij} K^{ij} = 16π G ρ`
  - Momentum constraint: `∇_j (K^{ij} − γ^{ij} K) = 8π G j^i`
  - Gauss-Codazzi relations
- Target ~12–16 theorems.

**Python side:**
- `src/classical_gr/adm_formalism.py` — ADM split of representative metrics (Schwarzschild in ADM form)

**Bridges:**
- Depends on Waves 1, 2
- Feeds 6g.5 (Cauchy problem) — critical
- Cross-references LeanMillenniumPrizeProblems PDE weak-solution framework

**Deliverables:**
- Module zero-sorry, building clean (target)
- `tests/test_adm_formalism.py`
- **Mathlib PR:** ADM formalism (possibly — coordinated with LMPP)
- Inventory update: +12–16 theorems, +1 Lean module, +1 Python script

**Estimated LOE:** 4–6 person-months
**Risk:** Medium–high. Heavy bookkeeping; interacts with LMPP PDE framework.

### Wave 6 — `TetradFormalism.lean` (6f.6) [Pipeline: Stages 1–8]

**Goal:** Tetrad as frame-bundle section; spin connection; torsion tensor; Einstein-Cartan action. Bridges classical-GR side to ADW's tetrad-native formalism.

**Prerequisites:** Waves 1, 2 complete. Existing tetrad work in `ADWMechanism.lean`, `TetradGapEquation.lean` — align conventions.

**Module structure:**
- `lean/SKEFTHawking/TetradFormalism.lean`
  - Tetrad / vierbein `e^a_μ` as frame-bundle section
  - Inverse vierbein `E_a^μ`, orthonormality `g_μν e^a_μ e^b_ν = η_{ab}`
  - Spin connection `ω^{ab}_μ`
  - Torsion tensor `T^a_{μν}` (aligns with 6e.6 Einstein-Cartan extension)
  - Curvature 2-form `R^{ab}_{μν}`
  - Einstein-Cartan action as tetrad/spin-connection functional
  - Bridge theorem: `tetrad_formalism_EFE = metric_formalism_EFE` (equivalence when torsion = 0)
- Target ~12–16 theorems.

**Python side:**
- `src/classical_gr/tetrad_formalism.py` — tetrad split of representative metrics

**Bridges:**
- Depends on Waves 1, 2
- Aligns conventions with `ADWMechanism.lean`, `TetradGapEquation.lean`
- Feeds 6e.6 (Einstein-Cartan extension)

**Deliverables:**
- Module zero-sorry, building clean
- `tests/test_tetrad_formalism.py`
- **Mathlib PR:** Tetrad formalism (possibly)
- Inventory update: +12–16 theorems, +1 Lean module, +1 Python script

**Estimated LOE:** 3–5 person-months
**Risk:** Medium.

---

## Decision Gates

**Gate F.1 — before Wave 1 begins:** Mathlib differential-geometry audit complete? Bonn team coordination decided? Gate determines whether Wave 1 is build-from-Mathlib-base (3–5 PM) or import-Bonn+specialize (1 PM).

**Gate F.2 — after Wave 3 (`EnergyConditions`) ships:** Is 6e.4 `T_μν^emerg` sufficiently formed to test against NEC? If YES → immediate NEC check as follow-up. If NO → NEC check activates later when 6e.4 ships.

**Gate F.3 — before Wave 5 (`ADMFormalism`) begins:** LeanMillenniumPrizeProblems PDE framework available? If YES → import-based structure. If NO → inline PDE-lite for ADM; document as follow-up dependency.

**Gate F.4 — Mathlib PR strategy:** Coordinate which 6f waves become Mathlib PRs vs in-project modules. Default: all 6f waves are Mathlib-PR candidates; decision per wave at Stage 12.

---

## Dependencies

```
6f.1 (Curvature) — foundational; depends on Mathlib DG audit
  ↓
6f.2 (EinsteinTensor) — depends on 6f.1
  ↓
6f.3 (EnergyConditions) — depends on 6f.1, 6f.2
6f.4 (ExactSolutions) — depends on 6f.1, 6f.2
6f.5 (ADMFormalism) — depends on 6f.1, 6f.2; LMPP optional
6f.6 (TetradFormalism) — depends on 6f.1, 6f.2

Parallelism:
  6f.1 then 6f.2 (serial)
  6f.3, 6f.4, 6f.5, 6f.6 all parallel after 6f.2
```

---

## Timeline

| Wave | Scope | PM | Dependencies | Priority |
|------|-------|-----|--------------|----------|
| 6f.1 | `Curvature.lean` + Mathlib PR | 3–5 | Mathlib DG audit | **TIER 0 — foundational** |
| 6f.2 | `EinsteinTensor.lean` + Mathlib PR | 2–4 | 6f.1 | **TIER 0** |
| 6f.3 | `EnergyConditions.lean` + Mathlib PR | 2–3 | 6f.1, 6f.2 | **TIER 1 (correctness-push downstream)** |
| 6f.4 | `ExactSolutions.lean` + Mathlib PR | 3–5 | 6f.1, 6f.2 | **TIER 1** |
| 6f.5 | `ADMFormalism.lean` + Mathlib PR (possibly) | 4–6 | 6f.1, 6f.2, LMPP opt | **TIER 1** |
| 6f.6 | `TetradFormalism.lean` + Mathlib PR | 3–5 | 6f.1, 6f.2 | **TIER 1** |

**Total Phase 6f LOE:** 17–28 person-months. 6f.1 + 6f.2 serial (5–9 PM), then 6f.3 + 6f.4 + 6f.5 + 6f.6 parallel: wall-clock 9–15 months minimum.

**Deliverables cumulative:**
- 6 new Lean modules
- 6 small Python scripts (validation only; 6f is Lean-heavy)
- 0 papers in-project; all output is Mathlib PRs
- ~64–84 new theorems; zero sorry target; zero new axioms target

---

## Open Questions

**O.1 — LOAD-BEARING.** Mathlib differential-geometry audit: what's already present? What needs fresh formalization? Drop deep-research prompt before Wave 1.

**O.2** — Bonn diff-geom coordination: does the user have a contact? Strategy doc §16 Open Q item 4 flags this explicitly.

**O.3** — LeanMillenniumPrizeProblems PDE framework: usable directly, or needs Einstein-specific additions? Affects Wave 5.

**O.4** — Mathlib PR acceptance timeline: PRs may take months to land. Parallel track: in-project module + PR submission; accept if PR lands.

---

## What Success Looks Like

**Per wave:**
- 6f.1: Riemann + Ricci + scalar curvature typed + identities; Mathlib PR submitted/landed
- 6f.2: Einstein tensor + Bianchi identity; Mathlib PR submitted/landed
- 6f.3: WEC/NEC/DEC/SEC predicates; enables `T_μν^emerg` NEC check (correctness-push downstream)
- 6f.4: Schwarzschild + Kerr + dS + FLRW catalog; EFE-verification theorems
- 6f.5: ADM formalism + Hamiltonian/momentum constraints; Cauchy-problem prerequisite
- 6f.6: Tetrad + spin connection + torsion; Einstein-Cartan action; convention-alignment with ADW

**Cumulative:**
- 6 new Lean modules, Mathlib PRs (0–6 depending on acceptance)
- ~64–84 new theorems, zero sorry target
- **Program-level value:** backbone for 6a.6, 6e, 6g; contributes to Mathlib community

---

## Cross-References

**Prior phases this extends:**
- Phase 3/5d (existing tetrad work) — `ADWMechanism.lean`, `TetradGapEquation.lean` conventions
- Phase 5 (Paper 5 KerrSchild) — `KerrSchild.lean` extension

**Feeds downstream phases:**
- Phase 6a.6 (positive mass theorem) — 6f.1, 6f.3
- Phase 6e (nonlinear effective action) — 6f.1, 6f.3, 6f.6
- Phase 6g (all waves) — 6f.1–6f.6 foundational
- Mathlib community — direct PR contributions

**Source strategy document:**
- `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 (2026-04-22) §9

**Correctness-push highlights from strategy doc §12:**
- 6f.3 + 6g.2: NEC for `T_μν^emerg` (correctness-push anchor activates downstream)

---

*Phase 6f roadmap. Prepared 2026-04-24 from `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0. Six infrastructure waves, no in-project papers (all output is Mathlib PRs). Correctness-push anchor activates downstream via 6f.3 enabling NEC check on 6e.4 `T_μν^emerg`. All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md). Total PM: 17–28. External Mathlib progress is the main schedule risk.*
