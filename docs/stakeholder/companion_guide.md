# SK-EFT Hawking: Educational Companion Guide

## What Is This Project About?

This project asks a deep question: can the mathematics of exotic states of matter — superfluids, topological insulators, quantum spin liquids — also describe the fundamental forces and particles of the universe, and where exactly does that idea break down? We investigate this with a combination of numerical computation, formal mathematical proof-checking in Lean 4, and automated theorem proving, producing experimentally testable predictions along the way.

Everything is machine-checked in the Lean 4 proof assistant. The library currently contains **5,855 theorems across 322 modules with zero sorry project-wide** and only **one remaining axiom** (the 4+1D gapped-interface conjecture — a standard open question in lattice QFT, not a project-originated assumption).

---

## The Big Ideas

### 1. Sound waves that behave like black holes

When a fluid flows faster than the speed of sound, it creates a sonic horizon — a boundary that traps sound waves the same way a black hole traps light. Hawking predicted in 1974 that black holes emit faint radiation due to quantum effects near the horizon. The same physics applies to sonic horizons in laboratory fluids.

We computed the first corrections to the acoustic Hawking temperature from dissipation — the fact that real fluids have viscosity. These corrections are tiny (~0.001–0.1% for BEC, far smaller for graphene) but have a specific frequency signature experimentalists can look for.

Two experimental platforms are now in scope:
- **Polariton superfluids** (light-matter hybrids), roughly 10¹⁰ times hotter than BEC systems. A Paris group (Falque et al.) has observed negative-energy partner modes; spontaneous Hawking radiation detection is plausible within 1–2 years.
- **Graphene Dirac fluids** (Phase 5w, 2026), a natively relativistic 2+1D platform where the Dean group (Columbia, 2025) has already realized the first electronic sonic horizon. Predicted T_H ≈ 2.4 K for the Dean bilayer nozzle — nine orders of magnitude above BEC — with a detection path via current-noise spectroscopy S_I(ω).

### 2. Why three generations of matter

The Standard Model has three copies ("generations") of its fundamental particles. Nobody knows why three. We derived that the number must be divisible by three, from two independent mathematical facts:

- Each generation contributes a chiral central charge of 8 (from its 16 Weyl fermions).
- The Dedekind eta function forces this charge to be divisible by 24 through a framing-anomaly consistency condition.

The ratio 24 / 8 = 3 constrains the generation count, with 1 and 2 proved impossible and 6 the next allowed value.

The algebraic core of this argument — the Ext computation over the A(1) Steenrod sub-algebra — is itself machine-checked (Phase 5q–5r, April 2026). This is the first machine-checked Ext computation over any Steenrod sub-algebra in any proof assistant. What remains as hypotheses are three standard topological facts (ko-spectrum cohomology, Adams SS collapse, ABP splitting) that require formalizing algebraic topology in Lean, which no proof assistant currently supports.

### 3. The number 16 appears everywhere

The Standard Model has 16 Weyl fermions per generation. The anomaly classification lives in Z/16. Rokhlin's theorem says spin-manifold signatures are divisible by 16. Kitaev's classification of topological superconductors has 16-fold periodicity.

We proved these are all the same 16, and we proved exactly where the number comes from: the algebraic bound from lattice theory is 8 (the E8 lattice achieves this), and the extra factor of 2 requires smooth topology. The jump from 8 to 16 encodes whether a mathematical space can be smoothed — a profound connection between particle physics and geometry.

### 4. A chain from lattice models to gauge theory

We formalized a complete mathematical chain connecting laboratory-accessible physics to fundamental gauge theory:

**Onsager algebra** (exactly solvable lattice models) → **quantum groups** (q-deformations with Hopf algebra structure) → **fusion categories** → **modular tensor categories** → **TQFT partition functions and knot invariants**.

Every link is machine-checked. The chain was extended to rank-2 in Phase 5i: **U_q(sl₃)** is the first rank-2 quantum group in any proof assistant, and **SU(3)_k fusion** at k=1,2 is the first SU(3)-fusion formalization anywhere. Phase 5m generalized this to a parameterized `QuantumGroup k A` typeclass over arbitrary Cartan matrices, with Kac-Walton fusion as a general algorithm. Phase 5n–5p added the Temperley–Lieb / Jones–Wenzl / WRT pipeline end-to-end, ending in a machine-checked Fibonacci-braiding universality proof for quantum computation.

### 5. The chirality problem

The biggest obstacle to deriving the Standard Model from condensed-matter physics is chirality. A January-2026 construction by Thorngren–Preskill–Fidkowski (TPF) likely evades the historical Nielsen–Ninomiya / Golterman–Shamir no-go theorems. We provided the first formal analysis of why the evasion works: 9 no-go conditions formalized, 5 proved violated by TPF, with a three-pillar master synthesis theorem (GS evasion + GT positive construction + Z₁₆ anomaly). Phase 5s added the first machine-checked 2+1D Fidkowski–Kitaev Cayley-calibrated gapped-interface construction (16×16 Hamiltonian, explicit E₀ = −14, Δ = 14), bundled with the 1+1D K-matrix analogue via a dimensional-ladder bridge theorem.

### 6. Can gravity emerge from quantum matter?

The Akama–Diakonov–Wetterich (ADW) mechanism proposes that gravity emerges from fermion condensation — analogous to how Cooper pairs form in superconductors. We formalized the mean-field structure, identified the tetrad gap equation (which had not been explicitly written down in the published literature), and proved its existence/uniqueness via IVT + Banach fixed-point. The ADW gap equation has a nontrivial Lorentzian-signature solution for G > G_c = 8π²/(N_f Λ²); two spin-2 graviton modes emerge as Nambu–Goldstone bosons. Instanton-assisted zero-mode counting is machine-checked (`InstantonZeroModes.lean`) by bypassing the 4D index theorem via Clifford separation of variables.

What definitively fails: the non-Abelian fracton → gravity route (machine-proved obstruction in `FractonNonAbelian.lean`) and the perturbative Wen–ADW coupling (~6000× too weak, quantified in `EmergentGravityBounds.lean`). Non-Abelian gauge structure cannot survive a fluid layer (gauge erasure is a structural theorem), but *can* originate from topological order via the quantum-group route.

On the dark-energy side, a sequence of deep-research rounds on Klinkhamer–Volovik-style emergent-vacuum mechanisms all returned NO-GO for DESI DR2 compatibility. The obstruction is structural and is now formalized: `GibbsDuhemTheorem.lean` proves that any single-scalar self-tuning emergent-vacuum framework with Gibbs–Duhem equilibrium locks `w_vac = −1` by Lorentz invariance, realization-independently. Paired with the first closed-form derivation of the vestigial-gravity EOS (`VestigialEOS.lean`, `w_vest(τ) = (1−τ²)/(5τ²−1)`) and the four-factor orthogonality principle (`DarkEnergyObstructionPrinciple.lean`), Layer-3 predictive scope is now explicitly scoped to SM+GR emergent physics; the dark-energy sector is documented as outside the architecture's tested predictive scope under the mechanisms explored (see `docs/ARCHITECTURE_SCOPE.md`).

### 7. Dark-matter connections

The same infrastructure that closes the dark-energy quest also lets us classify concrete dark-*matter* candidates:

- **Hidden-sector DM classification** (`HiddenSectorClassification.lean`, `HiddenSectorMixedCharge.lean`) — ℤ₁₆ anomaly-driven enumeration of SM-singlet Weyl sectors; the T-0 TQFT candidate is invisible to all planned direct-detection experiments.
- **SFDM merger forecast** (`SFDMMergerForecast.lean`, backing Paper 17's "money plot") — superfluid DM produces a smoking-gun sonic-boom step function at galaxy-cluster Mach transitions; Euclid × Roman stacked ≥ 30 mergers reaches 3.5–5.7σ; first 3σ detectable around 2028.
- **Fracton DM viability** (`FractonDarkMatter.lean`) — a p-wave dipole superfluid phase keeps fracton DM viable at MeV–TeV scales.
- **Fang–Gu torsion DM obstruction** (`FangGuTorsionDM.lean`) — traceless stress–energy tensor forces w = 1/3, kinematically excluding FG-DM at CDM level.
- **Dark-sector synthesis** (`DarkSectorSynthesis.lean`) — seven cross-connection theorems pinning the Paper 17 empirical-hook ranking to Lean-decidable ground.

### 8. A geometric quantum gate

A parallel strand uses the same formalization rigour on a finite-dimensional quantum-information target. `FermiHubbardDimer.lean` (backing Paper 18) formalizes a minimal Berry-phase theorem for a two-site Hubbard doublon system: the dark state carries a −1 sign under a π-sweep, the dynamical phase vanishes under the kernel-angle condition, and the accumulated phase is purely geometric. The SWAP unitary on the 3-dimensional singlet sector is realized as a Householder reflection in an explicit orthonormal eigenbasis. This is the first formally verified analysis of a symmetry-protected non-topological two-qubit gate, complementary to the Fibonacci-braiding universality proof in the quantum-group chain.

### 9. A new experimental platform: graphene Dirac fluid

The dissipative-Hawking chain was extended to a 2+1D relativistic Dirac fluid. Modules `DiracFluidMetric.lean`, `GrapheneHawking.lean`, `DiracFluidSK.lean`, `GrapheneNoiseFormula.lean`, and `QuasiOneDReduction.lean` form the graphene track. The 3×3 acoustic metric block-diagonalizes for quasi-1D flow, letting the existing 1+1D WKB machinery apply directly (≈92% Lean theorem reuse). Predicted T_H ≈ 2.4 K for the Dean bilayer nozzle (9 orders above BEC), dissipative correction δ_diss negligible relative to dispersive δ_disp (~−3%), noise formula `ΔS_I(ω) = 2ℏω σ_Q Γ(ω) n_H(ω)` derived from first principles (Keldysh FDT + Landauer–Büttiker). Paper 16a documents the platform end to end; collaboration outreach to Lucas/Dean (Columbia) and Kim (Harvard) is unblocked.

---

## How It Works

### Three-Layer Verification

Every result passes through three independent checks:

1. **Python computation** — numerical calculations with real experimental parameters, validated by 2,800+ automated tests.
2. **Lean 4 formal proofs** — machine-checked theorems ensuring logical correctness.
3. **Aristotle automated prover** — an AI system that filled 322 theorems across 44 runs where interactive proving was impractical.

### The Provenance Dashboard and Knowledge Graph

An interactive web dashboard (`uv run python scripts/provenance_dashboard.py`, localhost:8050) lets you trace any claim in any paper back through the computation pipeline to its source: which formula computed it, which Lean theorem verifies it, which experimental parameters it depends on, and which published paper those parameters come from. A PG+AGE knowledge graph (Phase 5v) with ~1,000+ nodes and 11+ edge types visualizes the full provenance chain, and a per-paper readiness state machine tracks 11 submission gates (citation integrity, parameter provenance, narrative grounding, first-claim verification, etc.).

### Adversarial Review (Stage 13)

Every paper is run through an adversarial-reviewer agent (Opus, fresh context) before submission. Findings are tracked in `papers/AutomatedReviews/` and auto-ingested as `ReviewFinding` nodes in the knowledge graph. Paper 17 and Paper 18 were shipped through this loop in the 2026-04-26 session with all P1 + all RECOMMENDED findings addressed.

---

## What's New Since You Last Looked (2026-04-24 → 2026-05-07 snapshot)

Since the 2026-04-24 snapshot, the program has shipped Phase 6 e/f/g/m/n/o substantive content + Phase 7a paper-bundle architecture freeze + Phase 7 absorption Sessions 1–5 closing all 14 bundle stages 9/10/13 to GREEN. Notable additions:

- **Classical-GR algebraic backbone in Lean** — first in any proof assistant. Phase 6f shipped Riemann, Einstein tensor, energy conditions with explicit counterexample witnesses, exact-solutions catalog, ADM 3+1, tetrad formalism, Lorentzian metric typeclass, and bundle-level Levi-Civita uniqueness via the substantive Koszul-bilinear-form argument from Wald §3.1.
- **Heat-kernel chain through $a_4$ + Stelle higher-curvature + Einstein–Cartan torsion bound passage** — Phase 6e closes the "GR from condensate" derivation chain. Four Decision Gates passed. Cosmological-constant prediction overshoots observation by ~$10^{122}$ at Planck-natural cutoff (CC problem reproduced, not solved — the honest verdict).
- **Phase 6m three-track dark-energy reframing** — combined with Phase 5y, all four major dark-energy mechanism families have now been formally exercised. Layer-3 dark-energy outside the architecture's tested predictive scope under all tested mechanisms.
- **First complete-mechanism-family NO-GO closure (Phase 6m Track B Entropic-gravity DE, 8/8 unanimous).** Phase 7 absorption Session 5 honest correction: Tsallis/Barrow figures relabeled as AIC/BIC-based (not Bayes-factor); aggregator updated to mixed-threshold form.
- **APS-η for analog horizons (Phase 6o W2a)** — first systematic substrate-side identification on a chirally-asymmetric analog Hawking horizon. Two-cell partition: parity-symmetric (BEC + ADW; APS = bulk AS) vs chirally-asymmetric (³He-A; substantive boundary correction).
- **First explicit classical Kerr-Schild double-copy on analog gravity in literature** (Phase 6o W1b) — positive Kerr-Schild + 3-obstruction strong-form BCJ NO-GO theorem-pair on Petrov-D acoustic metric.
- **Schellekens chain reframing of $24 | c_-$ → $N_{\rm gen} \equiv 0 \pmod 3$** (Phase 6o W2b) — reframed as theorem-quality classification corollary of Möller-Scheithauer 2024 c=24 holomorphic-VOA classification. Modular Bootstrap DR §8 Tier 1(a) "highest-leverage move."
- **Sakharov 4-criterion ↔ $\Lambda_J = \Lambda_{\rm HK}$ biconditional retired** in favor of honest one-way implication + load-bearing depletion factor (Phase 6o W4a verdict B). Per Volovik-Jannes 2012 §VII forward-only argument + FLS BEC primary-source verification.
- **First alphabet-independent kernel-verified quantitative Solovay-Kitaev substrate** (Phase 6u Waves 1–6 + Wave 4b). The Lie-algebraic core of Solovay-Kitaev (Dawson-Nielsen recursion, Cartan v4 classification, BCH bracket-closure, ε₀-net) packaged behind a generic `GeneratingSet` abstraction. Future quantum-gate-set formalizations now instantiate rather than re-derive.
- **First kernel-verified UNCONDITIONAL Clifford+T quantitative Solovay-Kitaev compiler** (Phase 6u Track T-S.5). The bundled-strict headline `solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight_unconditional` conjoins error bound `≤ ε` and polylog length bound at the same compile level. Clifford+T is the canonical fault-tolerant gate set; this is the verified specification.
- **First kernel-verified ⟨H, T⟩ density in SU(2)** (Phase 6u T-S.2) via Niven-based algebraic-integer obstruction on `√2·sin(π/8)` (the trace of `H_SU·T_SU`). The 1999 BMPRV folklore result, now machine-verified. The methodology generalizes to future alphabet density proofs (Read-Rezayi, etc.).
- **Paper-bundle architecture frozen** (Phase 7a). 14 publication targets: 1 flagship + 5 Tier-1 deep + 3 Tier-2 PRL + 3 Tier-3 infrastructure (I3 added Phase 6n Session 4 under Pipeline Invariant #14) + 2 Tier-4 experimental. 14-step BUNDLE_LIFT_PROCEDURE + LATE_PHASE6_ABSORPTION_PROTOCOL frozen.
- **All 14 bundles 🟢 GREEN** at Phase 7 absorption Session-5 close. The L1 → arXiv-voucher gate is the only remaining program-level blocker for the first three Tier-2 PRL splashes.
- **Standing primary-source WebFetch + verify policy** adopted at Session 5 ("do that kind of thing from now on"). Caught Luciano AIC vs Bayes methodology mismatch + BelgiornoCacciatori2024 fabricated-bibitem entry. 51 PDF caches → 0 missing.

The shipping-ready state is "all 14 bundles cleared per-bundle reviewer triple, awaiting submission gates per the dependency graph."

---

## By the Numbers (2026-05-06 snapshot)

| Metric | Count |
|--------|-------|
| Lean theorems | 5,855 (5,830 substantive + 25 placeholder) |
| Lean modules | 322 |
| Axioms | 1 (4+1D gapped-interface conjecture) |
| Sorry gaps | 0 project-wide |
| Python test files | 99 (4,179 pytest cases) |
| Python source modules | 130 across 18+ sub-packages including `dark_sector/`, `fermi_hubbard/`, `graphene/` (all new since Phase 5s) |
| Publication-quality figures | 154 |
| Paper drafts | 42 |
| Computational notebooks | 87 (technical + stakeholder pairs) |
| Aristotle prover runs | 44 (322 theorems proved) |
| Publication-bundle targets | 14 (1 flagship + 5 Tier-1 deep + 3 Tier-2 PRL + 3 Tier-3 infrastructure + 2 Tier-4 experimental) |
| Deep research files | Phase-1 through Phase-6o under `Lit-Search/` |
| Stakeholder docs | 29+ under `docs/stakeholder/` |

*Synced 2026-05-07 — counts refreshed from `docs/counts.json` (2026-05-06).*

### Formal Verification Firsts

- First formally verified anomaly constraint in particle physics (N_f ≡ 0 mod 3)
- First quantum group (U_q(sl₂)) in any proof assistant — and first Hopf algebra non-trivial instance
- First rank-2 quantum group (U_q(sl₃)) — and first parameterized `QuantumGroup k A` typeclass over arbitrary Cartan matrices
- First SU(2)_k and SU(3)_k fusion categories in any proof assistant
- First affine and restricted quantum groups (U_q(ŝl₂), u_q(sl₂))
- First ribbon category and modular tensor category definitions
- First pivotal and spherical category definitions
- First Drinfeld centers computed (toric code, non-abelian D(S₃))
- First complete braided modular tensor category (Ising: R-matrix, hexagon, ribbon, Gauss sum)
- First formally verified knot invariants (trefoil = −1, figure-eight from Ising MTC)
- First WRT TQFT pipeline end-to-end (surgery presentation → invariant computation)
- First Temperley–Lieb algebra and Jones–Wenzl idempotents in any proof assistant
- First Muger center formalization; first machine-checked general dual-closure theorem
- First Kac–Walton fusion algorithm in any proof assistant
- First E8 lattice verification and algebraic Rokhlin decomposition
- First machine-checked Ext^n_{A(1)}(F₂, F₂) computation over any Steenrod sub-algebra (Phase 5q)
- First Fidkowski–Kitaev 2+1D Cayley-calibrated gapped-interface construction
- First machine-checked Gibbs–Duhem obstruction theorem for emergent-vacuum dark-energy frameworks (Phase 5y)
- First closed-form derivation of the vestigial-gravity effective-fluid EOS
- First machine-checked Fermi-Hubbard geometric SWAP / Berry-phase theorem (Phase 5t)
- First verified jackknife and autocorrelation estimators for lattice Monte Carlo
- First formal analysis of the chirality wall (GS no-go ↔ TPF evasion, master synthesis)
- First Volovik–Zubkov Fermi-point topological-charge → emergent-gauge-group formalization

---

## Where to Learn More

| Topic | Document |
|-------|----------|
| Full technical README | [`README.MD`](../../README.MD) |
| Module inventory and quick-reference index | [`SK_EFT_Hawking_Inventory_Index.md`](../../SK_EFT_Hawking_Inventory_Index.md) |
| Strategic situation and proof-chain assessment | [`docs/RESEARCH_STATUS_OVERVIEW.md`](../RESEARCH_STATUS_OVERVIEW.md) |
| What each phase accomplished | `docs/stakeholder/Phase{N}_Implications.md` |
| Strategic positioning per phase | `docs/stakeholder/Phase{N}_Strategic_Positioning.md` |
| Phase 5y closure (2026-04-23) | [`Phase5y_Closure_Summary.md`](Phase5y_Closure_Summary.md) + four cross-phase impact memos |
| Phase 6e (heat-kernel through Einstein–Cartan) | [`Phase6e_Implications.md`](Phase6e_Implications.md) + [`Phase6e_Strategic_Positioning.md`](Phase6e_Strategic_Positioning.md) |
| Phase 6f (classical-GR algebraic backbone) | [`Phase6f_Implications.md`](Phase6f_Implications.md) + [`Phase6f_Strategic_Positioning.md`](Phase6f_Strategic_Positioning.md) |
| Phase 6g (singularities + area + no-hair) | [`Phase6g_Implications.md`](Phase6g_Implications.md) + [`Phase6g_Strategic_Positioning.md`](Phase6g_Strategic_Positioning.md) |
| Phase 6m (three-track dark-energy NO-GO closure) | [`Phase6m_Implications.md`](Phase6m_Implications.md) + [`Phase6m_Strategic_Positioning.md`](Phase6m_Strategic_Positioning.md) |
| Phase 6n (math-substrate compression) | [`Phase6n_Implications.md`](Phase6n_Implications.md) + [`Phase6n_Strategic_Positioning.md`](Phase6n_Strategic_Positioning.md) |
| Phase 6o (substrate-findings + first-mover discoveries) | [`Phase6o_Implications.md`](Phase6o_Implications.md) + [`Phase6o_Strategic_Positioning.md`](Phase6o_Strategic_Positioning.md) |
| Phase 6u (alphabet-independent quantum-compiler substrate + Clifford+T) | [`Phase6u_Implications.md`](Phase6u_Implications.md) + [`Phase6u_Strategic_Positioning.md`](Phase6u_Strategic_Positioning.md) |
| Phase 7 (paper-bundle architecture + absorption Sessions 1–5) | [`Phase7_Implications.md`](Phase7_Implications.md) + [`Phase7_Strategic_Positioning.md`](Phase7_Strategic_Positioning.md) |
| Predictive-scope boundary | [`docs/ARCHITECTURE_SCOPE.md`](../ARCHITECTURE_SCOPE.md) — Layer 3 scope: SM+GR in, dark sector out under all tested mechanisms |
| Bundle readiness heatmap | [`docs/BUNDLE_READINESS_HEATMAP.md`](../BUNDLE_READINESS_HEATMAP.md) — auto-regenerated per-bundle Stage-9/10/13 status |
| Paper strategy + per-draft mapping | [`docs/PAPER_STRATEGY.md`](../PAPER_STRATEGY.md) + [`docs/PAPER_DRAFT_MAPPING.md`](../PAPER_DRAFT_MAPPING.md) |
| The broader research program | [`Feasibility Study`](../Fluid-Based%20Approach%20to%20Fundamental%20Physics%20%20Feasibility%20Study.md) |
| Critical assessment | [`Consolidated Critical Review v3`](../Fluid-Based%20Approach%20to%20Fundamental%20Physics-%20Consolidated%20Critical%20Review%20v3.md) |
| What's next | [`docs/roadmaps/Phase6_Deferred_Targets.md`](../roadmaps/Phase6_Deferred_Targets.md) and [`Phase6_Roadmap.md`](../roadmaps/Phase6_Roadmap.md) |
| Interactive exploration | `uv run python scripts/provenance_dashboard.py` → http://localhost:8050 |

---

*Last updated: 2026-05-25 (Phase 6u closure).*
