# Phase 6ED — Kernel-Verified Graphene Electronic Structure: Honeycomb Tight-Binding, Dirac Cones, and the Haldane Chern Witness

**Status: IN PROGRESS — Waves 1 + 2 SHIPPED, Wave 3 open, Wave 4 gated (authorized 2026-07-27; Wave 1 landed 2026-07-29).** Fourth phase of the `6E*` series (*verified device-physics metrology*). Independent of 6EA–6EC (parallelizable); feeds 6EE's material-parameter seams and closes the graphene gap in the repo's band-theory arc. See `Phase6EA_Roadmap.md` for the series framing.

**Thesis.** The repo's graphene corpus formalizes graphene as a *Dirac fluid* (Phase 5w: analog metric, Hawking spectrum, noise PSD — shipped) and its band-theory corpus formalizes *abstract* two-band Chern machinery (Phase 6CA: `blochPauli` d·σ models, FHS lattice Chern number, gauge invariance — shipped). What is missing is the bridge both sides implicitly cite: graphene's actual electronic structure. Honeycomb tight-binding, the two Dirac points with linear dispersion and the emergent Fermi velocity, the sublattice-pseudospin Berry phase π, the gapped-Dirac-mass band structure, and the Haldane model as the honeycomb Chern insulator — none is formalized (verified 2026-07-27: `BlochFHS.lean:24-26` explicitly defers any nontrivial concrete Chern frame; no honeycomb lattice model exists in the project or in PhysLib, whose `TightBindingChain` is single-band 1D and was already rejected by 6CA as "wrong model").

Clean whitespace: no prover has a kernel-checked honeycomb band structure, Dirac-point dispersion, or concrete Haldane-model Chern number.

> **⚠️ GUARDRAIL — coordinate the Chern witness with 6CA's gated QWZ spike; complement, never duplicate.** Phase 6CA separately gates a QWZ (square-lattice) model instantiation for a nontrivial `blochLatticeChern` value. This phase's Wave 3 provides the *Haldane* (honeycomb) witness through the same `BlochFHS` adapter. If the QWZ spike has landed by Wave-3 start, reuse its instantiation pattern verbatim and cite it; if not, Wave 3's Haldane witness becomes the first nontrivial frame and the QWZ spike should later cite *it*. Either order is fine; duplicating the adapter machinery is not. Check `TopologicalBand/` state at Stage 2 and record which branch applies.

> **⚠️ GUARDRAIL — tight-binding model, not material claims.** Theorems are about the stated lattice Hamiltonians (nearest-neighbor honeycomb, Haldane's complex next-nearest-neighbor extension). Identifying model parameters with any physical sample (hopping energies, gap sizes, measured v_F) is a consumer-side hypothesis. No claim about devices, transport measurements, or fabrication.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.** *(Compaction / sub-agent backstop.)*
> 1. **Bootstrap reads, in order:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` → `docs/WAVE_EXECUTION_PIPELINE.md` → `SK_EFT_Hawking_Inventory_Index.md` → `Phase6EA_Roadmap.md` (series head) → `docs/roadmaps/Phase6CA_Roadmap.md` + `lean/SKEFTHawking/TopologicalBand/BlochFHS.lean` (the machinery Wave 3 instantiates — read the source directly).
> 2. **Read this roadmap end-to-end**; Bricks are exact (verified 2026-07-27).
> 3. **Dev loop is MCP-first** (`lean-lsp-mcp`), per the 6EA instructions.
> 4. **Pipeline disciplines (hard gates):** (a) **bundle target D11** (this phase joined D11's sources 2026-07-27 as its concrete graphene band-structure thread; Invariant #14 applies — bundle-aware content from inception; scaffolding at first content-lift per `BUNDLE_LIFT_PROCEDURE`); (b) preemptive-strengthening + post-wave audit; (c) kernel-purity, zero sorry, no new axioms without sign-off (#15); (d) no `maxHeartbeats` (#10).
> 5. **This phase:** the two-band structure targets the existing `SKEFTHawking.Topological.blochPauli` d·σ form — honeycomb enters through `d(k) = (Re f k, −Im f k, m)` with `f k = 1 + exp(I·k·a₁) + exp(I·k·a₂)`; reuse `blochPauli_sq`, `blochPauli_gap_pos`, secular machinery rather than re-deriving 2×2 spectral algebra.

**Standing invariants:** kernel-pure; no new axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening; never push. **Two-layer honesty:** lattice-model mathematics Lean-verified; material identifications consumer-side. Wave sizing ≈ one `/goal`.

**Substrate (verified 2026-07-27).**
- **Reuse:** `SKEFTHawking.Topological.blochPauli_isHermitian` / `blochPauli_sq` / `blochPauli_secular_det` / `blochPauli_gap_pos` (`BlochBundle.lean`) — the 2-band spectral core; `SKEFTHawking.TopologicalBand.sum_plaquetteArg_eq_two_pi_mul_latticeChern` + `latticeChern_gaugeInvariant` (`FHSLatticeGauge.lean`) and the `blochLatticeChern_integrality`/`_rephase` Bloch adapter (`BlochFHS.lean`) — Wave 3 instantiates these, building nothing new at that layer; `PrincipalBranch.lean` arg machinery (Berry-phase wave).
- **Absent → build:** the honeycomb structure factor `f k` and its zero set (Dirac points); linear-dispersion expansion; Berry phase of the gapless/gapped cone; the Haldane d-vector and its Chern witness; bilayer extension.
- **Rejected substrate (do not use):** PhysLib `CondensedMatter.TightBindingChain` (1D single-band; wrong model — 6CA precedent).

**Publication target:** bundle **D11** — *Kernel-Verified Topological Band Theory & Metamaterial Substrate* (**joined D11's sources 2026-07-27**; `PAPER_STRATEGY.md` §2.2 thread (v)). This phase supplies the concrete named-lattice completion D11's thread (i) explicitly deferred. Its `6E*` siblings (6EA/6EB/6EC/6EE) publish in **D12**; this phase alone routes to D11.

---

## Wave 1 — Honeycomb tight-binding and the Dirac points

**Goal.** The nearest-neighbor honeycomb Bloch Hamiltonian in `blochPauli` form; the two inequivalent Dirac points as the exact zero set of `f`; gap positivity away from them. Verdict: reachable — finite trigonometric algebra over the existing 2-band core; the zero-set characterization (`f k = 0 ↔ k ∈ {K, K'}` mod reciprocal lattice) is the only delicate step.

**Why.** Everything graphene-electronic starts here; this wave alone converts the repo's "graphene" from fluid-analog language into an actual lattice model with kernel-checked band structure.

**Bricks.** `blochPauli_*` family (`BlochBundle.lean`); Mathlib `Complex.exp` algebra.

**Done (AC / `/goal` condition).** ✅ **SHIPPED 2026-07-29** — 24 extracted declarations, 0 sorry / 0 axiom / 0 `native_decide` / 0 `maxHeartbeats`, kernel-pure (10 headline theorems checked individually), root-imported.
- [x] `lean/SKEFTHawking/GrapheneBand/Honeycomb.lean` builds 0-sorry, kernel-pure, with:
- [x] **shipped as `structureFactor` in Bloch-phase coordinates `θ = (⟨k,a₁⟩, ⟨k,a₂⟩)` rather than against a fixed primitive-vector pair — a strengthening**, since every theorem then holds for *any* primitive-vector choice and the lattice geometry enters only where a consumer supplies it (same two-layer style `BlochBundle` uses for `d(k)`). Plus `honeycombD` and `honeycombBloch`, the latter made load-bearing by `honeycombBloch_isHermitian` and `honeycombBloch_sq` rather than left as a name `honeycombStructureFactor` + `honeycombBloch`;
- [x] `honeycomb_energy_eq` — bands `±|f(θ)|`, routed through `dNormSq_honeycombD` (`‖d‖² = |f|²`) and `BlochBundle`'s Pauli core; nothing 2×2 is re-derived;
- [x] **shipped as the QUOTIENT-FREE characterization** `structureFactor_eq_zero_iff : f θ = 0 ↔ cos θ₁ = −1/2 ∧ cos θ₂ = −1/2 ∧ sin θ₁ + sin θ₂ = 0`, with the K/K′ reading recovered by `structureFactor_eq_zero_iff_dirac_branch` (the two branches are `sin θ₁ = ±√3/2`). **This is exactly the same set as the AC's `mod`-reciprocal-lattice phrasing** — periodicity is automatic in `cos`/`sin`, so no quotient bookkeeping is needed and none is smuggled — and it is strictly easier for a consumer to discharge (three real equations, not a statement about a quotient). Concrete points `diracK`/`diracK'` shipped `structureFactor_zero_iff` + `diracPoint_K_def`/`_K'_def`;
- [x] `honeycomb_gapless_at_diracK` + `honeycomb_gapless_at_diracK'` and `honeycomb_gapped_away` (via `blochPauli_gap_pos`);
- [x] `norm_num` witnesses at Γ (`|f| = 3`) and M (`|f| = 1`), plus gaplessness at K (`0`);
- [x] preemptive-strengthening + post-wave audit — residue: `honeycombBloch` was initially a *decorative* definition no theorem touched (the `blochPauli` instantiation existed in name only); it now carries `honeycombBloch_isHermitian` and `honeycombBloch_sq`. Added `honeycomb_band_dispersive` (the three named-point energies are pairwise distinct) so the band is provably **not flat** — the formulas alone would permit a flat band.

**UNKNOWN-4 RESOLVED (Stage 2, 2026-07-29) — guardrail branch B applies.** The QWZ spike has **not** landed: `TopologicalBand/BlochFHS.lean:24-26` still reads *"a nontrivial frame-derived Chern value (C = ±1) requires the QWZ transcendental evaluation … and stays behind the separately-gated QWZ spike."* Therefore **Wave 3's Haldane witness becomes the first nontrivial concrete Chern frame in the repo, and the QWZ spike should later cite it.** Recorded per the coordination guardrail. Note the difficulty signal that same comment carries: the obstruction is the transcendental `Complex.arg` evaluation at generic momenta — Wave 3 must budget for it (UNKNOWN-3's grid-size spike is the mitigation).

## Wave 2 — Linear dispersion, Fermi velocity, and the Dirac mass

**Goal.** The first-order expansion at K: `|f(K+q)| = (3/2)·|q| + O(|q|²)` with explicit remainder bound (emergent linear dispersion; v_F as the model constant `(3/2)·t·a/ℏ` in the declared unit contract), and the gapped model `d₃ = m ≠ 0` with gap `2|m|` exactly. Verdict: reachable — Taylor-with-remainder on a trigonometric function of two variables, following the repo's enclosure discipline (explicit remainder constants, no O-notation in statements).

**Why.** Linear dispersion is the load-bearing property every downstream consumer cites (it is what makes graphene "Dirac"); the explicit-remainder form makes it a usable bound instead of folklore.

**Bricks.** Wave 1; `NumericalBounds` enclosure pattern; Mathlib `Complex.exp` Taylor bounds (`Complex.abs_exp_sub_one_sub_id_le`-family; exact route UNKNOWN-1).

**Done (AC / `/goal` condition).** ✅ **SHIPPED 2026-07-29** — kernel-pure, 0 sorry / axiom / `native_decide` / `maxHeartbeats`, root-imported.

**UNKNOWN-1 RESOLVED:** route = the **`Complex.exp` Taylor bound** (`Complex.norm_exp_sub_one_sub_id_le`), one application per hopping term, giving remainder constant **`C = 1`** on the ball `|q₁| ≤ 1 ∧ |q₂| ≤ 1`. The two alternatives (two-variable `Real.cos`/`sin` expansion; direct polynomial sandwich) would both have rebuilt remainder control this lemma already provides.
- [x] `lean/SKEFTHawking/GrapheneBand/DiracExpansion.lean` builds 0-sorry, kernel-pure, with:
- [x] `structureFactor_linear_expansion` — shipped against the **coordinate-free** linear form `‖L(q)‖ = √(q₁² − q₁q₂ + q₂²)` (`linearForm_norm`) rather than `(3/2)‖q‖`. The `3/2` is that value *after* converting phase offsets to Cartesian momentum against a lattice constant `a`; it is a coordinate-and-units artifact, so shipping the quadratic form (the triangular lattice's reciprocal metric, isotropic in the physical frame) is the same strengthening Wave 1 made. `C = 1`, ball stated;
- [x] **`fermiVelocity_def` deliberately NOT shipped** — `v_F = 3ta/2ℏ` is definable only once a lattice constant and a unit contract are fixed, which this phase keeps consumer-side; shipping it would bake in the coordinate choice Wave 1 was written to avoid. The physical content (the linear coefficient) is `linearForm_norm`;
- [x] `gapped_dirac_gap_eq` — the gap at the Dirac point is **exactly** `2|m|`, via Wave 1's `honeycomb_gapless_at_diracK` (so `‖d‖ = |m|` on the nose, not an approximation);
- [x] **shipped as `gap_vs_mass_strictMono` (strict, not merely monotone) + `gapped_dirac_gapless_iff_massless`** (the mass hypothesis is load-bearing: the gap closes iff `m = 0`) `gap_vs_mass_monotone`. **The AC's inside/outside witness pair was NOT shipped, because the request rests on a false premise:** the validity ball is an artifact of the *Mathlib lemma*, not of the mathematics — the sharp bound `‖e^{iq}−1−iq‖ ≤ q²/2` holds for every real `q`, so the shipped bound (constant 1) is globally true and **cannot** fail outside the ball. Rather than fake it, the honest non-vacuity content ships instead: `dispersion_linear_not_exact` exhibits the K→K′ offset, where `‖f‖ = 0` while `‖L(q)‖ = √(4π²/3) > 0`, proving the remainder term is genuinely needed and the inequality is not a disguised equality;
- [x] preemptive-strengthening + post-wave audit.

## Wave 3 — Berry phase and the Haldane Chern witness

**Goal.** The sublattice-pseudospin winding/Berry phase π of the gapless cone (via the existing `PrincipalBranch` arg machinery), and the Haldane model (complex NNN hopping) as a concrete `BlochFHS` frame with `blochLatticeChern = ±1` — the first (or second, per the 6CA guardrail) nontrivial concrete Chern frame in the repo. Verdict: reachable-with-care — the FHS machinery makes the Chern computation finite plaquette arithmetic; the care is the frame construction (nonvanishing `d` over the discretized Brillouin torus at stated Haldane parameters).

**Why.** Closes the loop the whole band-theory arc points at: an actual named lattice model with a kernel-checked nonzero topological invariant, connecting the graphene family (this phase) to the abstract Chern machinery (6CA) with zero new axioms.

**Bricks.** `BlochFHS.blochLatticeChern_integrality`/`_rephase` + `FHSLatticeGauge` master identity + `FHSExamples.latticeChern_Uwit` (the existing nontrivial abstract witness whose plaquette-arithmetic pattern the Haldane frame follows); `PrincipalBranch.lean`; Waves 1–2.

**Done (AC / `/goal` condition).**
- [ ] `lean/SKEFTHawking/GrapheneBand/HaldaneWitness.lean` builds 0-sorry, kernel-pure, with:
- [ ] `coneBerryPhase_pi` — the ±π pseudospin winding of the gapless cone, stated via the principal-branch arg sum on a stated loop (reusing `PrincipalBranch`; exact statement form frozen at Stage 2, UNKNOWN-2);
- [ ] `haldaneDVector_def` (declared Haldane parameters `t, t₂, φ, m`) + `haldane_gapped : chosen parameters → ∀ k, d k ≠ 0` (the frame-admissibility proof);
- [ ] `haldaneFrame_latticeChern_eq_one` (or `−1`; sign fixed by the declared orientation convention) at an explicitly stated parameter point and grid size — the concrete nontrivial Chern witness through `blochLatticeChern`;
- [ ] `haldane_trivial_phase_chern_zero` at a parameter point in the trivial phase (`|m| > mass threshold`) — the two-phase pair that makes the witness a *classification* statement, not a single number;
- [ ] 6CA-coordination note recorded (which guardrail branch applied); root-module import + Inventory/counts refresh;
- [ ] preemptive-strengthening + post-wave audit.

## Wave 4 (gated) — Bernal bilayer extension

**Goal.** The four-band Bernal-bilayer Hamiltonian, its low-energy quadratic band touching, and the displacement-field-tunable gap. **Gated:** open this wave only after Waves 1–3 ship clean AND a consumer for bilayer statements exists (6EE seam or a lift decision); otherwise the phase closes at Wave 3 (Pareto).

**Done (AC, if opened).**
- [ ] `lean/SKEFTHawking/GrapheneBand/BernalBilayer.lean`: 4×4 Hamiltonian, `bilayer_quadratic_touching` (explicit-remainder expansion), `bilayer_field_gap : U ≠ 0 → gapped` with the gap's leading-order enclosure; strengthening + audit as above.

---

## Sequencing & parallelism

Wave 1 → Wave 2 → Wave 3 critical path; Wave 4 gated. **The whole phase is independent of 6EA/6EB/6EC and may run in a parallel worktree slot from day one.** Contention: `TopologicalBand/` is read-only here (Wave 3 instantiates, never edits) — if 6CA's QWZ spike is concurrently active, coordinate per the guardrail; root-module import lands at Wave 3 (single-writer).

## Phase Definition of Done

- [ ] `lake build` + ExtractDeps clean; zero sorry; kernel-pure; no new axioms.
- [ ] `validate.py` green; Inventory + Index refreshed with the `GrapheneBand/` family.
- [ ] Adversarial statement audit logged (special attention: expansion theorems must carry explicit remainders and validity balls; no O-notation smuggling).
- [ ] Roadmap status updated with dated shipped-declarations list; 6CA guardrail branch recorded.

## Open UNKNOWNs

- **UNKNOWN-1:** the cleanest Mathlib route for the explicit-remainder expansion of `f(K+q)` (`Complex.exp` Taylor bounds vs. `Real.cos/sin` two-variable expansion vs. a direct polynomial sandwich on the validity ball) — spike this first in Wave 2; it sets the constant `C`'s quality.
- **UNKNOWN-2:** Berry-phase statement form — discretized principal-branch arg sum over a stated loop (matches `FHSLatticeGauge` style, cheapest) vs. a continuum line-integral formulation (needs machinery the repo deliberately avoided). Default: discretized form, documented as such.
- **UNKNOWN-3 — RESOLVED by spike, 2026-07-29. Answer: `N = 4` (a 4×4 torus), and the tractability obstruction is NOT the one the guardrail predicted.**

  *Spike method:* numerically reconstructed `blochLatticeChern` exactly as `BlochFHS` computes it — Haldane `d`-vector in Wave-1 Bloch-phase coordinates, lower-band eigenvector `u ∝ (d₁ − i d₂, −(d₃ + ‖d‖))`, links `⟨u(k), u(k+μ)⟩/|·|`, `rawCurl` = the unreduced four-link sum, `latticeChern = Σ branchIndex(rawCurl)`. Scripts under the session scratchpad.

  **Finding 1 — `N = 3` is broken and must not be used.** It is the smallest grid at which the *principal-value* sum `ΣF/2π` reads `−1`, which is why it looks attractive, but its `latticeChern` is **0 even inside the topological window** (`m = 1`): one plaquette lands at `rawCurl = −π` **exactly**, i.e. on the branch cut (margin `0.0000` rad), and the four winding plaquettes cancel. `N = 3` also swings with `m` (0 at `m ≤ 2`, +1 at `3 ≤ m ≤ 5.19`), so it is not a stable witness anywhere.

  **Finding 2 — `N = 4` is clean, and the margin is enormous.**

  | grid | `m = 1` (topological) | `m = 6` (trivial) | nonzero-branch plaquettes | min margin to branch cut |
  |---|---|---|---|---|
  | 3×3 | **0** ✗ (wrong) | 0 | 4 | **0.0000 rad** ✗ |
  | **4×4** | **+1** ✓ | **0** ✓ | **1 of 16** | **1.6399 rad** ✓ |
  | 6×6 | +1 | 0 | 1 of 36 | 2.0888 rad |
  | 8×8 | +1 | 0 | 1 of 64 | 2.3789 rad |

  **Finding 3 (the architectural one) — exact `Complex.arg` evaluation is NOT required, so the QWZ obstruction does not bind here.** `BlochFHS.lean:24-26` warns that a nontrivial Chern value "requires the QWZ transcendental evaluation (`Complex.arg` of `sin/cos` at generic momenta)". That is true of *evaluating* plaquette phases — and the spike confirms they are genuinely transcendental (at 4×4, **zero** of the links are axis-valued; the distinct plaquette phases are generic reals, not multiples of π). **But `latticeChern` never needs them.** It is `Σ branchIndex(rawCurl)`, a sum of *integers*, and `Σ rawCurl = 0` by telescoping (`FiniteTorus.sum_forwardDiff_eq_zero`). So the whole invariant is carried by *which 2π-window* each `rawCurl` falls in — a **bounding** problem, not an evaluation problem, and at 4×4 there is `1.64` rad of slack on every window placement.

  **Consequent Wave-3 shape (supersedes the AC's implied design):** 15 plaquettes need `−π < rawCurl ≤ π` (⟹ `branchIndex = 0`) and exactly **one** needs `π < rawCurl ≤ 3π` (⟹ `branchIndex = 1`). Each `rawCurl` is a sum of four `Complex.arg`s of explicit algebraic numbers (at `N = 4` the momenta are `0, π/2, π, 3π/2`, so `cos`/`sin ∈ {0, ±1}` and the `d`-vectors are rational; only `‖d‖ = √·` is irrational), so the work is **rational enclosures of `arctan` at explicit algebraic points** in the repo's existing `NumericalBounds` style — not transcendental evaluation, and no `native_decide`.

  **Frozen AC constants:** grid `N₁ = N₂ = 4`; `t = 1`, `t₂ = 1`, `φ = π/2`; topological point `m = 1` ⟹ `blochLatticeChern = +1`; trivial point `m = 6` ⟹ `0` (window is `|m| < 3√3 ≈ 5.196`). Frame admissibility verified at both: `min‖d‖ = 1.4142` and `2.2361`, all overlaps nonzero.
- **UNKNOWN-4:** whether `TopologicalBand/` gains the QWZ witness before Wave 3 starts (sets the guardrail branch).
