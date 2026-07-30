# Phase 6ED — Kernel-Verified Graphene Electronic Structure: Honeycomb Tight-Binding, Dirac Cones, and the Haldane Chern Witness

**Status: IN PROGRESS — Waves 1 + 2 SHIPPED and REMEDIATED (fresh-context adversarial review, 2026-07-29), Wave 3 open, Wave 4 gated (authorized 2026-07-27).**

> **⚠️ REVIEW OUTCOME — read before consuming Waves 1–2.** A fresh-context adversarial review found two BLOCKERs and seven IMPORTANT findings against the first pass. Both BLOCKERs are remediated in-tree (see the Wave records below): (1) the claim that the Bloch-phase form "holds for **any** primitive-vector choice" was **false** and is now refuted by a kernel-checked theorem, with the true chart hypothesis shipped as `IsHoneycombChart`; (2) the wave's headline AC (`eigenvalues = ±|f|`) had been silently de-scoped to a norm identity and is now shipped as `honeycomb_band_secular`. Two AC items that had been dropped or declined on wrong grounds (`dispersion_linear_enclosure`, `fermiVelocity`) are shipped. Standing deviations are listed at the end of the Wave-2 record. Fourth phase of the `6E*` series (*verified device-physics metrology*). Independent of 6EA–6EC (parallelizable); feeds 6EE's material-parameter seams and closes the graphene gap in the repo's band-theory arc. See `Phase6EA_Roadmap.md` for the series framing.

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

**Done (AC / `/goal` condition).** ✅ **SHIPPED 2026-07-29; REMEDIATED 2026-07-29** after a fresh-context adversarial review found the wave's generality claim false and its headline AC item silently de-scoped. 0 sorry / 0 axiom / 0 `native_decide` / 0 `maxHeartbeats`, kernel-pure.
- [x] `lean/SKEFTHawking/GrapheneBand/Honeycomb.lean` builds 0-sorry, kernel-pure, with:
- [x] `structureFactor` in Bloch-phase coordinates, plus `honeycombD` and `honeycombBloch`.
  **⚠ CORRECTED — the original record's "holds for *any* primitive-vector choice" was FALSE.** `1 + e^{iθ₁} + e^{iθ₂}` is the honeycomb structure factor only for the pair `(δ₁−δ₃, δ₂−δ₃)` (equal length, 60° apart) and its six relabelings; it is **not** `GL₂(ℤ)`-invariant. Kernel-checked refutation: `structureFactor_zero_set_not_shear_invariant` — under the equally-primitive shear `(a₁, a₁+a₂)` the genuine Dirac point `K` gives `f = 3/2 + i√3/2 ≠ 0`, so `structureFactor_eq_zero_iff` would misidentify the Dirac set outright. **Shipped in its place:** `planeDot`, the named hypothesis `IsHoneycombChart` (equal length, 60°), `IsHoneycombNeighbours` (the 120° bond geometry) with canonical witnesses for both, `isHoneycombChart_of_neighbours` (**the honeycomb's geometry forces the chart** — this is the wave's real generality content), `chart_len_sq_of_neighbours` (`‖a₁‖² = 3·a_CC²`), the bridge `neighbourSum`/`neighbourSum_eq_structureFactor`/`norm_neighbourSum_eq` to the physical three-neighbour hopping sum, the admissible relabelings `structureFactor_norm_swap`/`_rotate`, and `not_isHoneycombChart_shear`;
- [x] `honeycomb_band_secular` — the AC's `eigenvalues = ±|f k|`, proved by **citing** `blochPauli_band_secular` as the AC instructed. **⚠ This was the de-scoped item:** the first pass shipped only `honeycomb_energy_eq` (`√(dNormSq d) = ‖f‖` — no matrix, no eigenvalue, no secular determinant) while three docstrings and this box asserted the eigenvalue content; `blochPauli_band_secular`/`_secular_det` were cited nowhere in `GrapheneBand/`. `honeycomb_energy_eq` is retained (unchanged signature) as the norm identity `honeycomb_band_secular` consumes; docstrings corrected;
- [x] the zero set in **both** forms: the quotient-free `structureFactor_eq_zero_iff` (three real equations — the working form) and `structureFactor_eq_zero_iff_dirac_branch`, **plus** `structureFactor_eq_zero_iff_orbit`, the AC's literal `f = 0 ↔ (θ ≡ K ∨ θ ≡ K') mod 2πℤ²`, now *proved* rather than declared equivalent-in-spirit (via `cos_sin_eq_iff_add_int_mul_two_pi`). `diracK'_ne_recip_translate_diracK` proves the two cones inequivalent — previously asserted only in a docstring;
- [x] `honeycomb_gapless_at_diracK`/`_diracK'`, `honeycomb_gapped_away`, and `honeycomb_gapped_away_of_phase` — the AC's contentful `k ∉ {K,K'} → 0 < gap`, taking the negation of the three phase equations (the `f θ ≠ 0` form alone is `norm_pos_iff` modulo `honeycomb_energy_eq`);
- [x] `structureFactorT`/`honeycombDT`/`honeycombT_energy_eq`/`_gamma`/`honeycombT_band_secular` — the hopping-parametrized family, so "in units of the hopping `t`" refers to something (`t` appeared nowhere before);
- [x] witnesses at Γ (`|f| = 3`) and M (`|f| = 1`), plus gaplessness at K (`0`); `honeycomb_band_dispersive` now carries all three pairwise comparisons (the missing `Γ ≠ K` conjunct left a two-valued band unexcluded);
- [x] preemptive-strengthening + post-wave audit. **Audit correction:** the original record credited `honeycombBloch_isHermitian` with making the `blochPauli` instantiation load-bearing. It did not — it was a pure forwarder (`blochPauli_isHermitian (honeycombD θ)`) whose statement carried zero honeycomb-specific information, the identity-wrapper pattern the checklist forbids. **Deleted**; `honeycomb_band_secular` is what makes the instantiation load-bearing.

**UNKNOWN-4 RESOLVED (Stage 2, 2026-07-29) — guardrail branch B applies.** The QWZ spike has **not** landed: `TopologicalBand/BlochFHS.lean:24-26` still reads *"a nontrivial frame-derived Chern value (C = ±1) requires the QWZ transcendental evaluation … and stays behind the separately-gated QWZ spike."* Therefore **Wave 3's Haldane witness becomes the first nontrivial concrete Chern frame in the repo, and the QWZ spike should later cite it.** Recorded per the coordination guardrail. Note the difficulty signal that same comment carries: the obstruction is the transcendental `Complex.arg` evaluation at generic momenta — Wave 3 must budget for it (UNKNOWN-3's grid-size spike is the mitigation).

## Wave 2 — Linear dispersion, Fermi velocity, and the Dirac mass

**Goal.** The first-order expansion at K: `|f(K+q)| = (3/2)·|q| + O(|q|²)` with explicit remainder bound (emergent linear dispersion; v_F as the model constant `(3/2)·t·a/ℏ` in the declared unit contract), and the gapped model `d₃ = m ≠ 0` with gap `2|m|` exactly. Verdict: reachable — Taylor-with-remainder on a trigonometric function of two variables, following the repo's enclosure discipline (explicit remainder constants, no O-notation in statements).

**Why.** Linear dispersion is the load-bearing property every downstream consumer cites (it is what makes graphene "Dirac"); the explicit-remainder form makes it a usable bound instead of folklore.

**Bricks.** Wave 1; `NumericalBounds` enclosure pattern; Mathlib `Complex.exp` Taylor bounds (`Complex.abs_exp_sub_one_sub_id_le`-family; exact route UNKNOWN-1).

**Done (AC / `/goal` condition).** ✅ **SHIPPED 2026-07-29; REMEDIATED 2026-07-29** after the same fresh-context review. Kernel-pure, 0 sorry / axiom / `native_decide` / `maxHeartbeats`.

**UNKNOWN-1 RESOLVED:** route = a **`Complex.exp` Taylor bound**, one application per hopping term, remainder constant **`C = 1`**. The two alternatives (two-variable `Real.cos`/`sin` expansion; direct polynomial sandwich) would both have rebuilt remainder control that already exists.
- [x] `lean/SKEFTHawking/GrapheneBand/DiracExpansion.lean` builds 0-sorry, kernel-pure, with:
- [x] `structureFactor_linear_expansion_global` — the expansion **with no validity ball**. **⚠ CORRECTED:** the first pass gated the bound on `|qᵢ| ≤ 1` (inherited from Mathlib's `Complex.norm_exp_sub_one_sub_id_le`) while *simultaneously* arguing in the file's own docstring that the ball was a lemma artifact and the bound globally true — and using that argument to decline an AC item. Having it both ways was the defect. `norm_exp_mul_I_sub_one_sub_id_le` now proves `‖e^{ix}−1−ix‖ ≤ x²` for every real `x` (mean-value inequality on `F(t) = e^{it}−1−it`, derivative norm `2|sin(t/2)| ≤ |t|`); `structureFactor_linear_expansion` is retained with its original signature as the corollary that discards the hypotheses;
- [x] **`fermiVelocity` SHIPPED** (reversing the Wave-2 decline, whose stated reason was wrong). A *parametrized* `fermiVelocity (t a_CC ℏ : ℝ) := 3·t·a_CC/(2ℏ)` bakes in no coordinate choice and no unit contract — the caller supplies all three. It is made load-bearing by the frame bridge, which is the actual physics the decline gave up: `quadForm_of_chart` (`q₁²−q₁q₂+q₂² = (3/4)‖a₁‖²‖p‖²` for an `IsHoneycombChart` pair — **"isotropic in the physical frame" is now a theorem**, and visibly chart-specific: a 120° pair sweeps a factor 3), `dispersion_slope_of_neighbours` (`‖L‖ = (3/2)·a_CC·‖p‖`), `dispersion_slope_eq_hbar_fermiVelocity` (`E = ℏ·v_F·‖p‖`). **The real obstruction the decline should have named** — the model carried no hopping parameter at all — is fixed by Wave 1's `structureFactorT` family.
  **⚠ UNITS CORRECTION:** the original record wrote "`(3/2)a` against a lattice constant `a`". Wrong by `√3`: the `3/2` multiplies the **nearest-neighbour distance** `a_CC`; against the lattice constant the slope is `(√3/2)·a_lattice` (`chart_len_sq_of_neighbours`: `‖a₁‖ = √3·a_CC`). D11 will lift this sentence;
- [x] `dispersion_linear_enclosure` — the AC's second item, **which the first pass dropped with no deviation recorded at all**: the two-sided rational enclosure `7/10 − ‖q‖ ≤ E(K+q)/‖q‖ ≤ 63/50 + ‖q‖`, from the anisotropy band `½‖q‖² ≤ q₁²−q₁q₂+q₂² ≤ 3⁄2‖q‖²` plus the global remainder. This is the statement that actually asserts *linearity with bounded slope*, as opposed to bounding a difference;
- [x] `gapped_dirac_gap_eq` — the gap at the Dirac point is **exactly** `2|m|`, via Wave 1's `honeycomb_gapless_at_diracK`. Now flanked by `gapped_gap_ge_dirac` + `gapped_gap_eq_dirac_iff`, so it reports the model's **minimum** gap (and its exact minimizer set) rather than one evaluation, and by `gappedHoneycombBloch` + `gappedHoneycomb_band_secular` (the gapped model had no `blochPauli` instance or spectral statement at all);
- [x] `gapped_gap_strictMono_in_mass` + `gapped_gapless_iff`, both at **general `θ`**. **⚠ CORRECTED:** the original `gap_vs_mass_strictMono` and `gapped_dirac_gapless_iff_massless` were stated only at `K`, where — after `gapped_dirac_gap_eq` — they reduce to multiplication by 2 and `abs_eq_zero` behind a factor 2 (the P3 pattern). Both are retained, reproved as one-line **specializations** of the general-`θ` theorems, which carry the content;
- [x] non-vacuity **stated where the theorem applies**: `dispersion_linear_not_exact_in_ball` at `q = (1,1)` (inside `|qᵢ| ≤ 1`; `‖f‖ = 2sin(1/2) ≠ 1 = ‖L‖`). **⚠ CORRECTED:** the original `dispersion_linear_not_exact` sits at `|qᵢ| = 2π/3 ≈ 2.09`, *outside* the ball of the theorem it was de-trivializing, so it said nothing where that theorem applied; it is retained as the companion witness for the global form. The AC's "bound must FAIL outside the ball" remains genuinely unsatisfiable — there is now no outside — and that is recorded as a **standing deviation**, not a discharged item;
- [x] preemptive-strengthening + post-wave audit; deletions/renames recorded above.

### Standing deviations (Waves 1–2, after remediation)

1. **AC "expansion bound must FAIL detectably outside the validity ball" — UNSATISFIABLE, not shipped.** The bound is globally true (`norm_exp_mul_I_sub_one_sub_id_le`), so no such witness exists. Replaced by in-ball and global non-exactness witnesses. This is now backed by a theorem rather than by prose.
2. **`honeycombBloch_isHermitian` deleted, not replaced.** Hermiticity of the honeycomb Hamiltonian follows from `blochPauli_isHermitian (honeycombD θ)` at the call site; a named forwarder added nothing.

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
