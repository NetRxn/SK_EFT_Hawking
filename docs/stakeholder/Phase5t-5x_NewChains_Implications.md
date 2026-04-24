# Phase 5t/5w/5x: Three New Proof Chains — Implications

*Last updated: 2026-04-24-1515.*

## What We Achieved

The project's original six proof chains (dissipative Hawking radiation, the generation constraint, Onsager-through-TQC, the chirality wall, ADW emergent gravity, and the vestigial-gravity Monte Carlo) are now joined by three more: a formally verified geometric quantum gate, a solid-state experimental platform for analog Hawking radiation, and a dark-sector phenomenology program. These sit alongside the original six as **peers, not extensions** — each addresses a physical domain that the original chains did not touch, and each stands or falls on its own evidence. Together, chains 7–9 add one new quantum-information result, one new experimental frontier, and one new observational program to the unified codebase.

---

## Chain 7 — Fermi-Hubbard Geometric Quantum Gate (Phase 5t)

### What's verified

`lean/SKEFTHawking/FermiHubbardDimer.lean` formalizes the entire finite-dimensional core of the doublon-gate mechanism demonstrated by Kiefer *et al.* (arXiv:2507.22112, Nature 2026), at 143 theorems and zero sorry. The 3×3 singlet-sector Hamiltonian is diagonalized in closed form; the chiral operator `Γ = diag(+1, -1, -1)` anticommutes with `H(t, Δ, 0)` and conjugates eigenvalues (BDI class); the zero-mode space is proved to be exactly `ℝ · darkVec` when `(t, Δ) ≠ (0, 0)`; and the geometric SWAP is constructed as a real Householder reflection `U_SWAP = I − (2/gap²)·darkVec ⊗ darkVec`, with unitarity discharged one-line via `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`. The minimal Berry-phase theorem `geometric_phase_minus_one_on_pi_loop` bundles three facts: the dark state acquires a `−1` sign under a π-sweep of the mixing angle (W8a), the Hamiltonian expectation value vanishes pointwise along the zero-energy path under the kernel-angle condition (W8d), and therefore the accumulated phase is purely geometric and equals `−1`. The 6×6 symmetry-adapted lift `U_SWAP_adapted` is registered as a structural unitary via `Matrix.fromBlocks`. A Python mirror (`src/fermi_hubbard/dimer.py`, `src/experimental/doublon_gate.py`) and one figure (`fig_doublon_gate_spectrum`) cross-verify every closed form against numpy `eigh`.

### Why it matters

This is the **first formally verified symmetry-protected (non-topological) two-qubit gate** in any proof assistant (Phase 5t, per README). The protection here is chiral symmetry plus fermionic exchange antisymmetry, not braiding — which makes it **complementary** to the Fibonacci-braiding universality proof in Chain 3 (protection via topological order). Quantum-information hardware platforms currently using symmetry-protected gates (neutral atoms, Fermi-Hubbard simulators) gain a machine-checked algebraic core for the gate mechanism they demonstrate experimentally, separate from the anyon-based roadmap that Microsoft, Google, and IBM are pursuing. It also demonstrates that the project's verification pipeline handles finite-dimensional hardware-facing gate proofs on a roughly one-session-per-wave cadence — a useful methodological data point for Paper 15.

### What's next

- **W8 Target B** — full Aharonov–Anandan / Berry-connection formalism over a parameterized finite-dimensional eigenbundle, including adiabatic following and holonomy integrals. Explicitly deferred to Phase 6 per the W8 decision gate.
- Paper 18 `papers/paper18_doublon_gate/paper_draft.tex` is drafted and has cleared all P1 claims-reviewer, figure-reviewer, and adversarial-reviewer findings (session-9 FINAL+++ memory).

---

## Chain 8 — Graphene Dirac-Fluid Platform (Phase 5w)

### What's verified

Five new Lean modules carry the SK-EFT pipeline from 1+1D BEC phonons to the 2+1D graphene Dirac fluid, all at zero sorry. `DiracFluidMetric.lean` (9 theorems) constructs the 3×3 acoustic metric, proves Lorentzian signature, and shows block-diagonalization of the (t, x) block for quasi-1D flow — which is what lets the existing 1+1D WKB machinery apply directly (92% theorem reuse from `WKBAnalysis.lean`, `WKBConnection.lean`, `HawkingUniversality.lean`, `AcousticMetric.lean`). `GrapheneHawking.lean` (7 theorems) packages the dispersive-correction bound, `T_eff > 0`, and the subluminal-robustness claim for the Dean bilayer-nozzle geometry. `DiracFluidSK.lean` (9 theorems) carries the 2+1D SK-EFT transport-counting: conformal bulk viscosity ζ = 0, two first-order transport coefficients, a KSS-bound lemma, and the EFT perturbativity envelope. `GrapheneNoiseFormula.lean` (8 theorems) records the corrected current-noise formula `ΔS_I(ω) = 2ℏω σ_Q Γ(ω) n_H(ω)` derived from Keldysh FDT + Landauer–Büttiker. `QuasiOneDReduction.lean` extensions (Wave 10c) verify the greybody factor Γ₀ ≈ 0.9994 and bound the quasi-1D reduction error at ≤ 1.8%. Predicted Hawking temperature for the Dean bilayer nozzle: **T_H ≈ 2.4 K** — nine orders of magnitude above BEC. Dissipative correction δ_diss ~ 10⁻¹³ is honestly reported as **negligible** (11 orders below the dispersive correction δ_disp ≈ −3%); the SK-EFT framework's value here is the systematic transport counting and FDR-derived noise formula, not a quantitative shift in T_H.

### Why it matters

The BEC and polariton experimental tracks are now joined by a solid-state one. The Dean group at Columbia (Geurs *et al.* 2509.16321, Sept 2025) realized the **first electronic sonic horizon** in bilayer graphene; the Kim group (Harvard) has the noise thermometer required to read the predicted current-noise excess. Neither group has attempted a Hawking-radiation detection yet. Critically, co-author Andrew Lucas (CU Boulder) has deep SK-EFT engagement (co-authored the original CGL papers with Glorioso). This is the **first graphene-Dirac-fluid analog-Hawking formalization with a Keldysh + Landauer–Büttiker noise formula** in any proof assistant (Phase 5w, per README). T_H in the 1–3 K range plus a realized horizon moves analog Hawking radiation from "technically plausible" to "detector-ready" in a solid-state setting.

### What's next

- Experimental-collaboration outreach: Lucas/Dean (Columbia bilayer nozzle), Kim (Harvard noise thermometer). The noise formula is now derived; collaboration conversations can proceed on the experimentalist-specific device geometry.
- Principal remaining device-level uncertainty is the **greybody factor Γ(ω)** — the framework derivation is complete but the sample-specific transverse transmission coefficient sets the final detection bandwidth.
- Paper 16a `papers/paper16_graphene_sk_eft/paper_draft.tex` is drafted and documents the platform end-to-end.

---

## Chain 9 — Dark-Sector Connections (Phase 5x)

### Sub-chain 9A — Dark-matter candidate classification

`HiddenSectorClassification.lean` (9 theorems) enumerates ℤ₁₆-anomaly-compatible SM-singlet Weyl hidden sectors (first verifier-backed DM-candidate constraint from formal methods; T1–T12). `HiddenSectorMixedCharge.lean` extends to the Wan–Wang mixed-charge channel via a joint U(1)_X³ + U(1)_X × gravity² cancellation conditional on a tracked ℤ₁₆ hypothesis. `FangGuTorsionDM.lean` (10 theorems) proves the kinematic obstruction `traceless T_μν → w = 1/3`, ruling out Fang–Gu torsion DM at the CDM level (`fg_cdm_obstruction`). `FractonDarkMatter.lean` (25 theorems) certifies fracton DM is **viable in the gapless p-wave dipole superfluid phase** at MeV–TeV, carrying forward `FractonFormulas.dipole_k4_damping` and `FractonNonAbelian.no_fracton_is_ym_compatible` to force the SM-singlet property. `SFDMMergerForecast.lean` (30 theorems) is Paper 17's "money plot": a Berezhiani–Khoury-fiducial sound-speed table, Rankine–Hugoniot density-jump closed form for γ = 2, Mach-number classifier for Bullet/El Gordo/Pandora/A520/MACS J0025, stacked-√N S/N scaling, and five decidable numerical S/N witnesses. The forecast: **Euclid × Roman stacked ≥ 30 canonical mergers reaches 3.5–5.7σ, with first 3σ detectable around 2028** — this is a *forecast-level* prediction, not an established detection. `DarkSectorSynthesis.lean` (22 theorems) ships seven cross-connection theorems and pins the Paper 17 empirical-hook ranking (cluster mergers > fracton direct detection > hidden-sector direct detection) to Lean-decidable ground.

### Sub-chain 9B — Structural obstruction on emergent dark energy

The structural obstruction theorems (Gibbs–Duhem emergent-vacuum obstruction locking `w_vac = −1`; Klinkhamer–Volovik q-theory no-go across all four tested realizations; four-factor orthogonality; the first closed-form vestigial-gravity EOS `w_vest(τ) = (1 − τ²)/(5τ² − 1)` with `c_s²(τ) = −(1 − τ²)/(3 − 5τ²)`) were shipped as Phase 5y. They are not restated here. See `docs/stakeholder/Phase5y_Closure_Summary.md` for the closure memo and `docs/stakeholder/Phase5y_Impact_on_5x.md` for the 5x-specific cross-reference. In brief: for Phase 5x's predictive-scope map, the obstruction sub-chain rules out the tested emergent-vacuum DE realizations under DESI DR2, leaving Layer-3 predictive-physics scope as SM + GR plus the Phase 5x DM candidates.

### Why it matters

The dark-sector chain connects the project's machine-verified infrastructure (ℤ₁₆ anomaly framework from Chain 2, ADW tetrad condensation from Chain 5, fracton formalization, vestigial gravity) to observable phenomenology under a specific cosmological context: **DESI DR2**, the **first JWST-plus-Euclid era** of cluster-merger weak lensing, and the **2025–2028 direct-detection landscape**. The empirical-hook ordering (SFDM cluster mergers > fracton direct detection > hidden-sector direct detection) is not an editorial preference — it is grounded in Lean-decidable theorems (`empirical_hook_ranking_strict`, `merger_outranks_direct_detection`, `merger_is_top_ranked`). This is the first time a dark-sector survey program has been ranked on machine-checked structural grounds rather than phenomenological intuition.

### What's next

- The vestigial-relic sub-thread (DM from the metric-without-tetrad phase) is **gated on the L ≥ 8 RHMC Monte Carlo (Chain 6) resolving the phase-transition order.** Until that lands, the relic-abundance calculation is blocked.
- **DESI DR3 (2026–2027)** is the decisive external milestone for the emergent-vacuum obstruction's DE implications. A strengthening away from `(w₀, wₐ) = (−1, 0)` would confirm the no-go; a retreat toward `(−1, 0)` would narrow but not rule out the KV frozen-plateau reframe.
- Paper 17 `papers/paper17_dark_sector/paper_draft.tex` is drafted and integrates both sub-chains.

---

## Cross-chain synthesis

These three chains emerged from the same verification infrastructure that powered the original six: the ℤ₁₆ anomaly framework (Chain 2) underwrites the Phase 5x hidden-sector enumeration; the ADW tetrad machinery (Chain 5) enters the cosmological-constant and vestigial-relic sub-threads; the 1+1D WKB Hawking machinery (Chain 1) lifts to 2+1D graphene via a block-diagonalization theorem instead of a rewrite; the finite-dimensional Hamiltonian infrastructure built for BdG and gapped-interface work (Phase 5a/5s) carries directly into the Fermi-Hubbard doublon gate (Phase 5t). That 92% theorem-reuse number for the graphene extension is the clearest quantitative evidence that the verification pipeline generalizes beyond the scope it was built for. The three new chains validate the infrastructure, and the infrastructure, in turn, kept the three new chains honest — e.g., the Phase 5x forecast explicitly labels SFDM merger detection as forecast-level rather than confirmed, because the Lean machinery distinguishes decidable S/N witnesses from established measurements.
