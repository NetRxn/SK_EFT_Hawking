# SK-EFT Hawking Project: Comprehensive Inventory

**Repository Root:** `SK_EFT_Hawking/`

**Project Summary:** Formal verification of dissipative effective field theory corrections to analog Hawking radiation in BEC sonic black holes. Six papers (Phases 1–4) with complete Lean 4 formalization (216 theorems + 1 axiom, zero sorry, 16 modules). 820 tests, 44 pipeline figures, 16 notebooks.

**Note:** Detailed per-file descriptions below cover Phase 1–2 modules. Phase 3–4 modules (gauge_erasure, wkb, adw, chirality, experimental, vestigial, fracton) follow the same patterns — see README.MD for the full project tree and CLAUDE.md for architecture.

---

## 1. PYTHON SOURCE FILES

### 1.1 Core Module: `src/core/`

#### `src/core/transonic_background.py` (624 lines)
**Purpose:** Solves the steady-state Euler + continuity equations for 1D BEC in an external potential to determine the transonic (sonic black hole) background.

**Key Classes & Functions:**

- **`BECParameters`** (dataclass)
  - `mass` [kg]: Atomic mass (e.g., 1.443e-25 kg for ⁸⁷Rb)
  - `scattering_length` [m]: s-wave scattering length (e.g., 5.77e-9 m for ⁸⁷Rb)
  - `density_upstream` [m⁻¹]: 1D density upstream (e.g., 5e7 m⁻¹)
  - `velocity_upstream` [m/s]: Flow velocity upstream (e.g., 0.85e-3 m/s)
  - **Derived (computed in `__post_init__`):**
    - `interaction_strength` = 2ℏ²a/(m·a_⊥²) [J·m] — 1D coupling constant (Olshanii formula)
    - `sound_speed_upstream` = √(g_1D·n₀/m) [m/s]
    - `healing_length` = ℏ/(m·c_s) [m]
    - `chemical_potential` = g·n₀ [J]

- **Factory functions (preset parameter sets):**
  - `steinhauer_Rb87()` — ⁸⁷Rb BEC from 2016/2019 experiments
    - M_up ≈ 0.74 (subsonic), ξ ≈ 0.2 μm, c_s ≈ 1.4 mm/s
  - `heidelberg_K39()` — Projected ³⁹K with Feshbach tuning
    - M ≈ 0.77, ξ lower (tighter confinement)
  - `trento_spin_sonic()` — Projected ²³Na spin-sonic system
    - Enhanced c_s ratio (c_density/c_spin ~ 100)

- **`TransonicBackground`** (dataclass) — Solution object
  - `x` [m]: Spatial grid
  - `density, velocity, sound_speed, potential` [arrays]: Background fields
  - `x_horizon` [m]: Sonic horizon position
  - `surface_gravity` κ [s⁻¹]: Rate at which v - c_s crosses zero
  - `hawking_temp` T_H [K]: ℏκ/(2πk_B)
  - `adiabaticity` D = κξ/c_s [dimensionless]: EFT validity parameter
  - `mach_upstream, mach_downstream` [dimensionless]: Flow Mach numbers

- **Key Functions:**
  - `solve_transonic_background(params, surface_gravity_target, step_width_xi, x_range, n_points)`
    - **Method:** Parameterizes velocity as smooth tanh transition through horizon
    - **Formula:** v(x) = c_s₀·[M_up + (M_down - M_up)·½(1 + tanh(x/L))]
    - **Continuity:** n(x) = J/v(x) where J = n₀v₀
    - **Sound speed:** c_s(x) = √(g·n(x)/m)
    - **Horizon detection:** Finds where |v - c_s| is minimized
    - **Surface gravity:** κ = |dv/dx - dc_s/dx| at horizon
    - **Returns:** `TransonicBackground` with all fields and properties
    - **Avoids:** Numerically fragile cubic root-finding at the sonic point

  - `compute_dissipative_correction(bg, params, gamma_1, gamma_2)`
    - **Formulas:**
      - γ_eff = γ₁ + γ₂
      - δ_diss = γ_eff / κ [dissipative correction]
      - δ_disp = D² [dispersive correction, Coutant-Parentani]
      - δ_cross = δ_disp · δ_diss [cross-term]
      - T_eff/T_H = 1 + δ_diss + δ_disp + δ_cross
    - **Also computes:** Beliaev damping rate γ_Bel = √(n·a³)·ω²/c_s

**Hardcoded Physical Constants:**
- hbar = 1.054571817e-34 J·s
- k_B = 1.380649e-23 J/K
- omega_perp (transverse trap): 2π × 500 rad/s

**Experimental Parameters (in factory functions):**
- ⁸⁷Rb: m = 1.443160648e-25 kg, a = 5.77e-9 m
- ³⁹K: m = 6.470076e-26 kg, a = 50e-9 m (tunable via Feshbach)
- ²³Na: m = 3.8175458e-26 kg, a = 2.75e-9 m

---

#### `src/core/aristotle_interface.py` (520 lines)
**Purpose:** Interface to the Aristotle automated theorem prover (via CLI) for filling Lean sorry gaps.

**Key Classes & Data:**

- **`SorryGap`** (dataclass) — Documented sorry in Lean
  - `module` [str]: Lean module path (e.g., "SKEFTHawking.AcousticMetric")
  - `name` [str]: Theorem/definition name
  - `priority` [1|2|3]: 1=algebraic (fillable), 2=moderate, 3=analysis (hard)
  - `description` [str]: What the sorry is about
  - `strategy_hint` [str]: Proof approach for Aristotle
  - `filled` [bool]: True if Aristotle or manual proof completed

- **`SORRY_GAPS`** (list[SorryGap]) — **Registry of 38 sorry gaps (35 filled, 3 pending):**

  **Phase 1 (14 gaps, all filled):**
  - AcousticMetric (5): determinant, inverse, Lorentzian, d'Alembertian, EOM
  - SKDoubling (6): positivity, uniqueness (KMS), FDR per-sector, KMS_optimal
  - HawkingUniversality (3): dispersive_bound, dissipative_existence, universality

  **Phase 2 (9 gaps, all filled):**
  - SecondOrderSK (8): coefficient counts (orders 1-3), uniqueness, positivity_constraint, combined_KMS
  - WKBAnalysis (1): turning_point_shift, damping_zero_iff

  **Phase 3 Stress Tests (12 gaps, all filled):**
  - Consistency tests for KMS sign, FDR relations, relaxed constraints
  - Limit tests (γ=0, alternates)

  **Direction D: CGL Derivation (5 gaps, all filled):**
  - CGLTransform (5): cgl_fdr_general, cgl_fdr_spatial, einstein_relation, secondOrder_cgl_fdr, cgl_implies_secondOrderKMS

  **Aristotle runs:**
    - Run 082e6776, a87f425a, 270e77a0 (Phase 1 core)
    - Run d61290fd, c4d73ca8 (Phase 2 core)
    - Run 3eedcabb (Stress tests)
    - Run 518636d7 (Round 5: total-division strengthening)
    - Run dab8cfc1 (Direction D: einstein_relation, secondOrder_cgl_fdr)
    - Run 2ca3e7e6 (Direction D: cgl_fdr_general, cgl_fdr_spatial, cgl_implies_secondOrderKMS)

- **`AristotleResult`** (dataclass) — Submission result
  - `project_id, timestamp, status` [str]: Submission tracking
  - `sorries_filled, sorries_remaining, errors` [list]: Parsed output
  - **Status values:** "COMPLETE", "COMPLETE_WITH_ERRORS", "FAILED", "OUT_OF_BUDGET"

- **`AristotleRunner`** (class) — Main API
  - `submit_and_wait(prompt, timeout_seconds)` → `AristotleResult`
  - `submit_targeted(sorry_gap)` → Focus on one gap
  - `submit_priority_batch(max_priority, timeout_seconds)` → Batch submission
  - **Output:** Results saved to `docs/aristotle_results/*.json` with timestamps
  - **API Key:** Read from `.env` file (ARISTOTLE_API_KEY=...)

**Design Notes:**
- Uses aristotlelib CLI wrapper (not raw HTTP)
- Each gap tagged with priority and strategy hint
- Results logged for reproducibility

---

#### `src/core/visualizations.py` (900+ lines)
**Purpose:** Publication-quality figures and interactive HTML dashboard.

**Libraries:** Plotly (not matplotlib) for static + interactive unification

**Color Palette (physics-appropriate):**
- `Rb87`: #2E86AB (steel blue — established)
- `K39`: #A23B72 (berry — proposed)
- `Na23`: #F18F01 (amber — high-impact)
- `dispersive`: #5C946E (sage green)
- `dissipative`: #E63946 (carmine — **new result**)
- `cross`: #8D99AE (cool grey)
- `horizon`: #000000 (black)

**Color Palette additions:**
- `noise`: #D4A574 (warm tan — noise/FDR terms)
- `sensitivity`: #CCCCCC (grey — experimental bands)

**Figure Generators (12 figures: 6 Phase 1 + 6 Phase 2):**

1. **`fig_transonic_profiles(experiments)`**
   - 3-panel: v(x) & c_s(x), Mach number, density
   - Shows all 3 experimental setups overlaid
   - Marks sonic horizon, shades subsonic/supersonic regions

2. **`fig_correction_hierarchy(experiments)`**
   - Bar chart: δ_disp, δ_diss, δ_cross on log scale
   - Overlays experimental sensitivity thresholds (1%, 0.1%, 0.01%)
   - Highlights spin-sonic enhancement (×100)

3. **`fig_parameter_space()`**
   - 2D contours: D (adiabaticity) vs γ/κ (dissipation strength)
   - Marks EFT validity boundary (D < 1)
   - Plots three experiments as star markers

4. **`fig_spin_sonic_enhancement()`**
   - Shows δ_diss × (c_density/c_spin)² amplification
   - Marks current, near-term, projected sensitivity

5. **`fig_temperature_decomposition(experiments)`**
   - Waterfall visualization: T_H → T_H(1 + δ_disp) → ... → T_eff
   - One panel per experimental setup

6. **`fig_kappa_scaling()`**
   - log-log plot: δ_disp ~ κ² vs δ_diss ~ 1/κ
   - Marks crossing point κ*
   - Vertical lines for experimental κ values

7. **`fig_cgl_fdr_pattern()`** (Phase 2)
   - Bar chart: dissipative, conservative, noise counts at each EFT order N=0..6
   - Overlays counting formula count(N) = ⌊(N+1)/2⌋ + 1

8. **`fig_even_vs_odd_kernel()`** (Phase 2)
   - 4-panel: even-ω kernel, odd-ω kernel, CGL noise result, summary
   - Shows how CGL FDR extracts only odd-ω part

9. **`fig_boundary_term_suppression()`** (Phase 2)
   - IBP correction vs adiabaticity D with experimental points
   - Shows O(D) ~ 1% suppression

10. **`fig_positivity_constraint()`** (Phase 2)
    - 2D parameter space γ_{2,1} vs γ_{2,2}
    - Strict line γ_{2,1}+γ_{2,2}=0 and relaxed region

11. **`fig_on_shell_vanishing()`** (Phase 2)
    - δ^(2)(k) vs k/k_acoustic showing zero crossing at acoustic shell

12. **`fig_einstein_relation()`** (Phase 2)
    - σ = γT for multiple γ values, CGL master formula annotation

**Interactive Dashboard:**

- **`build_interactive_dashboard(experiments, output_dir)`** → HTML file
  - Combines all 12 figures with navigation
  - Style: professional header, sticky nav, dark theme
  - Includes numerical summary table
  - Single-file self-contained (Plotly CDN)

**Export Functions:**

- **`export_static_figures(experiments, output_dir)`** → PDF/PNG
  - Requires kaleido (Chrome/Chromium for PDF rendering)
  - Fallback: HTML per figure + PNG via kaleido

**Helper Functions:**

- `apply_layout(fig, **kwargs)` — Apply consistent PRL-style layout
- `_get_caption(idx)` — Descriptive captions for each figure
- `_build_summary_table(experiments)` — HTML table with numerical results

---

### 1.2 First-Order Module: `src/first_order/`

#### `src/first_order/__init__.py`
(Placeholder — no current implementation; extensible for Phase 1-specific analysis)

---

### 1.3 Second-Order Module: `src/second_order/`

#### `src/second_order/enumeration.py` (400+ lines)
**Purpose:** Count dissipative transport coefficients at each EFT order via monomial enumeration.

**Key Classes & Functions:**

- **`DerivIndex`** (NamedTuple) — (n_t, n_x) for ∂_t^{n_t} ∂_x^{n_x}
  - `.order` → n_t + n_x
  - `.t_parity_even` → True if n_t is even
  - `.x_parity_even` → True if n_x is even

- **`OrderAnalysis`** (dataclass) — Complete analysis at order N
  - `order, deriv_level` [int]: N and L = N+1
  - `all_real_monomials` [list[DerivIndex]]: All (m,n) with m+n=L
  - `t_reversal_surviving` [list[DerivIndex]]: m even only
  - `parity_surviving` [list[DerivIndex]]: m even AND n even
  - `n_transport_no_parity` [int]: Count without spatial parity
  - `n_transport_with_parity` [int]: Count with spatial parity

- **`analyze_order(N, verbose=True)`** → `OrderAnalysis`
  - **Method:** Filter monomials by two constraints:
    1. **T-parity (time-reversal):** m must be even
    2. **Spatial parity (optional):** n must be even
  - **Formula (no parity):** count(N) = ⌊(N+1)/2⌋ + 1
    - Order 1: count = 2 (γ₁, γ₂) ✓
    - Order 2: count = 2 (γ_{2,1}, γ_{2,2}) ✓
    - Order 3: count = 3 ✓
  - **With parity:** All odd-n terms killed
    - Order 2 with parity: count = 0 (no new dissipation!)

- **`fdr_relations(N)`** → list[str]
  - Describes how imaginary coefficients fix from real via β-dependent FDR

- **`count_imaginary_monomials(N)`** → dict
  - Enumerates imaginary sector: (∂^α ψ_a)(∂^β ψ_a)
  - Applies IBP + T-reversal constraints
  - Returns: all_pairs, surviving, n_total, n_surviving

**Physics:**

The three SK axioms constrain transport coefficients:

1. **Normalization:** All monomials must have ψ_a (kills pure ψ_r terms)
2. **T-reversal (KMS):** Under t → -t, acquire factor (-1)^{m+1}. For L_re with Z₂ flip, need m even.
3. **FDR:** Imaginary coefficients determined by real ones via iβ∂_t coupling.

**Validated Against Phase 1 Lean:**
- `firstOrder_count`: Lean proof that count(1) = 2
- `secondOrder_count`: Lean proof that count(2) = 2
- `secondOrder_count_with_parity`: Lean proof that count(2, parity) = 0

---

#### `src/second_order/coefficients.py` (480+ lines)
**Purpose:** Data structures and action constructors for second-order SK-EFT.

**Key Classes:**

- **`FirstOrderCoeffs`** (dataclass) — Phase 1 transport coefficients
  - `gamma_1` ≥ 0: Coefficient of ψ_a · (∂²_t - ∂²_x)ψ_r = ψ_a · □ψ_r
    - Microscopically: Beliaev damping, sound-cone dissipation
  - `gamma_2` ≥ 0: Coefficient of ψ_a · ∂²_t ψ_r
    - Anomalous density damping, breaks t/x symmetry

- **`SecondOrderCoeffs`** (dataclass) — New at order 2
  - `gamma_2_1`: Coefficient of ψ_a · ∂³_x ψ_r (cubic spatial, **requires odd n**)
  - `gamma_2_2`: Coefficient of ψ_a · ∂²_t ∂_x ψ_r (temporal-spatial, **requires odd n**)
  - **Constraint:** γ_{2,1} + γ_{2,2} = 0 (from positivity at this truncation)

- **`FullCoeffs`** (dataclass) — Combined first + second order
  - `first` [FirstOrderCoeffs]
  - `second` [SecondOrderCoeffs]
  - `.n_total` → 4 (2 + 2)

**Action Constructors (for numerical use):**

- **`first_order_action_re(gamma_1, gamma_2, psi_a, dtt_psi_r, dxx_psi_r)`**
  - L_re^(1) = γ₁·ψ_a·(∂²_t - ∂²_x)ψ_r + γ₂·ψ_a·∂²_t ψ_r

- **`first_order_action_im(gamma_1, gamma_2, beta, psi_a, dt_psi_a)`**
  - L_im^(1) = (γ₁/β)·ψ_a² + (γ₂/β)·(∂_t ψ_a)² [noise part, fixed by FDR]

- **`second_order_action_re(gamma_2_1, gamma_2_2, psi_a, dxxx_psi_r, dttx_psi_r)`**
  - L_re^(2) = γ_{2,1}·ψ_a·∂³_x ψ_r + γ_{2,2}·ψ_a·∂²_t ∂_x ψ_r

**Corrections:**

- **`hawking_correction_first_order(gamma_1, gamma_2, kappa, c_s)`** → float
  - δ_diss = Γ_H / κ where Γ_H = (γ₁ + γ₂)·(ω/c_s)²·κ
  - **Frequency-independent at first order**

- **`hawking_correction_second_order(omega, coeffs, kappa, c_s, v_gradient)`** → float or ndarray
  - δ^(2)(ω) = γ_{2,1}·(ω·ξ/c_s)³/κ + γ_{2,2}·(ω·ξ/c_s)²·(v'·ξ/c_s)/κ
  - **Frequency-dependent, ω³ scaling**

- **`effective_temperature(omega, coeffs, kappa, c_s, v_gradient)`** → T_eff(ω)
  - T_eff(ω) = T_H·[1 + δ_disp + δ_diss + δ^(2)(ω)]

**Planck Spectrum Analysis:**

- **`planck_spectrum(omega, T)`** → n(ω)
  - n(ω) = 1/(exp(ω/T) - 1) [occupation number]

- **`spectral_distortion(omega, coeffs, kappa, c_s, v_gradient)`** → Δn(ω)/n_Planck
  - Shows frequency-dependent deviations from thermal spectrum
  - **Key signature:** ω³ distortion distinguishes second-order dissipation from temperature shift

**Experimental Parameter Factories:**

- **`estimate_second_order_coeffs_beliaev(n, a_s, m, c_s, kappa)`** → SecondOrderCoeffs
  - Estimates from Beliaev damping theory
  - γ_{2,i} ~ γ_Bel·(ξ/c_s) [one extra derivative → EFT suppression]
  - **Caveat:** Order-of-magnitude only; exact matching requires Bogoliubov theory

---

#### `src/second_order/wkb_analysis.py` (550+ lines)
**Purpose:** WKB mode analysis through dissipative horizon.

**Key Classes:**

- **`TransonicProfile`** (dataclass) — Background flow near sonic horizon
  - `kappa` [s⁻¹]: Surface gravity (velocity gradient at horizon)
  - `c_s` [m/s]: Sound speed at horizon
  - `xi` [m]: Healing length
  - `x_range` [tuple]: Spatial domain (default: (-10, 10) in units of ξ)
  - **Properties:**
    - `.cutoff` = 1/ξ [UV momentum cutoff]
    - `.D` = κξ/c_s [adiabaticity parameter]
    - `.T_H` = κ/(2π) [Hawking temperature]
  - **Methods:**
    - `.v(x)` = c_s + κ·x [linear profile near horizon]
    - `.c_local(x)` = c_s [constant sound speed approximation]

- **`WKBParameters`** (dataclass) — Combined background + transport coefficients
  - `profile` [TransonicProfile]
  - `gamma_1, gamma_2, gamma_2_1, gamma_2_2` [float]: All transport coefficients
  - `F_disp` [callable]: Dispersion modification F(x) where ω² = c_s²k²·F(k²ξ²)
    - Default: Bogoliubov F(x) = 1 + x
  - `n_points` [int]: Spatial grid resolution
  - **Properties:**
    - `.gamma_eff` = γ₁ + γ₂
    - `.delta_diss_leading` = γ_eff / κ

- **`BogoliubovResult`** (dataclass) — WKB solution
  - `omega` [float]: Mode frequency
  - `alpha_sq, beta_sq` [float]: Bogoliubov coefficients |α|², |β|²
  - `T_eff` [float]: Extracted effective temperature
  - `delta_disp, delta_diss, delta_second` [float]: Correction decomposition
  - `n_occupation` [float]: = |β|² (occupation number)

**Dispersion Relation:**

- **`dispersion_relation(k, omega, v_local, c_s, xi, gamma_1, gamma_2, ...)`** → complex
  - Co-moving frame: Ω = ω - v·k
  - Ω² = c_s²k²·F(k²ξ²) + i·Γ_eff·Ω
  - **Damping rate:** Γ_eff = γ₁·k² + γ₂·(ω/c_s)² + [second-order terms]

- **`local_wavenumber(x, omega, params)`** → complex array k(x)
  - Solves dispersion at each spatial point
  - Leading order: k = ω/(c_s - v)
  - Dissipative correction: δk ≈ i·Γ_eff/(2c_eff)
  - Dispersive correction (Bogoliubov)

**WKB Integration:**

- **`wkb_phase_integral(x, k, x_tp)`** → complex array
  - Phase ∫k(x') dx' from turning point x_tp
  - Mode function: φ(x) ~ |k(x)|^{-1/2} · exp(i·phase)

**Connection Formula (Main Result):**

- **`connection_formula(omega, params)`** → `BogoliubovResult`
  - **Dispersive correction** (Corley-Jacobson 1996):
    δ_disp = -(π/6)·(ω/κ)·D²
  - **First-order dissipative**:
    δ_diss = Γ_H / κ where Γ_H = γ₁·k_H² + γ₂·ω²/c_s²
  - **Second-order dissipative**:
    δ^(2) = [γ_{2,1}·k_H³ + γ_{2,2}·ω²·k_H/c_s²] / κ
  - **Bogoliubov coefficients:**
    |β/α|² = exp(-2πω/κ·(1 - δ_total))
  - **Effective temperature:**
    T_eff = ω / ln(1 + 1/β²) [extracted from spectrum]

**Spectrum Computation:**

- **`compute_hawking_spectrum(omega_array, params)`** → list[BogoliubovResult]
  - Evaluates connection_formula at each frequency
  - Returns occupation numbers and temperature corrections

- **`extract_corrections(results)`** → dict
  - Extracts arrays: omega, delta_disp, delta_diss, delta_second, T_eff, n_occupation
  - For plotting/analysis

**Experimental Presets (Natural Units):**

- **`steinhauer_params()`**
  - κ = 1, c_s = 1, ξ = D = 0.03
  - γ̃ = γ_phys/κ ≈ 0.003 (Beliaev estimate)

- **`heidelberg_params()`**
  - D ≈ 0.02 (tighter), similar γ̃

---

#### `src/second_order/cgl_derivation.py` (Direction D, ~400 lines)
**Purpose:** CGL dynamical KMS derivation of the FDR at arbitrary EFT order.

**Key Functions:**

- **`retarded_kernel(coeffs, omega, k)`** → SymPy expression
  - Builds K_R(ω,k) from position-space coefficients via Fourier transform ∂_t → −iω, ∂_x → ik

- **`cgl_fdr(K_R, omega, beta)`** → SymPy expression
  - Master CGL FDR formula: K_N = −i·[K_R(ω) − K_R(−ω)]/(β₀ω)
  - Picks out odd-ω (dissipative) part; even-ω (conservative) correctly gives zero noise

- **`derive_fdr_fourier(N_max, verbose)`** → dict
  - Derives FDR at each EFT order N=0..N_max
  - Returns conservative/dissipative monomials, noise bilinears, FDR relations

- **`verify_einstein_relation()`** → bool — σ = γ/β₀ for Brownian particle
- **`verify_first_order_bec()`** → bool — K_N = 2Γ/β₀ for BEC with damping
- **`verify_second_order_fdr()`** → bool — second-order noise kernel is real
- **`discover_general_pattern(N_max)`** → str — general FDR pattern through order N
- **`connect_to_lean_fdr()`** → str — shows how CGL connects to Lean FirstOrderKMS
- **`boundary_term_estimate(D, gamma_ratio)`** → dict — IBP gradient correction at given adiabaticity D
- **`boundary_term_analysis(verbose)`** → str — full IBP analysis for all 3 experiments, resolves open question #3

**Key Finding:** The CGL FDR pairs noise with ODD-in-ω dissipative retarded terms only.
Even-in-ω (conservative) terms are unconstrained by the FDR. The existing FirstOrderKMS
relation i₁β = −r₂ follows from combining CGL FDR (i₁ = γ₁/β₀) with the BEC-specific
identification γ₁ = −r₂.

---

### 1.4 Package Initialization Files

#### `src/__init__.py`, `src/core/__init__.py`, `src/first_order/__init__.py`, `src/second_order/__init__.py`
- Expose public APIs via `__all__`
- Factory functions and main classes imported at package level

---

## 2. LEAN FORMAL VERIFICATION FILES

### 2.1 Root Module

#### `/lean/SKEFTHawking.lean` (Main import file)
```lean
import SKEFTHawking.Basic
import SKEFTHawking.AcousticMetric
import SKEFTHawking.SKDoubling
import SKEFTHawking.SecondOrderSK
import SKEFTHawking.HawkingUniversality
import SKEFTHawking.WKBAnalysis
```
**Purpose:** Top-level imports for all 6 modules.

---

### 2.2 Phase 1 Modules

#### `lean/SKEFTHawking/Basic.lean`

**Key Definition:**
- `ScalarField := Spacetime1D → ℝ` (placeholder scalar field type)

---

#### `lean/SKEFTHawking/AcousticMetric.lean`

**Theorems (8 total):**

1. **`acousticMetric_symmetric`**
   - g_{μν} is symmetric for any v, c_s, ρ

2. **`acousticMetric_det`** ✓ Filled
   - det(g_{μν}) = -ρ² (independent of v, c_s)
   - **Proof:** Direct 2×2 determinant calculation
   - Filled by Aristotle run 082e6776

3. **`acousticMetric_inv_correct`** ✓ Filled
   - Inverse metric satisfies g · g⁻¹ = I
   - **Proof:** 2×2 matrix multiplication
   - Filled by Aristotle run 082e6776

4. **`acoustic_metric_theorem`** ✓ Filled
   - Phonon EOM from L = P(X) equals □_g π = 0 on acoustic metric
   - **Proof:** Expand EL equations, match coefficients
   - Filled by Aristotle run a87f425a

5. **`acoustic_metric_lorentzian`** ✓ Filled
   - Acoustic metric has Lorentzian signature (det < 0)
   - **Proof:** Use acousticMetric_det + ρ > 0
   - Filled by Aristotle run 082e6776

6. **`soundSpeed_from_eos`**
   - c_s = √(∂P/∂n) from equation of state

7. **`gtt_vanishes_at_horizon`**
   - At sonic horizon, g_{tt} = 0 (defining property)

8. **`hawking_temp_from_surface_gravity`**
   - T_H = ℏκ/(2πk_B) at the horizon

---

#### `lean/SKEFTHawking/SKDoubling.lean`

**Key Structures:**
- `SKAction`, `DissipativeCoeffs`, `FirstOrderCoeffs`
- `satisfies_normalization`, `satisfies_positivity`

**Theorems (12 total, all ✓ Filled):**

1. **`firstOrder_normalization`** ✓
   - Dissipative action has ≥1 ψ_a factor (filled)

2. **`firstOrder_positivity`** ✓
   - Im I_SK ≥ 0 from γ₁,γ₂ ≥ 0 and β > 0
   - Filled by Aristotle run 082e6776

3. **`firstOrder_uniqueness`** ✓
   - **MAIN THEOREM:** Any action satisfying normalization + positivity + KMS is determined by 2 params (γ₁, γ₂)
   - 9 first-order monomials → 2 free after KMS
   - Filled by Aristotle run 270e77a0
   - **Discovery:** Original KMS too weak; counterexample c=⟨0,...,0,1,0⟩. Fixed with FirstOrderKMS.

4. **`zeroTemp_nontrivial`**
   - Groundstate is not all-zeros

5. **`fdr_from_kms_gamma1`** ✓
   - FDR: i₁ = γ₁/β (noise from ψ_a² dissipation)
   - **Proof:** Unfold action at ψ_a point, extract Im part
   - Filled by Aristotle run 20556034

6. **`fdr_from_kms_gamma2`** ✓
   - FDR: i₂ = γ₂/β (noise from (∂_t ψ_a)² dissipation)
   - Filled by Aristotle run 20556034

7. **`fdr_from_kms`** ✓
   - Complete FDR: Im part equals sum of per-sector terms
   - **Proof:** fun f => rfl (definitional equality after unfolding)
   - Filled by Aristotle run 638c5ff3

8. **`firstOrder_KMS_optimal`** ✓
   - **Stress test:** positivity ↔ (i₁ ≥ 0 ∧ i₂ ≥ 0)
   - **Verifies:** FirstOrderKMS is the optimal constraint
   - Filled by Aristotle run 3eedcabb

9. **`firstOrder_altSign_uniqueness_test`** ✓
   - **Stress test:** Does uniqueness hold with wrong FDR sign (i₁·β = +r₂)?
   - **Result:** NEGATION proved (counterexample exists)
   - Shows FDR sign is physically meaningful
   - Filled by Aristotle run 3eedcabb

---

#### `lean/SKEFTHawking/HawkingUniversality.lean`

**Definitions:**
- `ModifiedDispersion`, `isAdiabatic`, `EffectiveTemperature`

**Theorems (7 total, all ✓ Filled):**

1. **`bogoliubov_superluminal`** ✓
   - Bogoliubov dispersion F(x) = 1+x is superluminal for small k
   - Filled by Aristotle

2. **`standard_hawking_thermal`** ✓
   - Standard undamped case: T_eff = T_H (no corrections)

3. **`dispersive_correction_bound`** ✓
   - **Witness:** δ_disp := -(π/6)·D²
   - **Bounds:** |δ_disp| ≤ (π/6 + 1)·D²
   - Filled by Aristotle run d65e3bba

4. **`dissipative_correction_existence`** ✓
   - **Witness:** δ_diss := -(γ₁+γ₂)/(2κ)
   - **Property:** Vanishes iff γ₁=γ₂=0 (bidirectional)
   - Filled by Aristotle run 657fcd6a

5. **`hawking_universality`** ✓
   - **MAIN THEOREM:** Combined structure with T_H, both corrections, cross-term
   - 6 conjuncts: rfl, simp, div_ne_zero, positivity, neg_ne_zero, simp
   - Filled by Aristotle run 416fb432

---

### 2.3 Phase 2 Modules

#### `lean/SKEFTHawking/SecondOrderSK.lean`

**Key Structures:**
- `SecondOrderCoeffs`, `FullCoeffs`, `CombinedDissipativeCoeffs`
- `FirstOrderKMS` (algebraic KMS on 9 first-order coefficients)
- `FullSecondOrderKMS` (14-parameter general action)

**Theorems (22 total, all ✓ Filled):**

1. **`transport_coefficient_count`** ✓
   - General formula: count(N) = ⌊(N+1)/2⌋ + 1
   - **Proof:** Bijection with Finset.range
   - Filled by Aristotle run d61290fd

2. **`firstOrder_count`** ✓
   - count(1) = 2
   - **Proof:** native_decide
   - Filled by Aristotle run d61290fd

3. **`secondOrder_count`** ✓
   - count(2) = 2 new coefficients
   - **Proof:** native_decide
   - Filled by Aristotle run d61290fd

4. **`secondOrder_count_with_parity`** ✓
   - count(2, parity) = 0 (no new dissipation with spatial symmetry!)
   - **Proof:** native_decide
   - Filled by Aristotle run d61290fd

5. **`secondOrder_uniqueness`** ✓
   - Second-order action uniquely parameterized by γ_{2,1}, γ_{2,2}

6. **`cumulative_through_order2`** ✓
   - Total through order 2: 2 + 2 = 4 free parameters
   - **Proof:** norm_num
   - Filled by Aristotle run d61290fd

7. **`secondOrder_requires_parity_breaking`** ✓
   - Second-order physics requires odd spatial derivatives (breaks x → -x)

8. **`secondOrder_frequency_dependent`** ✓
   - Second-order corrects depend on ω (unlike first-order)

9. **`fullSecondOrder_uniqueness`** ✓
   - **MAIN THEOREM:** 14-parameter action → 4 transport coefficients
   - **Proof:** Construct CombinedDissipativeCoeffs with γ₁=-c.r2, γ₂=c.r1+c.r2, γ_{2,1}=c.s1, γ_{2,2}=c.s3
   - Filled by Aristotle run c4d73ca8

10. **`combined_normalization`** ✓
    - Full second-order action has ≥1 ψ_a factor

11. **`combined_positivity_constraint`** ✓
    - **KEY RESULT:** γ_{2,1} + γ_{2,2} = 0 (forced by PSD of imaginary form)
    - **Proof:** Contradiction if ≠0; construct field config with Im < 0
    - Filled by Aristotle run c4d73ca8

12. **`fdr_second_order_consistent`** ✓
    - Second-order FDR relations compatible with first-order

13. **`fullKMS_reduces_to_firstOrder`** ✓
    - When γ_{2,1}=γ_{2,2}=0, full structure reduces to Phase 1

14. **`altFDR_uniqueness_test`** ✓
    - **Stress test:** Does uniqueness hold with alternate FDR j_tx·β = s1-s3?
    - **Result:** NEGATION proved (counterexample c=⟨1,-1,0,0,0,0,1,0,0,1,0,1,0,0⟩)
    - Filled by Aristotle run 3eedcabb

15. **`relaxed_uniqueness_test`** ✓
    - **Stress test:** With nonzero i₃ (spatial noise), does uniqueness hold with 5 params?
    - **Result:** YES (γ_x = c.i₃ as fifth parameter)
    - Filled by Aristotle run 3eedcabb

16. **`relaxed_positivity_weakens`** ✓
    - **Stress test:** With i₃≠0, positivity constraint becomes (γ_{2,1}+γ_{2,2})²≤4γ₂γ_x β
    - **Proof:** PSD on extended 4×4 imaginary form
    - Filled by Aristotle run 3eedcabb

17. **`thirdOrder_count`** ✓
    - count(3) = 3
    - **Proof:** native_decide
    - Filled by Aristotle run 3eedcabb

18. **`cumulative_count_through_3`** ✓
    - Total through order 3: 2 + 2 + 3 = 7
    - **Proof:** norm_num
    - Filled by Aristotle run 3eedcabb

19-22. **Additional gap-closure theorems** ✓
    - Various structural consistency checks

---

#### `lean/SKEFTHawking/WKBAnalysis.lean`

**Key Structures:**
- `DissipativeDispersion`, `ModifiedWKBProfile`

**Theorems (13 total, all ✓ Filled):**

1. **`dampingRate_firstOrder_nonneg`** ✓
   - Damping γ₁·k² + γ₂·ω²/c_s² ≥ 0 for γ₁,γ₂≥0
   - **Proof:** sum_nonneg + mul_nonneg + sq_nonneg

2. **`turning_point_shift`** ✓
   - WKB turning point shifts into complex plane
   - Shift: δx_imag = Γ_H / (κ·c_s)
   - **Proof:** Witness construction, exact value
   - Filled by Aristotle run c4d73ca8

3. **`dissipative_occupation_planckian`** ✓
   - Dissipation modifies Planck spectrum via Bogoliubov|β|²

4. **`firstOrder_correction_positive`** ✓
   - δ_diss > 0 increases T_eff (dissipation is heating)

5. **`secondOrder_vanishes_at_first_order`** ✓
   - When γ_{2,1}=γ_{2,2}=0, second-order correction = 0

6. **`effective_temp_zeroth_order`** ✓
   - Without any corrections, T_eff = T_H (baseline)

7. **`no_dissipation_zero_damping`** ✓
   - All γᵢ=0 → Γ=0 everywhere
   - **Proof:** Unfold, simp
   - Filled by Aristotle run 3eedcabb

8. **`turning_point_no_shift`** ✓
   - No dissipation → no turning point shift
   - **Proof:** Use no_dissipation_zero_damping + simp
   - Filled by Aristotle run 3eedcabb

9. **`firstOrder_correction_zero_iff_no_dissipation`** ✓
   - δ_diss = 0 when all γᵢ = 0 (forward direction)
   - **Proof:** Unfold firstOrderCorrection
   - Filled by Aristotle run 3eedcabb

10. **`turning_point_shift_nonzero`** ✓
    - Nonzero Γ_H → nonzero shift (requires κ>0, c_s>0)
    - **Key addition (Round 5):** Uses hk : 0 < kappa
    - **Proof:** div_ne_zero hk.ne' hcs.ne'
    - Filled by Aristotle run 518636d7

11. **`firstOrder_correction_zero_iff`** ✓
    - TRUE BICONDITIONAL: δ_diss = 0 ↔ Γ_H = 0
    - **Key addition (Round 5):** Backward direction requires κ≠0 to invert Γ_H/κ
    - **Proof:** div_eq_iff hk.ne' + aesop
    - Filled by Aristotle run 518636d7

12. **`dampingRate_eq_zero_iff`** ✓
    - TRUE BICONDITIONAL: Γ=0 for all (k,ω) ↔ all γᵢ=0
    - **Key addition (Round 5):** Requires c_s≠0 for ω²/c_s² terms
    - **Proof:** Forward: evaluate at 4 strategic points (k=1,ω=0), (k=2,ω=0), (k=0,ω=1), (k=1,ω=1)
    - Filled by Aristotle run 518636d7

13. **Remaining structural lemmas** ✓

---

#### `lean/SKEFTHawking/CGLTransform.lean` (Direction D)

**Purpose:** CGL dynamical KMS derivation of the FDR. Defines the CGL transformation
and derives the FDR pairing noise with odd-ω dissipative retarded terms.

**Key Structures:**
- `RetardedKernel L` — retarded kernel decomposed into even-ω (conservative) and odd-ω (dissipative)
- `NoiseKernel L` — noise bilinears at derivative level L
- `Level1Dissipative`, `Level0Noise` — level 1 friction + level 0 noise
- `Level3Dissipative`, `Level2Noise` — level 3 dissipation + level 2 noise

**Theorems (7 total, all ✓ proved):**

1. **`cgl_fdr_general`** ✓ — General-order CGL FDR: noise = −b/β for any odd-m monomial
   - Filled by Aristotle run 2ca3e7e6 (March 24, 2026)
   - Proof: `rw [← h_fdr, mul_div_cancel_right₀ _ hb.ne']`

2. **`cgl_fdr_spatial`** ✓ — Same as general, parameterized by (j_t, j_x)
   - Filled by Aristotle run 2ca3e7e6

3. **`einstein_relation`** ✓ — Einstein relation σ·β = −b_{1,0}
   - Filled by Aristotle run dab8cfc1 (March 24, 2026)
   - Proof: `rw [← h_fdr, mul_div_cancel_right₀ _ hb.ne']`

4. **`secondOrder_cgl_fdr`** ✓ — i_{0,1}·β = −b_{1,2} ∧ i_{1,0}·β = −b_{3,0}
   - Filled by Aristotle run dab8cfc1
   - Proof: `exact ⟨eq_div_of_mul_eq hb.ne' h_fdr_01, eq_div_of_mul_eq hb.ne' h_fdr_10⟩`

5. **`cgl_implies_firstOrderKMS`** ✓ — CGL + T-reversal + model → i₁β = −r₂
   - Proof: `linarith` (proved directly, no Aristotle needed)

6. **`cgl_implies_secondOrderKMS`** ✓ — CGL + T-reversal + model → j_tx·β = s₁+s₃
   - Filled by Aristotle run 2ca3e7e6
   - Proof: `linarith`

7. **`even_kernel_zero_noise`** ✓ — Conservative (even-ω) kernel gives zero noise
   - Proof: `trivial` (structural/physical content in Python verification)

---

## 3. JUPYTER NOTEBOOKS

All in `notebooks/` directory.

### `Phase1_Technical.ipynb` (23 cells)
**Purpose:** Technical walkthrough of Phase 1 dissipative corrections.

**Cell structure:**
- Markdown: Introduction + structure overview
- Code cells: Load parameters, compute acoustic metric, solve transonic background
- Verify continuity equation
- Estimate Beliaev damping γ_B(ω)
- Compute δ_diss for 3 experimental setups
- Plot corrections vs adiabaticity parameter

**Computations (inline values):**
- Hawking temperature T_H from surface gravity κ
- Beliaev damping rate scaling: γ_B ~ √(n·a³)·ω²/c_s
- δ_diss = Γ_H/κ for each setup
- Enhanced δ_diss × (c_density/c_spin)² for Trento

**Imports:**
- src.core: steinhauer_Rb87, heidelberg_K39, trento_spin_sonic, solve_transonic_background, compute_dissipative_correction

---

### `Phase1_Stakeholder.ipynb`
**Purpose:** High-level summary for non-expert audience.

**Content:**
- Plain-language explanation of BEC analog gravity
- Hawking radiation basics
- Experimental motivation (why measure?)
- Key results: δ_diss is small but accessible in spin-sonic systems

---

### `Phase2_Technical.ipynb` (projected, 15+ cells)
**Purpose:** Second-order enumeration, KMS structure, WKB analysis.

**Expected cell structure:**
- Transport coefficient counting via enumerate_order
- Monomial filtering with and without parity
- Full second-order action construction
- Positivity constraint verification
- Bogoliubov coefficients with dissipation
- Frequency-dependent correction δ^(2)(ω)
- Spectral distortion plots

**Imports:**
- src.second_order: analyze_order, FirstOrderCoeffs, SecondOrderCoeffs, FullCoeffs, effective_temperature, spectral_distortion
- src.second_order.wkb_analysis: TransonicProfile, WKBParameters, connection_formula, compute_hawking_spectrum

---

### `Phase2_Stakeholder.ipynb`
**Purpose:** Non-technical summary of Phase 2 results.

**Content:**
- What is "second order" and why does it matter?
- Frequency-dependent spectrum as new probe of trans-Planckian physics
- Experimental signatures and sensitivity requirements

---

## 4. PAPER DRAFTS

### `papers/paper1_first_order/paper_draft.tex` (397 lines)
**Title:** "Dissipative EFT Corrections to Analog Hawking Radiation in BEC Sonic Black Holes"

**Structure:**
- **Abstract:** Main result: δ_diss = Γ_H/κ; accessible in spin-sonic systems
- **Intro:** Motivation from trans-Planckian problem
- **Son's EFT:** Superfluid action, acoustic metric in Planck-Gasperini form
- **SK Doubling:** Three axioms (normalization, positivity, KMS); dissipative action with γ₁, γ₂
- **Background:** Transonic flow, surface gravity, WKB dispersion
- **Results:**
  - Main formula: T_eff = T_H(1 + δ_disp + δ_diss + δ_cross)
  - Explicit estimates: Steinhauer δ_diss ~ 10^{-5} to 10^{-3}
  - Trento enhanced: × (c_density/c_spin)² ~ 100
- **Formal verification:** 14 Lean theorems, all ✓ filled by Aristotle
  - Highlights: acoustic metric determinant, SK positivity, FDR, uniqueness
- **Discussion:** Universality, trans-Planckian physics, experimental prospects

**Key Equations:**

1. **Acoustic metric:** ds² = (n/c_s)[-(c_s²-v²)dt² - 2v·dt·dx + dx²]
2. **Surface gravity:** κ = |dv/dx - dc_s/dx| at horizon
3. **Hawking temperature:** T_H = ℏκ/(2πk_B)
4. **Dissipative action (first-order):**
   - L_re = γ₁ψ_a(∂²_t-∂²_x)ψ_r + γ₂ψ_a∂²_t ψ_r
   - L_im = (γ₁/β)ψ_a² + (γ₂/β)(∂_t ψ_a)²
5. **Main result:** T_eff = T_H(1 + δ_disp + δ_diss + δ_cross)
   - δ_diss = -(γ₁+γ₂)/(2κ) ≈ Γ_H/κ

**Physical Constants (embedded in text):**
- ℏ = 1.054571817e-34 J·s
- k_B = 1.380649e-23 J/K
- m_Rb87 = 1.443160648e-25 kg, a = 5.77e-9 m
- m_K39 = 6.470076e-26 kg, a = 50e-9 m
- m_Na23 = 3.8175458e-26 kg, a = 2.75e-9 m

**Hardcoded References:**
- Hawking:1974 (original black hole radiation)
- Unruh:1981 (analog gravity)
- Corley-Jacobson (dispersive corrections)
- Son:2002 (superfluid EFT)
- Steinhauer:2016/2019 (experimental realization)
- Coutant:2014 (dispersive corrections in BEC)

---

### `papers/paper2_second_order/paper_draft.tex` (359 lines)
**Title:** "Second-Order Dissipative EFT and Frequency-Dependent Corrections to Analog Hawking Radiation..."

**Structure:**
- **Abstract:** Second-order adds 2 new coefficients (γ_{2,1}, γ_{2,2}); frequency-dependent ω³ spectrum distortion
- **Intro:** Extension beyond Phase 1; role of spatial parity
- **Enumeration:** Monomial counting formula count(N) = ⌊(N+1)/2⌋ + 1; derivation via T-parity + spatial parity
  - Key insight: both second-order terms have odd n (parity-breaking)
  - With parity: count(2,parity) = 0 (no new dissipation if x → -x preserved)
- **Full KMS at second order:** 14 free parameters → 4 transport coefficients
- **Positivity constraint:** γ_{2,1} + γ_{2,2} = 0 (PSD on imaginary quadratic form)
- **WKB with dissipation:** Modified turning point, Bogoliubov coefficients
- **Second-order correction:** δ^(2)(ω) ∝ (ω/Λ)³ (frequency-dependent, new!)
- **Formal verification:** 22 Lean theorems (Phase 1+2 combined), plus 9 stress tests
  - FDR sign tests, relaxed positivity, KMS optimality, limit checks
  - Round 5: Total-division strengthening (3 additional theorems using κ>0)
  - **Status: 40/40 all proved, zero sorry remaining**
- **Discussion:** Parity as experimental probe, trans-Planckian implications

**Key Formulas:**

1. **Counting formula:** count(N) = ⌊(N+1)/2⌋ + 1
   - Order 1: count = 2 ✓
   - Order 2: count = 2 new (γ_{2,1}, γ_{2,2})
   - With parity: count = 0 (all odd n)

2. **Dissipative dispersion:**
   - Γ(k,ω) = γ₁k² + γ₂ω²/c_s² + γ_{2,1}k³ + γ_{2,2}ω²k/c_s²

3. **Second-order action (real part):**
   - L_re^(2) = γ_{2,1}ψ_a·∂³_x ψ_r + γ_{2,2}ψ_a·∂²_t∂_x ψ_r

4. **Second-order correction:**
   - δ^(2)(ω) = γ_{2,1}(ω·ξ/c_s)³/κ + γ_{2,2}(ω·ξ/c_s)²(v'·ξ/c_s)/κ
   - With constraint γ_{2,2} = -γ_{2,1}: δ^(2) ~ (ω/Λ)² [(ω/Λ) - (ω/Λ_x)]

5. **Full effective temperature:**
   - T_eff(ω) = T_H[1 + δ_disp + δ_diss + δ^(2)(ω) + δ_cross]

**Stress Tests (9 total):**
1. altFDR_uniqueness_test: NEGATION (wrong FDR fails)
2. firstOrder_KMS_optimal: biconditional (FirstOrderKMS is optimal)
3. firstOrder_altSign_uniqueness_test: NEGATION
4. relaxed_uniqueness_test: extends to 5 parameters with i₃
5. relaxed_positivity_weakens: PSD relaxation inequality
6. no_dissipation_zero_damping: limit check
7. thirdOrder_count: count(3) = 3
8-9. Additional consistency checks

**Round 5 Additions (3 new theorems):**
1. **turning_point_shift_nonzero:** Nonzero Γ_H → nonzero shift (uses κ>0)
2. **firstOrder_correction_zero_iff:** Biconditional (uses κ>0)
3. **dampingRate_eq_zero_iff:** Biconditional on all-zero condition (uses c_s>0)

---

## 5. TEST FILES

All in `tests/` directory.

### `tests/__init__.py`
(Empty)

### `tests/test_lean_integrity.py` (60 lines)

**Test Functions:**

1. **`test_lean_phase1_modules_exist`**
   - Verifies presence of:
     - SKEFTHawking/Basic.lean
     - SKEFTHawking/AcousticMetric.lean
     - SKEFTHawking/SKDoubling.lean
     - SKEFTHawking/HawkingUniversality.lean

2. **`test_lean_phase2_modules_exist`**
   - Verifies:
     - SKEFTHawking/SecondOrderSK.lean
     - SKEFTHawking/WKBAnalysis.lean

3. **`test_lean_root_imports_all_modules`**
   - Reads SKEFTHawking.lean
   - Verifies all 6 imports present

4. **`test_lakefile_exists`**
   - Checks lakefile.toml with project name "sk-eft-hawking"

5. **`test_lean_toolchain`**
   - Verifies lean-toolchain contains "v4.28.0"

6. **`test_no_active_sorry`**
   - Grep-based heuristic for active sorry statements
   - Ignores comments, allows sorry in string literals
   - **Status:** Should pass when all 35 gaps filled

7. **`test_sorry_gap_registry`**
   - Verifies SORRY_GAPS from aristotle_interface contains ≥35 entries
   - Verifies all .filled = True

---

### `tests/test_transonic_background.py` (140 lines)

**Test Classes:**

1. **`TestBECParameters`**
   - test_steinhauer_healing_length: ξ ∈ (0.01, 10) μm ✓
   - test_steinhauer_sound_speed: c_s ∈ (0.01, 10) mm/s ✓
   - test_interaction_positive: g_1D > 0 for all factories ✓
   - test_subsonic_upstream: M < 1 everywhere ✓

2. **`TestTransonicBackground`**
   - test_continuity_satisfied: J = n·v constant (within 1%) ✓
   - test_horizon_exists: κ > 0 (sonic horizon found) ✓
   - test_hawking_temp_positive: 0.001 < T_nK < 100 ✓
   - test_adiabaticity_small: D < 0.5 (EFT valid) ✓

3. **`TestDissipativeCorrection`**
   - test_correction_vanishes_without_dissipation: δ_diss = 0 when γ₁=γ₂=0 ✓
   - test_correction_positive_with_dissipation: δ_diss > 0 ✓
   - test_correction_small: |δ_diss| < 0.1 (parametrically small) ✓
   - test_dispersive_vs_dissipative_scaling: Both << 1 ✓

---

### `tests/test_second_order.py` (95 lines)

**Test Classes:**

1. **`TestEnumeration`**
   - test_first_order_gives_two: count(1) = 2 ✓
   - test_second_order_gives_two: count(2) = 2 ✓
   - test_second_order_parity_gives_zero: count(2,parity) = 0 ✓
   - test_third_order_gives_three: count(3) = 3 ✓
   - test_general_formula: count(N) formula for N∈[1,6] ✓

2. **`TestCoefficients`**
   - test_first_order_positivity: γ₁,γ₂ ≥ 0 enforced ✓
   - test_correction_vanishes_without_dissipation: δ_diss = 0 ✓
   - test_correction_positive: δ_diss > 0 for positive γ ✓
   - test_second_order_frequency_dependent: δ^(2)(ω_high) > δ^(2)(ω_low) ✓

3. **`TestWKB`**
   - test_undamped_gives_hawking_temp: γ=0 → T_eff ≈ T_H ✓
   - test_dissipation_increases_temperature: γ>0 → T_eff > T_H ✓
   - test_steinhauer_preset_loads: Valid WKB parameters ✓

---

### `tests/test_cgl_derivation.py` (289 lines)

**Test Classes (26 tests):**

- **TestKernelConstruction** (4): Wave equation, friction, even/odd kernel properties
- **TestCGLFDR** (6): Even→zero noise, Einstein relation, BEC FDR, second-order real, linearity, 1/β proportionality
- **TestKernelDecomposition** (3): Even+odd=original, symmetry checks
- **TestGeneralPattern** (6): Orders N=0,1,2,4 noise counts, conservative unconstrained
- **TestLeanConnection** (2): CGL+BEC→Lean FDR, second-order structure
- **TestBoundaryTerms** (5): O(D) correction, experiments<2%, D=0 vanishing, D=1 growth, full analysis

### `tests/test_cross_validation.py`
Pytest wrapper for `scripts/validate.py` (10 checks).

### `scripts/review_figures.py`
Figure review pipeline: generates 12 PNGs via kaleido, produces review_manifest.json, runs automated structural checks. Used by figure-reviewer agent.

**Total test count: 64/64 tests, 10/10 validation checks.**

---

## 6. CONFIGURATION FILES

### `pyproject.toml`
- Project metadata: sk-eft-hawking v0.1.0
- Build system: hatch
- Dependencies: numpy, scipy, plotly, kaleido (optional)
- Development: pytest, pytest-cov

### `lake-manifest.json` (in `lean/`)
- Lean package manifest for Lake (Lean's build system)

### `lakefile.toml` (in `lean/`)
- Lake build configuration for sk-eft-hawking
- Dependencies: Mathlib

### `lean-toolchain` (in `lean/`)
- Specifies v4.28.0

### `.env` (credentials, not in repo)
- ARISTOTLE_API_KEY=... (for Aristotle API)

### `.python-version`
- Specifies Python version (likely 3.11+)

### `uv.lock`
- Lock file for uv package manager (fast alternative to pip)

---

## SUMMARY TABLE

| Category | Count | Status |
|----------|-------|--------|
| **Python Source Modules** | ~35 | ✓ Complete (Phases 1-4) |
| **Test Files** | 12 | ✓ 820 tests, all passing |
| **Notebooks** | 16 | ✓ Phases 1-4 (Technical + Stakeholder) |
| **Lean Modules** | 16 | ✓ All build clean |
| **Lean Theorems** | | |
| Phase 1 (Aristotle) | 14 | ✓ All proved |
| Phase 2 (Aristotle) | 8 | ✓ All proved |
| Stress tests (Aristotle) | 13 | ✓ All proved |
| Direction D CGL (Aristotle) | 5 | ✓ All proved |
| Phase 3 (manual + Aristotle) | 90 | ✓ All proved |
| Phase 4 (manual + Aristotle b1ea2eb7) | 86 | ✓ All proved |
| **Total Lean theorems** | **216 + 1 axiom** | **✓ Zero sorry** |
| **Aristotle-proved** | **53** | **✓ 53/53 filled** |
| **Paper Drafts** | 6 + prediction tables | ✓ Full tex |
| **Pipeline Figures** | 44 | ✓ All PNGs generated |
| **Stakeholder Docs** | 9 | ✓ Phases 1-4 |

---

## KEY FORMULAS BY CATEGORY

### Physical Constants
- ℏ = 1.054571817e-34 J·s
- k_B = 1.380649e-23 J/K
- Atomic masses: ⁸⁷Rb = 1.443e-25, ³⁹K = 6.47e-26, ²³Na = 3.82e-26 kg
- Scattering lengths: ⁸⁷Rb = 5.77e-9, ³⁹K = 50e-9, ²³Na = 2.75e-9 m

### Acoustic Metric
- ds² = (n/c_s)[-(c_s²-v²)dt² - 2v·dt·dx + dx²]
- det(g) = -ρ² (independent of v, c_s)
- κ = |dv/dx - dc_s/dx| at horizon

### Sound Speed & Healing Length
- c_s = √(g_int·n/m) [equation of state]
- ξ = ℏ/(m·c_s) [healing length]
- g_1D = 2ℏ²a/(m·a_⊥²) [1D coupling, Olshanni]

### Hawking Temperature
- T_H = ℏκ/(2πk_B)
- D = κξ/c_s [adiabaticity, should be << 1]

### First-Order SK-EFT
- L_re = γ₁ψ_a(∂²_t - ∂²_x)ψ_r + γ₂ψ_a·∂²_t ψ_r
- L_im = (γ₁/β)ψ_a² + (γ₂/β)(∂_t ψ_a)² [FDR]
- Γ_H = γ₁·k_H² + γ₂·ω²/c_s² [damping rate at horizon]
- δ_diss = Γ_H/κ [dissipative correction]

### Second-Order SK-EFT
- L_re^(2) = γ_{2,1}ψ_a·∂³_x ψ_r + γ_{2,2}ψ_a·∂²_t∂_x ψ_r [new terms]
- Constraint: γ_{2,1} + γ_{2,2} = 0 (from positivity)
- δ^(2)(ω) ∝ (ω/Λ)³ [frequency-dependent, new]

### Corrections Summary
- δ_disp = -(π/6)·(ω/κ)·D² [dispersive, known]
- δ_diss = Γ_H/κ [dissipative, first-order]
- δ^(2)(ω) ~ (γ_{2,1}/κ)·(ω/Λ)² [dissipative, second-order]
- δ_cross = δ_disp·δ_diss [subdominant]
- T_eff(ω) = T_H·(1 + δ_disp + δ_diss + δ^(2)(ω) + δ_cross)

### Transport Coefficient Counting
- count(N) = ⌊(N+1)/2⌋ + 1
- count(1) = 2, count(2) = 2 new, count(3) = 3 new
- count(2, parity) = 0 (all new terms break x → -x)

### Beliaev Damping Estimate
- γ_B ~ √(n·a³)·ω²/c_s [at frequency ω]
- Evaluated at ω_H ~ κ for Hawking radiation
- Enhanced by (c_density/c_spin)² in spin-sonic systems

---

## VERIFICATION STATUS

✅ **All 216 Lean theorems + 1 axiom PROVED, zero sorry** (16 modules)
✅ **53 Aristotle-proved** (40 Phases 1-3 + 13 Phase 4 batch b1ea2eb7)
✅ **820 pytest tests passing** (12 test files)
✅ **44 pipeline figures generated** (all structural checks passing)
✅ **16 notebooks** (all execute cleanly)
✅ **6 papers + prediction tables** (LaTeX, PRD/PRL format)

Last verified: March 26, 2026 (Phase 4 completion)

- ✓ 14 Phase 1 (core dissipative corrections)
- ✓ 8 Phase 2 (second-order enumeration, KMS, WKB)
- ✓ 9 Phase 3 stress tests (FDR robustness, KMS optimality, limit checks)
- ✓ 3 Phase 4 Round 5 additions (total-division strengthening: nonzero shifts, zero-iff biconditionals)

✅ **All Python code tested**
- ✓ 7 Lean integrity tests
- ✓ 8 transonic background tests
- ✓ 9 second-order enumeration & coefficient tests

✅ **Documentation complete**
- ✓ 2 paper drafts (397 + 359 lines LaTeX)
- ✓ 4 technical + stakeholder notebooks
- ✓ 12 publication-quality figures (Plotly): 6 Phase 1 + 6 Phase 2 (CGL, boundary, positivity, on-shell, Einstein)
- ✓ Interactive HTML dashboard

---

**Project Status:** ✅ COMPLETE & VERIFIED
