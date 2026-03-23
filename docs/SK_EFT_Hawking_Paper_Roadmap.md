# Dissipative EFT Corrections to Analog Hawking Radiation: Technical Roadmap

## A Paper Blueprint for Connecting Schwinger-Keldysh Hydrodynamic EFT to Acoustic Horizon Physics

*Prepared March 2026 | Target: PRL (4 pages + supplement) or PRD Rapid Communication*

---

## 1. Why This Paper

No one has connected the Schwinger-Keldysh effective field theory for dissipative fluids to analog Hawking radiation. This is the single most valuable gap identified across our entire research program. The paper would simultaneously:

- Bridge two mature theoretical frameworks that have developed independently for 15+ years
- Produce a concrete experimental prediction (modified T_H with dissipative correction)
- Establish a new EFT methodology for analog gravity
- Speak to the trans-Planckian problem in gravitational Hawking radiation (robustness against UV dissipation)
- Be directly testable by next-generation BEC experiments (Trento spin-sonic, Heidelberg K-39)

The key result would be the dissipative correction to the Hawking temperature: **T_H → T_H(1 + δ_diss)**, where δ_diss is computed systematically within the SK framework and depends on the dissipative transport coefficients of the superfluid.

---

## 2. The Starting Point: Son's Superfluid EFT

The leading-order EFT for a relativistic U(1) superfluid is:

**L = P(X)**, where X = g^{μν} ∂_μ ψ ∂_ν ψ

with ψ the Goldstone boson (superfluid phase), P the pressure as a function of chemical potential μ = √X, and the equation of state fully determines all phonon interactions. The phonon field π is defined by ψ = μt + π, and expanding P(X) around the background gives:

L = P(μ²) + P'(μ²)(2μ π̇ + (∂π)²) + P''(μ²)(2μ π̇ + (∂π)²)² + ...

The phonon propagates on the acoustic metric:

g^{μν}_acoustic ∝ P'(μ²) η^{μν} + 2P''(μ²) ∂^μ ψ ∂^ν ψ

with sound speed c_s² = P'/( P' + 2μ²P'').

**For BEC specifically:** P(X) = (X - m²)²/(4λ) in the non-relativistic limit gives the Gross-Pitaevskii equation. The BEC healing length ξ = ℏ/mc_s sets the EFT cutoff.

---

## 3. The SK Doubling Procedure

The Crossley-Glorioso-Liu (CGL) formalism (JHEP 2017) constructs the dissipative EFT by:

**Step 1: Double the degrees of freedom.** Introduce fields on the forward (1) and backward (2) branches of the Schwinger-Keldysh contour: ψ_1, ψ_2. Define retarded/advanced combinations:

ψ_r = (ψ_1 + ψ_2)/2 (classical/physical field)
ψ_a = ψ_1 - ψ_2 (noise/response field)

**Step 2: Impose the dynamical KMS symmetry.** At thermal equilibrium with temperature T = 1/β, the KMS condition constrains the effective action:

I_SK[ψ_r, ψ_a] = I_SK[ψ_r, ψ_a]* under the KMS transformation:
ψ_a → ψ_a + iβ ∂_t ψ_r (to leading order)

This generates the fluctuation-dissipation relation automatically. In the classical limit (ℏ → 0, βω → 0), this becomes an emergent BRST supersymmetry guaranteeing the second law.

**Step 3: Write the most general action compatible with symmetries.** At first order in derivatives beyond the ideal superfluid (Son's L = P(X)):

I_SK = ∫ d⁴x [L_ideal(ψ_r) + dissipative terms involving ψ_a]

The dissipative terms at leading order take the form:

I_diss = ∫ d⁴x [iγ₁ ψ_a (∂²ψ_r) + iγ₂ ψ_a ∂_μ(u^μ ∂_ν(u^ν ψ_r)) + ...]

where γ₁, γ₂ are dissipative transport coefficients (related to bulk viscosity and phonon damping rate), and u^μ is the superfluid velocity.

**Key reference:** Dubovsky-Hui-Nicolis-Son (PRD 2012) for non-dissipative superfluid EFT; Endlich-Nicolis-Porto-Wang (PRD 2013) for first-order dissipative corrections; CGL (JHEP 2017) for the full SK framework.

---

## 4. The Transonic Background: Where the Calculation Becomes Novel

This is where no one has gone. The standard SK-EFT is formulated around **thermal equilibrium** (homogeneous, time-independent background). A sonic horizon requires an **inhomogeneous, transonic background** — the flow velocity transitions from subsonic to supersonic at the horizon.

**Background configuration for a sonic horizon:**

The mean-field superfluid has a spatially varying flow velocity v(x) and density n(x) satisfying the 1D Euler + continuity equations:

n(x) v(x) = J = const (mass current conservation)
½ m v² + g n + V_ext = const (Bernoulli)

The sonic horizon is at x_H where v(x_H) = c_s(x_H). Near the horizon, expand:

v(x) ≈ c_s + κ(x - x_H) + ...
c_s(x) ≈ c_s - α(x - x_H) + ...

where κ = dv/dx|_H + dc_s/dx|_H is the surface gravity. The standard Hawking temperature is T_H = ℏκ/(2πk_B).

**The technical challenge:** The SK action must be expanded around this inhomogeneous background, not around thermal equilibrium. The fields become:

ψ_r = ψ̄(x) + π_r(t,x), ψ_a = π_a(t,x)

where ψ̄(x) is the transonic background. The quadratic action for fluctuations π_r, π_a determines the retarded Green's function G_R and the statistical (Keldysh) function G_K. Hawking radiation appears as the specific structure of G_K near the horizon.

**Proposed approach (the core of the paper):**

(a) Start with the CGL effective action for a dissipative superfluid in 1+1D (the relevant case for quasi-1D BEC experiments).

(b) Expand around the transonic background to quadratic order in fluctuations.

(c) The retarded propagator G_R satisfies a modified wave equation with dissipative terms. Near the horizon, this becomes a confluent Heun equation (generalizing the hypergeometric equation of the non-dissipative case).

(d) The Keldysh function G_K is determined by the fluctuation-dissipation relation imposed by KMS symmetry. In the non-dissipative limit, G_K encodes the thermal Hawking distribution.

(e) The dissipative correction δ_diss emerges as a shift in the effective temperature read off from G_K.

---

## 5. The Five Technical Obstacles (and Proposed Solutions)

### Obstacle 1: SK-EFT assumes thermal equilibrium; Hawking radiation is non-equilibrium

**The problem:** The CGL formalism's KMS symmetry encodes equilibrium at temperature T. But the Hawking process is particle creation from the in-vacuum — fundamentally out of equilibrium.

**Proposed solution:** Work in the "near-equilibrium on the horizon" regime. The Hawking state itself is thermal (the Unruh state restricted to the exterior). The SK contour can be deformed to the Hartle-Hawking state, which IS a thermal state at temperature T_H. The dissipative corrections then appear as modifications to the equilibrium Green's functions. This parallels how Jana-Loganayagam-Rangamani (JHEP 2020) used SK methods for Hawking physics in holographic settings via influence functionals.

**Alternative:** Use the Unruh-DeWitt detector framework to extract the effective temperature from the response function, bypassing the KMS assumption entirely.

### Obstacle 2: BECs at T ≈ 0 are superfluids with negligible normal fraction

**The problem:** The dissipative SK-EFT is for normal fluids with viscosity. At T ≈ 0, the BEC is a superfluid with no normal component — where does dissipation come from?

**Proposed solution:** At T = 0, dissipation arises from quantum effects: three-body losses, Beliaev damping (phonon → two phonons), and the anomalous density ⟨ψ̂ψ̂⟩ identified by Schützhold et al. as having no gravitational counterpart. The SK formalism can accommodate zero-temperature quantum dissipation through the quantum noise terms that persist even as T → 0 (the fluctuation-dissipation theorem becomes the quantum ground-state fluctuation relation). The CGL action has well-defined T → 0 limit with non-trivial ψ_a sector.

**Key insight:** The T → 0 limit of the SK formalism does NOT trivialize — the Keldysh function G_K = coth(ω/2T) × Im G_R → sign(ω) × Im G_R, encoding the vacuum fluctuation spectrum. Dissipative corrections enter through higher-derivative terms in the action that modify Im G_R.

### Obstacle 3: UV completion at the healing length

**The problem:** The EFT breaks down at k ~ 1/ξ. The Hawking temperature T_H ~ ℏκ/2π involves frequencies ω ~ κ, and the ratio κξ/c ~ 0.02–0.04 in current experiments — comfortably within the EFT regime. But the trans-Planckian problem means Hawking quanta originated from exponentially blue-shifted modes near the horizon, which DID pass through the UV cutoff.

**Proposed solution:** This is actually a feature, not a bug. The entire point of the EFT calculation is to demonstrate that the answer is insensitive to UV details — the dissipative correction δ_diss should depend only on the IR transport coefficients (γ₁, γ₂), not on the UV completion. This is the analog of the Corley-Jacobson result for dispersive corrections: T_H is universal at leading order. The dissipative calculation would extend this universality statement to include dissipation.

**Matching condition:** At k ~ 1/ξ, match the SK-EFT to the microscopic Bogoliubov theory. The Bogoliubov dispersion ω² = c²k² + ℏ²k⁴/4m² provides the matching coefficients for the higher-derivative terms in the EFT.

### Obstacle 4: Interpretation of SK doubled fields near the horizon

**The problem:** The ψ_a field (noise/response field) has no standard interpretation in the Hawking context. In equilibrium, ψ_a generates the response functions and encodes fluctuations. Near a horizon, the causal structure changes — what does the SK doubling mean when one branch may probe inside the horizon?

**Proposed solution:** The SK doubling naturally maps to the two-point function structure of Hawking radiation: the Hawking state has specific correlations between the exterior (where an observer sits) and the interior (the partner particle). The ψ_1, ψ_2 fields on the two SK branches can be identified with the two sides of the horizon in the near-horizon Rindler decomposition. This identification was made explicit by Jana-Loganayagam-Rangamani for holographic Hawking radiation. The analog gravity version should follow by replacing the gravitational horizon with the sonic horizon.

### Obstacle 5: The anomalous density has no gravitational counterpart

**The problem:** Schützhold et al. (2005) showed BEC backreaction involves both normal density m̃ = ⟨ψ̂†ψ̂⟩ AND anomalous density ñ = ⟨ψ̂ψ̂⟩, the latter having no gravitational analog. Any BEC-specific EFT must include terms coupling to ñ.

**Proposed solution:** In the SK formalism, the anomalous density appears through the Keldysh (statistical) Green's function G_K = −i⟨{ψ̂(x), ψ̂†(x')}⟩. The anomalous component is G_anom = −i⟨{ψ̂(x), ψ̂(x')}⟩ (without the dagger). Both are naturally encoded in the doubled SK framework — G_K from ⟨ψ_1 ψ_2⟩ correlators and G_anom from ⟨ψ_1 ψ_1⟩ (or ⟨ψ_2 ψ_2⟩) correlators. The SK formalism is therefore the natural language for INCLUDING the anomalous density, which has been omitted in all previous analytic treatments.

---

## 6. Expected Form of the Result

The main result should take the form:

**T_eff = T_H (1 + δ_diss + δ_disp + δ_cross)**

where:

- T_H = ℏκ/(2πk_B) is the standard Hawking temperature
- δ_disp ~ O((ξ/λ_H)²) is the known dispersive correction (Coutant-Parentani)
- **δ_diss ~ O(γ/(κξ²))** is the NEW dissipative correction, where γ is the phonon damping rate
- δ_cross is a cross-term between dispersion and dissipation

For a BEC with Beliaev damping rate γ_B ~ (na³)^{1/2} ω²/c (where a is the scattering length, n the density), the dissipative correction scales as:

δ_diss ~ (na³)^{1/2} (T_H/T_max)² ~ 10⁻⁶ to 10⁻⁴

in current experiments — comparable to or larger than the dispersive correction, but still below experimental sensitivity. However, in two-component spin-sonic systems (Berti et al. 2025), the spin-sound speed c_spin ≪ c_density dramatically enhances the ratio T_H/T_max, potentially making δ_diss experimentally accessible.

The sign of δ_diss is physically meaningful: if dissipation REDUCES T_eff, Hawking radiation is more robust than expected against UV modifications (good news for trans-Planckian problem); if it INCREASES T_eff, there is an anomalous heating effect from dissipative fluctuations.

---

## 7. Concrete Calculation Steps for a Postdoc

### Phase 1: Warmup (2–4 weeks)
1. Reproduce the Corley-Jacobson dispersive correction using WKB methods
2. Write the Son EFT L = P(X) for a BEC and verify the phonon dispersion
3. Write the CGL SK action for a superfluid at T = 0 in 1+1D

### Phase 2: Background (2–4 weeks)
4. Solve the 1D transonic background (Euler + continuity) for a step potential
5. Expand the SK action around this background to quadratic order
6. Identify the retarded and Keldysh propagator equations

### Phase 3: Core calculation (4–8 weeks)
7. Solve the retarded Green's function G_R near the horizon with dissipative terms (modified Heun equation)
8. Apply the KMS/FDR constraint to obtain G_K
9. Extract the effective temperature from the asymptotic Keldysh function (Bose-Einstein distribution fit)
10. Compute δ_diss as a function of the dissipative transport coefficients

### Phase 4: Physical interpretation (2–4 weeks)
11. Match the EFT coefficients to the microscopic Bogoliubov theory
12. Evaluate δ_diss numerically for Steinhauer's ⁸⁷Rb parameters and for Trento's ²³Na spin-sonic parameters
13. Compare with δ_disp to determine which correction dominates
14. Discuss implications for the trans-Planckian problem and for BEC experiment design

### Phase 5: Paper (2–4 weeks)
15. Write PRL (4 pages): announce the result, give the formula, evaluate for current and planned experiments
16. Write supplementary material: full derivation, comparison with dispersive corrections, discussion of anomalous density effects

**Total estimated time: 3–6 months for an experienced postdoc in EFT/condensed matter theory.**

---

## 8. Lean Formalization Blueprint

Three mathematical structures in this calculation are amenable to Lean 4 formalization (blueprint+sorry approach):

### Structure A: The acoustic metric theorem
**Statement in Lean:** For a barotropic, irrotational, inviscid fluid with velocity v(x) and sound speed c_s(x), the linearized phonon equation of motion is equivalent to the massless Klein-Gordon equation on a Lorentzian manifold with metric g_{μν} determined algebraically by (v, c_s, ρ).

**Formalization approach:** Define the fluid background as a record type with fields (v, c_s, ρ) satisfying the Euler and continuity equations. Define the acoustic metric in Painlevé-Gullstrand form. Prove that the linearized phonon EOM matches □_g π = 0. This is a purely algebraic verification — all steps are explicit linear algebra.

**sorry gaps:** The PDE well-posedness (existence/uniqueness of solutions) would require sorry; the algebraic identity is fully formalizable.

### Structure B: The SK doubling structure
**Statement:** Given an action I[ψ] with global U(1) symmetry, the SK doubled action I_SK[ψ_r, ψ_a] satisfying (i) I_SK[ψ_r, 0] = 0, (ii) Im I_SK ≥ 0, (iii) KMS symmetry under ψ_a → ψ_a + iβ∂_tψ_r, is uniquely determined at each order in the derivative expansion up to the transport coefficients.

**Formalization approach:** Encode the SK symmetry constraints as propositions on a polynomial ring of field monomials. The uniqueness at each derivative order is a finite-dimensional linear algebra problem: count independent structures, impose symmetry constraints, identify the free parameters.

**sorry gaps:** The derivative expansion convergence; the physical interpretation of the transport coefficients.

### Structure C: The Hawking temperature universality
**Statement:** For any UV modification of the phonon dispersion relation satisfying (i) subluminal or superluminal at high k, (ii) smooth in the adiabatic sense (D = κL/Λ ≫ 1), the effective temperature extracted from the asymptotic occupation number satisfies T_eff = T_H(1 + O(T_H/Λ)²).

**Formalization approach:** This is the Corley-Jacobson/Coutant-Parentani result. The proof uses WKB matching across the horizon, which is a combination of asymptotic analysis and connection formulas. The WKB matching can be formalized as algebraic manipulation of asymptotic series; the connection formula is a known property of the confluent Heun equation.

**sorry gaps:** The asymptotic validity of WKB (requires analysis that is partially in Mathlib but not complete for complex turning points).

**Estimated Lean effort for all three structures: 3–5 person-months, assuming familiarity with Mathlib. This fits within the 22–43 person-month total Lean budget estimated for the full program.**

---

## 9. Connections to the Broader Program

This paper connects to the fluid physics program in three ways:

**Immediate:** It demonstrates that the SK-EFT framework is the correct language for Layer 2 → Layer 3 matching in the hybrid architecture. If the calculation works for analog Hawking radiation, the same framework applies to any emergent geometry arising from a superfluid background.

**Medium-term:** The result speaks to the universality of Hawking radiation — the central conceptual question of analog gravity. If δ_diss is parametrically small (as expected), this strengthens the case that Hawking radiation is a robust consequence of horizon structure, not an artifact of the UV completion. This has direct implications for the trans-Planckian problem in quantum gravity.

**Long-term:** The SK methodology developed here can be extended to compute corrections to other analog gravity phenomena: superradiance (Torres-Weinfurtner), cosmological particle creation (Viermann et al.), and quasinormal modes. Each extension is a separate publication.

---

## 10. Key References (Ordered by Relevance to This Calculation)

**SK-EFT foundations:**
- Crossley-Glorioso-Liu, JHEP 2017 (arXiv:1511.03646) — complete SK-EFT for dissipative fluids
- Dubovsky-Hui-Nicolis-Son, PRD 2012 (arXiv:1107.0731) — non-dissipative fluid EFT
- Endlich-Nicolis-Porto-Wang, PRD 2013 (arXiv:1211.6461) — first-order dissipation
- Son, arXiv:hep-ph/0204199 — superfluid EFT L = P(X)
- Glorioso-Liu, JHEP 2018 (arXiv:1612.07705) — SK for superfluids
- Jain-Kovtun, JHEP 2024 (arXiv:2309.00511) — UV ambiguity in SK-EFT

**Analog Hawking radiation:**
- Unruh, PRL 1981 — original prediction
- Corley-Jacobson, PRD 1996 (arXiv:hep-th/9601073) — dispersive corrections
- Coutant-Parentani, PRD 2014 (arXiv:1402.2514) — broadened horizon paradigm
- Steinhauer, Nature 2019 — experimental measurement of T_H
- Balbinot-Ciliberto-Fabbri-Pavloff, arXiv:2509.09403 (2025) — backreaction equations

**SK + Hawking (in gravitational context):**
- Jana-Loganayagam-Rangamani, JHEP 2020 (arXiv:2003.03088) — SK influence functional for Hawking
- Loganayagam-Martin, arXiv:2404.xxxxx (2024) — unitary exterior EFT for Hawking

**BEC-specific:**
- Biondi, arXiv:2504.08833 (2025) — EFT for flowing BEC (no SK)
- Schützhold-Uhlmann-Xu-Fischer, PRD 2005 — anomalous density in backreaction
- Carusotto-Fagnocchi-Recati-Balbinot-Fabbri, NJP 2008 — robustness against temperature
- Berti et al., Comptes Rendus Physique 2025 — spin-sonic horizon blueprint
- Ciliberto-Balbinot-Fabbri-Pavloff, PRA 2025 — complete backreaction calculation

**Fracton SK-EFT (for architecture context):**
- Glorioso-Huang-Guo-Rodriguez-Nieva-Lucas, JHEP 2023 (arXiv:2301.02680)

---

*This roadmap contains sufficient technical detail for an experienced postdoc to begin the calculation immediately. The five obstacles are identified, proposed solutions sketched, and the expected form of the result estimated. The Lean formalization blueprint identifies three structures amenable to formal verification within the program's existing Lean budget.*
