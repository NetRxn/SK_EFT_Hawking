# Fracton Hydrodynamics as Alternative Layer 2: Assessment

**Phase 4, Item 2B | Prepared 2026-03-25**

---

## 1. Executive Summary

Fracton hydrodynamics provides a rigorous alternative Layer 2 hydrodynamic framework that preserves dramatically more UV (microscopic) information than standard Navier-Stokes hydrodynamics. The string-membrane-net to fracton to SK-EFT chain is now mathematically rigorous for Type-I fracton models built from Abelian p-string condensation.

**Key quantitative findings:**

| System | Conserved charges | Info retention | Transport coefficients |
|--------|------------------|----------------|----------------------|
| Standard NS (3D) | 5 (= d + 2) | O(1) parameters | 3 (eta, zeta, kappa) |
| Fracton dipole (3D) | 8 (= C(4,3) + 3 + 1) | O(L) bits (HSF) | 6 (4 diss + 2 Hall) |
| Fracton quadrupole (3D) | 14 (= C(5,3) + 3 + 1) | O(L) bits (HSF) | >6 |
| Fracton n-pole (3D) | C(n+3,3) + 4 | O(L^d) bits (HSF) | grows with n |

**Central assessment on gauge information:** Fracton hydrodynamics preserves non-Abelian gauge information **partially** -- through fragmentation patterns and multipole structure, NOT through conventional gauge field transport. The gauge erasure theorem still blocks conventional transport, but subsystem symmetries evade the GKSW commutativity argument, providing a genuine structural loophole.

---

## 2. The Coarse-Graining Chain

### 2.1. String-Membrane-Net to Fracton

The Gorantla-Prem-Tantivasadakarn-Williamson construction (PRB 112, 125124, 2025) provides a non-perturbative, gap-preserving algebraic map:

1. **Input:** Stacked 2+1D string-net models (BF theories) on three orthogonal orientations
2. **Gauge:** The diagonal 1-form symmetry A_diag^(1)
3. **Output:** Foliated field theory of the X-Cube model (Type-I fracton)
4. **Validity:** Mathematically rigorous for all Abelian p-string condensation

The procedure is exact for Type-I fractons (X-Cube, checkerboard). Type-II fractons (Haah's code) with fractal operators do not fit this coupled-layer picture.

### 2.2. Fracton to SK-EFT

The Glorioso-Huang-Lucas SK-EFT (JHEP 2023) constructs the complete effective theory with:

- **Field content:** Coordinate fields X^i_s, dipole vector fields phi^s_i, charge scalar phi^s, all SK-doubled to r and a components
- **Key commutator:** [D, P] = iQ forces momentum susceptibility chi ~ n^2/k^2
- **Transport coefficients:** 4 dissipative (s1, s2, t1, t2) + 2 Hall-like (d1, d2) + 4 thermodynamic at leading order
- **SK axioms:** All three (normalization, positivity, KMS) satisfied identically to standard SK-EFT
- **Dispersion:** Quadratic sound omega = c_2 k^2 with subdiffusive damping omega ~ k^4

### 2.3. Higher Multipole Extension

The Guo-Glorioso-Lucas MSR formulation (PRL 2022) generalizes to n-pole conservation:

- n-pole conservation forces H_MSR to depend on d^{n+1}_x pi
- Dispersion: omega ~ k^{n+1}
- Upper critical dimension: d_c = 2(1+n) for n even, 2n for n odd
- d_c grows without bound, so fluctuations are always strong for high multipoles in physical dimensions

---

## 3. Information Retention Analysis

### 3.1. Exact Conserved Charges

Standard NS hydro: d + 2 conserved charges (energy + d momenta + particle number).

Fracton hydro with n-th multipole conservation: total multipole charges = C(n + d, d), growing as a polynomial in both n and d. Including momentum and energy:

- n=0 (charge only): d + 2 (same as standard)
- n=1 (dipole): C(1+d, d) + d + 1
- n=2 (quadrupole): C(2+d, d) + d + 1

### 3.2. Harmonic Moments (2D)

Hart-Lucas-Nandkishore (PRE 2022) proved that isotropic dipole-conserving fluids in 2D conserve infinitely many harmonic multipole charges Q_m = integral (x + iy)^m rho. These are exact at linear level; nonlinear corrections are dangerously irrelevant (power-law decay with increasing exponent).

### 3.3. Hilbert Space Fragmentation

The dominant information retention mechanism:

- **1D spin-1 model (Sala et al.):** Frozen states grow as ~(4/3)^L, giving >= L * log2(4/3) ~ 0.415L bits
- **X-Cube model (3D):** 6L - 3 logical qubits, scaling as O(L)
- **General:** O(L^d) bits for d-dimensional systems with subsystem symmetry constraints
- **Strong fragmentation:** dim(K_max) / dim(H) -> 0 exponentially with system size

### 3.4. Comparison Summary

| d | n | Standard charges | Fracton charges | Charge ratio | HSF bits (L=100) |
|---|---|-----------------|-----------------|--------------|------------------|
| 1 | 1 | 3 | 3 | 1.0 | 41.5 |
| 2 | 1 | 4 | 7 | 1.75 | 100 |
| 3 | 1 | 5 | 8 | 1.6 | 597 |
| 3 | 2 | 5 | 14 | 2.8 | 597 |
| 3 | 5 | 5 | 60 | 12.0 | 597 |
| 3 | 10 | 5 | 290 | 58.0 | 597 |

At large L, Hilbert space fragmentation dominates the multipole charge count: O(L^d) >> O(1) polynomially.

---

## 4. Gauge Information Assessment

### 4.1. The Gauge Erasure Theorem (Recap)

From Phase 3 (Paper 3): non-Abelian gauge DOF cannot survive standard hydrodynamization because:

1. Higher-form symmetries must be Abelian (GKSW: codimension >1 operators commute)
2. Non-Abelian groups have at most discrete Z_N center symmetry
3. Discrete breaking produces domain walls, not Goldstone bosons
4. No hydrodynamic modes for non-Abelian gauge DOF

### 4.2. The Fracton Loophole

Fracton systems present a **genuine structural loophole** through three mechanisms:

**Mechanism 1: Subsystem symmetry evasion.** Subsystem symmetries are NOT higher-form symmetries. Their operators are rigid and geometry-dependent, not topologically deformable. The GKSW commutativity argument applies to topologically deformable operators only. Therefore subsystem symmetry operators on intersecting planes need not commute.

**Mechanism 2: Fragmentation protection.** Hilbert space fragmentation prevents full exploration of configuration space. Standard thermalization assumptions (ergodic hypothesis) fail. Immobile fractons cannot rearrange to reach maximum-entropy configurations, protecting position-dependent degeneracies.

**Mechanism 3: Non-Abelian fracton models.** Bulmash-Barkeshli (PRB 2019) constructed non-Abelian fractons from gauging Z_2 layer-exchange of doubled X-Cube models. These have position-dependent degeneracies -- fundamentally different from conventional non-Abelian anyons. Wang-Xu-Yau (PRR 2021) built continuous non-Abelian tensor gauge theories with non-commutative structure outside the Yang-Mills paradigm.

### 4.3. Critical Gaps

1. **No finite-temperature analysis:** Non-Abelian fracton models have not been studied at finite T. The survival mechanism is demonstrated at T=0 but unproven at finite T.
2. **Not Yang-Mills gauge structure:** The Wang-Xu-Yau non-Abelian tensor gauge structure is non-commutative but not an ordinary Lie group. It sits outside the Yang-Mills paradigm.
3. **No fracton hydrodynamics for non-Abelian case:** Formulating non-Abelian fracton hydrodynamics analogous to the Abelian Glorioso-Huang-Lucas theory remains an open problem.

### 4.4. Verdict

**Fracton hydrodynamics preserves non-Abelian gauge information PARTIALLY.**

The information is encoded as fragmentation patterns and multipole structure, NOT as conventional gauge field degrees of freedom. This is a fundamentally different encoding than standard gauge transport. The loophole is conceptually compelling, supported by lattice model evidence (Bulmash-Barkeshli, Sala et al., Adler et al. experiments), but mathematically unproven as a mechanism for non-Abelian survival in the finite-temperature hydrodynamic limit.

---

## 5. Comparison: Fracton Layer 2 vs Standard Layer 2

| Feature | Standard NS Layer 2 | Fracton Layer 2 |
|---------|---------------------|-----------------|
| Conserved charges | O(d+2) | O(infinity) with HSF |
| Sound dispersion | omega ~ k (linear) | omega ~ k^2 (quadratic) |
| Damping | omega ~ k^2 (diffusive) | omega ~ k^4 (subdiffusive) |
| Transport coefficients | 3 at 1st order | 6 at leading order |
| SK axioms satisfied | Yes | Yes (identical structure) |
| Non-Abelian gauge info | Erased (gauge erasure theorem) | Partially preserved (fragmentation) |
| Experimental evidence | Extensive | Emerging (2024-2025 HSF observations) |
| UV/IR decoupling | Clean (EFT standard) | Problematic (Seiberg-Shao UV/IR mixing) |
| Lorentz symmetry | Compatible | Requires Aristotelian geometry |

---

## 6. Connection to Project Architecture

### 6.1. Relation to Existing Modules

- **`src/gauge_erasure/`:** The gauge erasure theorem established in Phase 3 is the baseline that fracton Layer 2 modifies. Standard hydro erases non-Abelian DOF; fracton hydro preserves more, but through a different mechanism.
- **`src/second_order/`:** The SK-EFT counting formulas (floor((N+1)/2) + 1) do not have a simple analog for fracton SK-EFT because the transport tensor carries two types of indices.
- **`src/core/constants.py`:** Physical constants are not directly relevant (fracton analysis is structural/algebraic, not numerical).

### 6.2. Module Structure

```
src/fracton/
    __init__.py                 # Module init with all public exports
    sk_eft.py                   # SK-EFT structure: symmetry, transport, action, dispersion
    information_retention.py    # Information comparison: standard vs fracton hydro
```

### 6.3. Future Directions (Phase 4 Waves 3-4)

- **3A (Fracton-Gravity Kerr-Schild):** Uses the fracton gauge theory from sk_eft.py to investigate the Pretko correspondence with linearized GR.
- **3B (Non-Abelian Fracton Hydro):** Extends the gauge information assessment to investigate whether Wang-Xu-Yau structures are Yang-Mills compatible.

---

## 7. Experimental Status

The 2024-2025 period saw fracton signatures confirmed across four platforms:

1. **Cold bosons (87Rb, MPQ Munich):** First 2D HSF observation (Nature 2024)
2. **Superconducting qubits:** 24-transmon ladder (PRX Quantum 2025)
3. **Rydberg atom arrays:** 57-75 atom HSF + many-body scars (PRX 2025)
4. **Untilted Bose-Hubbard (Yb):** HSF from strong interactions alone (Science Advances 2025)

No experiment has yet realized genuine fracton topological order (X-Cube, Haah's code). The 3D qubit connectivity required remains beyond current hardware.

---

## 8. References

1. Gorantla-Prem-Tantivasadakarn-Williamson, PRB 112, 125124 (2025)
2. Glorioso-Huang-Lucas, JHEP 05, 022 (2023)
3. Guo-Glorioso-Lucas, PRL 129, 150603 (2022)
4. Sala-Rakovszky-Gopalakrishnan-Knap-Pollmann, PRX 10, 011047 (2020)
5. Hart-Lucas-Nandkishore, PRE 105, 044103 (2022)
6. Bulmash-Barkeshli, PRB 100, 155146 (2019)
7. Wang-Xu-Yau, PRR 3, 013185 (2021)
8. Pretko, PRD 96, 024051 (2017)
9. Gaiotto-Kapustin-Seiberg-Willett, JHEP (2015)
10. Adler et al., Nature 636, 80-85 (2024)
11. Stephen-Hart-Nandkishore, PRL 132, 040401 (2024)
12. Feldmeier et al.: fracton hydrodynamics breakdown below d=4
