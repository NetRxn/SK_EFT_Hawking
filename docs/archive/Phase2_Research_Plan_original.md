# SK-EFT Phase 2: Research Plan

## Scope

Phase 2 extends the Phase 1 result (δ_diss ~ Γ_H/κ, formally verified, PRL-ready) in two directions. The paper topic will crystallize as the work develops.

### Direction A: Full WKB Derivation (Companion Paper)

**Goal:** Derive δ_diss from first principles via WKB mode analysis through the dissipative horizon.

**What Paper 1 defers:** The correction formula δ_diss ~ Γ_H/κ is stated as a scaling result in Paper 1. The full derivation — solving the modified mode equation, matching across the horizon, extracting the Bogoliubov coefficients — is deferred. This companion paper provides that derivation.

**Key steps:**
1. Modified dispersion relation with SK-EFT dissipation: ω² = c_s² k² F(k²/Λ²) + i γ_eff ω k²
2. WKB mode functions in asymptotic regions
3. Connection formula across the dissipative horizon (complex turning point)
4. Bogoliubov coefficients → T_eff decomposition
5. Exact correction functions δ_disp(ω), δ_diss(ω), δ_cross(ω)
6. Numerical validation against Macher-Parentani (2009)

**Lean targets:**
- `WKBAnalysis.lean`: WKB mode structure, turning point theorem, connection formula algebraics
- Aristotle: prove the turning point shift is O(γ/κ)

**References:** Corley-Jacobson (1996), Coutant-Parentani (2014), Macher-Parentani (2009)

### Direction B: Second-Order SK-EFT

**Goal:** Extend the SK-EFT to second order in the derivative expansion.

**Key questions:**
1. How many transport coefficients at second order? (First order: 2. Second order: N = ?)
2. Does positivity + KMS → uniqueness still hold? (i.e., is N finite and small?)
3. Does the correction become frequency-dependent at second order?
4. Are there qualitatively new effects (spectral shape distortion)?

**Key steps:**
1. Enumerate all second-order monomials in 1+1D
2. Impose normalization, positivity, KMS
3. Count free parameters → second-order transport coefficients
4. Compute δ_diss^(2)(ω) — frequency-dependent correction

**Lean targets:**
- `SecondOrderSK.lean`: SecondOrderCoeffs, secondOrder_uniqueness
- Aristotle: prove the parameter count and FDR at second order

**References:** Crossley-Glorioso-Liu (2017), Jain-Kovtun (2024)

---

## Shared Infrastructure

**Lean project:** `../SK_EFT_Hawking_Paper/lean/SKEFTHawking/`
- All Phase 1 theorems (14/14 proven, zero sorry)
- New Phase 2 modules added here: `WKBAnalysis.lean`, `SecondOrderSK.lean`
- Same Mathlib pin (commit 8f9d9cff), same Lean toolchain (4.28.0)

**Python bridge:** `src/phase1_bridge.py` imports Phase 1 modules:
- `BECParameters`, `TransonicBackground`, experiment factories
- `AristotleRunner`, `SORRY_GAPS`

**Aristotle:** Same API key and CLI infrastructure as Phase 1.

---

## Key Physics (Inherited from Phase 1)

T_eff = T_H(1 + δ_disp + δ_diss + δ_cross)

- T_H = κ/(2π) — standard Hawking temperature
- δ_disp = O(D²) where D = κξ/c_s — dispersive correction (Corley-Jacobson)
- δ_diss = Γ_H/κ — dissipative correction (Paper 1 result)
- δ_cross = δ_disp · δ_diss — subdominant
- Γ_H = 1.1 · γ_Bel, γ_Bel = √(na_s³) · κ²/c_s — Beliaev damping
- Spin-sonic enhancement: × (c_density/c_spin)² ≈ 100
- FirstOrderKMS: algebraic FDR on 9 first-order coefficients → 2 free params
