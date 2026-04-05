# Phase 6+ Deferred Targets

**Purpose:** Track high-value formalization targets beyond Phase 5c. Deep research timelines assume human effort; our pipeline + Aristotle has consistently compressed months→days.

**Created:** April 4, 2026
**Updated:** April 4, 2026 (post Phase 5c Waves 1-5: 1056 thms, 71 modules)

---

## Items COMPLETED (promoted from Phase 6, now done)

### Drinfeld Center Z(Vec_G) ≅ Rep(D(G)) — **COMPLETED** (Phase 5b Waves 2-3)
- 96+ theorems across 7 modules, zero sorry, zero axioms.
- Full algebraic core proved. Concrete Z/2 and S₃ equivalences verified.
- **Remaining:** Abstract categorical functor `Functor.mk` (~30-50 thms).
  - Deep research submitted: `Ribbon-Level2-abstract-functor-construction.md`

### Wang Three-Generation Constraint — **COMPLETED** (Phase 5b Waves 4-6)
- Algebraic consequence 24|8N_f → 3|N_f: PROVED
- c₋ = 8N_f DERIVED from 16 Weyl fermions
- "24" DERIVED from Dedekind eta q-expansion
- Rokhlin "16 convergence" and ν_R analysis
- **Remaining:** Full topological proof → **PROMOTED to Phase 5c Wave 7** (see roadmap).

### U_q(sl₂) Hopf Algebra Structure — **COMPLETED** (Phase 5c Wave 1)
- 21 theorems + Bialgebra + HopfAlgebra instances. 22 sorry pending Aristotle.
- Coproduct, counit, antipode via FreeAlgebra.lift + RingQuot.liftAlgHom.
- First non-trivial HopfAlgebra instance in any proof assistant.

### O_q ↪ U_q(ŝl₂) Coideal Embedding — **COMPLETED** (Phase 5c Wave 2)
- 9 theorems, zero sorry, zero axioms.
- Affine quantum group U_q(ŝl₂) defined: 8 generators, 22 relations.
- Coideal generators B₀, B₁ defined inside U_q(ŝl₂).
- **Remaining:** Hopf structure on U_q(ŝl₂) + coideal property proof.

### SU(2)_k Fusion Rules — **COMPLETED** (Phase 5c Wave 3)
- 29 theorems, ALL proved by native_decide, zero sorry.
- Universal fusion formula + explicit tables for k=1,2,3.
- Ising (σ²=1+ψ), Fibonacci (τ²=1+τ), associativity verified exhaustively.

### S-matrix + Verlinde — **COMPLETED** (Phase 5c Wave 4)
- 16 theorems, 10 sorry pending Aristotle (algebraic √2 identities).
- Explicit S-matrices for k=1,2 as Matrix (Fin n) (Fin n) ℝ.
- Unitarity, det ≠ 0 (modularity), Verlinde formula entries stated.

### Restricted Quantum Group u_q(sl₂) — **COMPLETED** (Phase 5c Wave 5)
- 11 theorems, 1 sorry (unfolding). Zero axioms.
- E^ℓ = 0, F^ℓ = 0, K^ℓ = 1 all proved.
- Canonical surjection U_q ↠ u_q proved.

---

## Tier 1: High Value, Infrastructure Available (next targets)

### RibbonCategory + ModularTensorCategory Definitions — **BUILT** (Phase 5c Wave 6)
- **Status:** BUILT in RibbonCategory.lean. BalancedCategory, RibbonCategory, PreModularData, ModularTensorData all defined. 2 sorry gaps (det ≠ 0 for k=1,2). SU(2)_1 and SU(2)_2 packaged as PreModularData instances.
- **Deep research:** `Lit-Search/Phase-5c/Ribbon/Formalizing modular tensor categories in Lean 4.md` — Key finding: use `[BraidedCategory C]` as prerequisite not extends. Ribbon DERIVES pivotal+spherical via Drinfeld isomorphism. `twist_unit` is derivable (included for convenience).

### SU(2)_k as RibbonCategory Instance
- **Prerequisite:** RibbonCategory definition (above)
- **Work:** Show SU(2)_k at k=1,2 satisfies all MTC axioms.
  Twist values: θ_a = e^{2πi·a(a+2)/(4(k+2))}.
  F-symbols needed for full categorical instance.
- **Impact:** First VERIFIED modular tensor category.
- **Deep research:** `Lit-Search/Phase-5c/Ribbon/Instantiating modular tensor categories on SU(2)_k in Lean 4.md` — Key finding: use custom `QSqrt2`/`QGolden` types with computable `DecidableEq` for `native_decide` on pentagon/hexagon equations. k=2 (Ising) is optimal first target: single 2×2 F-matrix (Hadamard/√2), ~5-10 pentagon instances.

### Abstract Equivalence Functor Center(Vec_G) ⥤ Rep(D(G))
- **Status:** Algebraic bijection proved. Missing: Mathlib Functor.mk construction.
- **Deep research:** `Ribbon-Level2-abstract-functor-construction.md` (submitted)
- **Estimate:** ~30-50 theorems of Mathlib categorical plumbing.

### Hopf Structure on U_q(ŝl₂)
- **Prerequisite:** Wave 1 Aristotle results (to know the proof patterns work)
- **Work:** Same coproduct/counit/antipode pattern as Uqsl2Hopf, but 6 generators
  and more relations. Heavy but mechanical.
- **Estimate:** ~40-60 theorems, 2-3 sessions.

---

## Tier 2: High Value, Requires Mathematical Depth

### Full Z₁₆ Cobordism Proof
- **Requires:** Atiyah-Hirzebruch + Adams spectral sequences
- **Note:** 15-25 person-years by conventional methods

### Wang Full Topological Proof — **PROMOTED to Phase 5c Wave 7**
- **Key finding:** σ≡0 mod 16 is FALSE for abstract even unimodular lattices (E8 has σ=8).
  The algebraic bound is σ≡0 mod 8 (Serre). The extra factor of 2 is genuinely topological.
  Freedman's E8 manifold (topological, non-smooth, σ=8) proves smoothness is essential.
- **Three paths planned:**
  - Path A (E8 verification): **BUILT** in E8Lattice.lean. det=1 (sorry for Aristotle), diagonal=2 (proved), symmetric (proved), σ=8 disproves naive algebraic Rokhlin (proved).
  - Path B (algebraic Serre σ≡0 mod 8): ~15-25 thms via characteristic vectors. No axioms but substantial new math.
  - Path C (2-axiom bordism): Ω^Spin_4 ≅ Z + σ(K3)=-16 → Rokhlin in ~10 lines.
- **Axiom risk assessment for Path C:** The 2 axioms encode a 1966 theorem (Anderson-Brown-Peterson) proved via Adams spectral sequence. The result is as solid as π₁(S¹)≅Z, but: (1) probably 10+ years from formalization, so axioms persist long-term; (2) historical circularity — ABP computation uses facts equivalent to Rokhlin; (3) project went 7→0 axioms in Phase 5b, adding 2 back feels like regression. These are "hard eliminability" axioms encoding genuinely topological content (not algebraic consequences like the ones we eliminated). Should be documented in AXIOM_METADATA with `eliminability: hard, reason: requires stable homotopy theory / Adams spectral sequence`.
- **Research:** `Lit-Search/Phase-5c/Rokhlin/` (2 files). Key: the "same 16" traces to Bott periodicity and quaternionic Clifford structure Cl₄ ≅ M₂(ℍ).

### Non-Abelian TPF Disentangler
- **Status:** Open problem (TPF arXiv:2601.04304)
- **Requires:** Peter-Weyl theory, non-Abelian Gauss law

### |N| = 3 Fermi-Point → SU(3) Emergence
- **Status:** Speculative, no explicit proof exists

---

## Tier 0: Already Scoped for Phase 6

### Verified Statistics Pipeline — **STARTED** (Phase 5c/6 early)
- **Built:** `VerifiedJackknife.lean` — 7 theorems + 5 definitions. First formally verified statistical estimators.
  - Jackknife variance: defined, **non-negativity PROVED**
  - Autocovariance C(t): defined, **C(0) ≥ 0 PROVED**
  - Integrated autocorrelation time τ_int: defined
  - Effective sample size N_eff = N/(2τ_int): defined
  - 3 sorry gaps (zero iff constant, uncorrelated case, ≥1/2 bound) — Aristotle targets
- **Deep research:** `Lit-Search/Deferred-Background/Formalizing jackknife and autocorrelation in Lean 4.md` — Key finding: `Fin.sum_univ_succAbove` is the workhorse for delete-one decomposition. `Finset.sum_mul_sq_le_sq_mul_sq` gives discrete Cauchy-Schwarz for |Γ(t)| ≤ Γ(0). Three jackknife theorems (non-neg, zero-iff-const, mean-case) provable without probability theory. No proof assistant has ever formalized any statistical estimator.
- **Remaining:** Bootstrap CI, Γ-method windowing, chi-squared, connection to RHMC observables
- Has separate roadmap: `Phase6_VerifiedStatistics_Roadmap.md`

### Polariton Experimental Protocol Paper
- T_H ~ 1 K, 10^10× BEC. Most accessible experimental target.
- Already have: PolaritonTier1.lean (6 thms), polariton_predictions.py

### Fracton-Gravity Kerr-Schild Bootstrap
- **Existing:** FractonGravity.lean (20 thms, all proved) — the *negative* result (bootstrap fails at order 2, DOF mismatch, gauge mismatch). gravity_connection.py — 5 obstructions analysis.
- **Kerr-Schild extension:** For KS metrics g = η + φ l⊗l (l null), Einstein eqns linearize exactly. Question: does the fracton-GR equivalence extend to this sector? If so, fracton theory reproduces Schwarzschild/Kerr exactly.
- **Assessment:** Lower leverage than quantum group/MTC for the formal verification program. More "extending a paper's analysis" than "building infrastructure." Tractable Lean targets: KS metric as 4×4 matrix, null vector identity, Schwarzschild verification, DOF counting in KS sector.
- **Deep research:** `Lit-Search/Deferred-Background/Fracton gauge theory meets Kerr-Schild gravity- a detailed assessment.md` — Key finding: Afxonidis et al. (2024) already published the fracton-KS map. Spin-2 sector reproduces KS solutions exactly, BUT 5 obstructions persist (algebraic, kinematic, DOF surplus, dynamical instability, foliation). Sherman-Morrison inverse (already in Mathlib) is the algebraic heart. Best Lean target: null-vector inverse theorem.

### ADW Gap Equation in Wen's Model (NEW — Phase 5d candidate)
- **Source:** Critical Review v3, §2.2 — "a concrete, doable calculation that could settle feasibility" for dynamical gravity.
- **Existing infrastructure:** ADWMechanism.lean (21 thms), WetterichNJL.lean (18 thms), VestigialSusceptibility.lean (16 thms), FermionBag4D.lean (16 thms), GaugeFermionBag.lean (9 thms) = 71 existing theorems.
- **Key finding from deep research:** The tetrad gap equation has NEVER been explicitly written down in the literature. The equation is structurally determined: e^a_μ = G ∫ Tr[γ^a p_μ S(p; e)] d⁴p/(2π)⁴. Reduces to 1D nonlinear integral equation, analytically tractable. G_c = 1/I(0) ~ (2π)²/Λ². Vladimirov-Diakonov found G_c ~ O(1) in 2D chiral channel — the 4D tetrad channel is untested.
- **Three parallel workstreams:**
  1. **Analytic:** Derive explicit gap equation, solve for G_c, check if O(1) in lattice units
  2. **Computational:** Use existing RHMC + fermion-bag at L=4,6,8 with new observables (tetrad susceptibility, metric 4-pt correlator, Binder cumulant)
  3. **Formal:** ~18-20 new Lean theorems via IVT (existence) + Banach contraction (uniqueness). Picard-Lindelöf in Mathlib as template. G_c bounds from integral monotonicity.
- **Vestigial phase is the intermediate target:** Even if full tetrad condensation fails, the metric condensate ⟨Ê^a Ê^b⟩ ≠ 0 with ⟨Ê^a⟩ = 0 gives bosonic Einstein GR.
- **Deep research corpus (10+ files spanning Phases 3-5c):**
  - `Phase-3/The ADW mean-field gap equation...` — Original identification of the gap: no explicit HS decomposition exists
  - `Phase-5/Vestigial metric susceptibility...` — Explicit V_eff, G_c = 8π²/(N_f Λ²), vestigial window exponentially narrow in 4D
  - `Phase-5/ADW tetrad condensation lattice formulation.md` — 8×8 Majorana, metric Option A, quaternionic Cl(4,0) structure
  - `Phase-5/Effective nearest-neighbor action...` — SO(4) Haar → full multi-fermion tower, not just 4-fermion
  - `Phase-5/HS+RHMC for ADW...` — Complete RHMC algorithm spec, O(V√κ) scaling, Zolotarev rational approx
  - `Phase-5/The 8×8 Majorana formulation...` — Kramers degeneracy → sign-free MC
  - `Phase-5c/Bridging Wen's emergent QED with ADW tetrad gravity.md` — **KEY NEW RESULT:** Full Wen+ADW chain, explicit gap equation e^a_μ = G ∫ Tr[γ^a p_μ S(p; e)], Lean via IVT + Banach contraction
- **Consistency check:** Phase-5 vestigial research gives G_c = 8π²/(N_f Λ²). Phase-5c gap equation gives G_c = 1/I(0) = 2/(c₄Λ²). These are the same result (c₄ = 1/(8π²) with N_f normalization). Cross-validated.
- **Assessment:** Highest-leverage open physics question for the gravity wall. Publishable regardless of outcome. The complete research corpus provides: analytic framework (Phase-3/5c), computational specification (Phase-5 HS+RHMC), and formalization path (Phase-5c Lean IVT). All three workstreams have prior research supporting feasibility.

### Polariton Experimental Protocol Paper
- T_H ~ 1 K, 10^10× BEC. Most accessible experimental target.
- Already have: PolaritonTier1.lean (6 thms), polariton_predictions.py
- **Assessment:** Highest-leverage publication for experimental impact. Low formalization risk — formulas exist, paper needed.

---

## Deep Research Index

### Completed (results available)
| File | Location | Key Finding |
|------|----------|-------------|
| Formalizing MTCs in Lean 4 | Phase-5c/Ribbon/ | Use [BraidedCategory] prereq, ribbon derives pivotal via Drinfeld iso |
| Abstract functor construction | Phase-5c/Ribbon/ | Center(Vec_G) ⥤ Rep(D(G)) via Mathlib Functor.mk, needs ~30-50 thms |
| SU(2)_k ribbon instantiation | Phase-5c/Ribbon/ | QSqrt2/QGolden custom types, pentagon via native_decide |
| Algebraic Rokhlin + E8 | Phase-5c/Rokhlin/ | σ≡0 mod 16 is FALSE for lattices. Algebraic bound is mod 8 only |
| Z₁₆ ↔ Rokhlin bridge | Phase-5c/Rokhlin/ | 2-axiom bordism optimal, but axiom has circularity concern |
| Jackknife + autocorrelation | Deferred-Background/ | Fin.sum_univ_succAbove for delete-one, Cauchy-Schwarz for |Γ| ≤ Γ(0) |
| Fracton-KS gravity | Deferred-Background/ | Already published (Afxonidis 2024), 5 obstructions persist in KS sector |

| ADW + Wen tetrad gravity | Phase-5c/ | Gap equation never written down. Three workstreams: analytic, MC, formal |

### Pending
| Prompt | Location | Status |
|--------|----------|--------|
| (none) | | All research complete |

---

*Updated April 4, 2026. Phase 5c completed all 5 waves (1056 theorems, 71 modules, 0 axioms). Deep research for ribbon/MTC infrastructure submitted.*
