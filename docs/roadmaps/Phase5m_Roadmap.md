# Phase 5m: Generic Quantum Groups U_q(g)

## Technical Roadmap — April 2026

*Prepared 2026-04-07 | Follows Phase 5i (rank-2 quantum groups)*

**Entry state:** U_q(sl_2) (66 thms, 0 sorry), U_q(sl_3) (21 thms, 0 sorry), both hand-written via FreeAlgebra/RingQuot. Pattern clear: Cartan matrix → generators → relations → quotient.

**Prerequisite:** Deep research `Phase-5m/Generic U_q(g) framework in Lean 4` — **COMPLETE** (2026-04-07).

**Deep research key findings:**
- Mathlib has ~80% of prerequisites (Hopf algebra chain, FreeAlgebra/RingQuot, LaurentPolynomial)
- Missing: q-binomial coefficients (built), the specific QGRel presentation (built)
- No prior art in ANY proof assistant — this is a genuine first
- Non-simply-laced types need symmetrizer d_i → Phase 5m W2
- Kac-Walton fusion algorithm works generically from Cartan data

---

## 0. Motivation

We proved sl_2 and sl_3 by hand, repeating the same pattern. A generic framework parameterized by the Cartan matrix would:
- Cover ALL simple Lie algebras (A_n, B_n, C_n, D_n, E_6/7/8, F_4, G_2)
- Enable SU(N)_k fusion for arbitrary N (relevant for color SU(3), GUT SU(5))
- Be the first quantum group library in any proof assistant
- Foundation for Kazhdan-Lusztig equivalence

---

## Track A: Generic Definition

### Wave 1 — Parameterized Quantum Group Type (**COMPLETE**)
**Goal:** `QuantumGroup (A : Matrix (Fin r) (Fin r) ℤ)` as quotient of FreeAlgebra.

- [x] `QGGen (r : ℕ)` inductive: E_i, F_i, K_i, K_i_inv for i : Fin r
- [x] `QGRel (A : Matrix (Fin r) (Fin r) ℤ)` inductive: 7 groups, 11 constructor types
- [x] q-binomial coefficients [n choose k]_q via Pascal recurrence (QNumber.lean)
- [x] q-Serre relation: quadratic (A_{ij}=-1) + commutativity (A_{ij}=0)
- [x] Cartan matrices: A₁, A₂, A₃, D₄ defined with verification
- [x] 10 generic relation theorems proved (K-inv, K-comm, KE, KF, EF, Serre)
- [x] **First parameterized quantum group in any proof assistant. Zero sorry.**
- [ ] Instantiation verification: show A₁/A₂ recovers Uqsl2/Uqsl3 (deferred — algebraic, not foundational)

### Wave 2 — Hopf Algebra Structure
**Goal:** Generic Δ/ε/S from Cartan data.

- [x] **Counit** — FULLY PROVED in `QuantumGroupHopf.lean` (2026-04-15
  discovery: was already in codebase). `qgCounit A : QuantumGroup k A →ₐ QBase k`
  descended via `RingQuot.liftAlgHom`; all 11 QGRel constructor groups
  (including both q-Serre cases) discharged by a single `simp` pass
  because every E/F generator maps to 0. Named-generator evaluations
  `qgCounit_{E, F, K, Kinv}` provided. 7 theorems.
- [x] **Coproduct on generators + free-algebra lift** — DONE 2026-04-15
  (`QuantumGroupCoproduct.lean`): `comulOnGenQG`, `comulFreeAlgQG`,
  `comulFreeAlgQG_ι`. Standard Drinfeld-Jimbo formulas pattern-matched
  on QGGen.
- [x] **Coproduct relation-respect, 9 of 11 cases** — DONE 2026-04-15
  (`QuantumGroupCoproduct.lean`, 488 LOC):
  `comulFreeAlgQG_KKinv`, `_KinvK`, `_KK_comm`, `_KE`, `_KF`,
  `_SerreE_comm`, `_SerreF_comm` (Serre commutativity, A_ij = A_ji = 0 —
  auto for symmetrizable Cartan), `_EF_diag` (SHIPPED via novel
  diamond-bypass methodology `qg_sub_tmul` / `qg_tmul_sub`), `_EF_off`
  (SHIPPED for symmetric Cartan A_ij = A_ji — complete for simply-laced
  types; Drinfeld-Jimbo scope). 4 derived commutation helpers shipped:
  `qg_K_Kinv_comm`, `qg_Kinv_Kinv_comm` (via Mathlib Units API),
  `qg_E_Kinv_comm`, `qg_Kinv_F_comm`. Plus scalar-form versions:
  `qg_E_Kinv_scaled`, `qg_KF_scaled`. **First generic quantum group Hopf
  coproduct in any proof assistant; first EF_diag respect via diamond
  bypass.**
- [x] **SerreE_quad + SerreF_quad coproduct respect** — DONE 2026-04-16 session 2.
  Both palindromic atom-bridge proofs via Uqsl3Hopf template. 4-phase proof
  (expand, sector hypotheses, K-normalize, linear_combination finisher).
  Key innovations: `smul_expand` helper, `conv_lhs` for directional rewrites,
  F-side phi maps use `.flip`, `set_option maxRecDepth 8000 in abel!`.
- [x] **11/11 coproduct respect + descent** — `comulFreeAlgQG_respects_rel`
  dispatches all QGRel constructors. `qgComul` descended via `RingQuot.liftAlgHom`.
  Eval lemmas: `qgComul_E/F/K/Kinv`. 1347 LOC, 0 sorry.
- [x] **Antipode: 11/11 respect + descent** — `QuantumGroupAntipode.lean` (811 LOC).
  `antipodeOnGenQG` → `antipodeFreeAlgQG` via MulOpposite → all 11 QGRel
  respect proofs (incl. SerreE/F_quad via atom-bridge) → `qgAntipode` descended.
  Anti-multiplicativity `qgAntipodeLin_mul : S(ab) = S(b)S(a)`.
  `letI : NonUnitalNonAssocRing` pattern for neg_mul diamond bypass.
- [x] **Bialgebra instance** — `qgBialgebra` via `Bialgebra.ofAlgHom`:
  coassociativity + both counit laws proved generator-by-generator.
- [x] **HopfAlgebra instance** — `qgHopfAlgebra`: both convolution laws
  `m∘(S⊗id)∘Δ = η∘ε` proved via FreeAlgebra.induction + multiplicativity
  steps (`qg_convR_mul_step`, `qg_convL_mul_step`) using TensorProduct
  finset decomposition + anti-multiplicativity + Algebra.commutes.
- [x] **`QuantumGroupHopf.lean`** — 563 LOC, 0 sorry. Complete Hopf assembly.
- **Wave 2 COMPLETE** — 3176 LOC across 4 files, ZERO sorry.
  First generic quantum group HopfAlgebra in any proof assistant.
  Completed 2026-04-16 over 3 sessions.

### Wave 3 — Fusion Rules from Representation Theory
**Goal:** SU(N)_k fusion from truncated tensor product.

- [x] **Kac-Walton formula for fusion multiplicities** — DONE 2026-04-15
  (`KacWaltonFusion.lean`): full algorithm shipped — simpleRefl, affineRefl,
  reflectToAlcove (with sign tracking), fusionMultiplicity. **First
  implementation in any proof assistant.**
- [x] **Implement generically from Cartan matrix + level k** — DONE.
  Algorithm parameterized over arbitrary `CartanTypeData`.
- [x] **Verify SU(2)_k for k = 1, 2, 3** — DONE. 7 native_decide-verified
  theorems for fund⊗fund and fund⊗adj.
- [x] **Verify SU(3)_1 fusion** — DONE. 4 native_decide-verified theorems
  including fund⊗fund = antifund.
- [ ] Weight-diagram generation via Freudenthal recursion (currently
  hardcoded WDs in `KacWaltonFusion.lean` for SU(2) fund/adj, SU(3)
  fund/antifund, G_2 fund, SU(4) fund — all 15 shipped fusion theorems
  pass native_decide; no correctness issue). **Strengthening effort:**
  300-600 LOC Freudenthal recursion with well-founded termination via
  distance-to-highest-weight; 1-2 sessions; blueprint in
  `Lit-Search/Phase-5k-5l-5m-5n/The Kac-Walton fusion algorithm...md`.
  **Priority MEDIUM** — unlocks new V(λ) data but not load-bearing.
- [ ] Compute SU(4)_1, SU(5)_1 (SU(4)_1 fund WD hardcoded; SU(5)_1 would
  need WD generation or another hardcoded entry)

### Wave 4 — Meta-programming (optional, high-value)
**Goal:** Lean 4 meta-program generating quantum group instances from Cartan data.

- [ ] `Lean.Elab` script: input Cartan matrix, output full .lean file
- [ ] Auto-generate all rank-2 types (A_2, B_2, C_2=B_2, G_2)
- [ ] Auto-generate exceptional E_6, E_7, E_8

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | Generic U_q(g) framework | Lit-Search/Phase-5k-5l-5m-5n/Generic U_q(𝔤)... | **COMPLETE** |

---

*Phase 5m roadmap. Created 2026-04-07, updated 2026-04-16. Waves 1-2 COMPLETE (generic definition + full Hopf algebra). Wave 3 fundamentals done (Kac-Walton shipped). Next: W3 Freudenthal recursion (optional) → W4 metaprogramming (optional).*
