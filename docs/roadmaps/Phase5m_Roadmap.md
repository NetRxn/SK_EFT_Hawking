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
- [ ] Coproduct relation-respect, remaining 2 (HARDEST):
  - `SerreE_quad`, `SerreF_quad` (palindromic atom-bridge per CAS
    deep research). LOC audited 2026-04-15 against Uqsl3Hopf structure:
    **600-1000 LOC per theorem (generic parametric version)**, including
    shared sector helpers (5 sect3_hUqId lemmas + 2 q-binomial aux).
    Uqsl3Hopf comul-side Serre is ~1800 LOC for 4 concrete theorems +
    shared helpers; generic version needs only ONE theorem per side
    but parametric indices offset ~40% of savings. 2-3 sessions for
    SerreE_quad + 1-2 for SerreF_quad mirror.
- [ ] Antipode: S(E_i) = -E_iK_i^{-1}, S(F_i) = -K_iF_i, S(K_i) = K_i^{-1} —
  analogously requires q-Serre respect (F12/F21 tranches in Uqsl3Hopf).
  Historical sl_3 ratio: antipode side = 85% of comul side LOC (not 40%);
  800-1200 LOC / 2-3 sessions after SerreE/F_quad.
- [ ] `qgComul` descended via `RingQuot.liftAlgHom` — mechanical (50 LOC)
  once all 11 relation-respects land.
- [ ] `Bialgebra` + `HopfAlgebra` typeclass instances on `QuantumGroup k A`
  — mechanical (~100-300 LOC) via Uqsl3Hopf template (commits `dadce3e`,
  `bdf0ee9`: 24 per-generator eval lemmas + 3 coalgebra axioms +
  Drinfeld's S² = Ad(K₁²K₂²)).
- **Strengthening audit (2026-04-15):** see
  `temporary/working-docs/phase5m_generic_hopf_state.md ## Strengthening audit`
  for per-item priorities. TL;DR: SerreE/F_quad is the single blocker for
  wave closure; everything downstream is mechanical.

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

*Phase 5m roadmap. Created 2026-04-07, updated 2026-04-07. Deep research complete. Wave 1 DONE (generic definition + q-binomials + all relation proofs). Next: Hopf structure (W2) → fusion rules (W3) → metaprogramming (W4).*
