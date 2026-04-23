# Phase 5t: Doubloon Geometric Gate — Symmetry-Protected Two-Qubit Logic

## Technical Roadmap — April 2026

*Prepared 2026-04-09 | Follows Phase 5s: extract the finite-dimensional core first, defer heavy analysis until the exact matrix structure is closed.*

**Current state:** 131 Lean modules, 2237+ theorems, 1 axiom, 11 sorry. The repo already has strong finite-dimensional Hamiltonian infrastructure via `PauliMatrices.lean`, `BdGHamiltonian.lean`, `GTCommutation.lean`, and `FKGappedInterface.lean`, plus a complete topological-quantum-computation chain through `IsingGates.lean` and `FibonacciUniversality.lean`. What does **not** exist yet is a formalization of an experimentally current **symmetry/geometric protected gate** in a neutral-atom / Fermi-Hubbard setting.

**Entry state:** The TQC chain already gives the mathematically strongest protection story in the codebase: Ising = Clifford, Fibonacci = universal, with MTC/ribbon/modularity structure machine-checked. Phase 5t is not a replacement for that chain. It is a complementary hardware-facing case study: a finite-dimensional Fermi-Hubbard doublon gate whose protection comes from dark-state structure, fermionic exchange antisymmetry, and Hamiltonian symmetries rather than braiding/topological order.

**Motivation:** The ETH paper `arXiv:2507.22112` gives a timely experimental target: a geometric SWAP gate in a dynamical optical lattice with loss-corrected amplitude fidelity ~99.9%, built from doublon states in a Fermi-Hubbard dimer. Formalizing the idealized gate mechanism would:
- give the project a second quantum-computing entry point besides anyons
- showcase the Lean + Aristotle workflow on a near-term hardware-relevant gate
- support methodology / positioning claims about “protected logic from structure” without overstating topological overlap
- create a lower-risk, shorter-cycle formalization target than the remaining q-Serre/Hopf blocker

**Scope boundary:** Phase 5t should start with the **finite-dimensional exact model only**. Do **not** begin by trying to formalize the full adiabatic theorem, experimental fidelity extraction, or noise plateaus. The target is the algebraic core of the gate mechanism. If that closes cleanly, later waves can strengthen the phase and robustness story.

---

## Track A: Effective Fermi-Hubbard Dimer (Most Tractable)

### Wave 1 — Deep Research: Exact Dimer Model + Basis Conventions [MANUAL — John]

**Task:** `Lit-Search/Tasks/submitted/Phase-5t_effective_Hubbard_dimer_basis_and_symmetries.md`

**Goal:** Extract the exact 6-state Hamiltonian, the singlet/triplet basis change, fermionic sign conventions, and the minimal theorem set needed for a Lean formalization.

**Why first:** The main risk in this phase is not abstract mathematics. It is convention drift: basis ordering, normal ordering, doublon signs, and which symmetry statements survive at `U = 0` versus `U ≠ 0`.

**Status:** Prompt written. Ready for asynchronous deep research.

---

### Wave 2 — `FermiHubbardDimer.lean` [Pipeline: Stages 1-5] ✅ SHIPPED 2026-04-23 session 6

**Goal:** Define the doublon-gate Hamiltonian in the site basis and prove the block decomposition into triplet and singlet sectors.

**Shipped (2026-04-23 session 6):**
- [x] `lean/SKEFTHawking/FermiHubbardDimer.lean` — ~230 LOC, 14 theorems, 0 sorry, 0 new axioms
  - 3×3 singlet-sector Hamiltonian `H_singlet` in the {D+, D-, s} basis
  - 6×6 site-basis Hamiltonian `H_full` with alternating ±t signs encoding fermionic anticommutation
  - Chiral operator `chiralOp = diag(+1, -1, -1)` and dark-state vector `darkVec = (0, 2t, Δ)`
- [x] Layer-1 core theorems T1-T7:
  - T1 `H_singlet_isSymm` — Hᵀ = H (real symmetric, all U)
  - T2 `dark_state_in_kernel` — H₃(t, Δ, 0) · (0, 2t, Δ) = 0
  - T3 `darkVec_ne_zero` — nonzero unless (t, Δ) = (0, 0)
  - T4 `chiralOp_sq` — Γ² = I
  - T5 `chiral_anticommutes` — {Γ, H₃(t, Δ, 0)} = 0
  - T6 `det_H_singlet` — det = -4Ut² (T6a det_U0 = 0)
  - T7 `trace_H_singlet` — tr = 2U (trace_U0 = 0)
- [x] Triplet eigenvectors T10a-c: |↑,↑⟩, |↑,↓⟩+|↓,↑⟩, |↓,↓⟩ all zero-energy for all (t, Δ, U)
- [x] Corollary `dark_state_nontrivial_kernel` (T2 + T3 bundled)
- [x] Import added to `lean/SKEFTHawking.lean`
- [x] Python mirror `src/fermi_hubbard/dimer.py` + 74 parametric/random-grid tests in `tests/test_fermi_hubbard_dimer.py`

**Wave 2 deferred (promoted to W3+):**
- Explicit 6×6 ↔ 3×3 basis-change unitary P and the block-diagonal proof P†H₆P = diag(0₃, H₃) (~80 LOC of `fromBlocks` bookkeeping — T11 in deep research)
- Full characteristic polynomial λ³ − 2Uλ² + (U² − Δ² − 4t²)λ + 4Ut² (T8 — needs `charmatrix` + polynomial coefficient matching)

**Estimated LOE:** 2-4 days (actual: ~1 session)
**Risk:** Low (actual: zero blockers)

---

### Wave 3 — Reduced 3×3 Singlet Block [Pipeline: Stages 1-5] ✅ SHIPPED 2026-04-24 session 7

**Goal:** Isolate the `S = {D+, D-, s}` sector and prove it matches the effective Hamiltonian used in the paper.

**Shipped (2026-04-24 session 7):**
- [x] `H_singlet` definition retained from W2 (3×3 reduced Hamiltonian in {|D₊⟩, |D₋⟩, |s⟩} basis, `!![U, Δ, -2t; Δ, U, 0; -2t, 0, 0]`)
- [x] Exact `U`, `Δ`, `t` dependence confirmed via block-match theorems below
- [x] New Section 3b added to `lean/SKEFTHawking/FermiHubbardDimer.lean` (~90 LOC, 10 theorems, 0 sorry)
  - Unnormalized symmetry-adapted basis vectors as `Fin 6 → ℝ`: `v_Dplus`, `v_Dminus`, `v_s`, `v_t0`, plus computational basis `up_down`, `down_up`
  - **W3a** `H_full_acts_on_v_Dplus`: `H₆ · |D₊⟩ = U • |D₊⟩ + Δ • |D₋⟩ + (-2t) • |s⟩` (first row of H_singlet)
  - **W3b** `H_full_acts_on_v_Dminus`: `H₆ · |D₋⟩ = Δ • |D₊⟩ + U • |D₋⟩` (second row; no s-coupling — sublattice structure)
  - **W3c** `H_full_acts_on_v_s`: `H₆ · |s⟩ = (-2t) • |D₊⟩` (third row; no self-coupling)
  - **W3d** `H_full_acts_on_v_t0`: `H₆ · |t₀⟩ = 0` — triplet decoupling from the (-t, +t) alternating-sign cancellation
  - **W3e** `two_updown_eq_t0_plus_s`: `2 • |↑,↓⟩ = |t₀⟩ + |s⟩` (computational-basis decomposition)
  - **W3f** `two_downup_eq_t0_minus_s`: `2 • |↓,↑⟩ = |t₀⟩ − |s⟩`
- [x] Python mirror `src/fermi_hubbard/dimer.py` extended with `V_DPLUS`, `V_DMINUS`, `V_S`, `V_T0`, `UP_DOWN`, `DOWN_UP` constants + `block_match_Dplus/Dminus/s` helpers
- [x] Tests: `TestSymmetryAdaptedBasisEmbeddings` class in `tests/test_fermi_hubbard_dimer.py` with 34 new tests (basis components, orthogonality, block-match on deterministic + random grids, computational decomposition, row-consistency via projection onto H_singlet entries). 108 dimer tests pass.

**Design decision (recorded):** Used **unnormalized** symmetry-adapted basis (omitting `1/√2` normalization) so every W3 theorem closes over `ℝ` via `ext ; fin_cases ; simp ; ring` without dragging `Real.sqrt 2` through row identities. The `1/√2` re-enters only if W6 needs unitarity on the normalized computational qubit subspace. The block-match identities (W3a-c) are exactly the rows of `H_singlet` re-expressed in the 6-dim site basis, verified by Python projection onto `{v_Dplus, v_Dminus, v_s}` (test `test_block_match_singlet_rows_match_H_singlet`).

**Wave 3 deferred (promoted to W4+ or deferred):**
- Explicit 6×6 → 3×3 basis-change unitary P and `P†H₆P = diag(0₃, H₃)` (T11 — ~80 LOC, defers to W5 or is superseded by W3a-d + T10a-c which together establish the block structure without needing P explicitly)

**Estimated LOE:** 2-3 days (actual: ~1 session)
**Risk:** Low (actual: zero blockers; one mixed-closure pattern hit and resolved via `first | (simp; ring) | simp` per prior feedback memory)

---

## Track B: Dark State and Symmetry Protection

### Wave 4 — Dark State at `U = 0` [Pipeline: Stages 1-5] ✅ SHIPPED 2026-04-24 session 7 (strong form)

**Goal:** Prove the existence of the exact dark state in the singlet sector and its zero eigenvalue, plus the full spectral content at `U = 0`.

**Shipped (2026-04-24 session 7, strong form):** Extension of `FermiHubbardDimer.lean` (+14 new theorems, +2 summary markers, 0 sorry, 0 new axioms). Kept in the W2/W3 file rather than split to `DoublonDarkState.lean` for contiguous-section continuity.

- [x] Definitions: `darkStateθ θ := ![0, sin θ, cos θ]`, `brightVecPlus t Δ := ![√(Δ²+4t²), Δ, -2t]`, `brightVecMinus t Δ := ![-√(Δ²+4t²), Δ, -2t]`, `gapAtU0 t Δ := √(Δ²+4t²)`. All `noncomputable` since they depend on `Real.sin`/`Real.cos`/`Real.sqrt`.
- [x] **W4a** `dark_state_theta_in_kernel`: if `Δ·sin θ = 2t·cos θ` then `H_singlet t Δ 0 · darkStateθ θ = 0`. Angular condition equivalent to `tan θ = 2t/Δ` but avoids Δ = 0 singularity.
- [x] **W4b/c** `H_singlet_U0_brightVecPlus/Minus`: `H · brightVecPlus = +gap • brightVecPlus` and `H · brightVecMinus = -gap • brightVecMinus`. Row-0 identity uses `Real.sq_sqrt` on `0 ≤ Δ²+4t²` with `linarith` closing.
- [x] **W4d** `gapAtU0_pos`: `(t ≠ 0 ∨ Δ ≠ 0) → 0 < gap`.
- [x] **W4d'** `gapAtU0_sq_eq`: `gap² = Δ² + 4t²` (exact identity, useful downstream).
- [x] **W4e** `brightVecPlus_ne_zero` + **W4e'** `brightVecMinus_ne_zero`: bright vecs nonzero whenever `(t, Δ) ≠ (0, 0)`.
- [x] **W4e''** `darkStateθ_ne_zero`: darkStateθ is **always** nonzero — independent of (t, Δ) — via `sin²θ + cos²θ = 1 ≠ 0`.
- [x] **W4f** `charpoly_H_singlet` (T9): full characteristic polynomial `X³ − 2U·X² + (U² − Δ² − 4t²)·X + 4U·t²`. Closed by `simp [Matrix.charpoly, det_fin_three, charmatrix_apply_eq, charmatrix_apply_ne, map_mul, map_pow, map_ofNat] + show(i ≠ j) decide-witnesses ; ring`.
- [x] **W4g** `charpoly_H_singlet_U0` (T8): at `U = 0`, charpoly factors as `X · (X² − (Δ² + 4t²))`.
- [x] **W4h** `H_singlet_U0_spectrum_is_three_eigenvalues`: fully factored form `X · (X − C√g) · (X + C√g)`. Uses `map_mul` + `hsq` + `ring` via an intermediate `hCsq` lemma.
- [x] **W4i** `eigenvalues_distinct_at_U0`: when `(t, Δ) ≠ (0, 0)`, the three eigenvalues `{0, +gap, -gap}` are pairwise distinct.
- [x] **W4j** `eigenvectorMatrix_det`: determinant of the eigenvector matrix (rows = darkVec, brightVecPlus, brightVecMinus) is `2·(Δ²+4t²)·√(Δ²+4t²) = 2·(gap)³`.
- [x] **W4k** `eigenvectors_linearIndependent_at_U0`: alternate spectrum-completeness witness — det ≠ 0 ⇒ 3 independent eigenvectors ⇒ spectrum is exhausted by `{0, +gap, -gap}`. Complements the charpoly-factorization argument (W4h).
- [x] **W4l** `dark_brightPlus_orthogonal`: `⟨darkVec, brightVecPlus⟩ = 0` (pure `simp + ring`)
- [x] **W4m** `dark_brightMinus_orthogonal`: `⟨darkVec, brightVecMinus⟩ = 0` (mirror of W4l)
- [x] **W4n** `brightPlus_brightMinus_orthogonal`: `⟨brightVecPlus, brightVecMinus⟩ = 0` (needs `Real.sq_sqrt` via `linarith`). Together, W4l/m/n establish the three eigenvectors form a pairwise-orthogonal set — load-bearing for W6 SWAP-gate construction (phase accumulation on bright subspace, zero phase on dark subspace).
- [x] **W4o** `charpoly_H_singlet_U0_roots`: `(charpoly).roots = {0} + {√g} + {-√g}` as `Multiset ℝ`. Derived from W4h via `Polynomial.roots_mul` (twice) + the `@[simp]` lemmas `roots_X`, `roots_X_sub_C`, `roots_X_add_C`. Nonzero-product hypotheses discharged via `Polynomial.X_ne_zero`, `X_sub_C_ne_zero`, `X_add_C_ne_zero`.
- [x] **W4p** `H_singlet_U0_mem_spectrum_iff`: canonical `spectrum ℝ` API bridge — `μ ∈ spectrum ℝ (H_singlet t Δ 0) ↔ μ = 0 ∨ μ = +√g ∨ μ = -√g`. Uses `Matrix.mem_spectrum_iff_isRoot_charpoly` (field-level bridge) + `Polynomial.mem_roots` (gated by `Matrix.charpoly_monic.ne_zero`). **First `spectrum ℝ` theorem in the project** — establishes the Mathlib-canonical pattern for future parametric-spectrum work (polariton, fracton lattices).
- [x] Python mirror `src/fermi_hubbard/dimer.py` (+5 new functions): `dark_state_theta`, `bright_vec_plus`, `bright_vec_minus`, `gap_at_U0`, `charpoly_coeffs`.
- [x] Tests: `TestU0SpectrumW4` class in `tests/test_fermi_hubbard_dimer.py` (+34 new tests). Cross-check eigenvalue equations on deterministic + random grids; charpoly coefficients cross-checked against `np.poly(np.linalg.eigvalsh(H))`; spectrum at U=0 matches `{0, ±gap}` within tolerance 1e-12.
- [x] `lake build SKEFTHawking.ExtractDeps` clean (8422 jobs); pytest 2334/2334 pass; `validate.py` 21/21 pass.

**Design decisions (recorded):**
- **Strong form chosen** over eigenvector-equations-only: includes both T8 charpoly-at-U=0 AND T9 general-U charpoly, plus the linear-independence witness via `eigenvectorMatrix_det`. This double-witnesses spectrum completeness (via charpoly factorization AND via linear independence) at small LOC cost (~60 LOC vs ~30 for weak form).
- **Tactical pattern for charpoly:** `simp [Matrix.charpoly, det_fin_three, charmatrix_apply_eq, charmatrix_apply_ne, map_mul, map_pow, map_ofNat, show (i≠j : Fin 3) from by decide for each pair] ; ring`. The `map_mul/pow/ofNat` lemmas push `C` through the multiplicative/power structure so the final `ring` on `ℝ[X]` closes cleanly. This is now the replicable pattern for future parametric 3×3 charpoly work (polariton, fracton lattices).
- **Kernel hypothesis as condition, not derivation:** W4a takes `Δ·sin θ = 2t·cos θ` as a hypothesis — the caller supplies the specific angle — rather than deriving a specific θ from (t, Δ). This avoids the `Δ = 0` division issue and matches the `CenterFunctor.H_CF1` abstract-hypothesis precedent.
- **Unnormalized bright vectors:** norm-squared is `2·(Δ²+4t²)` rather than 1; no bookkeeping cost for the gate physics since the eigenvalue equation is norm-insensitive. Normalization can be added in W6 if the SWAP gate construction requires it.

**Wave 4 deferred (promoted to W5+):**
- ~~Orthogonality of darkVec vs brightVecPlus vs brightVecMinus~~ **— shipped as W4l/m/n in the same session** via direct `simp + ring` (+ `Real.sq_sqrt` for the bright-bright pair). +22 new pytest.
- ~~`Polynomial.roots` / `spectrum ℝ` form of the spectrum theorem~~ **— shipped as W4o/p in the same session.** +7 new pytest. First project use of `Matrix.mem_spectrum_iff_isRoot_charpoly` and `Polynomial.mem_roots` — replicable template for future spectrum work.
- **Normalized eigenvectors — still deferred; specifically gated on Phase 5t Wave 6 SWAP-gate unitarity arguments.** The W6 construction expresses the idealized geometric SWAP as a unitary operator `U_SWAP` on the 3-dimensional singlet subspace, parametrized by accumulated phase on the bright states and zero phase on the dark state. Unitarity of `U_SWAP` requires the three eigenvectors to be orthonormal (not just orthogonal, which W4l/m/n already gives). Two implementation paths, to be decided when W6 starts:
  - **Path A — retype eigenvectors as `EuclideanSpace ℝ (Fin 3)`** to use the canonical L2 norm. Explore-agent flag: the default `Fin 3 → ℝ` type uses the **sup-norm** (L∞), NOT Euclidean — applying Mathlib's `norm_smul_inv_norm` on raw `Fin 3 → ℝ` normalizes by max-absolute-value, a hard semantic bug. ~150+ LOC refactor across W4 defs; cleaner Mathlib interop.
  - **Path B — local `Matrix.dotProduct v v = 1` normalization predicate** (~50-80 LOC). Localized, avoids InnerProductSpace machinery, but not "true" Mathlib norm so future InnerProductSpace-typed downstream users would need a separate bridge.
  Decision deferred to W6: the choice depends on whether the SWAP unitarity proof ends up needing full `InnerProductSpace` machinery (e.g. adjoint operator, orthogonal projection) — if yes, Path A; if the SWAP just needs `v ⬝ v = 1` for normalization bookkeeping, Path B. **Do not normalize until we know what the SWAP construction requires** — picking the wrong path is costly to backtrack.

**Estimated LOE:** 3-5 days
**Risk:** Low to medium (mostly trigonometric simplification)
**Actual:** ~1 session, 14 theorems + 2 summary markers, zero blockers (caught `noncomputable` marker requirement and two `linear_combination` coefficient issues, both resolved via MCP multi_attempt iteration).

---

### Wave 5 — Symmetry Layer: Real Path + Chiral Constraint [Pipeline: Stages 1-5] ✅ SHIPPED 2026-04-25 session 8

**Goal:** Prove the symmetry structure that makes the dark-state path geometrically constrained.

**Deep research:** `Lit-Search/Phase-5t/Geometric Phase Formalization Scope for the Doublon Gate.md`

**Shipped (2026-04-25 session 8):** Extension of `lean/SKEFTHawking/FermiHubbardDimer.lean` (+10 new theorems — W5a-h + W5g' + wave5_summary marker, 0 sorry, 0 new axioms, ~170 LOC added). Kept contiguous with W2-W4 sections rather than split to a separate module.

- [x] **Definition of the chiral operator** — reused `chiralOp = diag(+1, -1, -1)` from W2 (Section 1).
- [x] **W5a** `chiralOp_conjugation_neg`: `Γ · H_singlet(t, Δ, 0) · Γ = -H_singlet(t, Δ, 0)`. BDI-class conjugation rule `Γ H Γ⁻¹ = -H` in concrete form (since `chiralOp_sq` gives Γ⁻¹ = Γ). Closed by direct `ext; fin_cases; simp [chiralOp, H_singlet, Matrix.mul_apply, Fin.sum_univ_three]`.
- [x] **W5b** `chiral_maps_eigenvector`: if `H_singlet(t, Δ, 0) · v = E • v`, then `H_singlet(t, Δ, 0) · (Γ v) = (-E) • (Γ v)`. Core BDI-spectrum-pairing mechanism. Closed via an algebraic `calc` chain using `Matrix.mulVec_mulVec`, `Matrix.neg_mulVec`, `Matrix.mulVec_smul`, `neg_smul` + the `H · Γ = -(Γ · H)` rearrangement from W2 T5 via `add_eq_zero_iff_eq_neg'`.
- [x] **W5c** `spectrum_pairing_U0`: `μ ∈ spectrum ℝ H ↔ -μ ∈ spectrum ℝ H`. Proved directly from W4p by case-splitting the three-element spectrum; every case closes with `rfl` or `linarith`. Establishes the BDI ± pairing at the spectral-set level.
- [x] **W5d** `zero_mem_spectrum_U0`: `(0 : ℝ) ∈ spectrum ℝ (H_singlet t Δ 0)`. Direct consequence of W4p — zero-mode existence.
- [x] **W5e** `darkVec_in_chiral_minus_eigenspace`: `Γ · darkVec(t, Δ) = -darkVec(t, Δ)`. Pins the zero mode to the 2-dim `(-1)`-eigenspace of Γ (the BDI sublattice `{|D₋⟩, |s⟩}`). Closed by direct `fin_cases + simp`.
- [x] **W5f** `darkVec_is_zero_mode_pinned`: bundle of (i) `H · darkVec = 0`, (ii) `Γ · darkVec = -darkVec`, (iii) `darkVec ≠ 0` — zero-mode pinning theorem in single-package form.
- [x] **W5g** `brightVecPlus_chiral_image`: `Γ · brightVecPlus = -brightVecMinus`. Witnesses the ± eigenvector pairing under chiral symmetry.
- [x] **W5g'** `brightVecMinus_chiral_image`: `Γ · brightVecMinus = -brightVecPlus`. Mirror of W5g; together they imply `Γ² · brightVecPlus = +brightVecPlus`, consistent with W2 T4.
- [x] **W5h** `H_singlet_real_anti_unitary_trivial`: paper-facing framing lemma. `H_singlet.map id = H_singlet` — documents that on a real-typed matrix the "anti-unitary time-reversal" symmetry required for BDI-class classification is trivially realized (complex conjugation = identity over ℝ). Collapses the (T, Γ) symmetry class to the chiral-only content already captured by W5a-c.
- [x] Python mirror `src/fermi_hubbard/dimer.py` (+6 new functions): `chiral_conjugation_U0`, `chiral_image_plus`, `chiral_image_minus`, `chiral_image_dark`, `spectrum_U0`, `spectrum_symmetric_under_neg`.
- [x] Tests: `TestChiralPinningW5` class in `tests/test_fermi_hubbard_dimer.py` (+63 new tests). Covers deterministic + random (t, Δ) grids for every W5 theorem: chiral conjugation reconstructs -H, Γ-image of bright+/- is ∓ of the other, spectrum symmetric under negation, zero in spectrum, darkVec pinned to -1 eigenspace of Γ, zero-mode bundle, Γ² = I consistency, real H ⇒ trivial anti-unitary TR.
- [x] `lake build SKEFTHawking.ExtractDeps` clean (8422 jobs); pytest 2426/2426 pass (+63 W5 on top of 2363 W4-round-2 baseline); validate.py 21/21 PASS (52 advisory warnings unchanged).

**Design decisions (recorded):**
- **Direct `ext + fin_cases + simp` for W5a** chosen over algebraic derivation from T4 + T5 (which would require a longer matrix-algebra chain). The 3×3 matrix product is small; direct case analysis is both shorter and more obviously correct. The algebraic route remains available through the proved lemma (consumers that want a non-3×3-specific argument can rederive).
- **`Matrix.mulVec_mulVec` + smul chain for W5b** chosen over `ext + fin_cases` because it generalizes directly to any dimension if reused. The tactic chain uses only standard matrix-action lemmas from Mathlib 4.29.
- **Spectrum-as-set casework for W5c** chosen over a single-line "set is symmetric under negation" lemma because Mathlib's `Set.neg` / `Multiset.map (-·)` handling is heavier than a direct 3-case disjunction when the spectrum is already factored as `μ = 0 ∨ μ = +√g ∨ μ = -√g` (W4p).
- **`darkVec` is in the (-1) not (+1) eigenspace of Γ** — the D₊ component of `darkVec` is 0, so Γ·darkVec negates the other two components. This is the BDI `n_+ - n_- = 1 - 2 = -1` sublattice-dimension-difference statement in concrete form (single zero mode, pinned to the larger sublattice).
- **W5h intentionally light** — real-symmetric H ⇒ anti-unitary TR trivial is a framing marker, not a load-bearing theorem. The genuine BDI content is the chiral anticommutation (T5) + conjugation rule (W5a). Full anti-unitary TR infrastructure (e.g., `ComplexConjugate` action on vectors, T² = ±1 case analysis) would be over-engineering for the real-valued case.

**Wave 5 round-2 strengthening (shipped same session 8):** +11 new theorems + 1 summary marker = +12 total (substantive + placeholder). Extension of Section 11 in `FermiHubbardDimer.lean`.
- [x] **W5i** `zero_mode_space_is_chiral_invariant`: `H · v = 0 ⟹ H · (Γ v) = 0`. Γ restricts to an involution on ker(H). Direct corollary of W5b with E = 0.
- [x] **W5j** `chiral_preserves_nonzero`: `v ≠ 0 ⟹ Γ v ≠ 0`. Via Γ² = I injectivity. Makes W5b/g/g' pairing genuine (rules out pathological `Γ v = 0`).
- [x] **W5k** `charpoly_roots_U0_symmetric_under_neg`: `(charpoly).roots.map Neg.neg = (charpoly).roots`. Strengthens W5c (set-level) to multiset level (with multiplicities). Proof via W4o explicit multiset + `Multiset.map_add` + `Multiset.map_singleton` + `add_right_comm`.
- [x] **W5l** `chiralProjPlus_sq`: `P_+² = P_+` (idempotent).
- [x] **W5m** `chiralProjMinus_sq`: `P_-² = P_-` (idempotent).
- [x] **W5n / W5n'** `chiralProjPlus_chiralProjMinus` + `chiralProjMinus_chiralProjPlus`: `P_+ · P_- = P_- · P_+ = 0` (orthogonal projectors). +1/-1 eigenspaces intersect trivially.
- [x] **W5o** `chiralProj_complete`: `P_+ + P_- = 1` (complete projectors). Full `V_+ ⊕ V_-` sublattice decomposition of ℝ³.
- [x] **W5o1 / W5o2** `chiralOp_mul_chiralProjPlus` + `chiralOp_mul_chiralProjMinus`: `Γ · P_+ = P_+` and `Γ · P_- = -P_-`. Γ acts as ±1 on the ±1 eigenspaces — load-bearing for W6 SWAP subspace decomposition.
- [x] **W5p** `zero_mode_unique_up_to_scalar`: `∀ v, H · v = 0 → ∃ c, v = c • darkVec` when `(t, Δ) ≠ (0, 0)`. The kernel of `H_singlet t Δ 0` is exactly `ℝ · darkVec`. Strongest "pinning" theorem — not just "a zero mode exists and is Γ-pinned" but "the zero-mode space *is* ℝ · darkVec". Proof by direct componentwise expansion of the mulVec equation + case split on Δ = 0 vs Δ ≠ 0 with explicit scalar witnesses in each branch.
- [x] Python mirror additions: `chiral_proj_plus()`, `chiral_proj_minus()` (3×3 projector matrices).
- [x] Tests: `TestChiralStrengthW5Round2` class (+37 new tests). Ker invariance via darkVec (random scalar multiples); Γ nonzero preservation; roots multiset negation-symmetry; projector idempotency/orthogonality/completeness; Γ ±1 action matches expected P_± signs; eigendecomposition consistency; SVD-based nullspace dim = 1 verification for W5p.
- [x] `lake build SKEFTHawking.ExtractDeps` clean (8422 jobs); pytest 2463/2463 pass (+37 round-2 on top of 2426 round-1); validate.py 21/21 PASS.

**Wave 5 fully deferred (future phase):**
- Formal "dark state traces a closed path in parameter space" statement — would require `Real.cos`/`Real.sin`/`Real.tan` manipulation parameterized by the sweep schedule, plus the Berry-phase statement that integrated curvature vanishes because the dark state has zero dynamical phase. Explicit Berry/Aharonov-Anandan formalization remains deferred to W8 (minimal geometric phase theorem) per roadmap.
- Continuous parameterized eigenvector theory (needed for the full Z₂ Berry phase quantization theorem). Not load-bearing for W6 SWAP-gate construction (which only needs the exact sign flip `|dark(2π)⟩ = -|dark(0)⟩`, not holonomy integrals).

**Estimated LOE:** 4-7 days
**Risk:** Medium
**Actual:** ~1 session, 21 theorems (10 core + 11 round-2) + 2 summary markers, zero blockers. Two tactic issues encountered + resolved: (i) `linear_combination` on non-commutative matrix ring → fixed via `add_eq_zero_iff_eq_neg'.mp`; (ii) `ac_rfl` on multiset goal → fixed via `simp [neg_zero, neg_neg]` + `rw [add_right_comm]`.

---

## Track C: Logical Gate Action

### Wave 6 — Geometric SWAP on the Computational Subspace [Pipeline: Stages 1-5] ✅ SHIPPED 2026-04-25 session 8 (W6A + W6B + W6C)

**Goal:** Show that a relative sign flip on the singlet component induces SWAP on the computational qubit subspace.

**Shipped (2026-04-25 session 8):** Three stages W6A/B/C landed in one session. **+39 new theorems** + 8 noncomputable defs + 3 summary markers (Sections 12–14 of `FermiHubbardDimer.lean`). Path A (EuclideanSpace) chosen per explore-agent recon.

**W6A — EuclideanSpace infrastructure (Section 12, +19 thms + 6 defs):**
- `darkVecE`, `brightVecPlusE`, `brightVecMinusE` via `EuclideanSpace.equiv.symm` (retains `.ofLp = originalVec` by rfl)
- Componentwise apply lemmas; explicit L2 norms (`‖darkVecE‖ = gap`, `‖brightVec±E‖ = √2·gap`)
- Normalized eigenvectors `darkVecNorm`, `brightVecPlusNorm`, `brightVecMinusNorm` with unit-norm witnesses
- Inner-product bridge via `@inner ℝ _ _ x y = dotProduct y.ofLp (star x.ofLp)` (rfl) + `dotProduct_comm`
- **`eigenvector_triple_orthonormal`**: `Orthonormal ℝ ![darkVecNorm, brightVecPlusNorm, brightVecMinusNorm]` under nontrivial params

**W6B — OrthonormalBasis + change-of-basis unitarity (Section 13, +7 thms + 2 defs):**
- `eigenBasisModule` via `basisOfOrthonormalOfCardEqFinrank`; `eigenBasis` via `Module.Basis.toOrthonormalBasis`
- Apply lemmas `eigenBasis_zero/one/two` matching the normalized eigenvectors
- **`eigenBasis_change_of_basis_unitary`**: one-liner via `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary` — change-of-basis matrix from `EuclideanSpace.basisFun` to eigenbasis is in `Matrix.unitaryGroup`
- `eigenBasis_change_of_basis_transpose_mul_self`: `M · Mᵀ = 1`

**W6C — Geometric SWAP operator + action (Section 14, +12 thms):**
- **`U_SWAP_singlet`** defined as Householder reflection `I - (2/(Δ²+4t²)) · darkVec ⊗ darkVec`
- **W6C-A1** `U_SWAP_singlet_darkVec`: `U · darkVec = -darkVec` — Berry-phase sign flip on dark state (core BDI gate action)
- **W6C-A2/A3** identity on bright states `U · brightVec± = brightVec±`
- **W6C-S1/S2/S3** symmetry + involution + orthogonality — the **unitarity witness in the singlet basis**, with S3 as a one-liner from S1 + S2
- **W6C-E1** bundled eigenvalue theorem `{-1, +1, +1}`
- **W6C-D1/T1** `det U = -1`, `tr U = +1` consistency

**Python mirror:** `dark_vec_norm`, `bright_vec_plus_norm`, `bright_vec_minus_norm`, `u_swap_singlet` (Householder form). Tests: `TestNormalizedEigenvectorsW6A` (+19) + `TestGeometricSWAPW6C` (+48) = **+67 new pytest**.

**W6 Design decisions:**
- **Path A (retype)** confirmed — one-line unitarity via Mathlib's canonical OrthonormalBasis API.
- **Additive retype** — new `darkVecE` etc. alongside existing `darkVec`, no breakage of W4/W5 theorems.
- **Householder form** for U_SWAP — `I - 2P` with `P = |dark⟩⟨dark|/gap²` projector. Symmetry + involution + orthogonality all via the `P² = P` algebra.
- **`@inner ℝ _ _ x y = dotProduct y.ofLp (star x.ofLp)` is definitional (rfl)** — use `show` + `dotProduct_comm` instead of `rw` which fails to pattern-match.

**W6 deferred (Phase 6):**
- SWAP action on the full 6×6 computational basis `{|↑,↓⟩, |↓,↑⟩}` via W3e/f lift. Current W6C action is in the 3×3 singlet-sector basis; full-basis lift + triplet identity extension ~30-50 LOC additional. Not load-bearing for the core BDI unitarity claim.
- `φ = π/2` entangling partial-SWAP family.

**Estimated LOE:** 4-6 days
**Risk:** Low
**Actual:** ~1 session. Blockers hit + resolved: (1) `rw [RCLike.inner_apply]` / `rw [EuclideanSpace.inner_eq_star_dotProduct]` fail to pattern-match `@inner ℝ _ _` — use `show` instead since these are `rfl`. (2) `dotProduct_comm` is bare (not namespaced `Matrix.`). (3) `isSymm` field_simp introduced spurious `True ∨ denom=0` disjunctions; fixed by using `mul_comm` as simp arg instead of `field_simp + ring`.

**Wave 6 round-2 strengthening (shipped 2026-04-26 session 9):** +5 theorems + 1 summary marker. Extension of Section 15 in `FermiHubbardDimer.lean`.
- [x] **W6C-A1s/A2s/A3s** `U_SWAP_singlet_smul_{darkVec,brightVecPlus,brightVecMinus}`: generalize W6C-A1/A2/A3 from explicit eigenvectors to any scalar multiple. `U · (c • v) = ±(c • v)` via `Matrix.mulVec_smul`. Covers the normalized form as the special case `c = gap⁻¹`.
- [x] **W6C-U1** `U_SWAP_singlet_mem_unitaryGroup`: packages `Uᵀ · U = 1` as `U_SWAP_singlet ∈ Matrix.unitaryGroup (Fin 3) ℝ`. One-liner via `Matrix.mem_unitaryGroup_iff'` + `Matrix.star_eq_conjTranspose` + `Matrix.conjTranspose_eq_transpose_of_trivial` (trivial star over ℝ).
- [x] **W6C-K1** `U_SWAP_singlet_on_kernel`: for any `v` with `H_singlet t Δ 0 · v = 0` and `(t, Δ) ≠ (0, 0)`, `U_SWAP · v = -v`. Combines W5p zero-mode uniqueness with W6C-A1s — the strongest "SWAP acts as −1 on the full pinned zero-mode subspace" theorem.
- [x] Python mirror `u_swap_action_on_kernel` (cross-check form).
- [x] Tests: `TestGeometricSWAPW6Round2` (+29 new tests). SWAP acts correctly on random scalar multiples; unitary-group transpose identity; SWAP acts as `-1` on kernel verified both via explicit darkVec scalars AND via SVD-based kernel extraction.

---

### Wave 7 — Direct Exchange vs. Superexchange [Pipeline: Stages 1-5] ✅ SHIPPED 2026-04-26 session 9

**Goal:** Formalize the cleanest scaling comparison between the direct-exchange and superexchange regimes.

**Deep research:** `Lit-Search/Phase-5t/Direct exchange vs superexchange in doublon gates- what is safely formalizable.md`

**Shipped (2026-04-26 session 9):** Section 16 in `lean/SKEFTHawking/FermiHubbardDimer.lean`. +9 new theorems + 1 summary marker + 3 new noncomputable defs. Approach follows the deep-research recommendation: bypass the Hubbard Hamiltonian and state results as pure real-analysis facts about the explicit function `E_plus(t, U) := (U + √(U² + 16·t²))/2`.

**W7 roster:**
- [x] **W7a** `E_plus_value_at_zero`: `E_plus(t, 0) = 2·|t|` — direct-exchange gap value at `U = 0`. `√(16·t²) = 4·|t|` via `mul_pow + sq_abs`.
- [x] **W7b** `E_plus_plus_E_minus`: `E_plus + E_minus = U` — Vieta trace identity for the 2×2 symmetric-sector quadratic `λ² − U·λ − 4·t²`. Closes by `ring` on the closed forms.
- [x] **W7c** `E_plus_times_E_minus`: `E_plus · E_minus = −4·t²` — Vieta product identity. Closes via `Real.mul_self_sqrt` + `nlinarith`.
- [x] **W7d** `E_plus_hasDerivAt_at_zero`: `HasDerivAt (fun U ↦ E_plus t U) (1/2) 0` for `t ≠ 0`. **The direct-exchange linear-in-U scaling theorem** — the Taylor coefficient of `E_plus` at `U = 0` is exactly `1/2`. Chained via `HasDerivAt.pow/add/sqrt/div_const`.
- [x] **W7e** `sqrt_lower_bound_abs_t`: `√(U² + 16·t²) ≥ 4·|t|` — foundational sqrt lower bound.
- [x] **W7f** `E_plus_monotone_nonneg`: `MonotoneOn (fun U ↦ E_plus t U) (Set.Ici 0)` — monotonic in `U` on `U ≥ 0`. Proof via `Real.sqrt_le_sqrt` + `nlinarith` for `U₁² ≤ U₂²`.
- [x] **W7g** `J_superexchange_at_zero`: `J(t, 0) = 2·|t|` — superexchange and direct-exchange regimes meet at `U = 0`. Corollary of W7a.
- [x] **W7h** `sqrt_one_add_le`: `√(1 + x) ≤ 1 + x/2` for `x ≥ 0` — AM-GM sqrt upper bound, used inside W7i.
- [x] **W7i** `J_superexchange_bound`: **for `0 < 4·|t| ≤ U`, `|J(t, U) − 4·t²/U| ≤ 16·t⁴/U³`** — the superexchange approximation theorem with explicit remainder. Tier-2 in the deep research. Key algebraic identity `J − 4·t²/U = -(s − U)²/(4·U)` where `s := √(U² + 16·t²)`, then `s − U ≤ 8·t²/U` from `U² + 16·t² ≤ (U + 8·t²/U)² = U² + 16·t² + 64·t⁴/U²`.

**W7 design decisions (recorded):**
- **Real-analysis formulation over matrix reduction.** The deep research explicitly recommends bypassing the Hubbard Hamiltonian at the Lean level and stating results as pure real-analysis facts. The matrix connection is established separately via W4's charpoly factorization; W7 operates on the explicit eigenvalue function without reconstructing the matrix spectrum.
- **Tier 1 + one Tier 2 target shipped.** All "Tier 1" (exact algebraic) deep-research targets landed: direct-exchange value, Vieta identities, derivative at zero, monotonicity, sqrt bounds. One "Tier 2" (asymptotic bound with remainder) also landed: the W7i superexchange approximation bound. The "Tier 3" items (experimental `4× sensitivity`, Berry-connection holonomy, many-body convergence) are intentionally left to paper discussion per the deep-research directive.
- **No Taylor theorem dependency.** W7i avoids `taylor_mean_remainder_lagrange` by proving the key algebraic identity `J − 4·t²/U = -(s − U)²/(4·U)` directly, then bounding `(s − U)²` via the sqrt-monotonicity inequality `s ≤ U + 8·t²/U`. This keeps the proof self-contained within standard Mathlib APIs (`Real.sqrt_sq`, `Real.mul_self_sqrt`, `Real.sqrt_le_sqrt`, `field_simp`, `nlinarith`).

**Python mirror:** `E_plus`, `E_minus`, `J_superexchange`, `J_leading_superexchange` (the `4·t²/U` textbook leading term, for cross-check of W7i).

**Tests:** `TestDirectExchangeSuperexchangeW7` class in `tests/test_fermi_hubbard_dimer.py` (+61 new tests). Covers every W7 theorem + scaling-signature sanity tests: direct-exchange linear-in-U scaling, superexchange 4t²/U asymptotic convergence, bound tightness.

**Estimated LOE:** 3-6 days
**Risk:** Medium
**Actual:** ~1 session. Blockers hit + resolved: (1) `div_le_div_of_nonneg_right` requires `0 ≤ c` (hypothesis), not `0 < c` — passed `.le` coercion. (2) `positivity` can't close `a ≤ b + c` goals from `Real.sqrt_le_sqrt` — used explicit `linarith`. (3) `field_simp` behaviour in `hJdiff_eq` needed `nlinarith [hs_sq]` to close the post-normalization polynomial — direct `ring` failed because the `s · s` term must be substituted via `s² = U² + 16t²`.

**Scope boundary maintained.** Did **not** turn into a full noise-analysis program. The formal target — qualitative scaling distinction plus explicit Tier-2 bound — is shipped. Extensions like 4× lattice-imperfection sensitivity, Berry-phase holonomy, and many-body convergence remain paper-level discussion per the deep research directive.

**Wave 7 round-2 strengthening (shipped 2026-04-26 session 9):** +8 theorems + 1 summary marker. Extension of Section 17 in `FermiHubbardDimer.lean`. Matrix-bridge layer that ties the scalar claims of W7 back to the actual Hubbard dimer matrix.
- [x] **W7j** `E_plus_char_eq`: `E_plus² − U·E_plus − 4·t² = 0` — foundational characteristic equation.
- [x] **W7k** `E_minus_char_eq`: mirror for E_minus.
- [x] **W7l** `charpoly_H_singlet_Δ0_factored`: `charpoly(H_singlet t 0 U) = (X − C U) · (X² − C U · X − C (4·t²))`. **The matrix-bridge theorem** — proves that `{U, E_plus, E_minus}` is the complete spectrum of the Hubbard dimer at Δ=0.
- [x] **W7m/n** `H_singlet_Δ0_E_{plus,minus}_eigenvector`: explicit eigenvectors `![E_{±}, 0, -2·t]` for `H_singlet t 0 U`; closed via the characteristic equation (W7j/k) + `fin_cases + nlinarith`.
- [x] **W7o** `H_singlet_Δ0_U_eigenvector`: at Δ=0 the antisymmetric doublon `![0, 1, 0]` is an eigenvector of `H_singlet` with eigenvalue `U`.
- [x] **W7p** `E_minus_value_at_zero`: `E_minus(t, 0) = −2·|t|` — mirror of W7a.
- [x] **W7q** `E_plus_lipschitz`: `|E_plus(t, U₁) − E_plus(t, U₂)| ≤ |U₁ − U₂|` — global 1-Lipschitz bound (Tier-1 per deep research). Non-trivial proof: sqrt 1-Lipschitz in `U` via `|s₁ − s₂|·(s₁+s₂) = |U₁−U₂|·|U₁+U₂|` + triangle inequality `|U₁+U₂| ≤ |U₁| + |U₂| ≤ s₁ + s₂`.
- [x] Python mirror: `E_plus_eigenvector`, `E_minus_eigenvector`, `antisymmetric_doublon_vec`, `E_plus_char_residual`, `E_minus_char_residual`. Tests: `TestW7Round2Strengthening` (+68 tests).

**W6 deferred shipment (also 2026-04-26 session 9):** +7 theorems + 1 summary marker. Extension of Section 18. 6×6 block-diagonal lift of `U_SWAP_singlet` to the symmetry-adapted basis via `Matrix.fromBlocks`.
- [x] **Def** `U_SWAP_adapted (t Δ) := fromBlocks (U_SWAP_singlet t Δ) 0 0 1`, typed `Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ` (singlet ⊕ triplet).
- [x] **W6D-S1/S2/S3/S3'** symmetric + involution + orthogonal + transpose-mul — all inherited from W6C via `Matrix.fromBlocks_{transpose, multiply, one}`.
- [x] **W6D-U1** `U_SWAP_adapted ∈ Matrix.unitaryGroup (Fin 3 ⊕ Fin 3) ℝ`.
- [x] **W6D-A1/A2** action agreement: on `Sum.inl v` (singlet embedding) the adapted SWAP acts as `U_SWAP_singlet`; on `Sum.inr w` (triplet embedding) it acts as identity. Via `Matrix.fromBlocks_mulVec`.
- [x] Python mirror `u_swap_adapted` (6×6 block-diagonal); tests `TestW6Deferred6x6Lift` (+43 tests) cover unitarity, involution, block-action, eigenvalues `{−1, +1, +1, +1, +1, +1}`, det=−1, trace=4.
- [x] **Scope note:** this is **structural** unitarity, NOT a claim about SWAP on `{|↑,↓⟩, |↓,↑⟩}`. The latter requires Berry-phase holonomy from a closed parameter loop (W8 / Phase 6), which remains deferred.

---

## Track D: Phase Quantization and Robustness Boundary

### Wave 8 — Minimal Geometric Phase Theorem [Decision Gate] ✅ TARGET A SHIPPED 2026-04-26 session 9

**Goal:** Decide how far the project should go on geometric phase.

**Target A decision:** SHIPPED. Target B remains Phase 6 per the original scope boundary.

**Shipped (2026-04-26 session 9, Target A):** Section 19 in `lean/SKEFTHawking/FermiHubbardDimer.lean`. **+5 new theorems + 1 summary marker** (no new defs — uses existing `darkStateθ`).

**Target A — shipped roster:**
- [x] **W8a** `darkStateθ_add_pi_sign_flip`: `darkStateθ(θ + π) = −darkStateθ(θ)` — **the closed-path sign statement**. Direct consequence of `Real.sin_add_pi` and `Real.cos_add_pi`. This is the core Berry-phase −1 factor accumulated over a π-sweep in the mixing angle.
- [x] **W8b** `darkStateθ_add_two_pi`: `darkStateθ(θ + 2π) = darkStateθ(θ)` — 2π periodicity of the parameterization, equivalent to applying W8a twice.
- [x] **W8c** `darkStateθ_dotProduct_self`: `dotProduct (darkStateθ θ) (darkStateθ θ) = 1` via `Real.sin_sq_add_cos_sq`. Dark state is automatically L²-normalized — no separate normalization step needed.
- [x] **W8d** `dark_state_dynamical_phase_vanishes`: **the zero-dynamical-phase statement**. Under the kernel-angle condition `Δ·sin θ = 2t·cos θ`, the expectation value `⟨darkStateθ, H · darkStateθ⟩ = 0`, so the integrated dynamical phase along any parameter loop vanishes identically. Direct consequence of W4a `dark_state_theta_in_kernel`.
- [x] **W8e** `geometric_phase_minus_one_on_pi_loop`: **the bundled geometric-phase theorem**. Combines W8a (sign flip) + W8d (dynamical phase vanishes) into a single statement: on any π-sweep of the θ parameterization satisfying the kernel-angle condition, the dark state acquires `−1` **while remaining at zero energy throughout**, so the accumulated phase is purely geometric and equals `−1`. This is the finite-dimensional algebraic core of the Kiefer et al. doublon-gate Berry-phase mechanism.

**Python mirror:** `dark_state_theta_norm(θ)`, `geometric_phase_loop_check(θ)` (structured witness for W8a/b/c cross-check). Tests: `TestGeometricPhaseW8` (+42 pytest covering W8a/b/c/d + kernel-angle condition + bundled witness + two-π-sweep sanity).

**Target A design decisions (recorded):**
- **No half-angle parameterization added.** Existing `darkStateθ θ := ![0, sin θ, cos θ]` uses full-angle convention, so the sign flip is at `π` (not `2π` as in half-angle-convention physics texts). This is stated explicitly in W8a. Introducing a `darkStateHalf φ := ![0, sin(φ/2), cos(φ/2)]` convention would change only the superficial parameterization and was judged not worth the extra notation.
- **No adiabatic integral formalization.** The dynamical phase statement W8d uses `⟨ψ, H·ψ⟩ = 0` **pointwise** along the path, which is stronger than ∫⟨ψ, H·ψ⟩ dt = 0 and avoids needing path-integral machinery. This is the "weakest exact form needed for Wave 6" condition from the original roadmap.
- **Scope boundary maintained:** did not touch Berry-connection formalism, parameterized eigenbundle geometry, or adiabatic theorem. Those remain Target B / Phase 6.

**Estimated LOE:** 2-4 days (Target A)
**Risk:** Medium (Target A)
**Actual:** ~1 session (5 theorems + Python mirror + tests; all tactics closed via simp + sin/cos Mathlib lemmas, no novel infrastructure).

**Target B — deferred (Phase 6):**
- [ ] Aharonov-Anandan or Berry phase formalization for a parameterized finite-dimensional Hamiltonian
- [ ] Adiabatic following theorem strong enough to justify the entire cycle in Lean
- [ ] Gauge-fixed phase computation over the loop

**Decision rule applied:** Target B would require substantial analysis infrastructure (parameterized eigenbundle, connection 1-form, holonomy group). Target A shipped per the explicit roadmap directive "Phase 5t should remain a finite-matrix success, not become an analysis sink."

**Estimated LOE:**
- ~~Target A: 2-4 days~~ ✅ SHIPPED ~1 session
- Target B: 2-6 weeks, high variance (deferred to Phase 6)

---

## Track E: Pipeline Integration and Hardware-Facing Outputs

### Wave 9 — Python Cross-Validation + Visualization [Pipeline: Stages 1-12] ✅ SHIPPED 2026-04-26 session 9

**Goal:** Add a lightweight Python layer for spectrum plots and reduced-model sanity checks if the Lean core lands cleanly.

**Shipped (2026-04-26 session 9):** Pipeline Stage 8–12 completion. **+1 new module + 1 new test file + 1 new figure** (43 pytest tests).

**Deliverables (shipped):**
- [x] **`src/experimental/doublon_gate.py`** — exact diagonalization wrapper around the W2-W8 Lean core. Exports: `DimerSpectrum` NamedTuple; `exact_diagonalize(t, Δ, U)` for 3×3 + 6×6 numpy `eigh`; `scaling_comparison_curves(t, U_range)` for W7 curves; `dimer_spectrum_at_U0(t, Δ)` for W4p; `swap_action_on_singlet(t, Δ)` for W6C; `gate_6x6_unitarity_witness(t, Δ)` for W6D; `bench_superexchange_bound(t, factors)` for W7i. Thin wrapper — no new physics, no new constants.
- [x] **`tests/test_doublon_gate.py`** — 43 tests across 6 classes (`TestExactDiagonalization`, `TestU0Spectrum`, `TestScalingComparisonCurves`, `TestSwapActionOnSinglet`, `TestGate6x6Unitarity`, `TestSuperexchangeBoundBenchmark`).
- [x] **`fig_doublon_gate_spectrum`** in `src/core/visualizations.py` — two-panel figure. Left panel: singlet-sector spectrum vs U (Δ=0), three eigenvalues E_plus/E_minus/U (antisymmetric doublon) from Lean closed-form AND numpy `eigh` markers (W7l cross-verification). Right panel: superexchange gap J(t,U) with 4t²/U asymptote + Lean W7i bound envelope ±16t⁴/U³. Registered in `scripts/review_figures.py`.

**Deferred (not load-bearing):**
- [ ] Optional notebook (Phase5t_DoublonGate_Technical.ipynb) — can ship alongside first paper for Phase 5t if/when paper is drafted.
- [ ] Optional `fig_exchange_vs_superexchange_scaling` as a separate figure — covered by right panel of `fig_doublon_gate_spectrum`.

**Python mirror summary (updated totals):**
- Python source modules: 65 → 66 (+1: `experimental/doublon_gate.py`)
- Test files: 57 → 58 (+1: `test_doublon_gate.py`)
- Figures: 109 → 110 (+1: `fig_doublon_gate_spectrum`)
- Pytest: 2620 → 2774 (+154 session 9: +68 W7r2 + +43 W6D + +43 W9)

**Estimated LOE:** 2-4 days after Lean core closes
**Risk:** Low
**Actual:** ~1 session. No blockers — module is purely a thin wrapper around Lean-verified primitives.

---

## Dependencies

```text
Wave 1 (dimer research) → Wave 2 (6×6 Hamiltonian) → Wave 3 (3×3 block)
Wave 3 → Wave 4 (dark state) → Wave 5 (symmetry layer)
Wave 4 + Wave 5 → Wave 6 (logical SWAP theorem)
Wave 3 → Wave 7 (exchange vs superexchange scaling)
Wave 4 + Wave 6 → Wave 8 (minimal phase theorem)
Wave 2-8 → Wave 9 (Python/tests/figures)
```

**Critical path:** Waves 2 → 3 → 4 → 6

**Non-critical but useful:** Wave 7, then Wave 9

---

## Timeline

| Wave | Scope | LOE | Dependencies | Priority |
|------|-------|-----|--------------|----------|
| 1 | Exact dimer research | 1-2 days async | None | Highest |
| 2 | 6×6 Hamiltonian + basis change | 2-4 days | Wave 1 | Highest |
| 3 | Reduced 3×3 singlet block | 2-3 days | Wave 2 | Highest |
| 4 | Dark state theorem at `U = 0` | 3-5 days | Wave 3 | Highest |
| 5 | Symmetry layer | 4-7 days | Wave 4 + research | High |
| 6 | Logical SWAP theorem | 4-6 days | Wave 4 + 5 | Highest |
| 7 | Direct vs superexchange scaling | 3-6 days | Wave 3 + research | Medium |
| 8 | Minimal geometric phase theorem | 2-4 days (Target A) | Wave 4 + 6 | Medium |
| 9 | Python/tests/figures | 2-4 days | Lean core closed | Medium |

**Total realistic LOE for the high-value core (Waves 2-6):** ~2-3 weeks

**Total realistic LOE including scaling + minimal phase + Python layer:** ~3-5 weeks

**Do not budget Target B geometric-phase formalization into the core estimate.** That is a separate escalation path.

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | Exact dimer Hamiltonian + basis conventions | `Lit-Search/Tasks/submitted/Phase-5t_effective_Hubbard_dimer_basis_and_symmetries.md` | **READY** |
| 2 | Geometric phase formalization scope in Lean 4 | `Lit-Search/Tasks/submitted/Phase-5t_geometric_phase_formalization_scope.md` | **READY** |
| 3 | Direct exchange vs superexchange formalizable claims | `Lit-Search/Tasks/submitted/Phase-5t_direct_exchange_superexchange_formalizable_claims.md` | **READY** |

---

## Citation Guide: `arXiv:2507.22112`

### What the citation is good for

- Use it as **hardware-motivation evidence** that symmetry- and geometry-protected two-qubit gates are experimentally live in neutral-atom / Fermi-Hubbard platforms.
- Use it to justify Phase 5t as a **complement** to Chain 3: our current TQC stack formalizes topological protection; this paper motivates a second, non-topological protected-gate case study.
- Use it in overview / methodology / discussion text to support the broader claim that the field values gate mechanisms derived from global structure rather than pulse fine-tuning.

### What the citation is **not** good for

- Do **not** cite it as evidence for quantum groups, modular tensor categories, anyon braiding, Muger triviality, or the Chain 3 formal results directly.
- Do **not** cite it in support of the chirality wall, Z₁₆ anomalies, gapped interfaces, or any Chain 4 claims.
- Do **not** present it as experimental confirmation of our formally verified TQC chain. It is adjacent in theme, not evidentiary overlap.

### Safe wording

- “Recent neutral-atom experiments demonstrate that two-qubit gates can inherit meaningful robustness from symmetry and quantum geometry in finite-dimensional Hubbard-type systems, complementing the stronger topological protection mechanisms formalized in our anyonic gate pipeline.”
- “The doublon geometric SWAP gate is not a realization of our quantum-group/MTC chain, but it provides a timely hardware-facing example of protected logic derived from exact structure rather than control fine-tuning.”
- “We cite `arXiv:2507.22112` as experimental motivation for a complementary protected-gate formalization, not as validation of our topological quantum computation results.”

### Best placement in our documents

- `docs/RESEARCH_STATUS_OVERVIEW.md` — Chain 3 implication/discussion paragraph, if we add a “complementary hardware directions” sentence
- Paper 11 discussion / outlook — to show adjacent hardware relevance for protected gates
- Paper 15 methodology / outlook — as a case for why finite-dimensional exact-gate formalization is worth doing

### Places to avoid

- Papers 7/8 chirality wall discussion
- Any section arguing for anomaly or cobordism conclusions
- Any sentence that would read as “this experiment supports our anyon/topological claims”

---

## Strategic Assessment

**What Phase 5t would strengthen most:**
- the project’s methods story
- hardware-facing quantum-computing relevance
- the claim that the repo handles more than one kind of protected-gate mechanism

**What it would strengthen least:**
- the core mathematical foundation of Chain 3
- any active blocker in the q-Serre / Hopf closure work
- any Chain 4 load-bearing claim

**Recommendation:** Pursue Waves 2-6 if and only if the phase is treated as a **bounded finite-Hamiltonian case study**. If the work starts drifting into full adiabatic-analysis machinery, stop at the exact algebraic core and publish the smaller result.

---

*Phase 5t roadmap. Created 2026-04-09. Positioned as a complementary protected-gate case study: finite-dimensional, hardware-relevant, and explicitly non-competitive with the higher-leverage q-Serre/Hopf closure work. Deep-research prompts written and placed in `Lit-Search/Tasks/submitted/`. The recommended success criterion for this phase is a closed idealized geometric SWAP theorem in Lean, not a full reproduction of the experimental control stack.*