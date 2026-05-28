# Phase 6z — Substrate Inventory (reuse map + new-build list)

*Progressive-disclosure detail doc for `docs/roadmaps/Phase6z_Roadmap.md`. Pointers are
`module :: symbol` (durable; `grep` / `lean_local_search` the symbol for the current line — line
numbers drift). All under `lean/SKEFTHawking/` unless noted.*

The 6z thesis: **the spread half is already built and alphabet-agnostic; the new work is the seed →
first-flow lift.** This doc catalogs (A) what to reuse verbatim, and (B) what must be built new.

---

## A. REUSE VERBATIM (shipped by 6y / 6u — alphabet-agnostic)

### A1. Conjugation transport (the spread engine)
- `FKLW/GenericSUdFlowConj.lean :: GenericSUd.flow_conj_mem`
  — for `R ∈ H` and a flow for `X`, gives a flow for `R·X·R⁻¹`. **The core of the spread.** Generic in `d`.
- `FKLW/CliffordCCZSU8EntanglerSpread.lean :: permMatrix_fin8_conj`
  — permutation-matrix conjugation = `submatrix` index relabel (no 8-term blowup). Also
  `CNOT_{12,13,23}_mat_inv`, `cnot12_conj_X1`/`cnot13_conj_X1`/`cnot23_conj_X2`/`cnot23_conj_X1X2`
  (base CNOT Pauli-conjugation table).
- `FKLW/CliffordCCZSU8FactorConj.lean :: qubit{1,2,3}Embed_conj`
  — conjugation by `qubit_iEmbed C` rotates only tensor factor `i` (clean Kronecker algebra) +
  `qubit{1,2,3}Embed_val_inv`.
- `FKLW/CliffordCCZSU8EntanglerFlow.lean` — the **54 entangling-flow spread** built for 6y's A′:
  `qubit{1,2,3}_conj_tangent_flow`, `qubit{2,3}_conj_flow_scaled`, `cliffX`/`signX`/`cliffX_conj`
  (σ_x ↦ ±σ_a single-qubit Clifford selector), `flow_drop_sign`, `suEightTangentAux_flow`,
  `suEightTangent_flow`. **The exact pattern 6z's Wave 4 mirrors** (once it has the seed flow, the
  spread to the 63 tangents is this machinery).

### A2. Tensor-Pauli / SU(8) algebra
- `FKLW/CliffordCCZSU8Tangents.lean :: kronSU8`, `kronSU8_trace`, `kronSU8_conjTranspose`,
  `suEightTangentAux (a b c)`, `suEightTangent`, `suEightTangent_in_sud`, `idx63`.
- `FKLW/CliffordCCZSU8TangentSpan.lean :: suEightTangent_spans`
  — **the 63 tensor-Paulis ℝ-span `𝔰𝔲(8)`** (Hilbert–Schmidt completeness). Reuse directly for the
  Wave-4 spanning argument (the target basis the conjugation orbit must fill).
- `FKLW/CliffordCCZAlphabet.lean :: CliffordCCZ.CCZ_mat` (`= diagonal(1,…,1,−1)`), `det_CCZ_mat = −1`.
- `FKLW/CCZ_SU.lean :: CCZSUExtension.CCZ_SU` (`= ω·CCZ_mat ∈ SU(8)`), `CCZ_SU_subtype`.

### A3. Per-qubit embeddings + gate generators (SU(8))
- `FKLW/CliffordCCZSU8QubitEmbed.lean :: qubit{1,2,3}Embed` (SU(2) →* SU(8)) + continuity.
- `FKLW/CliffordCCZSU8CNOT.lean :: CNOT_{12,13,23}_SU8`, `CNOT_{ij}_mat`, `permMatrix_fin8_mem_specialUnitaryGroup`.
- `FKLW/CliffordCCZSU8UniversalGates.lean :: H_SU_on_qubit{1,2,3}_SU8`, `T_SU_on_qubit{1,2,3}_SU8`
  (= `qubit_iEmbed H_SU` / `qubit_iEmbed T_SU`).
- `FKLW/CliffordCCZSU8PerQubitContainment.lean :: qubit{1,2,3}Embed_mem_H_of_G` (per-qubit ⊆ H_of_G —
  **but note this routes through Clifford+T density; 6z's literal set has no T**, so containment of the
  *seed* is via "seed is a product of literal generators" not this).

### A4. BCH / Trotter (for Wave 3 bracket closure)
- `MatrixBCHCubic.lean :: bch_order_2_cubic_thm` — `‖e^{iF}e^{iG}e^{-iF}e^{-iG} − e^{−[F,G]}‖ ≤ 320δ³`,
  **dimension-generic over `{d}`**. The analytic core for bracket→flow.
- `FKLW/SU2BCHBracketClosure.lean :: trotter_sequence_tendsto`, `fourfoldComm`, `exp_bracket_mem_H`
  — the **SU(2) Trotter limit** (`exp(t[X,Y]) = lim(Pₙ)ⁿ`). The template 6z.3 generalizes to SU(d)
  (Mathlib's `NormedSpace.exp` tail bounds are dimension-free; ~250 LoC mechanical port).

### A5. The SU(2) von-Neumann-density TEMPLATE (most relevant prior art — read it)
- `FKLW/CliffordTV4WitnessUnconditional.lean :: cliffordT_H_of_G_eq_top_unconditional`
  + `FKLW/CliffordTClosureDenseWitness.lean` — the `{H,T}` density proof: an **infinite-order element
  with irrational eigen-angle** (the `H_SU·T_SU` product, Niven-style obstruction) → accumulation at 1
  → von-Neumann one-parameter-subgroup extraction → Cartan ⟹ ⊤. **6z's SU(8) seed lift is the direct
  d=2→d=8 analogue of this entire chain** — study its proof skeleton before building Waves 2–4.
- `FKLW/CartanSubstrate.lean :: CartanFinalStep_SU2_v4` + `GenericSUd*Cartan*.lean ::
  CartanFinalStep_SUd_v4` — closed dense subgroup ⟹ ⊤ (consumes flow lines).

### A6. Witness → headline (Wave 5 plugs straight in)
- `FKLW/GenericSUdClosureDenseWitness.lean :: ClosureDenseWitness` (structure: `n`, `X`, `hX_in_sud`,
  `hX_spans`, `hX_flow`).
- `FKLW/GenericSUdPerAlphabetHeadlineFromWitness.lean :: cliffordCCZSU8_headline_of_witness`
  (and `trappedIonSU4_headline_of_witness`) — **feed the literal-alphabet `ClosureDenseWitness` here →
  UNCONDITIONAL `SolovayKitaevHeadline_FreeGroup_SUd`.** 6z reuses this verbatim with a literal-alphabet
  generating set.
- `FKLW/TrappedIonSU4WitnessFull.lean` + `FKLW/CliffordCCZSU8WitnessFull.lean` — assembly templates
  (how to wire the 3 witness fields → tracked-Prop discharge → headline). 6z.5 mirrors these.

### A7. Single-qubit Clifford conjugation (reusable for the σ-rotations in the spread)
- `FKLW/TrappedIonSU4EntanglerSpread.lean :: cliffordSU2`, `cliffordSU2_conj`,
  `clifford_σ{z,x,y}_conj_σ{x,y}`(`_p`), `one_conj_σ{x,y}_p` — the σ_a↦±σ_b single-qubit Clifford
  conjugations (already reused by 6y's `cliffX`).

### A8. Phase A.1 foundation (shipped under 6y, commit `70e17b9`)
- `FKLW/CliffordCCZSU8LiteralSeed.lean :: litHadamard`, `litSeed (= CCZ_mat·(H⊗H⊗H))`,
  `litSeed_trace (= 1/√2)`, `trace_CCZ_mul`, `kron_litHadamard_apply_7_7`. Kernel-only.
  **NB:** the operative seed switches to DR2's `g₀=(H₃·CCX)²` (explicit `(3±i√7)/4` eigenblock); A.1's
  trace lemma is a standalone result, its machinery is reused.

---

## B. BUILD NEW (none of this exists yet)

### B1. The literal generating set (NO `T`) — Wave 1 prerequisite
- A `GenericSUd.GeneratingSet 8` instance `cliffordCCZLiteralGeneratingSetSU8 = {H_qi, S_qi, CNOT_ij, CCZ}`.
  Mirror `FKLW/CliffordCCZGeneratingSetSU8Full.lean :: cliffordCCZGeneratingSetSU8` but **replace the
  T-gate tokens with `S` tokens**. Needs `S_SU` per qubit (phase-corrected `diag(1,i)`; analogue of
  `T_SU_mat` in `FKLW/CliffordTGeneratingSet.lean`). Token map + `FreeGroup (Fin K)` + `ρ_hom`.
- **Key contrast with 6y:** density of THIS set is NOT from per-qubit flows (no T → `{H,S}` finite).
  It is from the seed (B2).

### B2. Seed element + irrationality — Wave 1 (~860 raw LoC; see `PreLean_CAS_Gates.md` first)
- `g₀ = (H⊗H⊗H · CCX)² ∈ SO(8)`, char poly `(x−1)⁶(x²−(3/2)x+1)`, `λ_±=(3±i√7)/4` (DR2).
- `not_rootOfUnity_of_minpoly_not_int` (algebraic-integer obstruction; ~70 LoC) — the highest-leverage
  new lemma, independently reusable.
- Membership: `g₀ ∈ H_of_G cliffordCCZLiteralGeneratingSetSU8` (a product of literal generators —
  use `H_of_G_ρ_mem` per generator + `mul_mem`, as 6y did for `CNOT_*_SU8_mem_H_of_G` in
  `CliffordCCZSU8EntanglerFlow.lean`).

### B3. First-flow lift — Wave 2 (~375 raw LoC)
- `irrational_dense_on_circle` (~25 LoC) over `AddSubgroup.dense_or_cyclic` (Mathlib — see `Mathlib_Decls.md`).
- Unitary spectral-log wrapper (~150 LoC): `g₀ = U·diag(e^{iθ})·U† → X := U·diag(θ)·U† ∈ 𝔰𝔲(8)`,
  `exp(tX) ∈ closure⟨…⟩`. (Mathlib spectral theorem is **Hermitian-only** → wrap via `(g₀±g₀†)`.)

### B4. SU(d) Trotter — Wave 3 (~250 raw LoC; iff Wave 0 says BCH needed)
- Generalize `trotter_sequence_tendsto` (A4) from SU(2) to SU(8) using the dimension-generic
  `bch_order_2_cubic_thm`. **NB: Track S left the SU(d) Trotter sum formula conditional/pending** — 6z
  is where it gets discharged if the orbit-dimension gate (Wave 0) requires bracket closure.

### B5. Spread + spanning — Wave 4 (400 / 900 / 1800 raw, per Wave 0)
- Clifford-orbit of `X` via `flow_conj_mem` + A1/A7; close brackets via A4/B4; show the result spans the
  63-dim `suEightTangent_spans` basis (A2) ⟹ `ClosureDenseWitness cliffordCCZLiteralGeneratingSetSU8`.

### B6. *(Deferred)* multi-D Kronecker–Weyl on `𝕋^d` — `SKEFTHawking/KroneckerWeyl/Multidim.lean`
- ABSENT from Mathlib; **not needed for the first flow**. Re-evaluate post-6z.5.
