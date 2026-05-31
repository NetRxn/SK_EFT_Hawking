# Phase 6x′ — Clifford/CCZ channel-representation characterization (Fact 3.9 / Theorem 3.8)

*A `prime` continuation of Phase 6x: the deep deferred layer of the Tier-2 Item-L exact-synthesis arc
(Mukhopadhyay arXiv:2401.08950 — the channel rep, Fact 3.9, Lemma 3.10, Theorem 3.8 that the Item-L
continuation explicitly documented as residual). Builds on the 6z Pauli substrate; discharges residuals
consumed in 6x (Lemma 3.10, the Item-L `T^of ≥ sde₂` bound) and 6z (CCZ-essentiality converse).*

**Status:** ✅✅ **PHASE 6x′ COMPLETE — both phases shipped, kernel-pure, 2026-05-30.** Phase 1 capstone
(`cliffordOnly_not_dense`, Stage-13 GREEN) + Phase 2 full discharge (UNCONDITIONAL `T^of(U) ≥ sde₂(Û)`)
both done. Build clean (9944 thm / 0 axiom / 0 sorry / 751 mod), 0 new native_decide, no maxHeartbeats.
**All three residuals CLOSED**: (1) Lemma 3.10 (`channelRep_interp_isRat`, rational/ℤ[1/2] entries),
(2) unconditional `T^of ≥ sde₂` (`channelSde2_le_toffoliCost`), (3) the 6z converse
(`cliffordOnly_not_dense`). Phase-2 chain (A–F): `MukhopadhyayMatrixSde2` (measure) → `…ToffoliUnconditional`
hC → `…CCZChannelRep` Theorem 3.8 half-integer (`channelRep_CCZ_isHalfInt`) → `…HCCZ` hCCZ
(`channelSde2_ccz_le`) → Lemma 3.10 + headline. L.C PARAMETRIC docstrings flipped to discharged. Full
Toffoli MINIMALITY (MITM / Conjecture 4.8) remains permanently out of scope. (Historical status below.)

**Status (Phase 1, historical):** ✅ Phase 1 COMPLETE (capstone shipped, Stage-13 GREEN). Phase-1 capstone = `cliffordOnly_not_dense`
(`MukhopadhyayCliffordNotDense.lean`, commit `838d96ff`): **⟨H,S,CNOT⟩ (no CCZ) is NOT dense in SU(8)** —
the genuine 6z CCZ-essentiality converse, fresh-context Opus Stage-13 review GREEN (no findings). Phase 2
C.1 (`MukhopadhyayCCZConjugation.lean`) = the CCZ diagonal-conjugation identity
`(CCZ·M·CCZ)_ij = ccz_i·ccz_j·M_ij` + CCZ-commutes-with-diagonals. **Per the off-ramp (below), the full
off-diagonal Theorem-3.8 structure + hCCZ + Lemma 3.10 + unconditional `T^of` are a DOCUMENTED RESIDUAL**
(deferred, not ground out): a marginal `PARAMETRIC → unconditional` upgrade on a non-tight bound (full
minimality is out of scope per the dossier regardless), gated on a delicate `sde₂`-on-ℂ matrix measure +
the 64-Pauli entry table. Net: of the three residuals, **(3) the 6z converse is CLOSED**; (1) Lemma 3.10
and (2) unconditional `T^of` remain documented (now with their C.1 substrate + `hC` substantiation in
place).

> **UPDATE 2026-05-30 (post-diligence) — Phase 2 FULL DISCHARGE GREEN-LIT (user sign-off).** The off-ramp
> residual is being promoted to active work: discharge `hCCZ` + Lemma 3.10 + the **unconditional**
> `T^of(U) ≥ sde₂(Û)`. **Rationale:** a fully-machine-checked *unconditional* resource lower bound is a
> novel, citable infrastructure artifact (the PARAMETRIC form is not), and the publication strategy is due
> for re-evaluation across several phases. A pre-flight diligence scan (3 parallel Explore agents over the
> 6u/6x/6x′/6y/6z roadmaps + paper bundles + the shipped Clifford+T `sde` arc) established: **(i)** the work
> is on *no* downstream critical path (no wave/bundle consumes it — it is pure rigor upside); **(ii)** the
> `sde₂`-on-ℂ *matrix* measure is mostly a **port**, not from-scratch — `KMM.sdeC` (`RossSelinger/SdeMatrix.lean`,
> `Finset.univ.sup … denExp`) is a working matrix-`sde` template, and `sde2` + `sde2_half_sum_le` are already
> shipped on ℚ; the **only** genuinely net-new piece is the ℂ→dyadic *extraction* `sde2ℂ` (route via the
> real part, since Mukhopadhyay guarantees channel-rep entries are real); **(iii)** Theorem 3.8's entry table
> is "Medium" with strong substrate (`kronK8_mul_trace`, `channelRep_eq_trace`, C.1, per-qubit conj tables) —
> net-new is per-index Pauli entries at |111⟩ + the `i`-cancellation bookkeeping. **De-risk order: do A
> (the `sde2ℂ` extraction) FIRST** — it is the one true unknown. Internal off-ramp retained: if A's extraction
> or C's entry table is genuinely Lean-intractable after honest effort, STOP and report (no axiom, no sorry,
> no grind) — the capstone + C.1 stand. Full Toffoli MINIMALITY (MITM / Conjecture 4.8) stays permanently
> out of scope. **Active plan: "Phase 2 full discharge (A–F)" section below.**

### Increment ledger status (2026-05-30)
- **A** (per-qubit 3-qubit H/S conj lifts) — ✅ already in-tree from Phase 6z (`hsu/ssu_q{1,2,3}_kronK8_conj`
  + `cnot{12,13,23}_kronK8_conj` + `qubit{i}Embed_conj`); no new work needed.
- **B** (channelRep of each Clifford gen is a signed monomial — Fact 3.9 ⟹) — ✅ SHIPPED (`497584e`):
  `channelRep_eq_signedMonomial` + `channelRep_{hsu,ssu}_q{1,2,3}` + `channelRep_cnot{12,13,23}` +
  the `su8val_conjTranspose_eq_inv` / `permMatrix_fin8_conjTranspose` bridges.
- **Capstone (6z converse)** — ✅ SHIPPED 2026-05-30 (`838d96ff`), Stage-13 GREEN. Three increments:
  inc1 `MukhopadhyaySignedPerm.lean` (`161e359b`, `IsSignedPerm` one/mul/inverse closure + finiteness via
  `Equiv.Perm L × (L → Bool)`); inc2 `MukhopadhyayCliffordConverse.lean` (`87f6302a`,
  `cliffordOnlyGeneratingSetSU8` + `cliffordWord_channelRep_signedPerm` via `FreeGroup.induction_on`);
  inc3+4 `MukhopadhyayCliffordNotDense.lean` (`838d96ff`, `continuous_channelRep` +
  `channelRep_eq_one_imp_scalar` faithfulness via `Matrix.center_eq_range` + `channelRep_seedSU8_pow_ne_one`
  infinite order via det ⟹ `cliffordOnly_not_dense`). Flipped the 6z `CliffordCCZSU8Density` docstrings.
- **Phase 2 (C.1)** — ✅ SHIPPED 2026-05-30 (`MukhopadhyayCCZConjugation.lean`): `CCZ_mat_conj_apply`
  (`(CCZ·M·CCZ)_ij = ccz_i·ccz_j·M_ij`) + `CCZ_conj_diagonal` (CCZ commutes with diagonal operators →
  the single-`+1` Theorem-3.8 rows). **C.2 / hCCZ / Lemma 3.10 / unconditional `T^of` = documented
  residual** (off-ramp; see "Highest-risk step"). The `hC` half is substantiated by inc2's
  `channelRep_cliffordOnlyGen_isSignedPerm` (signed perms preserve dyadic denominators).

## What it unlocks (the three residuals)

1. **6x Lemma 3.10** — the channel-rep entries of any Clifford+CCZ word lie in `ℤ[1/2]` (dyadic).
2. **Item-L unconditional `T^of(U) ≥ sde₂(Û)`** — discharges the `hC` / `hCCZ` hypotheses of the shipped
   parametric `toffoliCost_ge_measure` (`MukhopadhyayToffoliBound.lean`), making the Toffoli lower bound
   unconditional (no longer PARAMETRIC).
3. **6z CCZ-essentiality converse** — `⟨H,S,CNOT⟩` alone is finite, hence not dense (the unproved
   converse softened in `CliffordCCZSU8Density.lean`).

## The core claim

- **Clifford generators** (H_q i, S_q i, CNOT_ij) conjugate each Pauli to **± a Pauli** — i.e.
  `channelRep g` is a *signed permutation* of the 64 Pauli coordinates (entries ∈ {0,±1}, one per
  row/col). This is **Fact 3.9 (⟹ direction)**.
- **CCZ** conjugates each Pauli to a **sum of ≤4 Paulis with coefficients in {±1, ±1/2}** (the
  row-addition structure of **Theorem 3.8**): `CCZ·X_i·CCZ = X_i·CZ_{jk}`, `CZ = (1/2)(I+Z_j+Z_k−Z_jZ_k)`.

## Massive reuse (inventory 2026-05-30) — the Clifford half is ~90% already proved

| Item | FQN | file |
|---|---|---|
| H single-qubit signed-perm conj | `H_SU_conj_pauli4` (`hSign`/`hLabel`) | `CliffordCCZSU8GenConjValues.lean` |
| S single-qubit signed-perm conj | `S_SU_conj_pauli4` (`sSign`/`sLabel`) | `CliffordCCZSU8GenConjValues.lean` |
| CNOT **3-qubit kronK8** signed-perm conj | `cnot{12,13,23}_kronK8_conj` (`cnotSign`/`cnotLabel`) | `CliffordCCZSU8CNOTConj.lean` |
| perm-conj reindex | `permMatrix_conj_eq_submatrix` | `CliffordCCZSU8CNOTConj.lean` |
| Clifford label orbit (transitive on 63) | `clifford_label_transitive`, `onQubit` | `CliffordCCZSU8LabelTransitivity.lean` |
| Pauli-by-Pauli conj law | `pauli4_conj`, `sigmaSign`, `symForm4` | `CliffordCCZSU8PauliConj.lean` |
| Kronecker hom | `kronSU8_mul`, `kronSU8`, `kronK8` | `CliffordCCZSU8TangentSpan.lean` |
| Pauli basis + HS coords | `kronK8Basis`, `kronK8Basis_repr_eq`, `kronK8_mul_trace`, `kronK8_sq` | `CliffordCCZSU8TangentSpan.lean` |
| channel rep + homomorphism | `channelRep`, `channelRep_mul`, `channelRep_one`, `channelRep_eq_trace`, `channelRep_interp_mem` | `MukhopadhyayChannelRep.lean` |
| Fact 3.14 (+1 half-sum) | `sde2_half_sum_le`, `sde2` | `MukhopadhyaySde2.lean` |
| parametric T^of bound | `toffoliCount_ge_measure`, `toffoliCost_ge_measure` | `MukhopadhyayToffoliBound.lean` |
| generator orders | `litHadamard_sq`, `S_val_sq`, CNOT = `permMatrix` (order 2) | `*GenConjValues`/`*PauliWords`/`*CNOT` |
| CCZ diagonal facts | `CCZ_mat_sq_eq_one`, `CCZ_mat_conjTranspose_self`, `CCZ_mat` (diag, −1 at idx 7) | `CCZ_SU.lean` |

**Absent (net-new):** any `CCZ · kronK8 v · CCZ` conjugation identity; CCZ↔Z commutation; a `CZ`
definition; any `channelRep`-of-a-specific-gate computation; any "signed permutation" abstraction or
Clifford-finiteness machinery.

## Staged plan

### Phase 1 — Clifford (mostly assembly; closes 6z converse + Fact 3.9 ⟹ + `hC`)

- **A. Per-qubit 3-qubit H/S conj lifts.** Lift `H_SU_conj_pauli4` / `S_SU_conj_pauli4` through
  `kronSU8_mul` (gate ⊗ I ⊗ I etc.) to `H_on_qubit_i · kronK8 v · (…)⁻¹ = sign • kronK8 (onQubit hLabel i v)`
  — the H/S analogs of `cnot12_kronK8_conj`. 6 lemmas. **Low risk** (pure tensor lift; `onQubit` exists).
- **B. Signed-permutation channel rep + Fact 3.9 ⟹.** For each of the 9 Clifford gens, from
  `g·kronK8 v·g⁻¹ = ε_g(v)•kronK8(σ_g v)` derive `channelRep g s = ε_g(s) • (indicator at σ_g s)`
  (single ±1 per col/row; `σ_g` a bijection by `decide` on the finite label map). Package as
  `channelRep_cliffordGen_signedPerm`. Corollary **`hC`**: `sde₂(channelRep g · M) = sde₂(M)` (a signed
  permutation permutes/sign-flips entries, preserving the max). **Low-med risk.**
- **6z converse.** `channelRep` is a monoid hom (shipped) ⟹ `channelRep(⟨H,S,CNOT⟩)` ⊆ the finite set of
  signed 64×64 permutation matrices. `channelRep` continuous + `channelRep(SU(8))` infinite (the shipped
  infinite-order seed maps to infinite order under the hom) ⟹ `⟨H,S,CNOT⟩` is **not dense**. Ships the
  CCZ-essentiality converse; replace the softened 6z docstring with the theorem. **Med risk** (the
  continuity + finite-image-closure argument).

### Phase 2 — CCZ, C.1 (SHIPPED) — the structural engine

- **C.1. CCZ diagonal conjugation** — ✅ SHIPPED (`MukhopadhyayCCZConjugation.lean`): `CCZ_mat_conj_apply`
  (`(CCZ·M·CCZ)_{ij} = ccz_i·ccz_j·M_{ij}`, CCZ diagonal) + `CCZ_conj_diagonal` (CCZ commutes with diagonal
  ops ⟹ the single-`+1` Theorem-3.8 rows). The diagonal-entrywise route into Theorem 3.8.

### Phase 2 full discharge (A–F) — GREEN-LIT 2026-05-30; closes Lemma 3.10 + unconditional `T^of`

Order chosen to **de-risk first**: A (the one genuine unknown) before the C entry-table investment. Each
increment: `lean_diagnostic_messages` clean → build → `lean_verify` kernel-pure → commit.

- **A (DO FIRST — the only net-new infra; de-risks everything).** The `sde₂`-valued measure on ℂ-matrices:
  `sde2ℂ : ℂ → ℕ` (dyadic-denominator exponent of `z`; **route via `z.re`** since channel-rep entries are
  real, `0` if not real-dyadic, `Classical` extraction of the rational value) + sign-invariance
  `sde2ℂ (−z) = sde2ℂ z` + the **ℂ-lift of `sde2_half_sum_le`** (the `+1`-under-four-term-half-sum bound) +
  `matrixSde2 : Matrix L L ℂ → ℕ` (**port `KMM.sdeC`'s `Finset.univ.sup … per-entry` pattern**) +
  `μ := matrixSde2 ∘ channelRep` + `μ 1 = 0`. *Reuse:* `sde2`, `sde2_half_sum_le` (ℚ, shipped);
  `KMM.sdeC` template (`RossSelinger/SdeMatrix.lean`). *Risk:* medium — the ℂ→ℚ extraction is the delicate
  bit; if intractable, internal off-ramp (below).
- **B. `hC` (Cliffords preserve the measure).** `μ(gateMatrix(clifford c)·M) ≤ μ M`: `channelRep_mul` +
  `channelRep_cliffordOnlyGen_isSignedPerm` (shipped) ⟹ left-mult by a signed perm permutes/sign-flips
  entries ⟹ `matrixSde2` preserved. *Risk:* low-med (reuses inc2 signed-perm machinery).
- **C. Theorem 3.8 — `channelRep CCZ` entry structure (the bulk; DR "Medium").** Each row is a single `±1`
  (the 8 diagonal Z-type Paulis — from `CCZ_conj_diagonal`) OR four `±1/2` (the 56 X/Y Paulis); entries
  `∈ {0,±1,±1/2}`. *Route:* `channelRep CCZ r s = δ_{rs} − (1/4)[(P_r P_s)₇₇ + (P_s P_r)₇₇] + (1/2)(P_r)₇₇(P_s)₇₇`
  via C.1 + `channelRep_eq_trace` + `kronK8_mul_trace`. *Net-new:* per-index Pauli-entry lemmas at `7 = |111⟩`
  (`(kronK8 v)₇₇` = ±1 if all-{I,Z} else 0) + the `i`-cancellation showing entries are real. *Risk:* the
  highest; bounded by the strong substrate.
- **D. `hCCZ`.** `μ(CCZ_mat·M) ≤ μ M + 1` from C's row structure (each product entry is `±` one entry, or
  `(1/2)·(four ±entries)`) + A's ℂ half-sum lift. *Risk:* med, mechanical once A+C land.
- **E. Lemma 3.10.** Clifford+CCZ word channel-rep entries `∈ ℤ[1/2]`, by induction over the word (Clifford
  integer/signed-perm + CCZ dyadic + homomorphism `channelRep_mul`). State **faithfully** (`∈ ℤ[1/2]`).
  *Risk:* low-med (assembly).
- **F. Final.** Instantiate `toffoliCost_ge_measure` with `μ`, discharging `h1`(A)/`hC`(B)/`hCCZ`(D) ⟹
  **UNCONDITIONAL `T^of(U) ≥ sde₂(Û)`**; flip the L.C PARAMETRIC docstrings → discharged. *Risk:* low (plug-in).

## Internal off-ramp (revised — STOP-and-report, not permanent residual)

The Phase-1 off-ramp has been **exercised and superseded**: Phase 2 is now GREEN-LIT for full discharge.
The retained off-ramp is procedural: if **A** (the ℂ→dyadic extraction) or **C** (the 64-Pauli entry table)
proves genuinely Lean-intractable after honest effort, **STOP and report** — do **not** add an axiom, a
`sorry`, or grind a hopeless proof, and do **not** ship a vacuous measure (`μ ≢ 0` — guard against the
trivial measure that self-satisfies `hC`/`hCCZ`). The capstone + C.1 already stand, so a partial result is
still net-positive. Full Toffoli MINIMALITY (MITM / Conjecture 4.8) remains permanently out of scope.

## Kernel-purity discipline (load-bearing)

`ext` + `ring`/`noncomm_ring` over ℂ for matrix identities; **plain `decide`** (kernel-pure, Category-B
per ADR-002 — NOT `native_decide`) for finite symplectic label maps over `Fin 4`/`Fin 64`/`ZMod 2`. The
work adds **zero** to the `native_decide` trust surface, and is `{propext, Classical.choice, Quot.sound}`
throughout. No new project axioms (Inv #15); no `maxHeartbeats` in proof bodies (Inv #10).

## Increment ledger (rough; each: build clean + `lean_verify` kernel-pure + commit; per-phase Stage-13)

**Phase 1 (DONE):**
1. **A/B + capstone** — Fact 3.9 ⟹ (signed-perm channel reps) + `cliffordOnly_not_dense`; 6z docstrings
   flipped.   ← ✅ shipped, Stage-13 GREEN (`161e359b`/`87f6302a`/`838d96ff`).
2. **C.1** — `CCZ_mat_conj_apply` + `CCZ_conj_diagonal`.   ← ✅ shipped (`2db6f6c3`).

**Phase 2 full discharge (GREEN-LIT 2026-05-30; de-risk order A→F):**
3. **A** — `sde2ℂ` (ℂ→dyadic via `re`) + sign-invariance + ℂ-lift of `sde2_half_sum_le` + `matrixSde2`
   (port `KMM.sdeC`) + `μ := matrixSde2 ∘ channelRep` + `μ 1 = 0`.   ← DO FIRST.
4. **B** — `hC`: signed-perm left-mult preserves `matrixSde2`.
5. **C** — `channelRep_CCZ` entry structure (Theorem 3.8): rows = single `±1` or four `±1/2`,
   entries `∈ {0,±1,±1/2}`; via the C.1 trace route + |111⟩ Pauli-entry lemmas.
6. **D** — `hCCZ`: `sde₂(channelRep CCZ · M) ≤ sde₂ M + 1`.
7. **E** — Lemma 3.10: `channelRep_interp_entries_dyadic` (`∈ ℤ[1/2]`).
8. **F** — instantiate `toffoliCost_ge_measure` ⟹ UNCONDITIONAL `T^of(U) ≥ sde₂(Û)`; flip L.C docstrings
   PARAMETRIC → discharged.   ← Phase 2 done.

## Stage 9/10 + sync

After each phase: `lake build SKEFTHawking.ExtractDeps` + `update_counts.py` + `validate.py --check
counts_fresh,axiom_closure_allowlist`; update the 6x/6z/Item-L roadmaps + the consolidated review doc
(flip the corresponding documented-residual entries to shipped). Public repo only.
