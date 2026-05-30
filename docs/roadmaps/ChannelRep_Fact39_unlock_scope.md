# Scope — the Clifford/CCZ channel-rep (Fact 3.9 / Theorem 3.8) unlock

**Status:** SCOPED 2026-05-30 (not started). The single highest-leverage remaining formalization: prove
each generator's conjugation action on the 64 three-qubit Paulis, kernel-pure, to retire **three**
deferred residuals at once. Cross-phase (6x / 6z / Item-L). Substance-preferred per the principal's
green-light.

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

### Phase 2 — CCZ (net-new; closes `hCCZ` → Lemma 3.10 → unconditional T^of)

- **C.1. CCZ diagonal conjugation.** `(CCZ·M·CCZ)_{ij} = ccz_i·ccz_j·M_{ij}` (CCZ diagonal ±1); the
  rank-1 sign pattern `ccz_i·ccz_j` expands as a fixed sum of Z-type Paulis. Establish CCZ↔Z commutation
  + `CCZ·X_i·CCZ = X_i·CZ_{jk}` with `CZ = (1/2)(I+Z_j+Z_k−Z_jZ_k)`.
- **C.2. Theorem 3.8 row structure + `hCCZ`.** `CCZ·kronK8 v·CCZ = Σ(≤4) (±1,±1/2)•kronK8 (…)` ⟹
  `channelRep CCZ` rows are either one ±1 entry (Z-type Paulis) or four ±1/2 entries (X-containing).
  Corollary **`hCCZ`**: `sde₂(channelRep CCZ · M) ≤ sde₂(M) + 1` via `sde2_half_sum_le`. **High risk /
  bulk of effort.** Mitigation: the diagonal-entrywise route avoids multi-X Pauli-product gymnastics.
- **Final assembly.** `hC` (B) + `hCCZ` (C.2) + homomorphism closure ⟹ **Lemma 3.10** (Clifford reps are
  integer, CCZ rep dyadic, product dyadic). Define `μ = sde₂ ∘ (dyadic-extract) ∘ channelRep` and
  instantiate `toffoliCost_ge_measure` ⟹ **unconditional `T^of(U) ≥ sde₂(Û)`**. (ℂ→dyadic extraction is
  the glue; uses Lemma 3.10 to land entries in ℚ.) Med risk.

## Highest-risk step

**C.2** (CCZ general-Pauli conjugation / Theorem 3.8). Off-ramp: if the fully-general 64-case kernel-pure
proof is disproportionate, **Phase 1 ships standalone** (6z converse + Fact 3.9 ⟹ + `hC`), and `hCCZ` /
Lemma 3.10 / full-unconditional-T^of stay documented residuals — still a real net gain (two of three
unlocks).

## Kernel-purity discipline (load-bearing)

`ext` + `ring`/`noncomm_ring` over ℂ for matrix identities; **plain `decide`** (kernel-pure, Category-B
per ADR-002 — NOT `native_decide`) for finite symplectic label maps over `Fin 4`/`Fin 64`/`ZMod 2`. The
work adds **zero** to the `native_decide` trust surface, and is `{propext, Classical.choice, Quot.sound}`
throughout. No new project axioms (Inv #15); no `maxHeartbeats` in proof bodies (Inv #10).

## Increment ledger (rough; each: build clean + `lean_verify` kernel-pure + commit; per-phase Stage-13)

1. **A** — `cliffordGen_kronK8_conj` (9 gens, unified `g·kronK8 v·g⁻¹ = ε•kronK8(σ v)`).
2. **B** — `channelRep_cliffordGen_signedPerm` (Fact 3.9 ⟹) + `channelRep_clifford_sde2_preserve` (`hC`).
3. **6z converse** — `cliffordOnly_not_dense`; flip the 6z docstring to the theorem.   ← Phase 1 done
4. **C.1** — CCZ↔Z commute + `CCZ·X_i·CCZ = X_i·CZ_{jk}` + `CZ` Pauli expansion.
5. **C.2** — `CCZ_kronK8_conj_sum` (Theorem 3.8 rows) + `channelRep_CCZ` dyadic + `hCCZ`.
6. **Final** — Lemma 3.10 (`channelRep_interp_entries_dyadic`) + unconditional `toffoli_ge_sde2`; flip
   the L.C docstring from PARAMETRIC to discharged.   ← Phase 2 done

## Stage 9/10 + sync

After each phase: `lake build SKEFTHawking.ExtractDeps` + `update_counts.py` + `validate.py --check
counts_fresh,axiom_closure_allowlist`; update the 6x/6z/Item-L roadmaps + the consolidated review doc
(flip the corresponding documented-residual entries to shipped). Public repo only.
