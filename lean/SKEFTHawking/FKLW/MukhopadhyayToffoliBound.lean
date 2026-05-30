/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Item L.C — Mukhopadhyay Toffoli-count lower bound: the telescoping mechanism (L.B.2b)

The dossier (Q2.3) reports that arXiv:2401.08950 does not *state* an algebraic `T^of(U) ≥ sde₂(Û)`
lower bound, and concludes none follows. Checking the mechanism directly (per the Item-L guardrail —
secondary sources can err): the bound **does** follow from Lemma 3.16's per-step bound. Each
generator multiplication changes `sde₂` by at most one (the `+1` direction is Fact 3.14,
`sde2_half_sum_le`; Cliffords — signed permutations, Fact 3.9 — leave `sde₂` unchanged), and a
Clifford base has `sde₂ = 0`, so along any decomposition `Û = Ĝ_m ··· Ĝ_1 · Ĉ` the value telescopes:
`sde₂(Û) ≤ 0 + m`. Hence the Toffoli count `m ≥ sde₂(Û)`.

This increment ships the **telescoping mechanism**, abstracted over the measure `μ` but anchored to
the concrete Clifford+CCZ gate alphabet (`interp`, `gateMatrix`):

  - `toffoliCount gs` — the number of `CCZ` (Toffoli) gates in a gate word (Cliffords are free).
  - **`toffoliCount_ge_measure`** — for any `μ` with `μ(1) = 0`, `μ` non-increasing under each
    Clifford gate, and `μ` rising by at most one under `CCZ`, every gate word satisfies
    `μ(interp gs) ≤ toffoliCount gs`.

Instantiating `μ = sde₂ ∘ channelRep` (matrix `sde₂` of the channel rep) yields the genuine Toffoli
lower bound `T^of(U) ≥ sde₂(Û)`. The instantiation's hypotheses are the per-generator channel-rep
facts — `sde₂(Ĉ·M) ≤ sde₂(M)` (Cliffords are signed permutations, Fact 3.9) and
`sde₂(ĈCZ·M) ≤ sde₂(M) + 1` (the row-addition `+1`, Theorem 3.8.3 / Fact 3.14), with `sde₂(channel
rep)` well-defined over `ℤ[1/2]` (Lemma 3.10). Those per-generator entry analyses are the deeper
number-theoretic layer flagged in the dossier (Q5); they are stated as the explicit bridge hypotheses
here and itemized as documented follow-ons. The telescoping logic itself — the lower-bound mechanism —
is fully proved and unconditional.

**Honest scope on minimality:** `T^of(U) ≥ sde₂(Û)` is a valid lower bound but is NOT proved tight.
Full Toffoli-count minimality (no shorter circuit) requires the exhaustive nested meet-in-the-middle
search (Lemma 4.5 / §4.2.1) whose heuristic optimality rests on the unproved Conjecture 4.8; that is
not Lean-tractable and is the documented residual (L.C).

**Phase 6x′ status (2026-05-30):** the `hC` direction (Cliffords leave `sde₂` unchanged, Fact 3.9) is
substantiated by Phase 6x′ — every Clifford generator's channel rep is a signed permutation
(`MukhopadhyayCliffordConverse.channelRep_cliffordOnlyGen_isSignedPerm`), which permutes/sign-flips
entries and so preserves their dyadic denominators. The `hCCZ` direction needs the full Theorem 3.8
off-diagonal channel-rep structure of `CCZ` (`Ĉ_{CCZ}` rows of four `±1/2`); its structural engine — the
CCZ diagonal-conjugation identity `(CCZ·M·CCZ)_{ij} = ccz_i·ccz_j·M_{ij}` — is shipped as
`MukhopadhyayCCZConjugation.CCZ_mat_conj_apply` (Phase 6x′ Phase 2, C.1). **Making `toffoliCost_ge_measure`
unconditional** (instantiating `μ = sde₂ ∘ channelRep` and discharging both `hC` and `hCCZ`) additionally
requires a total `sde₂`-valued measure on `ℂ`-matrices (dyadic-exponent extraction) plus the 64-Pauli
Theorem-3.8 entry table; per the Phase 6x′ off-ramp it is a **documented residual**, deferred (not ground
out) as a marginal `PARAMETRIC → unconditional` upgrade on this non-tight bound. See
`docs/roadmaps/Phase6x_prime_Roadmap.md`.

PUBLIC math layer only (per the Item-L brief): no private-repo content.

## Pipeline invariants
- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.MukhopadhyayCCZ
import SKEFTHawking.FKLW.MukhopadhyaySde2

set_option autoImplicit false

namespace SKEFTHawking.FKLW.MukhopadhyayCCZ

/-- Boolean test for the `CCZ` (Toffoli) generator. -/
def isCCZ : CliffordCCZGate → Bool
  | .ccz => true
  | .clifford _ => false

/-- **Toffoli (CCZ) count of a Clifford+CCZ gate word**: the number of `CCZ` generators (each
Mukhopadhyay generating element `G_{P,Q,R}` is one Toffoli; the literal Cliffords are free). -/
def toffoliCount (gs : List CliffordCCZGate) : ℕ := gs.countP isCCZ

@[simp] theorem toffoliCount_nil : toffoliCount [] = 0 := rfl

@[simp] theorem toffoliCount_clifford (c : Fin 9) (gs : List CliffordCCZGate) :
    toffoliCount (CliffordCCZGate.clifford c :: gs) = toffoliCount gs := by
  simp [toffoliCount, isCCZ]

@[simp] theorem toffoliCount_ccz (gs : List CliffordCCZGate) :
    toffoliCount (CliffordCCZGate.ccz :: gs) = toffoliCount gs + 1 := by
  simp [toffoliCount, isCCZ]

/-- **The sde₂ Toffoli lower bound — telescoping mechanism.** For any measure `μ` on `8×8` unitaries
with `μ(1) = 0`, non-increasing under each Clifford gate, and rising by at most one under `CCZ`, every
Clifford+CCZ gate word `gs` satisfies `μ(interp gs) ≤ toffoliCount gs`. Reading `μ = sde₂ ∘ channelRep`
this is the Toffoli lower bound `T^of(U) ≥ sde₂(Û)` (the hypotheses are then the per-generator
channel-rep facts: Fact 3.9 for Cliffords, Fact 3.14 / Theorem 3.8.3 for `CCZ`). The telescoping logic
is unconditional.

**PARAMETRIC**: this is the telescoping skeleton. The physical Toffoli content (the actual
`T^of ≥ sde₂` bound) lives entirely in the *intended* instantiation `μ = sde₂ ∘ channelRep` together
with its per-generator bridge hypotheses `hC` / `hCCZ` — both the documented follow-on (the per-generator
channel-rep entry analyses), NOT discharged here. A trivial `μ ≡ 0` also satisfies the hypotheses (giving
the vacuous `0 ≤ toffoliCount gs`); the non-vacuous value is realized only by the un-shipped instantiation. -/
theorem toffoliCount_ge_measure (μ : Matrix (Fin 8) (Fin 8) ℂ → ℕ) (h1 : μ 1 = 0)
    (hC : ∀ (c : Fin 9) (M : Matrix (Fin 8) (Fin 8) ℂ),
      μ (gateMatrix (CliffordCCZGate.clifford c) * M) ≤ μ M)
    (hCCZ : ∀ M : Matrix (Fin 8) (Fin 8) ℂ, μ (gateMatrix CliffordCCZGate.ccz * M) ≤ μ M + 1)
    (gs : List CliffordCCZGate) : μ (interp gs) ≤ toffoliCount gs := by
  induction gs with
  | nil => rw [interp_nil, h1]; exact Nat.zero_le _
  | cons g gs ih =>
    rw [interp_cons]
    cases g with
    | clifford c =>
      rw [toffoliCount_clifford]
      exact le_trans (hC c (interp gs)) ih
    | ccz =>
      rw [toffoliCount_ccz]
      exact le_trans (hCCZ (interp gs)) (Nat.add_le_add_right ih 1)

/-- **The Toffoli cost `T^of(U)`**: the minimum number of `CCZ` (Toffoli) gates over all exact
Clifford+CCZ gate words for `U` — `sInf` of the achievable Toffoli counts (`0` if `U` is not exactly
Clifford+CCZ-representable). This is the Toffoli count of arXiv:2401.08950. -/
noncomputable def toffoliCost (U : Matrix (Fin 8) (Fin 8) ℂ) : ℕ :=
  sInf {n | ∃ gs : List CliffordCCZGate, interp gs = U ∧ toffoliCount gs = n}

/-- **The Toffoli-count lower bound `T^of(U) ≥ μ(U)`**, for the actual minimum Toffoli cost and any
telescoping measure `μ` (`μ(1) = 0`, non-increasing under each Clifford gate, `+1` under `CCZ`).
Reading `μ = sde₂ ∘ channelRep` this is the genuine `sde₂` Toffoli lower bound `T^of(U) ≥ sde₂(Û)`
(every exact Clifford+CCZ circuit for `U` uses at least `sde₂(Û)` Toffolis). NOT proved tight — full
minimality needs the intractable meet-in-the-middle search (Lemma 4.5 / Conjecture 4.8), the
documented residual; see the module docstring.

**PARAMETRIC** (as for `toffoliCount_ge_measure`): the substantive `μ = sde₂ ∘ channelRep`
instantiation + its per-generator bridges are the un-shipped follow-on; this theorem is the
telescoping-to-`sInf` packaging, not the discharged Toffoli bound. -/
theorem toffoliCost_ge_measure (μ : Matrix (Fin 8) (Fin 8) ℂ → ℕ) (h1 : μ 1 = 0)
    (hC : ∀ (c : Fin 9) (M : Matrix (Fin 8) (Fin 8) ℂ),
      μ (gateMatrix (CliffordCCZGate.clifford c) * M) ≤ μ M)
    (hCCZ : ∀ M : Matrix (Fin 8) (Fin 8) ℂ, μ (gateMatrix CliffordCCZGate.ccz * M) ≤ μ M + 1)
    {U : Matrix (Fin 8) (Fin 8) ℂ} (hU : IsExactlyCliffordCCZ U) :
    μ U ≤ toffoliCost U := by
  apply le_csInf
  · obtain ⟨gs, hgs⟩ := hU; exact ⟨toffoliCount gs, gs, hgs, rfl⟩
  · rintro b ⟨gs, hgs, rfl⟩
    rw [← hgs]
    exact toffoliCount_ge_measure μ h1 hC hCCZ gs

end SKEFTHawking.FKLW.MukhopadhyayCCZ
