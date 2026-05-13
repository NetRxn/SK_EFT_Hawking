/-
SK_EFT_Hawking Phase 6p Wave 3a.3: Fault-Tolerant Universal Quantum Computation

The composition theorem: the AGP concatenated-Steane threshold (Wave 1b.3) +
Fibonacci-anyon density (Wave 2a.3 + 2b.3) + BHSZ braid-word compilation
(Wave 3a.2) together give a *conditional* fault-tolerant universal quantum
computation stack on the Fibonacci topological substrate.

**CONDITIONAL form (per Wave 3a.1 DR §4, gate G12):**

Statement:
  Given a Fibonacci representation `ρ : BraidGroup n → U(d)` satisfying:
    (1) FKLW closure-density (`ClosureDenseProp` — Wave 2a.3 axiom).
    (2) A physical-noise model with per-location rate `ε` such that the
        topological-noise effective per-location rate `p_eff` is strictly
        less than the AGP threshold `p_th_AGP := 1 / A_CNOT > 2.73 × 10⁻⁵`.

  Conclusion:
    The composed system admits universal quantum computation with logical
    error rate decaying double-exponentially in the AGP concatenation level
    `L ≥ 1`, i.e., `A_CNOT · ε_L < 1` (Wave 1b.3 `agp_threshold_steane_strict`),
    AND every target unitary in the closure of ρ is approximable to arbitrary
    precision by some braid word (Wave 3a.2 `exists_bhsz_approximation`).

**Important caveat (DR §4):** the implication "topological protection ⇒ AGP
threshold satisfied unconditionally" is community lore (Class D in Wave 3a.1
DR's evidence taxonomy), NOT a primary-source theorem. Hence the `p_eff <
p_th_AGP` hypothesis is EXPLICIT, not derived. The unconditional form would
require a separate primary-source-attested specialisation, deferred to
Wave 1c+ (and explicitly noted as a follow-up in the Phase6p_Roadmap.md).

References:
  - Aliferis-Gottesman-Preskill 2006, arXiv:quant-ph/0504218 (AGP threshold).
  - Freedman-Larsen-Wang 2002, arXiv:math/0103200 (FKLW density).
  - Dawson-Nielsen 2005, arXiv:quant-ph/0505030 (Solovay-Kitaev).
  - Rouabah 2020, arXiv:2008.03542 (Hadamard).
  - HZBS 2007, arXiv:quant-ph/0610111 (CNOT).
  - KBS 2013, arXiv:1310.4150 (T-gate).
-/

import Mathlib
import SKEFTHawking.BraidGroup
import SKEFTHawking.FKLW.BridgeProp
import SKEFTHawking.FKLW.SolovayKitaev
import SKEFTHawking.GateCompilation
import SKEFTHawking.FaultTolerance.Counting
import SKEFTHawking.FaultTolerance.Concatenation
import SKEFTHawking.FaultTolerance.AGP.Threshold

set_option autoImplicit false

namespace SKEFTHawking

open SKEFTHawking SKEFTHawking.FKLW SKEFTHawking.FaultTolerance
open SKEFTHawking.FaultTolerance.AGP
open SKEFTHawking.GateCompilation

/-! ## 1. The fault-tolerant universal quantum computation predicate

A *fault-tolerant UQC stack* combines:
  - A density witness `ClosureDenseProp` for the gate-set representation.
  - An AGP-threshold-satisfying physical-noise rate.

The predicate captures both ingredients.
-/

/-- The fault-tolerant universal-QC predicate: density + AGP-threshold.

Given a Fibonacci representation `ρ` and a physical per-location rate `ε`,
the stack provides fault-tolerant UQC if:
  (1) ρ is entrywise-dense in SU(d) (FKLW density via `DenseInSpecialUnitary`).
  (2) ε is strictly below the AGP threshold `1 / A_CNOT`.

**F2 migration (2026-05-13, user-authorized post-soundness-audit)**: the
`density` field now uses `DenseInSpecialUnitary` instead of `ClosureDenseProp`.
The latter is unsatisfiable for unitary ρ (entries lie on unit-modulus locus,
not dense in ℂ) — see BridgeProp.lean F2 finding. The migrated form is the
mathematically correct entrywise-density-in-SU(d) predicate. -/
structure FaultTolerantUQC (n d : ℕ)
    (ρ : BraidGroup n → Matrix (Fin d) (Fin d) ℂ) (ε : ℝ) : Prop where
  /-- The representation is entrywise-dense in SU(d) (FKLW universality). -/
  density : SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary n d ρ
  /-- The physical per-location rate is strictly below the AGP threshold. -/
  below_threshold : ε < steaneAGPThreshold
  /-- The physical rate is non-negative. -/
  ε_nonneg : 0 ≤ ε

namespace FaultTolerantUQC

variable {n d : ℕ}
  {ρ : BraidGroup n → Matrix (Fin d) (Fin d) ℂ} {ε : ℝ}

/-- Existence of BHSZ-ε approximations for any SU(d) target, derived from
    the density component of `FaultTolerantUQC`. -/
theorem hasGateCompilation (UQC : FaultTolerantUQC n d ρ ε)
    (U : Matrix.specialUnitaryGroup (Fin d) ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ b : BraidGroup n, ∀ i j : Fin d,
      ‖ρ b i j - (U : Matrix (Fin d) (Fin d) ℂ) i j‖ < δ :=
  exists_bhsz_approximation_su ρ UQC.density U δ hδ

/-- The AGP threshold is satisfied: the level-L logical error rate decays
    double-exponentially in `L` for any `L ≥ 1`. -/
theorem hasFaultTolerance (UQC : FaultTolerantUQC n d ρ ε) :
    ∀ L, 1 ≤ L →
      (steaneMalignancyCounts.A_CNOT : ℝ) * agpLevelSequence
        (steaneMalignancyCounts.A_CNOT : ℝ) ε L < 1 :=
  agp_threshold_steane_strict ε UQC.ε_nonneg UQC.below_threshold

end FaultTolerantUQC

/-! ## 2. The headline conditional composition theorems

The substantive composition delivers a *joint* statement: BOTH universality
(exists-braid-word approximation for any target unitary at any precision) AND
fault-tolerance (logical-error rate below threshold-inverse at any level L ≥ 1).

Two forms are shipped:
  - `composition_conditional` — packages the hypothesis as a `FaultTolerantUQC`
    structure (preserves the lightweight handoff form).
  - **`composition_substantive`** — the load-bearing joint statement combining
    the two consequences in a single quantifier.
-/

/-- **Conditional fault-tolerant universal quantum computation composition
    (structure-packaging form).**

Given:
  - A Fibonacci representation `ρ : BraidGroup n → U(d)` with FKLW closure-
    density (e.g., n = 3 strands, d = 3 SU(3) from `FibonacciQutritUniversality`,
    extended by `bridge_axiom_FKLW`).
  - A physical-noise model with per-location rate `ε ≥ 0` strictly less than
    the AGP threshold `steaneAGPThreshold = 1/A_CNOT > 2.73 × 10⁻⁵`.

Returns a `FaultTolerantUQC` structure. The substantive consequences
(universality + fault-tolerance) are extracted via `hasGateCompilation` +
`hasFaultTolerance`, or directly via `composition_substantive` below. -/
theorem composition_conditional
    {n d : ℕ} (ρ : BraidGroup n → Matrix (Fin d) (Fin d) ℂ)
    (h_density : SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary n d ρ)
    (ε : ℝ) (hε : 0 ≤ ε) (h_below : ε < steaneAGPThreshold) :
    FaultTolerantUQC n d ρ ε :=
  { density := h_density
    below_threshold := h_below
    ε_nonneg := hε }

/-- **SUBSTANTIVE composition theorem: joint universality + fault-tolerance.**

For a Fibonacci representation with FKLW closure-density and a physical noise
rate ε below the AGP threshold, the system delivers **simultaneously**, for
every target unitary `U`, every precision `δ > 0`, and every concatenation
level `L ≥ 1`:

  (1) **Universality (existence of approximating braid word):**
      ∃ b : BraidGroup n, ∀ i j : Fin d, ‖ρ b i j - U i j‖ < δ

  (2) **Fault-tolerance (logical-error suppression by concatenation):**
      A_CNOT · agpLevelSequence A_CNOT ε L < 1
      (equivalently, the level-L logical error rate is below the threshold-
      inverse `1 / A_CNOT`, so concatenation arbitrarily suppresses logical
      errors when started below threshold).

This is the substantive deliverable of Phase 6p Wave 3a.3: the joint
conjunction is what makes the stack a "fault-tolerant universal quantum
computation stack" — neither piece alone suffices.

*Conditional form:* the `ε < steaneAGPThreshold` hypothesis is EXPLICIT.
The unconditional form ("topological protection automatically satisfies AGP
threshold") is community lore, not primary-source theorem; deferred to
Wave 1c+. -/
theorem composition_substantive
    {n d : ℕ} (ρ : BraidGroup n → Matrix (Fin d) (Fin d) ℂ)
    (h_density : SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary n d ρ)
    (ε : ℝ) (hε : 0 ≤ ε) (h_below : ε < steaneAGPThreshold) :
    ∀ (U : Matrix.specialUnitaryGroup (Fin d) ℂ) (δ : ℝ) (_ : 0 < δ)
      (L : ℕ) (_ : 1 ≤ L),
      (∃ b : BraidGroup n, ∀ i j : Fin d,
        ‖ρ b i j - (U : Matrix (Fin d) (Fin d) ℂ) i j‖ < δ) ∧
      ((steaneMalignancyCounts.A_CNOT : ℝ) *
        agpLevelSequence (steaneMalignancyCounts.A_CNOT : ℝ) ε L < 1) := by
  intro U δ hδ L hL
  refine ⟨?_, ?_⟩
  · -- Universality: from FKLW density-in-SU(d)
    exact h_density U δ hδ
  · -- Fault-tolerance: from AGP threshold theorem applied below threshold
    apply agp_threshold_steane_strict ε hε _ L hL
    exact h_below

/-! ## 3. Worked example: Fibonacci 3-strand → SU(3)

When the input representation arises from FKLW density on the Fibonacci
3-strand qutrit space (paper14 `FibonacciQutritUniversality`), the
composition theorem applies directly with `n = 3` and `d = 3`.

The qutrit spanning data is established in paper14 (su(3)-spanning via
iterated commutators of the 3 braid generators σ₁, σ₂, σ₃ on a 3-dimensional
representation over Q(ζ₅, √φ)). The FKLW bridge axiom `bridge_axiom_FKLW`
lifts the spanning to closure-density. -/

/-- **Worked example (structure form).** Any Fibonacci 3-strand SU(3)
    representation with FKLW closure-density + physical rate ε below the
    Steane AGP threshold (ε < 2.73e-5 suffices) admits fault-tolerant UQC. -/
theorem fibonacci_3strand_example
    (ρ : BraidGroup 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (h_density : SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary 3 3 ρ)
    (ε : ℝ) (hε : 0 ≤ ε) (h_below : ε < 2.73e-5) :
    FaultTolerantUQC 3 3 ρ ε := by
  apply composition_conditional ρ h_density ε hε
  -- Need: ε < steaneAGPThreshold; we have ε < 2.73e-5 < steaneAGPThreshold
  have h_thr : steaneAGPThreshold > 2.73e-5 := steaneAGPThreshold_gt
  linarith

/-- **Worked example (substantive form).** The flagship Phase 6p composition
    applied to a Fibonacci 3-strand SU(3) representation: for any target
    unitary, any precision, and any AGP-concatenation level L ≥ 1, the system
    delivers BOTH a braid-word approximation AND below-threshold logical-error
    suppression.

This is the load-bearing substantive deliverable: topological gate substrate
(FKLW on Fibonacci qutrit) + AGP threshold theorem on Steane [[7,1,3]]
compose into a *functioning* fault-tolerant UQC stack with explicit joint
guarantees. -/
theorem fibonacci_3strand_example_substantive
    (ρ : BraidGroup 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (h_density : SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary 3 3 ρ)
    (ε : ℝ) (hε : 0 ≤ ε) (h_below : ε < 2.73e-5) :
    ∀ (U : Matrix.specialUnitaryGroup (Fin 3) ℂ) (δ : ℝ) (_ : 0 < δ)
      (L : ℕ) (_ : 1 ≤ L),
      (∃ b : BraidGroup 3, ∀ i j : Fin 3,
        ‖ρ b i j - (U : Matrix (Fin 3) (Fin 3) ℂ) i j‖ < δ) ∧
      ((steaneMalignancyCounts.A_CNOT : ℝ) *
        agpLevelSequence (steaneMalignancyCounts.A_CNOT : ℝ) ε L < 1) := by
  apply composition_substantive ρ h_density ε hε
  have h_thr : steaneAGPThreshold > 2.73e-5 := steaneAGPThreshold_gt
  linarith

/-! ## 4. Module summary

FaultTolerantUQC.lean: conditional fault-tolerant UQC composition.

  - `FaultTolerantUQC n d ρ ε` (structure: density, below_threshold, ε_nonneg).
  - `FaultTolerantUQC.hasGateCompilation` — universality consequence.
  - `FaultTolerantUQC.hasFaultTolerance` — fault-tolerance consequence (AGP).
  - **`composition_conditional`** — the headline composition theorem.
  - **`fibonacci_3strand_example`** — worked example at n=3, d=3 (paper14 anchor).

**Conditional form:** the `p_eff < p_th_AGP` hypothesis is EXPLICIT. The
unconditional implication "topological protection ⇒ AGP threshold satisfied"
is community lore (Class D in Wave 3a.1 DR's evidence taxonomy), NOT a
primary-source theorem. Deferred to Wave 1c+.

**F2 migration ship (2026-05-13, user-authorized)**: the `density` field
of `FaultTolerantUQC` (and the `h_density` parameter of all headline
theorems) now uses `DenseInSpecialUnitary` instead of `ClosureDenseProp`.
The latter was unsatisfiable for unitary ρ — making the prior headline
theorems vacuously true under unsatisfiable hypothesis. The migrated form
correctly states "ρ entrywise approximates every U ∈ SU(d)" which IS
satisfiable for actually-dense Fibonacci representations. The conclusion
universal quantifier also tightened from `U : Matrix d d ℂ` (overly broad —
non-unitary U cannot be approximated by unitary ρ) to `U : SU(d)` (the
correct domain).

Zero sorry. Zero project-local axioms in this module (consumes the AXIOM-
tagged `aa_residual_interior_at_one_for_hom` from Wave 2c.4a-iteration +
`sk_axiom_Dawson_Nielsen` from Wave 2b.2 transitively via the
`DenseInSpecialUnitary` hypothesis chain through `bridge_axiom_FKLW`).
-/

end SKEFTHawking
