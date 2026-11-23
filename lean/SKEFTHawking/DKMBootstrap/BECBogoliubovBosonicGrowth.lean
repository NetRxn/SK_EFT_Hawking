/- Prescribed factorial sequence and true mathematical growth controls.

The legacy becBogoliubovCommutatorNorm is DEFINED as(2*kappa)!; it is not
derived from a BEC Hamiltonian or density observable. The code proves its
superfactorial property, the resulting conditional contradiction and a
contrast with a separately prescribed zero sequence. No actual platform
classification, physical BEC no-go or uniqueness conclusion follows.
Actual BEC operator/domain/state/regulator and Hamiltonian commutator-growth
construction remain BUILD. Unbounded occupation alone does not identify
this sequence or a finite norm bound.

Relevant conditional locality sources are Yin/Lucas arXiv:2106.09726v2,
Finite speed of quantum information in models of interacting bosons at
finite density, and Kuwahara/Saito arXiv:2103.11592v3. Their specified
lattice/state/weighted-norm results must not be substituted for an actual
BEC Hamiltonian derivation. No universal physical threshold is inferred. -/
import SKEFTHawking.DKMBootstrap.HorizonTransportBootstrap
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace SKEFTHawking.DKMBootstrap

/-! ## Prescribed benchmark sequence, not a Hamiltonian-derived norm. -/

/-- Defined sequence(2*kappa)!, retained under its legacy public name. No physical norm identity is asserted. -/
noncomputable def becBogoliubovCommutatorNorm : ℕ → ℝ :=
  fun κ => (Nat.factorial (κ + κ) : ℝ)

/-- Nonnegativity of the prescribed factorial sequence. -/
theorem becBogoliubovCommutatorNorm_nonneg (κ : ℕ) :
    0 ≤ becBogoliubovCommutatorNorm κ := by
  unfold becBogoliubovCommutatorNorm
  exact Nat.cast_nonneg _

/-! ## Combinatorial bound(2*kappa)! >= (kappa!)^2. -/

/-- The factorial-square inequality follows from central-binomial divisibility and positivity. -/
theorem factorial_two_kappa_ge_factorial_kappa_squared (κ : ℕ) :
    (Nat.factorial κ : ℝ)^2 ≤ (Nat.factorial (κ + κ) : ℝ) := by
  -- Divisibility form `κ! · κ! ∣ (κ+κ)!` is in Mathlib at
  -- `Nat.factorial_mul_factorial_dvd_factorial_add`; combine with
  -- positivity of `(κ+κ)!` to convert to ≤.
  have h_dvd : Nat.factorial κ * Nat.factorial κ ∣ Nat.factorial (κ + κ) :=
    Nat.factorial_mul_factorial_dvd_factorial_add κ κ
  have h_pos : 0 < Nat.factorial (κ + κ) := Nat.factorial_pos _
  have h_nat : Nat.factorial κ * Nat.factorial κ ≤ Nat.factorial (κ + κ) :=
    Nat.le_of_dvd h_pos h_dvd
  have h_cast : (Nat.factorial κ : ℝ) * (Nat.factorial κ : ℝ) ≤
      (Nat.factorial (κ + κ) : ℝ) := by
    exact_mod_cast h_nat
  have hsq : (Nat.factorial κ : ℝ)^2 = (Nat.factorial κ : ℝ) * (Nat.factorial κ : ℝ) := by
    ring
  rw [hsq]
  exact h_cast

/-! ## Factorial domination of an exponential with fixed positive multiplier. -/

/-- For positive epsilon and M, some factorial exceeds epsilon^kappa*M. This is a scalar sequence statement. -/
theorem exists_kappa_factorial_gt_pow_mul (ε M : ℝ) (_hε : 0 < ε) (hM : 0 < M) :
    ∃ κ : ℕ, ε^κ * M < (Nat.factorial κ : ℝ) := by
  -- Step 1: `ε^κ / κ!` tends to zero as κ → ∞. Note: Mathlib's
  -- `FloorSemiring.tendsto_pow_div_factorial_atTop` holds unconditionally
  -- in ε ∈ ℝ (the limit is 0 by absolute-value comparison), so the
  -- positivity hypothesis `_hε` is documented but not load-bearing.
  -- We keep it because the substrate-level statement is intended for
  -- positive epsilon; no calibrated microscopic scale is asserted.
  have h_tendsto : Filter.Tendsto (fun n : ℕ => ε^n / (Nat.factorial n : ℝ))
      Filter.atTop (nhds 0) :=
    FloorSemiring.tendsto_pow_div_factorial_atTop ε
  -- Step 2: pick an `M⁻¹`-neighbourhood of 0 to get the eventual bound.
  have h_Minv_pos : 0 < M⁻¹ := inv_pos.mpr hM
  have h_evt : ∀ᶠ n : ℕ in Filter.atTop,
      ε^n / (Nat.factorial n : ℝ) < M⁻¹ := by
    have := h_tendsto.eventually (gt_mem_nhds h_Minv_pos)
    simpa using this
  obtain ⟨κ, hκ⟩ := h_evt.exists
  refine ⟨κ, ?_⟩
  -- Step 3: rearrange `ε^κ/κ! < M⁻¹` to `ε^κ · M < κ!`.
  have h_fact_pos : (0 : ℝ) < (Nat.factorial κ : ℝ) := by
    exact_mod_cast Nat.factorial_pos κ
  have h1 : ε^κ < M⁻¹ * (Nat.factorial κ : ℝ) := by
    have := (div_lt_iff₀ h_fact_pos).mp hκ
    linarith
  -- Multiply both sides by M (positive).
  have h2 : ε^κ * M < M⁻¹ * (Nat.factorial κ : ℝ) * M :=
    mul_lt_mul_of_pos_right h1 hM
  have h3 : M⁻¹ * (Nat.factorial κ : ℝ) * M = (Nat.factorial κ : ℝ) := by
    field_simp
  linarith

/-! ## The prescribed sequence satisfies the abstract growth predicate. -/

/-- For each positive epsilon/reference, some kappa has kappa!*epsilon^kappa*reference < (2*kappa)!. No physical sequence is identified. -/
theorem becBogoliubovCommutatorNorm_isSuperFactorialUnbounded :
    IsSuperFactorialUnbounded becBogoliubovCommutatorNorm := by
  intro ε n0Norm hε hn
  -- §3 gives: ∃ κ, ε^κ · n0Norm < κ!.
  obtain ⟨κ, hκ⟩ := exists_kappa_factorial_gt_pow_mul ε n0Norm hε hn
  refine ⟨κ, ?_⟩
  -- Goal: κ! · ε^κ · n0Norm < (2κ)!.
  unfold becBogoliubovCommutatorNorm
  -- Bound via κ! · κ! ≤ (2κ)! and ε^κ · n0Norm < κ!.
  have h_fact_pos : (0 : ℝ) < (Nat.factorial κ : ℝ) := by
    exact_mod_cast Nat.factorial_pos κ
  -- κ! · (ε^κ · n0Norm) < κ! · κ! ≤ (2κ)!.
  have h_left : (Nat.factorial κ : ℝ) * (ε^κ * n0Norm) <
      (Nat.factorial κ : ℝ) * (Nat.factorial κ : ℝ) :=
    mul_lt_mul_of_pos_left hκ h_fact_pos
  have h_right : (Nat.factorial κ : ℝ) * (Nat.factorial κ : ℝ) ≤
      (Nat.factorial (κ + κ) : ℝ) := by
    have := factorial_two_kappa_ge_factorial_kappa_squared κ
    have hsq : (Nat.factorial κ : ℝ)^2 = (Nat.factorial κ : ℝ) * (Nat.factorial κ : ℝ) := by ring
    linarith
  -- Associativity rearranges κ! · ε^κ · n0Norm = κ! · (ε^κ · n0Norm).
  have h_assoc : (Nat.factorial κ : ℝ) * ε^κ * n0Norm =
      (Nat.factorial κ : ℝ) * (ε^κ * n0Norm) := by ring
  linarith

/-! ## Conditional growth-bound failure for the prescribed sequence. -/

/-- The defined factorial sequence violates every supplied positive factorial-power bound. Legacy name does not identify an actual BEC platform. -/
theorem bec_falls_under_sharpened_no_go
    (ε n0Norm : ℝ) (hε : 0 < ε) (hn : 0 < n0Norm) :
    ¬ HasOperatorGrowthBound becBogoliubovCommutatorNorm ε n0Norm :=
  sharpened_no_go_super_factorial becBogoliubovCommutatorNorm ε n0Norm hε hn
    becBogoliubovCommutatorNorm_isSuperFactorialUnbounded

/-- Right side of inclusive OR for the prescribed sequence, for any real mirConst. This is not an exclusive physical classification. -/
theorem bec_bimodal_outcome (mirConst : ℝ) :
    PlatformBimodalOutcome becDKMParameters mirConst becBogoliubovCommutatorNorm := by
  right
  exact becBogoliubovCommutatorNorm_isSuperFactorialUnbounded

/-! ## Contrast between two prescribed mathematical sequences. -/

/-- The identically zero sequence satisfies the stated bound for positive epsilon and nonnegative reference norm. -/
theorem zero_seq_hasOperatorGrowthBound
    (ε n0Norm : ℝ) (hε : 0 < ε) (hn : 0 ≤ n0Norm) :
    HasOperatorGrowthBound (fun _ => 0) ε n0Norm := by
  intro κ
  -- 0 ≤ κ! · ε^κ · n0Norm because each factor is nonneg.
  have h1 : (0 : ℝ) ≤ (Nat.factorial κ : ℝ) := by exact_mod_cast Nat.zero_le _
  have h2 : (0 : ℝ) ≤ ε^κ := pow_nonneg hε.le κ
  have h3 : (0 : ℝ) ≤ (Nat.factorial κ : ℝ) * ε^κ := mul_nonneg h1 h2
  exact mul_nonneg h3 hn

/-- Conjunction contrasting zero with the prescribed factorial sequence. It does not compare actual graphene and BEC commutators or prove KMS quality. -/
theorem bec_distinguishes_from_graphene_super_factorial
    (ε n0Norm : ℝ) (hε : 0 < ε) (hn : 0 < n0Norm) :
    HasOperatorGrowthBound (fun _ => 0) ε n0Norm ∧
      ¬ HasOperatorGrowthBound becBogoliubovCommutatorNorm ε n0Norm :=
  ⟨zero_seq_hasOperatorGrowthBound ε n0Norm hε hn.le,
   bec_falls_under_sharpened_no_go ε n0Norm hε hn⟩

/-! ## Scope retained.
The factorial inequality, domination and contradiction proofs remain valid
for their actual quantifiers. The actual BEC Hamiltonian/growth construction
and its domains, state, regulator and physical controls are still BUILD;
this benchmark does not close or replace that original physical task. -/

end SKEFTHawking.DKMBootstrap
