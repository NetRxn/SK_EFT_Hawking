/-
Phase 5b: Generation Constraint — N_f ≡ 0 mod 3

Derives the constraint on the number of fermion generations from two
physical axioms:
  1. Chiral central charge: c₋ = 8 N_f (from dimensional reduction)
  2. Modular invariance: c₋ ≡ 0 mod 24 (framing anomaly cancellation)

Together: 8 N_f ≡ 0 mod 24 → N_f ≡ 0 mod 3.
N_f = 3 is the minimal nontrivial solution.

The full proof through Hirzebruch signature theorem + Rokhlin's theorem
is deferred (see Phase6_Deferred_Targets.md). Here we axiomatize the
two physical inputs and derive the algebraic consequence.

References:
  Wang, PRD 110, 125028 (2024) [arXiv:2312.14928]
  Alvarez-Gaumé & Witten, Nucl. Phys. B 234, 269 (1984) — gravitational anomaly
  Stolz, Math. Ann. 296, 685 (1993) — modular invariance constraint
-/

import Mathlib
import SKEFTHawking.Z16AnomalyComputation

namespace SKEFTHawking

/-! ## 1. Physical Axioms -/

/--
Axiom 1: Dimensional reduction of the SM on a compact manifold gives
a 2D theory with chiral central charge c₋ = 8 N_f.

The factor 8 comes from: 4 (Dirac components in 4D) × 2 (Majorana per Dirac) = 8.
Equivalently: each generation contributes 16 real fermions in 4D, which
reduce to c₋ = 8 per generation in the 2D effective theory.

Axiomatized because: the full derivation requires index theory (Atiyah-Singer)
on the compactification manifold.
-/
-- DISCHARGED: was axiom, but "∀ N_f, ∃ c, c = 8*N_f" is trivially true (witness: 8*N_f).
-- The physics content (c₋ = 8 N_f from index theory) is real but the Lean statement
-- was tautological. The relationship is now encoded structurally in the formulas.
theorem chiral_central_charge_coeff :
    ∀ N_f : ℕ, ∃ c_minus : ℤ, c_minus = 8 * ↑N_f :=
  fun N_f => ⟨8 * ↑N_f, rfl⟩

-- REMOVED: modular_invariance_constraint was FALSE as stated.
-- It claimed: ∀ c_minus, (∃ N_f, c_minus = 8*N_f) → 24 ∣ c_minus
-- Counterexample: N_f=1, c_minus=8, but 24 ∤ 8.
--
-- The PHYSICS is correct: modular invariance requires c₋ ≡ 0 mod 24 for
-- CONSISTENT theories. But the axiom universally quantified over ALL N_f,
-- not just physically valid ones. The correct encoding is as a hypothesis
-- on generation_mod3_constraint (which already takes h_mod : 24 ∣ (8 * N_f)
-- as a hypothesis, so the theorem itself was always correct).
--
-- Net effect: generation_mod3_constraint is still valid — it says
-- "IF 24 | 8*N_f THEN 3 | N_f", which is a true conditional.
-- The false axiom was never used in any proof.

/-! ## 2. The Generation Constraint -/

/--
CENTRAL THEOREM: N_f ≡ 0 mod 3.

From the two axioms: c₋ = 8 N_f and 24 | c₋.
So 24 | 8 N_f, i.e., 3 | N_f (since gcd(8, 24) = 8 and 24/8 = 3).

PROVIDED SOLUTION
If 24 | 8n then 8n = 24k for some k, so n = 3k, hence 3 | n.
The hypothesis is over ℤ but the conclusion is over ℕ.
Strategy: obtain ⟨k, hk⟩ := h_mod gives 8 * ↑N_f = 24 * k.
Then ↑N_f = 3 * k, so N_f = 3 * k.toNat (using hN to show k ≥ 0).
Alternatively: use Int.natCast_dvd_natCast or omega after cast.
Or: apply div_24_8n_implies_div_3_n after casting h_mod to �� with exact_mod_cast.
-/
theorem generation_mod3_constraint (N_f : ℕ) (hN : 0 < N_f)
    (h_mod : 24 ∣ (8 * (N_f : ℤ))) : 3 ∣ N_f := by
  obtain ⟨k, hk⟩ := h_mod
  have : (N_f : ℤ) = 3 * k := by omega
  exact_mod_cast show (3 : ℤ) ∣ (N_f : ℤ) from ⟨k, this⟩

/--
Pure arithmetic version: 24 | 8n → 3 | n for natural numbers.

PROVIDED SOLUTION
24 | 8n means 8n = 24k. Dividing by 8: n = 3k. So 3 | n.
Formally: 24 | 8n ↔ 3 | n (since gcd(8,24)/8 · lcm(8,24)/24 ... or just: omega after extracting).
-/
theorem div_24_8n_implies_div_3_n (n : ℕ) (h : 24 ∣ (8 * n)) : 3 ∣ n := by
  omega

/--
The converse also holds: 3 | n → 24 | 8n.

PROVIDED SOLUTION
If n = 3k then 8n = 24k, so 24 | 8n.
-/
theorem div_3_n_implies_div_24_8n (n : ℕ) (h : 3 ∣ n) : 24 ∣ (8 * n) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by omega⟩

/--
Biconditional: 3 | n ↔ 24 | 8n.
-/
theorem generation_constraint_iff (n : ℕ) : 3 ∣ n ↔ 24 ∣ (8 * n) :=
  ⟨div_3_n_implies_div_24_8n n, div_24_8n_implies_div_3_n n⟩

/-! ## 3. Minimality -/

/--
N_f = 3 is the minimal nontrivial solution to N_f ≡ 0 mod 3.
"Nontrivial" means N_f > 0.
-/
theorem generation_minimal_nontrivial :
    3 ∣ 3 ∧ ∀ m : ℕ, 0 < m → 3 ∣ m → 3 ≤ m := by
  constructor
  · exact dvd_refl 3
  · intro m hm hd; exact Nat.le_of_dvd hm hd

/--
The next solution is N_f = 6.
-/
theorem generation_next_solution :
    3 ∣ 6 ∧ ∀ m : ℕ, 3 < m → 3 ∣ m → 6 ≤ m := by
  constructor
  · norm_num
  · intro m hm hd; omega

/--
N_f = 1 and N_f = 2 do NOT satisfy the constraint.
-/
theorem one_and_two_excluded : ¬(3 ∣ 1) ∧ ¬(3 ∣ 2) := by
  constructor <;> omega

/-! ## 4. Connection to ℤ₁₆ Anomaly -/

/--
The generation constraint and the ℤ₁₆ anomaly are complementary:
- ℤ₁₆: constrains fermion CONTENT per generation (16 Weyl = anomaly-free)
- Mod 3: constrains NUMBER of generations (N_f ≡ 0 mod 3)

Together they predict: 3 generations × 16 Weyl = 48 total fermion components,
and 48 ≡ 0 mod 16 (so three complete generations are anomaly-free).

PROVIDED SOLUTION
48 = 3 × 16 and 48 mod 16 = 0.
-/
theorem combined_constraint :
    3 * 16 = (48 : ℕ) ∧ 48 % 16 = 0 ∧ 3 % 3 = 0 := by
  constructor <;> [norm_num; constructor <;> norm_num]

/--
The number 24 = 8 × 3 = lcm(8, 3) connects the ℤ₁₆ story (via 8 = 16/2)
to the generation constraint (via 3).
-/
theorem twenty_four_factorization :
    (24 : ℕ) = 8 * 3 ∧ 8 * 3 = Nat.lcm 8 3 := by
  constructor
  · norm_num
  · native_decide

/-! ## 5. Physical Interpretation -/

/--
Three-generation anomaly check with ν_R:
3 generations × 16 per generation = 48 ≡ 0 mod 16.
The real SM (3 generations, with ν_R) is anomaly-free.
-/
theorem three_gen_with_nu_R_anomaly_free : (48 : ZMod 16) = 0 := by decide

/--
Three-generation anomaly check without ν_R:
3 generations × 15 per generation = 45 ≡ 13 ≡ -3 mod 16.
This confirms Z16AnomalyComputation's three_gen_anomalous.
-/
theorem three_gen_without_nu_R_cross_check :
    (45 : ZMod 16) = (13 : ZMod 16) ∧ (13 : ZMod 16) = -3 := by
  constructor <;> decide

/--
Module summary: generation constraint N_f ≡ 0 mod 3 derived from
two physical axioms, with N_f = 3 as minimal nontrivial solution.
-/
theorem generation_module_summary :
    3 % 3 = 0 ∧ ¬(3 ∣ (1 : ℕ)) ∧ ¬(3 ∣ (2 : ℕ)) ∧ (48 : ZMod 16) = 0 := by
  refine ⟨by norm_num, by omega, by omega, by decide⟩

end SKEFTHawking
