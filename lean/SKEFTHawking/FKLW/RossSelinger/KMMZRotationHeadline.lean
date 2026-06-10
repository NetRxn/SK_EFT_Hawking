/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 36) — the KMM z-rotation word: error ≤ √2/2ᵏ at O(k) gates

The assembly of the whole Track-2 pipeline into the **z-rotation headline word**: for every phase
`φ` and precision `k` there is an explicit three-qubit Clifford+T word `W` (system + 2 ancillas) of
length `≤ 16800·k + 270` — **linear in `k`, i.e. O(log 1/ε) with exponent 1** — realizing the KMM
controlled-`C` (arXiv:1212.0822 §2.2) with, **unconditionally** (no prime-density hypothesis):

  * the `|0,00⟩` column **ring-exact** (`W` fixes the system-`|0⟩`, ancilla-`|00⟩` state on the
    nose — the `FixesE00` design),
  * the `|1,00⟩` column equal to `|1⟩ ⊗ |v⟩` with `|v⟩` the KMM ancilla state: a **unit** column
    whose `|00⟩`-amplitude is within `√2/2ᵏ` of `e^{iφ}` and whose ancilla-leakage mass is
    `≤ 2·√2/2ᵏ` (the inc-8/9 budget, `kmm_ancilla_state_full`).

By linearity these two columns are the full KMM guarantee on ancilla-initialized inputs:
`(α|0⟩+β|1⟩)⊗|00⟩ ↦ α|000⟩ + β|1⟩|v⟩ ≈ α|000⟩ + β·e^{iφ}|100⟩`. The pipeline: Lagrange four-squares
(inc 1) → the rounded approximant + unit state + leakage budget (inc 7–9) → the unconditional
quantitative column lemma (inc 32–33, `column_lemma_bounded`: circuit `C` within `280·colDenExp + 9`)
→ the controlled lift (inc 35, `ctrlLift_word_spec`: factor 30, `D` fixing `|00⟩`).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.Gate3Control
import SKEFTHawking.FKLW.RossSelinger.GilesSelingerColumnLemma
import SKEFTHawking.FKLW.RossSelinger.AncillaLeakage

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger
namespace Gate3

open ZOmegaSqrt2

/-! ### The KMM state column -/

/-- The KMM ancilla-state column: `|v⟩ = (u, 0, t₁, t₂)/√2^K` — approximant amplitude at `|00⟩`,
zero at `|01⟩`, the four-squares completion on the leakage slots. -/
def kmmCol (u t₁ t₂ : ZOmega) (K : ℕ) : Fin 2 × Fin 2 → ZOmegaSqrt2 := fun j =>
  if j = (0, 0) then mk u K else if j = (1, 0) then mk t₁ K else if j = (1, 1) then mk t₂ K else 0

theorem kmmCol_00 (u t₁ t₂ : ZOmega) (K : ℕ) : kmmCol u t₁ t₂ K (0, 0) = mk u K := rfl

theorem kmmCol_01 (u t₁ t₂ : ZOmega) (K : ℕ) : kmmCol u t₁ t₂ K (0, 1) = 0 := rfl

theorem kmmCol_10 (u t₁ t₂ : ZOmega) (K : ℕ) : kmmCol u t₁ t₂ K (1, 0) = mk t₁ K := rfl

theorem kmmCol_11 (u t₁ t₂ : ZOmega) (K : ℕ) : kmmCol u t₁ t₂ K (1, 1) = mk t₂ K := rfl

/-- The KMM column is a unit vector exactly when the three-slot `normSq`-sum is `1`. -/
theorem kmmCol_unit {u t₁ t₂ : ZOmega} {K : ℕ}
    (h : normSq (mk u K) + normSq (mk t₁ K) + normSq (mk t₂ K) = 1) :
    ∑ j, normSq (kmmCol u t₁ t₂ K j) = 1 := by
  have hexp : ∑ j, normSq (kmmCol u t₁ t₂ K j)
      = normSq (mk u K) + normSq 0 + (normSq (mk t₁ K) + normSq (mk t₂ K)) := by
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
    rfl
  rw [hexp, normSq_zero, add_zero, ← add_assoc]
  exact h

/-- Every entry of the KMM column sits at denominator level `≤ K`. -/
theorem kmmCol_colDenExp_le (u t₁ t₂ : ZOmega) (K : ℕ) :
    Gate2.colDenExp (kmmCol u t₁ t₂ K) ≤ K := by
  refine Finset.sup_le fun j _ => ?_
  show denExp (if j = (0, 0) then mk u K else if j = (1, 0) then mk t₁ K
    else if j = (1, 1) then mk t₂ K else 0) ≤ K
  split_ifs
  · rw [denExp_mk]
    exact ZOmega.lowestDenExp_le _ _
  · rw [denExp_mk]
    exact ZOmega.lowestDenExp_le _ _
  · rw [denExp_mk]
    exact ZOmega.lowestDenExp_le _ _
  · rw [show (0 : ZOmegaSqrt2) = mk 0 0 from rfl, denExp_mk]
    exact (ZOmega.lowestDenExp_le _ _).trans (Nat.zero_le _)

/-! ### Column facts for the controlled lift -/

/-- The `|0,00⟩` column of `ctrl8 D M` is ring-exactly the `|0,00⟩` indicator when `D` fixes
`|00⟩` — the initialized state is preserved on the nose. -/
theorem ctrl8_col_init {D M : Mat4} (hD : FixesE00 D) (i : Fin 2 × Fin 2 × Fin 2) :
    ctrl8 D M i (0, 0, 0) = if i = (0, 0, 0) then 1 else 0 := by
  rcases i with ⟨i₁, i₂⟩
  by_cases h1 : i₁ = (0 : Fin 2)
  · subst h1
    rw [show ctrl8 D M (0, i₂) (0, 0, 0) = D i₂ (0, 0) from by
        show (if (0 : Fin 2) = (0 : Fin 2) then
          (if (0 : Fin 2) = 0 then D i₂ (0, 0) else M i₂ (0, 0)) else 0) = D i₂ (0, 0)
        rw [if_pos rfl, if_pos rfl],
      hD i₂]
    by_cases h2 : i₂ = ((0 : Fin 2), (0 : Fin 2))
    · subst h2
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h2, if_neg fun h => h2 (Prod.ext_iff.mp h).2]
  · rw [show ctrl8 D M (i₁, i₂) (0, 0, 0) = 0 from if_neg h1,
      if_neg fun h => h1 (Prod.ext_iff.mp h).1]

/-- The `s = 0` block of the `|1,00⟩` column vanishes (no back-leakage into system-`|0⟩`). -/
theorem ctrl8_col_one_sys0 (D M : Mat4) (j : Fin 2 × Fin 2) :
    ctrl8 D M (0, j) (1, 0, 0) = 0 := by
  show (if (0 : Fin 2) = 1 then (if (0 : Fin 2) = 0 then D j (0, 0) else M j (0, 0)) else 0) = 0
  rw [if_neg (by decide : ¬ (0 : Fin 2) = 1)]

/-- The `s = 1` block of the `|1,00⟩` column is `M`'s `|00⟩` column. -/
theorem ctrl8_col_one_sys1 (D M : Mat4) (j : Fin 2 × Fin 2) :
    ctrl8 D M (1, j) (1, 0, 0) = M j (0, 0) := by
  show (if (1 : Fin 2) = 1 then (if (1 : Fin 2) = 0 then D j (0, 0) else M j (0, 0)) else 0)
    = M j (0, 0)
  rw [if_pos rfl, if_neg (by decide)]

/-! ### The z-rotation headline word -/

/-- **The KMM z-rotation word (UNCONDITIONAL, O(k) gates).** For every phase `φ` and precision
`k` there is a three-qubit Clifford+T word `W` of length `≤ 16800·k + 270` — linear in `k`,
i.e. `O(log 1/ε)` with exponent 1 for `ε = √2/2ᵏ` — such that:

  * the `|0,00⟩` column of `W` is **ring-exactly** the `|0,00⟩` indicator (initialized state
    preserved on the nose),
  * the `|1,00⟩` column is `|1⟩ ⊗ |v⟩` (zero on the system-`|0⟩` block) for a **unit** column
    `v` with `v(0,1) = 0`, `|00⟩`-amplitude within `√2/2ᵏ` of `e^{iφ}`, and total ancilla
    leakage `≤ 2·√2/2ᵏ`.

By linearity this is the full KMM ≤2-ancilla guarantee on ancilla-initialized inputs:
`(α|0⟩+β|1⟩)⊗|00⟩ ↦ α|000⟩ + β|1⟩⊗|v⟩ ≈ α|000⟩ + β·e^{iφ}|100⟩`. **No prime-density
hypothesis** — the only inputs are Lagrange four-squares and the constructive column lemma. -/
theorem kmm_z_rotation_word (φ : ℝ) (k : ℕ) :
    ∃ (W : List Gate3) (v : Fin 2 × Fin 2 → ZOmegaSqrt2),
      W.length ≤ 16800 * k + 270 ∧
      (∀ i, interp3 W i (0, 0, 0) = if i = (0, 0, 0) then 1 else 0) ∧
      (∀ j, interp3 W (0, j) (1, 0, 0) = 0) ∧
      (∀ j, interp3 W (1, j) (1, 0, 0) = v j) ∧
      (∑ j, normSq (v j) = 1) ∧
      v (0, 1) = 0 ∧
      ‖ZOmegaSqrt2.toComplex (v (0, 0)) - Complex.exp ((φ : ℂ) * Complex.I)‖
        ≤ Real.sqrt 2 / (2 : ℝ) ^ k ∧
      Complex.normSq (ZOmegaSqrt2.toComplex (v (1, 0)))
        + Complex.normSq (ZOmegaSqrt2.toComplex (v (1, 1)))
        ≤ 2 * (Real.sqrt 2 / (2 : ℝ) ^ k) := by
  obtain ⟨m₁, m₂, t₁, t₂, hunit, hamp, hleak⟩ := kmm_ancilla_state_full φ k
  have hvunit :
      ∑ j, normSq (kmmCol ((m₁ : ZOmega) + (m₂ : ZOmega) * ZOmega.ω ^ 2) t₁ t₂ (2 * k) j) = 1 :=
    kmmCol_unit hunit
  obtain ⟨M, hM, hMcol⟩ := Gate2.column_lemma_bounded _ hvunit
  obtain ⟨w, hw, hwlen⟩ := hM
  obtain ⟨D, hDinterp, hDfix, hDlen⟩ := ctrlLift_word_spec w
  refine ⟨ctrlLiftWord w, kmmCol ((m₁ : ZOmega) + (m₂ : ZOmega) * ZOmega.ω ^ 2) t₁ t₂ (2 * k),
    ?_, ?_, ?_, ?_, hvunit, rfl, hamp, hleak⟩
  · have h1 := kmmCol_colDenExp_le ((m₁ : ZOmega) + (m₂ : ZOmega) * ZOmega.ω ^ 2) t₁ t₂ (2 * k)
    omega
  · intro i
    rw [hDinterp, hw]
    exact ctrl8_col_init hDfix i
  · intro j
    rw [hDinterp, hw]
    exact ctrl8_col_one_sys0 D M j
  · intro j
    rw [hDinterp, hw, ctrl8_col_one_sys1]
    exact congrFun hMcol j

end Gate3
end SKEFTHawking.RossSelinger
