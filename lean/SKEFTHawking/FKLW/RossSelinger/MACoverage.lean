/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — the Matsumoto-Amano coverage recursion

With `ma_step_exists` (`MAStepStructural.lean`) supplying the reducing syllable for
every `kSO3 M ≥ 1`, the MA coverage is a structural recursion on `kSO3`:

  * **base** `kSO3 M = 0` (⟺ `M` is a Clifford): `cliffordBase` supplies a `≤ 6`-gate word;
  * **step** `kSO3 M ≥ 1`: strip the `ma_step` syllable `s` (`kSO3` drops by ≥ 1),
    recurse on `stripMat s M`, and prepend `sylWord s` (`interp_sylWord_stripMat`
    reconstructs `M`; `sylWord s` adds `≤ 3` gates).

This yields `maCoverage : realizable M → kSO3 M ≤ 3 → ∃ gs, interp gs = M ∧
gs.length ≤ 3·kSO3 M + 6` (`≤ 15`). The Clifford base (`kSO3 = 0 ⟹ Clifford ≤ 6`)
and the bridge (`μ ≤ 3 ⟹ kSO3 ≤ 3`) are kept as hypotheses here, discharged
separately; the recursion is unconditional.

## References

  * Giles-Selinger 2013 (arXiv:1312.6584) — MA normal form (Thm 2.3/4.1),
    T-count = `kSO3` (Lemma 4.10); length `≤ 3·kSO3 + (Clifford tail)`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected (`cliffordBase` is a hypothesis).

-/

import SKEFTHawking.FKLW.RossSelinger.MAStepStructural
import SKEFTHawking.FKLW.RossSelinger.MuDecrease
import SKEFTHawking.FKLW.RossSelinger.KMMReduceMu

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2

/-- **The MA coverage recursion** (fuel = `kSO3 M`): given the Clifford base case,
every realizable `M` with `kSO3 M ≤ 3` has a word of length `≤ 3·kSO3 M + 6`. Strong
induction on `n = kSO3 M`; the step strips an `ma_step` syllable (drops `kSO3`) and
prepends `sylWord s`. -/
theorem maCoverage_aux
    (cliffordBase : ∀ M, IsCliffordTRealizable M → kSO3 M = 0 →
      ∃ gs : List CliffordTGate, interp gs = M ∧ gs.length ≤ 6) :
    ∀ (n : ℕ) (M : Mat2), IsCliffordTRealizable M → kSO3 M = n → n ≤ 3 →
      ∃ gs : List CliffordTGate, interp gs = M ∧ gs.length ≤ 3 * n + 6 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M hM hkn hn3
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      obtain ⟨gs, hgs, hlen⟩ := cliffordBase M hM hkn
      exact ⟨gs, hgs, by omega⟩
    · have hk1 : 1 ≤ kSO3 M := by omega
      obtain ⟨s, hlt⟩ := ma_step_exists hM hk1
      have hmn : kSO3 (stripMat s M) < n := by rw [← hkn]; exact hlt
      obtain ⟨gs', hgs', hlen'⟩ :=
        ih (kSO3 (stripMat s M)) hmn (stripMat s M) (stripMat_realizable s hM) rfl (by omega)
      refine ⟨sylWord s ++ gs', ?_, ?_⟩
      · rw [interp_append, hgs', interp_sylWord_stripMat]
      · rw [List.length_append]
        have h3 := sylWord_length_le s
        omega

/-- **MA coverage**: a realizable `M` with `kSO3 M ≤ 3` has a word of length
`≤ 3·kSO3 M + 6` (given the Clifford base). -/
theorem maCoverage
    (cliffordBase : ∀ M, IsCliffordTRealizable M → kSO3 M = 0 →
      ∃ gs : List CliffordTGate, interp gs = M ∧ gs.length ≤ 6)
    {M : Mat2} (hM : IsCliffordTRealizable M) (hk3 : kSO3 M ≤ 3) :
    ∃ gs : List CliffordTGate, interp gs = M ∧ gs.length ≤ 3 * kSO3 M + 6 :=
  maCoverage_aux cliffordBase (kSO3 M) M hM rfl hk3

/-- **Coverage with the relaxed `N₃ = 15` bound** (the MA-deterministic value;
DR-confirmed to fit Item G's `L ≤ 90 < 100`): given the Clifford base and the
`μ → kSO3` bridge, every realizable `μ ≤ 3` matrix has a `≤ 15`-gate word. -/
theorem coverage_fifteen
    (cliffordBase : ∀ M, IsCliffordTRealizable M → kSO3 M = 0 →
      ∃ gs : List CliffordTGate, interp gs = M ∧ gs.length ≤ 6)
    (bridge : ∀ M, IsCliffordTRealizable M → muMeasure M ≤ 3 → kSO3 M ≤ 3)
    (M : Mat2) (hM : IsCliffordTRealizable M) (hμ : muMeasure M ≤ 3) :
    ∃ gs : List CliffordTGate, interp gs = M ∧ gs.length ≤ 15 := by
  have hk3 := bridge M hM hμ
  obtain ⟨gs, hgs, hlen⟩ := maCoverage cliffordBase hM hk3
  exact ⟨gs, hgs, by omega⟩

/-! ## Discharge of `Nonempty KMMReduction` at the relaxed `N₃ = 15` -/

open scoped Classical in
/-- The relaxed base finder: a `≤ 15`-gate word for `M` when one exists, else `[]`. -/
noncomputable def baseFinder15 (M : Mat2) : List CliffordTGate :=
  if h : ∃ gs : List CliffordTGate, interp gs = M ∧ gs.length ≤ 15 then Classical.choose h else []

theorem baseFinder15_length (M : Mat2) : (baseFinder15 M).length ≤ 15 := by
  unfold baseFinder15
  split
  · next h => exact (Classical.choose_spec h).2
  · simp

theorem baseFinder15_correct
    (coverage : ∀ M, IsCliffordTRealizable M → muMeasure M ≤ 3 →
      ∃ gs : List CliffordTGate, interp gs = M ∧ gs.length ≤ 15)
    (M : Mat2) (hM : IsCliffordTRealizable M) (hμ : muMeasure M ≤ 3) :
    interp (baseFinder15 M) = M := by
  have h := coverage M hM hμ
  unfold baseFinder15
  rw [dif_pos h]
  exact (Classical.choose_spec h).1

/-- **`Nonempty KMMReduction` from the Clifford base + the `μ → kSO3` bridge**: composing
the MA `coverage_fifteen` (`N₃ = 15`) with the `μ`-tracking recursion. The two hypotheses
(`cliffordBase`, `bridge`) are the sole remaining inputs — discharging them makes the KMM
exact-synthesis algorithm unconditional (orphan #2 substrate). No axiom (Inv #15). -/
theorem nonempty_kmmReduction_of_clifford_bridge
    (cliffordBase : ∀ M, IsCliffordTRealizable M → kSO3 M = 0 →
      ∃ gs : List CliffordTGate, interp gs = M ∧ gs.length ≤ 6)
    (bridge : ∀ M, IsCliffordTRealizable M → muMeasure M ≤ 3 → kSO3 M ≤ 3) :
    Nonempty KMMReduction :=
  ⟨{ reduce := fun M => kmmReduceMu baseFinder15 (muMeasure M) M
     N₃ := 15
     correct := fun M hM => interp_kmmReduceMu baseFinder15
       (fun M' hM' hμ' => baseFinder15_correct
         (fun M'' hM'' hμ'' => coverage_fifteen cliffordBase bridge M'' hM'' hμ'') M' hM' hμ')
       (muMeasure M) M hM (le_refl _)
     length_bound := fun M _ =>
       length_kmmReduceMu baseFinder15 15 baseFinder15_length (muMeasure M) M }⟩

end KMM

end SKEFTHawking.RossSelinger
