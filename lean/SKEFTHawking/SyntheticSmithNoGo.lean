/-
# Phase 5q.H (E3/E4) — NO-GO: no synthetic (empty-carrier) Smith map into the tied carrier

Kernel backing for the settled fork `synthetic-smith-map-to-tied-carrier` (SETTLED_FORKS, 2026-07-03;
audit-flagged refutable-but-unencoded, encoded 2026-07-12 arm-2 per ADR-007 N-E): the `smithDataHom`
shortcut — mapping every Smith-neighbor class to `[emptySM, (σ, 0)]` and transporting the grade
synthetically — CANNOT build the Smith map into the 5q.H TIED carrier `pinPlusGMTiedData`. The tie
field `htie : reduce16to2 grade16 = swTotalNe s t2` that defeats `synthetic-grade-ker-bot-nogo`
SIMULTANEOUSLY forces every tied structure on an EMPTY carrier to have EVEN `ℤ/16`-grade
(`swTotalNe = 0` on empty carriers), so the odd generator (`grade16 = 1`, the ℝP⁴ class) can never
be synthetically hosted on `emptySM` — an odd grade requires a REAL `w₁⁴ = 1` manifold. The genuine
geometric Smith map into the tied carrier is irreducibly the §9.3 geometric input (gap-map node N1b).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusGMTiedData

open SKEFTHawking.PinPlusTiedData

namespace SKEFTHawking.PinPlusGMTiedData

variable {k : WithTop ℕ∞} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **Empty carriers are forced EVEN**: any tied GM structure on a singular manifold with empty
carrier has `reduce16to2 grade16 = 0` — the `htie` parity tie evaluated at `swTotalNe = 0`. -/
theorem gmTiedStr_grade_even_of_isEmpty {s : SingularManifold PUnit k I} [IsEmpty s.M]
    (σ : GMTiedStr I s) : reduce16to2 σ.grade16 = 0 := by
  rw [σ.htie]
  exact swTotalNe_of_isEmpty σ.t2

/-- **The synthetic-Smith no-go (registered backing)**: no tied GM structure on an EMPTY carrier can
carry the odd generator — `grade16 ≠ 1`. So the `emptySM`-based `smithGMTiedHom` shortcut is
uninhabitable at the odd class: the tie that makes `ker = ⊥` possible blocks every synthetic Smith
map into the tied carrier. Falsifiable and non-vacuous: on the UNTIED carrier the analogous structure
with `grade16 = 1` exists (the tie field is exactly what fails). -/
theorem gmTiedStr_empty_grade16_ne_one {s : SingularManifold PUnit k I} [IsEmpty s.M]
    (σ : GMTiedStr I s) : σ.grade16 ≠ 1 := by
  intro h
  have heven := gmTiedStr_grade_even_of_isEmpty σ
  rw [h] at heven
  exact absurd heven (by decide)

end SKEFTHawking.PinPlusGMTiedData
