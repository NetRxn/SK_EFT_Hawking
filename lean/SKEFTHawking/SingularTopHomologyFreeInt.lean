/-
# Phase 5q.H (E1 CSC-PD tower) — top relative homology is free (the `hfree` foundation)

`hfree` (top-degree relative-homology freeness of a good-compact, `Module.Free ℤ (RelHomologyInt Sᶜ (m+2))`)
is a deep input threaded through the pdWindow. Its **base case** — a single point `S = {x}` — is a clean
discharge: `manifoldLocalHomologyIsoInt` gives `H₄(M, M∖x; ℤ) ≅ ℤ`, and `ℤ` is free, so
`Module.Free ℤ (RelHomologyInt {y | y ≠ x} 4)` follows by transport. This is the seed of the general
good-compact freeness (a good-compact is a finite chart-ball union; its top homology assembles from these
local `ℤ`'s via excision/MV — the substantial remaining step).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularLocalHomologyIsoInt
import SKEFTHawking.SingularGoodCompactInt

open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularLocalHomologyIsoInt
open SKEFTHawking.SingularGoodCompactInt (determinedByPointsInt)
open SKEFTHawking.IntOrientationSection (restrictToPointInt)

namespace SKEFTHawking.SingularTopHomologyFreeInt

/-- **The top relative homology at a point is free**: `H₄(M, M∖x; ℤ)` is a free ℤ-module (it is `≅ ℤ`
via `manifoldLocalHomologyIsoInt`). The base case of the good-compact top-homology freeness `hfree`. -/
theorem relHomology_point_top_free {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (x : M) :
    Module.Free ℤ (RelHomologyInt (X := TopCat.of M) {y | y ≠ x} 4) :=
  Module.Free.of_equiv (manifoldLocalHomologyIsoInt x).symm

/-- The local homology at a point is **torsion-free** (it is `≅ ℤ`). Stated on `{y | y ≠ x}` = `{x}ᶜ`
(the `restrictToPointInt` codomain), matching `manifoldLocalHomologyIsoInt`'s domain. -/
theorem localHomology_noZeroSMul {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (x : M) :
    NoZeroSMulDivisors ℤ (RelHomologyInt (X := TopCat.of M) {y | y ≠ x} 4) := by
  refine ⟨fun {c a} h => ?_⟩
  have hz : c • (manifoldLocalHomologyIsoInt x a) = 0 := by rw [← map_smul, h, map_zero]
  rcases smul_eq_zero.mp hz with hc | ha
  · exact Or.inl hc
  · exact Or.inr ((LinearEquiv.map_eq_zero_iff _).mp ha)

/-- **The top relative homology of a good-compact is TORSION-FREE.** `determinedByPointsInt 4 K` embeds
`H₄(M|K;ℤ)` into the product of the pointwise locals `H₄(M|x;ℤ) ≅ ℤ`, each torsion-free; a `ℤ`-multiple
of a class that dies is `0`. This is HALF of `hfree` (top-homology freeness): free = torsion-free +
finitely-generated (the latter from the finite chart-cover MV — the remaining step). -/
theorem relHomology_goodCompact_top_noZeroSMul {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] {K : Set ↑(TopCat.of M)}
    (hdbp : determinedByPointsInt 4 K) :
    NoZeroSMulDivisors ℤ (RelHomologyInt (X := TopCat.of M) Kᶜ 4) := by
  refine ⟨fun {m α} hmα => ?_⟩
  rcases eq_or_ne m 0 with hm | hm
  · exact Or.inl hm
  · refine Or.inr (hdbp α (fun x hx => ?_))
    haveI : NoZeroSMulDivisors ℤ (RelHomologyInt (X := TopCat.of M) ({x}ᶜ) 4) :=
      localHomology_noZeroSMul (M := M) x
    have hres : m • restrictToPointInt hx 4 α = 0 := by
      rw [← map_smul, hmα, map_zero]
    exact (smul_eq_zero.mp hres).resolve_left hm

end SKEFTHawking.SingularTopHomologyFreeInt
