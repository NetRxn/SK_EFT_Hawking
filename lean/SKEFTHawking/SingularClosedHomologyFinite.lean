import Mathlib
import SKEFTHawking.SingularPD4Instances
import SKEFTHawking.SingularUCFinite

/-!
# Phase 5q.H — the closed-4-manifold HOMOLOGY finiteness + homology-side Poincaré duality

Track-2's terminal cylinder engine `CylinderWAdmPinned.ofClosedPDSuspIntertwineNorm` consumes, on the
base `M`, the finiteness of the mod-2 HOMOLOGY in degrees `2,3,4` (`hM2/hM3/hM4`) and the homology-side
Poincaré-duality equality `finrank H₁(M) = finrank H₃(M)` (`basePD`). The 5q.G substrate discharged the
COHOMOLOGY side (`finiteDimensional_cohomology_of_closed`, degrees `1,2,3`, and `dimeq_of_closed`,
`H¹ = H³`); this module transports it to the homology side.

The `P₄(univ)` fundamental-duality windows already produce, internally to
`finiteDimensional_cohomology_windows`, the three degree-crossing equivalences

    `H¹(M) ≅ H₃(M)`,  `H²(M) ≅ H₂(M)`,  `H³(M) ≅ H₁(M)`

(each is `(compactlySupportedTopEquiv).symm.trans (fundamentalDuality_bijective …)`). We reconstruct
those windows here and read off:

* `finiteDimensional_homology_of_closed` — `H₁, H₂, H₃` finite-dimensional (from the cohomology findims);
* the homology `basePD`: `finrank H₁ = finrank H₃` = `finrank H³ = finrank H¹` (the window transports the
  cohomology `dimeq_of_closed` to the homology side).

Degree `4` (`hM4`) is the TOP class and is NOT in the `P₄` window (which covers `1,2,3`); it is handled
separately (`SingularClosedTopHomologyFinite`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularUCFinite SKEFTHawking.SingularCompactlySupportedTop
open SKEFTHawking.SingularPDWindow4 SKEFTHawking.SingularPD4Instances
open SKEFTHawking.SingularFundamentalClass SKEFTHawking.SingularChartBridge
open SKEFTHawking.SingularRelativeHomologyMod2

namespace SKEFTHawking.SingularClosedHomologyFinite

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-- **The homology finiteness (degrees 1,2,3) + homology-side Poincaré duality of a closed charted
4-manifold**, hypothesis-free (the fundamental-class `P₄(univ)` windows cross the cohomology findims
`finiteDimensional_cohomology_of_closed` onto the homology side, and transport `dimeq_of_closed`
`H¹ = H³` to `H₁ = H₃`). -/
theorem finiteDimensional_homology_of_closed :
    FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 1)
      ∧ FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 2)
      ∧ FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3)
      ∧ Module.finrank (ZMod 2) (Homology (TopCat.of M) 1)
        = Module.finrank (ZMod 2) (Homology (TopCat.of M) 3) := by
  obtain ⟨zM, hzM, hcyc, hloc, _⟩ := exists_fundClass_P4_data (M := M)
  have hP4 := pdWindowP4_univ zM hzM hcyc hloc isOpen_univ
  obtain ⟨⟨h21, h30, _hD0⟩, h12⟩ := hP4
  have e12 : Cohomology (TopCat.of M) 1 ≃ₗ[ZMod 2] Homology (TopCat.of M) 3 :=
    (compactlySupportedTopEquiv (M := TopCat.of M) (0 + 1)).symm.trans
      (LinearEquiv.ofBijective _
        (fundamentalDuality_bijective_of_openDuality_univ_bijective isOpen_univ _ _ h12))
  have e21 : Cohomology (TopCat.of M) 2 ≃ₗ[ZMod 2] Homology (TopCat.of M) 2 :=
    (compactlySupportedTopEquiv (M := TopCat.of M) (1 + 1)).symm.trans
      (LinearEquiv.ofBijective _
        (fundamentalDuality_bijective_of_openDuality_univ_bijective isOpen_univ _ _ h21))
  have e30 : Cohomology (TopCat.of M) 3 ≃ₗ[ZMod 2] Homology (TopCat.of M) 1 :=
    (compactlySupportedTopEquiv (M := TopCat.of M) (2 + 1)).symm.trans
      (LinearEquiv.ofBijective _
        (fundamentalDuality_bijective_of_openDuality_univ_bijective isOpen_univ _ _ h30))
  have hc := finiteDimensional_cohomology_of_closed (M := M)
  haveI := hc.1
  haveI := hc.2.1
  haveI := hc.2.2
  refine ⟨e30.finiteDimensional, e21.finiteDimensional, e12.finiteDimensional, ?_⟩
  rw [← e30.finrank_eq, ← e12.finrank_eq]
  exact (dimeq_of_closed (M := M)).symm

/-- **The TOP mod-2 homology `H₄(M)` of a closed CONNECTED charted 4-manifold is finite-dimensional**
(the `P₄` window does not cover the top class). Route: the single-point restriction
`ρ_{x₀} : H₄(M) → H₄(M | x₀)` is injective for connected `M`
(`restrictHomologyToPoint_injective`, the clopen-vanishing-set argument), and the local homology
`H₄(M | x₀) ≅ ℤ/2` (`manifoldLocalIso`) is finite-dimensional, so `H₄(M)` embeds into a `1`-dimensional
space. Requires `PreconnectedSpace M` — the disconnected case is a separate residual. -/
theorem finiteDimensional_topHomology_of_closed_connected [PreconnectedSpace M] :
    FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4) := by
  obtain ⟨x₀⟩ := ‹Nonempty M›
  haveI : FiniteDimensional (ZMod 2)
      (RelativeHomology (X := TopCat.of M) ({x₀}ᶜ) 4) :=
    (manifoldLocalIso (m := 2) (M := M) x₀).symm.finiteDimensional
  exact FiniteDimensional.of_injective
    (restrictHomologyToPoint (X := TopCat.of M) x₀ 4)
    ((injective_iff_map_eq_zero _).mpr
      (fun α h => restrictHomologyToPoint_injective (m := 2) (x₀ := x₀) h))

end SKEFTHawking.SingularClosedHomologyFinite
