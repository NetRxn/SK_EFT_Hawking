import Mathlib
import SKEFTHawking.SingularPDWindow4
import SKEFTHawking.SingularUCFinite
import SKEFTHawking.PoincareDualityConstruct
import SKEFTHawking.SingularFundamentalDualityEndpoint
import SKEFTHawking.SingularCupH13
import SKEFTHawking.SingularBockstein
import SKEFTHawking.PoincareDualityWuFormula

/-!
# Phase 5q.G (G1 X6) — the `PoincareDual4Mid` INSTANCE: the genuine PD datum is a THEOREM

For any closed (compact, `T2`, nonempty) charted 4-manifold, the Poincaré-duality datum
`PoincareDual4Mid (TopCat.of M)` is CONSTRUCTED: `mu := fundamentalFunctional` (the Kronecker
pairing against the geometric fundamental class `[M]`), `findim` from the Erdős–Kaplansky window
assembly (X5b) on the `P₄(univ)` Bott–Tu tower, and `nondeg` through the committed
`capH`-injectivity / `nondeg_of_duality_injective` chain, with the `(2,1)`-window bijectivity of
`P₄(univ)` feeding the `⊤`-collapse endpoint bridge. No hypothesis-structure remains.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.SingularOpenDualityMVConnSquare SKEFTHawking.SingularPDWindow4
open SKEFTHawking.SingularUCFinite SKEFTHawking.PoincareDualityConstruct
open SKEFTHawking.SingularFundamentalClass SKEFTHawking.SingularChartBridge
open SKEFTHawking.SingularFundamentalDualityEndpoint

namespace SKEFTHawking.SingularPD4Instances

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-- The `P₄(univ)` package at a fundamental-class chain representative: the master cycle, its
boundary/cycle data, the local-generator property, and the class identification. -/
theorem exists_fundClass_P4_data :
    ∃ (zM : SingularChain (TopCat.of M) (1 + 0 + 3))
      (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
      (hcyc : castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
        ∈ cycles (TopCat.of M) (2 + 2)),
      (∀ x : M, SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
          (X := TopCat.of M) x (2 + 2) (Homology.mk (TopCat.of M) (2 + 2)
            ⟨castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
        = (manifoldLocalIso x).symm 1)
      ∧ Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩
        = SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M) := by
  obtain ⟨zc, hzc⟩ := Submodule.Quotient.mk_surjective _
    (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M))
  have hcast : castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega)
      (zc.1 : SingularChain (TopCat.of M) (1 + 0 + 3)) = zc.1 := by
    rw [castChain_eq]
  refine ⟨zc.1, LinearMap.mem_ker.mp zc.2, by rw [hcast]; exact zc.2, ?_, ?_⟩
  · intro x
    have hclass : Homology.mk (TopCat.of M) (2 + 2)
        ⟨castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zc.1,
          by rw [hcast]; exact zc.2⟩
        = SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M) :=
      (congrArg (Homology.mk (TopCat.of M) (2 + 2)) (Subtype.ext hcast)).trans hzc
    rw [hclass]
    exact SKEFTHawking.SingularFundamentalClass.fundamentalClass_restricts x
  · exact (congrArg (Homology.mk (TopCat.of M) (2 + 2)) (Subtype.ext hcast)).trans hzc

/-- The three window findims of the closed charted 4-manifold, hypothesis-free. -/
theorem finiteDimensional_cohomology_of_closed :
    FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 1)
      ∧ FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 2)
      ∧ FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 3) := by
  obtain ⟨zM, hzM, hcyc, hloc, _⟩ := exists_fundClass_P4_data (M := M)
  exact finiteDimensional_cohomology_windows zM hzM isOpen_univ
    (pdWindowP4_univ zM hzM hcyc hloc isOpen_univ)

/-- The middle-dimension non-degeneracy of the closed charted 4-manifold, hypothesis-free. -/
theorem nondeg_of_closed :
    Function.Injective
      ⇑((cupH24 (X := TopCat.of M)).compr₂ (fundamentalFunctional (m := 2) (M := M))) := by
  obtain ⟨zM, hzM, hcyc, hloc, hclass⟩ := exists_fundClass_P4_data (M := M)
  have hP4 := pdWindowP4_univ zM hzM hcyc hloc isOpen_univ
  refine nondeg_of_duality_injective ?_
  -- the capH-injectivity at the castChain'd presentation, transported to `[M]`
  have hbij := fundamentalDuality_bijective_of_openDuality_univ_bijective
    (M := TopCat.of M) isOpen_univ
    (castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
    (chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM) hP4.1.1
  have hinj := capH_injective_of_fundamentalDuality_injective (M := TopCat.of M)
    (k := 2) (m := 1)
    (castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
    (chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM) hbij.injective
  have hclass' : Homology.mk (TopCat.of M) (2 + 1 + 1)
      ⟨castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM,
        SKEFTHawking.SingularDualityEmpty.cycle_of_subspaceChains_empty _
          (by rw [chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM]
              exact Submodule.zero_mem _)⟩
      = SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M) :=
    (congrArg (Homology.mk (TopCat.of M) (2 + 1 + 1))
      (Subtype.ext rfl)).trans hclass
  rwa [hclass'] at hinj

open SKEFTHawking.PoincareDualityWu in
/-- **G1 (X6): `PoincareDual4Mid` is a THEOREM** — the middle-dimension Poincaré-duality datum
of a closed charted 4-manifold is constructed from the geometric fundamental class and the
Bott–Tu `P₄(univ)` tower. No hypothesis-structure remains. -/
noncomputable def poincareDual4Mid_of_closed :
    PoincareDual4Mid (TopCat.of M) where
  mu := fundamentalFunctional (m := 2)
  findim := (finiteDimensional_cohomology_of_closed (M := M)).2.1
  nondeg := nondeg_of_closed (M := M)

/-- **The descended cap–cup adjunction with `[M]` at `(1,3)`**: `μ(a ∪ b) = ⟨b, a ⌢ [M]⟩` —
the `(1,3)`-mirror of `fundamentalFunctional_cupH24` (`kronecker_cup_cap` is `(k,l)`-generic). -/
theorem fundamentalFunctional_cupH13 (a : Cohomology (TopCat.of M) 1)
    (b : Cohomology (TopCat.of M) 3) :
    fundamentalFunctional (m := 2) (M := M) (cupH13 a b)
      = kroneckerH (X := TopCat.of M) 3 b (capH 1 2 a
          (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M))) := by
  obtain ⟨fa, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨fb, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  obtain ⟨zM, hzM⟩ := Submodule.Quotient.mk_surjective _
    (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M))
  rw [fundamentalFunctional_apply, ← hzM]
  simp only [cupH13_mk_mk, kroneckerH_mk_mk]
  exact SKEFTHawking.SingularCapChainIncl.kronecker_cup_cap fa.1 fb.1 zM.1

/-- Fresh-budget helper: the `(1,2)`-window `capH`-injectivity at the fundamental class. -/
private theorem capH12_injective_of_closed :
    Function.Injective (fun a : Cohomology (TopCat.of M) 1 =>
      capH 1 2 a
        (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M))) := by
  obtain ⟨zM, hzM, hcyc, hloc, hclass⟩ := exists_fundClass_P4_data (M := M)
  have hP4 := pdWindowP4_univ zM hzM hcyc hloc isOpen_univ
  have hbij := fundamentalDuality_bijective_of_openDuality_univ_bijective
    (M := TopCat.of M) (k := 1) (m := 2) isOpen_univ
    (castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
    (chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM) hP4.2
  have hinj := capH_injective_of_fundamentalDuality_injective (M := TopCat.of M)
    (k := 1) (m := 2)
    (castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
    (chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM) hbij.injective
  have hclass' : Homology.mk (TopCat.of M) (1 + 2 + 1)
      ⟨castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM,
        SKEFTHawking.SingularDualityEmpty.cycle_of_subspaceChains_empty _
          (by rw [chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM]
              exact Submodule.zero_mem _)⟩
      = SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M) :=
    (congrArg (Homology.mk (TopCat.of M) (1 + 2 + 1)) (Subtype.ext rfl)).trans hclass
  rwa [hclass'] at hinj

/-- **The `(1,3)` non-degeneracy of the closed 4-manifold** — direct through the `(1,2)`-window
of `P₄(univ)` (no transpose argument needed: the extended predicate carries the window). -/
theorem nondeg13_of_closed :
    Function.Injective
      ⇑((cupH13 (X := TopCat.of M)).compr₂ (fundamentalFunctional (m := 2) (M := M))) := by
  have hinj := capH12_injective_of_closed (M := M)
  rw [injective_iff_map_eq_zero]
  intro a ha
  refine hinj ?_
  show capH 1 2 a (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M))
    = capH 1 2 0 (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M))
  rw [map_zero, LinearMap.zero_apply]
  refine homology_eq_zero_of_kroneckerH (2 + 1) _ (fun ω => ?_)
  rw [← fundamentalFunctional_cupH13]
  exact LinearMap.congr_fun ha ω

/-- **`dim H¹ = dim H³`** — the `(1,2)`-window equivalence + the UC dual-dimension chain. -/
theorem dimeq_of_closed :
    Module.finrank (ZMod 2) (Cohomology (TopCat.of M) 1)
      = Module.finrank (ZMod 2) (Cohomology (TopCat.of M) 3) := by
  obtain ⟨zM, hzM, hcyc, hloc, _⟩ := exists_fundClass_P4_data (M := M)
  have hP4 := pdWindowP4_univ zM hzM hcyc hloc isOpen_univ
  have e12 : Cohomology (TopCat.of M) 1
      ≃ₗ[ZMod 2] Homology (TopCat.of M) (2 + 1) :=
    (SKEFTHawking.SingularCompactlySupportedTop.compactlySupportedTopEquiv
      (M := TopCat.of M) 1).symm.trans
      (LinearEquiv.ofBijective _
        (fundamentalDuality_bijective_of_openDuality_univ_bijective (k := 1) (m := 2)
          isOpen_univ _ _ hP4.2))
  haveI hfd1 := (finiteDimensional_cohomology_of_closed (M := M)).1
  haveI hfd3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) (2 + 1)) :=
    LinearEquiv.finiteDimensional e12
  have u3 := ucDualEquiv (TopCat.of M) 2
  calc Module.finrank (ZMod 2) (Cohomology (TopCat.of M) 1)
      = Module.finrank (ZMod 2) (Homology (TopCat.of M) (2 + 1)) := e12.finrank_eq
    _ = Module.finrank (ZMod 2)
          (Module.Dual (ZMod 2) (Homology (TopCat.of M) (2 + 1))) :=
        Subspace.dual_finrank_eq.symm
    _ = Module.finrank (ZMod 2) (Cohomology (TopCat.of M) 3) := u3.symm.finrank_eq

open SKEFTHawking.PoincareDualityWuFormula in
/-- **G1 (X6): `PoincareDual4Lo` is a THEOREM** — the `(1,3)` Poincaré-duality datum of a closed
charted 4-manifold, fully constructed: the genuine cup pairing `cupH13`, the genuine Bockstein
`Sq1`, the Erdős–Kaplansky findims, the direct `(1,2)`-window non-degeneracy, and the PD
dimension equality. No hypothesis-structure remains. -/
noncomputable def poincareDual4Lo_of_closed :
    PoincareDual4Lo (TopCat.of M) where
  mu := fundamentalFunctional (m := 2)
  cup13 := cupH13
  sq1₃ := SKEFTHawking.SingularBockstein.Sq1 (n := 2)
  findim₁ := (finiteDimensional_cohomology_of_closed (M := M)).1
  findim₃ := (finiteDimensional_cohomology_of_closed (M := M)).2.2
  nondeg₁₃ := nondeg13_of_closed (M := M)
  dimeq := dimeq_of_closed (M := M)


end SKEFTHawking.SingularPD4Instances
