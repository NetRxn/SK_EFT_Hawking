/-
# Phase 5q.H (E1 integral topology) — the cohomology MV middle-exactness node `(B)` (concrete lift)

The concrete heart of `relCohomMv_exact_middleInt`, obtained by dualising the degreewise-split
relative-homology MV chain SES `0 → K → Q → RelChain(U∪V) → 0` (`Q = C(M)/(C(U)+C(V))`, `K = ker π`) —
the field-UC-free, torsion-safe route the on-main real-coefficient
`SingularRelativeCohomologyMVMiddle.relCohomMv_exact_middle` cannot take (it needs the universal
coefficient theorem / finite-dimensional Kronecker duality).

`exists_lift_cochain`: given a cocycle `ω` (`coboundary ω = 0`) vanishing on the small chains `C(U)+C(V)`,
there is `H` (also vanishing on the small chains) with `ω − δH` vanishing on all of `C(U∪V)`. The lift
`ω − δH ∈ relCochainsInt (U∪V)` is the `Δ`-preimage witness of the middle exactness. The construction
descends `ω` to `Hom(Q)`, restricts to the acyclic `Hom(K)`
(`SingularKComplexAcyclicInt.hom_K_cocycle_eq_coboundary`), and extends the resulting primitive back
through the split retract of `π`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `native_decide`, no `maxHeartbeats`, no axiom.
-/
import Mathlib
import SKEFTHawking.SingularKComplexAcyclicInt
import SKEFTHawking.SingularRelativeCohomologyMVChaseInt

open SKEFTHawking.SingularCohomologyInt SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeMVInt SKEFTHawking.SingularSmallChainsSplitInt
open SKEFTHawking.SingularKComplexAcyclicInt
open SKEFTHawking.SingularEuclideanCapIsoInt SKEFTHawking.SingularRelativeCohomologyRestrictInt
open SKEFTHawking.SingularRelativeCohomologyMVInt SKEFTHawking.SingularRelativeCohomologyMVChaseInt

namespace SKEFTHawking.SingularCohomMvMiddleInt

variable {M : TopCat}

/-- **The concrete cohomology-MV lift `(B)`.** Given `ω : Cᵐ⁺¹(M;ℤ)` vanishing on the small chains
`C(U)+C(V)` and a cocycle (`δω = 0`), there is `H : Cᵐ(M;ℤ)` vanishing on `C(U)+C(V)` with `ω − δH`
vanishing on **all** of `C(U∪V)`. -/
theorem exists_lift_cochain (U V : Set M) (hU : IsOpen U) (hV : IsOpen V) (m : ℕ)
    (ω : SingularCochainInt M (m + 1))
    (hmv : ∀ c ∈ mvUnionChainsInt U V (m + 1), kronecker ω c = 0)
    (hcocy : coboundary M (m + 1) ω = 0) :
    ∃ H : SingularCochainInt M m,
      (∀ c ∈ mvUnionChainsInt U V m, kronecker H c = 0)
      ∧ (∀ c ∈ subspaceChainsInt (U ∪ V) (m + 1), kronecker (ω - coboundary M m H) c = 0) := by
  classical
  -- descend `kronecker ω` to `Q_{m+1}`
  have hvanish : ∀ c ∈ mvUnionChainsInt U V (m + 1), Finsupp.linearCombination ℤ ω c = 0 := by
    intro c hc; rw [← kronecker_eq_linearCombination]; exact hmv c hc
  set qω : QChainInt U V (m + 1) →ₗ[ℤ] ℤ :=
    Submodule.liftQ (mvUnionChainsInt U V (m + 1)) (Finsupp.linearCombination ℤ ω) hvanish with hqω
  have hqω_mk : ∀ c, qω (QChainInt.mk U V (m + 1) c) = kronecker ω c := by
    intro c; rw [hqω]; rw [kronecker_eq_linearCombination]; rfl
  -- restrict to the acyclic `Hom(K)`; it is a cocycle
  set kω : ↥(LinearMap.ker (piMapInt U V (m + 1))) →ₗ[ℤ] ℤ :=
    qω.comp (LinearMap.ker (piMapInt U V (m + 1))).subtype with hkω
  have hkcocy : kω.comp (dK U V (m + 1)) = 0 := by
    apply LinearMap.ext; intro k'
    rw [LinearMap.comp_apply, LinearMap.zero_apply, hkω, LinearMap.comp_apply,
      Submodule.subtype_apply, dK_coe]
    obtain ⟨c', hc'⟩ := Submodule.Quotient.mk_surjective _ (k' : QChainInt U V (m + 2))
    rw [show (k' : QChainInt U V (m + 2)) = QChainInt.mk U V (m + 2) c' from hc'.symm,
      qBoundaryInt_mk, hqω_mk, ← kronecker_coboundary_chainBoundary, hcocy]
    simp [kronecker_apply]
  obtain ⟨h, hh⟩ := hom_K_cocycle_eq_coboundary U V hU hV m kω hkcocy
  -- extend `h` to `Q_m` through the split retract of `π`
  haveI : Module.Free ℤ (RelativeChainInt (U ∪ V) m) := free_relChainUnion U V m
  obtain ⟨sec, hsec⟩ := LinearMap.exists_rightInverse_of_surjective (piMapInt U V m)
    (LinearMap.range_eq_top.mpr (piMapInt_surjective U V m))
  have hretr_mem : ∀ x, (LinearMap.id - sec.comp (piMapInt U V m) : QChainInt U V m →ₗ[ℤ] QChainInt U V m) x
      ∈ LinearMap.ker (piMapInt U V m) := by
    intro x
    rw [LinearMap.mem_ker]
    -- v4.32: the goal is not type-correct at `instances` transparency (the LinearMap-level
    -- `instHSub`), so `simp only` reports "made no progress" rather than a type error.
    -- `rw` works at default transparency and steps through it.
    erw [LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.comp_apply, map_sub]
    have hgy : piMapInt U V m (sec (piMapInt U V m x)) = piMapInt U V m x := by
      simpa using LinearMap.congr_fun hsec (piMapInt U V m x)
    rw [hgy, sub_self]
  set retr : QChainInt U V m →ₗ[ℤ] ↥(LinearMap.ker (piMapInt U V m)) :=
    (LinearMap.id - sec.comp (piMapInt U V m)).codRestrict _ hretr_mem with hretr
  have hretr_sub : ∀ k : ↥(LinearMap.ker (piMapInt U V m)),
      retr (k : QChainInt U V m) = k := by
    intro k
    apply Subtype.ext
    have hk0 : piMapInt U V m (k : QChainInt U V m) = 0 := LinearMap.mem_ker.mp k.2
    simp only [hretr, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_coe, id_eq,
      LinearMap.comp_apply, hk0, map_zero, sub_zero]
  set H : SingularCochainInt M m := fun σ => h (retr (QChainInt.mk U V m (Finsupp.single σ 1))) with hH
  -- key: `kronecker H c = h (retr (mk c))`
  have hHc : ∀ c : SingularChainInt M m, kronecker H c = h (retr (QChainInt.mk U V m c)) := by
    have hlin : Finsupp.linearCombination ℤ H
        = (h ∘ₗ retr ∘ₗ (mvUnionChainsInt U V m).mkQ) := by
      apply Finsupp.lhom_ext'
      intro σ
      apply LinearMap.ext_ring
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.linearCombination_single,
        one_smul, hH]
      rfl
    intro c
    rw [kronecker_eq_linearCombination, hlin]
    rfl
  refine ⟨H, ?_, ?_⟩
  · -- `H` vanishes on `C(U)+C(V)`
    intro c hc
    rw [hHc, show QChainInt.mk U V m c = 0 from (QChainInt.mk_eq_zero_iff U V m c).mpr hc,
      map_zero, map_zero]
  · -- `ω − δH` vanishes on `C(U∪V)`: `kronecker (δH) c = kronecker ω c`
    intro c hc
    have hmem : QChainInt.mk U V (m + 1) c ∈ LinearMap.ker (piMapInt U V (m + 1)) := by
      rw [LinearMap.mem_ker, piMapInt_mk, RelativeChainInt.mk_eq_zero_iff]; exact hc
    set k_c : ↥(LinearMap.ker (piMapInt U V (m + 1))) := ⟨QChainInt.mk U V (m + 1) c, hmem⟩ with hkc
    have hmk_bdry : QChainInt.mk U V m (chainBoundary M m c) = (dK U V m k_c : QChainInt U V m) := by
      rw [dK_coe, hkc, qBoundaryInt_mk]
    have hstep : kronecker (coboundary M m H) c = kronecker ω c := by
      rw [kronecker_coboundary_chainBoundary, hHc, hmk_bdry, hretr_sub, ← LinearMap.comp_apply, ← hh,
        hkω, LinearMap.comp_apply, Submodule.subtype_apply, hkc, hqω_mk]
    have hsub : kronecker (ω - coboundary M m H) c
        = kronecker ω c - kronecker (coboundary M m H) c := by
      rw [sub_eq_add_neg, ← neg_one_zsmul (coboundary M m H), kronecker_add_left,
        kronecker_smul_left, neg_one_zsmul, ← sub_eq_add_neg]
    rw [hsub, hstep, sub_self]

/-- Two relative cocycles whose underlying cochains differ by `δH` (with `H` a relative cochain) have the
same relative cohomology class. -/
theorem mk_eq_of_coboundary_diff {S : Set M} (n : ℕ)
    (z w : LinearMap.ker (relCoboundaryIntₗ S (n + 1))) (Hc : relCochainsInt S n)
    (hdiff : ((z : relCochainsInt S (n + 1)) : SingularCochainInt M (n + 1))
        - ((w : relCochainsInt S (n + 1)) : SingularCochainInt M (n + 1))
      = coboundary M n (Hc : SingularCochainInt M n)) :
    RelativeCohomologyInt.mk S (n + 1) z = RelativeCohomologyInt.mk S (n + 1) w := by
  rw [← sub_eq_zero]
  have hms : RelativeCohomologyInt.mk S (n + 1) z - RelativeCohomologyInt.mk S (n + 1) w
      = RelativeCohomologyInt.mk S (n + 1) (z - w) :=
    (Submodule.Quotient.mk_sub _).symm
  rw [hms, RelativeCohomologyInt.mk_eq_zero_iff]
  refine ⟨Hc, ?_⟩
  apply Subtype.ext
  rw [relCoboundaryIntₗ_coe, AddSubgroupClass.coe_sub]
  exact hdiff.symm

/-- **`ker Σ_H ≤ range Δ_H`** — the substantive half of the integral cohomology MV middle exactness,
assembled from the chase (`exists_intersection_cocycle_of_sumInt`) and the concrete lift
(`exists_lift_cochain`). -/
theorem ker_relCohomMvSumInt_le_range_relCohomMvDiagInt (U V : Set M) (hU : IsOpen U) (hV : IsOpen V)
    (m : ℕ) (A : RelativeCohomologyInt U (m + 1)) (B : RelativeCohomologyInt V (m + 1))
    (hAB : (A, B) ∈ LinearMap.ker (relCohomMvSumInt U V (m + 1))) :
    (A, B) ∈ LinearMap.range (relCohomMvDiagInt U V (m + 1)) := by
  obtain ⟨α, rfl⟩ := RelativeCohomologyInt.mk_surjective U (m + 1) A
  obtain ⟨β, rfl⟩ := RelativeCohomologyInt.mk_surjective V (m + 1) B
  have h0 : relCohomMvSumInt U V (m + 1)
      (RelativeCohomologyInt.mk U (m + 1) α, RelativeCohomologyInt.mk V (m + 1) β) = 0 :=
    LinearMap.mem_ker.mp hAB
  obtain ⟨ωU, ωV, hcochain, hUeq, hVeq⟩ := exists_intersection_cocycle_of_sumInt U V m α β h0
  set ω' : SingularCochainInt M (m + 1) := ((ωU : relCochainsInt U (m + 1)) : SingularCochainInt M (m + 1))
    with hω'
  -- `ω'` vanishes on the small chains and is a cocycle
  have hcobadd : ∀ (a b : SingularCochainInt M (m + 1)),
      coboundary M (m + 1) (a - b) = coboundary M (m + 1) a - coboundary M (m + 1) b := by
    intro a b
    show coboundaryₗ M (m + 1) (a - b) = coboundaryₗ M (m + 1) a - coboundaryₗ M (m + 1) b
    rw [map_sub]
  have hcobneg : ∀ (a : SingularCochainInt M m), coboundary M m (-a) = -coboundary M m a := by
    intro a
    show coboundaryₗ M m (-a) = -coboundaryₗ M m a
    rw [map_neg]
  have hmv : ∀ c ∈ mvUnionChainsInt U V (m + 1), kronecker ω' c = 0 := by
    intro c hc
    rw [mvUnionChainsInt, Submodule.add_eq_sup, Submodule.mem_sup] at hc
    obtain ⟨a, ha, b, hb, rfl⟩ := hc
    rw [kronecker_add_right]
    have h1 : kronecker ω' a = 0 :=
      (mem_relCochainsInt U (m + 1) ω').mp (ωU : relCochainsInt U (m + 1)).2 a ha
    have h2 : kronecker ω' b = 0 := by
      rw [hcochain]; exact (mem_relCochainsInt V (m + 1) _).mp (ωV : relCochainsInt V (m + 1)).2 b hb
    rw [h1, h2, add_zero]
  have hcocy : coboundary M (m + 1) ω' = 0 := by
    have h0' : relCoboundaryIntₗ U (m + 1) (ωU : relCochainsInt U (m + 1)) = 0 := LinearMap.mem_ker.mp ωU.2
    have h1 : ((relCoboundaryIntₗ U (m + 1) (ωU : relCochainsInt U (m + 1)) :
        relCochainsInt U (m + 2)) : SingularCochainInt M (m + 2)) = 0 := by rw [h0']; rfl
    rwa [relCoboundaryIntₗ_coe] at h1
  obtain ⟨H, hHmv, hHf⟩ := exists_lift_cochain U V hU hV m ω' hmv hcocy
  set f : SingularCochainInt M (m + 1) := ω' - coboundary M m H with hf
  have hf_mem : f ∈ relCochainsInt (U ∪ V) (m + 1) := (mem_relCochainsInt (U ∪ V) (m + 1) f).mpr hHf
  have hf_cocy : coboundary M (m + 1) f = 0 := by
    rw [hf, hcobadd, hcocy, coboundary_comp_coboundary, sub_zero]
  have hf_ker : (⟨f, hf_mem⟩ : relCochainsInt (U ∪ V) (m + 1))
      ∈ LinearMap.ker (relCoboundaryIntₗ (U ∪ V) (m + 1)) := by
    rw [LinearMap.mem_ker]; apply Subtype.ext; rw [relCoboundaryIntₗ_coe]; exact hf_cocy
  have hHU_mem : H ∈ relCochainsInt U m := (mem_relCochainsInt U m H).mpr
    (fun c hc => hHmv c (subspaceChainsInt_le_mvUnionChainsInt_left U V m hc))
  have hHV_mem : H ∈ relCochainsInt V m := (mem_relCochainsInt V m H).mpr
    (fun c hc => hHmv c (subspaceChainsInt_le_mvUnionChainsInt_right U V m hc))
  refine ⟨RelativeCohomologyInt.mk (U ∪ V) (m + 1) ⟨⟨f, hf_mem⟩, hf_ker⟩, ?_⟩
  rw [relCohomMvDiagInt_apply]
  refine Prod.ext ?_ ?_
  · rw [relCohomRestrictInt_mk, ← hUeq]
    refine mk_eq_of_coboundary_diff m _ ωU (-(⟨H, hHU_mem⟩ : relCochainsInt U m)) ?_
    rw [relCocycleRestrictInt_coe, relCochainRestrictInt_coe]
    show f - ω' = coboundary M m (-H)
    rw [hf, hcobneg]; abel
  · rw [relCohomRestrictInt_mk, ← hVeq]
    refine mk_eq_of_coboundary_diff m _ ωV (-(⟨H, hHV_mem⟩ : relCochainsInt V m)) ?_
    rw [relCocycleRestrictInt_coe, relCochainRestrictInt_coe]
    show f - ((ωV : relCochainsInt V (m + 1)) : SingularCochainInt M (m + 1)) = coboundary M m (-H)
    rw [hf, ← hcochain, hcobneg]; abel

/-- **Integral relative cohomology MV exactness at the middle** `Hᵏ(M|A) ⊕ Hᵏ(M|B)`:
`Function.Exact (relCohomMvDiagInt) (relCohomMvSumInt)`, i.e. `range Δ = ker Σ` — the torsion-safe ℤ
analogue of `SingularRelativeCohomologyMVMiddle.relCohomMv_exact_middle`, built by dualising the
degreewise-split relative-homology MV chain SES (no UCT / finite-dimensionality). The middle term of the
integral cohomology MV long exact sequence — the top row of the integral Poincaré-duality `5`-lemma ladder. -/
theorem relCohomMv_exact_middleInt (U V : Set M) (hU : IsOpen U) (hV : IsOpen V) (m : ℕ) :
    Function.Exact (relCohomMvDiagInt U V (m + 1)) (relCohomMvSumInt U V (m + 1)) := by
  rw [LinearMap.exact_iff]
  refine le_antisymm (fun p hp => ?_) (fun p hp => ?_)
  · obtain ⟨A, B⟩ := p
    exact ker_relCohomMvSumInt_le_range_relCohomMvDiagInt U V hU hV m A B hp
  · obtain ⟨q, rfl⟩ := hp
    rw [LinearMap.mem_ker, relCohomMvSumInt_relCohomMvDiagInt]

end SKEFTHawking.SingularCohomMvMiddleInt
