/-
# Phase 5q.H (E1 integral topology) — the dual excision iso `RelCohom(U∪V) ≅ QCohom`

The cochain inclusion `relCochainsInt(U∪V) ↪ mvUnionCochainsInt U V` (a cochain vanishing on
`subspaceChainsInt(U∪V) ⊇ mvUnion` a fortiori vanishes on `mvUnion`) is a **cochain map** (both differentials
are the coboundary), inducing `dualExcisionInt : RelativeCohomologyInt(U∪V) n → QCohomologyInt U V n`. This
is the cohomology dual of the small-chains excision `iotaEquivInt`; it is an **isomorphism** because the
quotient complex is the acyclic `Hom(K)` (`SingularKComplexAcyclicInt`). Surjectivity is the `(B)`-node
`exists_lift_cochain` (every `Q`-cocycle is cohomologous to a genuine `relCochainsInt(U∪V)` cocycle);
injectivity uses the K-complex acyclicity `hom_K_cocycle_eq_coboundary`.

This module builds the **map** `dualExcisionInt` + its computation rule (`mapQ` mirror of
`relCohomRestrictInt`). Surjectivity/injectivity + the packaged `LinearEquiv` follow.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularQCohomologyInt
import SKEFTHawking.SingularEuclideanCapIsoInt
import SKEFTHawking.SingularCohomMvMiddleInt
import SKEFTHawking.SingularKComplexAcyclicInt
import SKEFTHawking.SingularSmallChainsSplitInt

open SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeMVInt
open SKEFTHawking.SingularQCohomologyInt
open SKEFTHawking.SingularKComplexAcyclicInt
open SKEFTHawking.SingularSmallChainsSplitInt (free_relChainUnion)
open SKEFTHawking.SingularCohomMvMiddleInt (exists_lift_cochain)

namespace SKEFTHawking.SingularQCohomologyExcisionInt

variable {M : TopCat}

/-- **`relCochainsInt(U∪V) ≤ Q-cochains`**: vanishing on `subspaceChainsInt(U∪V) ⊇ mvUnion` implies vanishing
on `mvUnion`. -/
theorem relCochainsInt_le_mvUnionCochainsInt (U V : Set ↑M) (n : ℕ) :
    relCochainsInt (U ∪ V) n ≤ mvUnionCochainsInt U V n := by
  have hle : mvUnionChainsInt U V n ≤ subspaceChainsInt (U ∪ V) n := by
    rw [mvUnionChainsInt]
    exact sup_le (subspaceChainsInt_mono Set.subset_union_left n)
      (subspaceChainsInt_mono Set.subset_union_right n)
  intro f hf c hc
  exact hf c (hle hc)

/-- The cochain-level inclusion `relCochainsInt(U∪V) n →ₗ mvUnionCochainsInt U V n`. -/
noncomputable def relToQCochainInt (U V : Set ↑M) (n : ℕ) :
    relCochainsInt (U ∪ V) n →ₗ[ℤ] mvUnionCochainsInt U V n :=
  Submodule.inclusion (relCochainsInt_le_mvUnionCochainsInt U V n)

@[simp] theorem relToQCochainInt_coe (U V : Set ↑M) (n : ℕ) (f : relCochainsInt (U ∪ V) n) :
    (relToQCochainInt U V n f : SingularCochainInt M n) = (f : SingularCochainInt M n) := rfl

/-- The inclusion **commutes with the coboundary** `δ_{U∪V} ↝ δ_Q` (both cod-restrict the same absolute
`coboundary`). -/
theorem relToQCochainInt_coboundary (U V : Set ↑M) (n : ℕ) (f : relCochainsInt (U ∪ V) n) :
    relToQCochainInt U V (n + 1) (relCoboundaryIntₗ (U ∪ V) n f)
      = qCoboundaryIntₗ U V n (relToQCochainInt U V n f) := by
  apply Subtype.ext
  rw [relToQCochainInt_coe, relCoboundaryIntₗ_coe, qCoboundaryIntₗ_coe, relToQCochainInt_coe]

/-- The inclusion sends `(U∪V)`-relative cocycles to `Q`-cocycles. -/
theorem relToQCochainInt_mem_ker (U V : Set ↑M) (n : ℕ)
    (z : relCochainsInt (U ∪ V) n) (hz : z ∈ LinearMap.ker (relCoboundaryIntₗ (U ∪ V) n)) :
    relToQCochainInt U V n z ∈ LinearMap.ker (qCoboundaryIntₗ U V n) := by
  rw [LinearMap.mem_ker] at hz ⊢
  rw [← relToQCochainInt_coboundary, hz, map_zero]

/-- The inclusion on cocycles `ker δ_{U∪V} →ₗ ker δ_Q`. -/
noncomputable def relToQCocycleInt (U V : Set ↑M) (n : ℕ) :
    LinearMap.ker (relCoboundaryIntₗ (U ∪ V) n) →ₗ[ℤ] LinearMap.ker (qCoboundaryIntₗ U V n) :=
  (relToQCochainInt U V n).restrict (fun z hz => relToQCochainInt_mem_ker U V n z hz)

@[simp] theorem relToQCocycleInt_coe (U V : Set ↑M) (n : ℕ)
    (z : LinearMap.ker (relCoboundaryIntₗ (U ∪ V) n)) :
    (relToQCocycleInt U V n z : mvUnionCochainsInt U V n)
      = relToQCochainInt U V n (z : relCochainsInt (U ∪ V) n) :=
  rfl

/-- The inclusion sends `(U∪V)`-relative coboundaries to `Q`-coboundaries. -/
theorem relToQCochainInt_mem_qCoboundaryRange (U V : Set ↑M) (n : ℕ)
    (f : relCochainsInt (U ∪ V) n) (hf : f ∈ relCoboundaryRangeInt (U ∪ V) n) :
    relToQCochainInt U V n f ∈ qCoboundaryRangeInt U V n := by
  cases n with
  | zero =>
    rw [relCoboundaryRangeInt, Submodule.mem_bot] at hf
    rw [hf, map_zero]
    exact Submodule.zero_mem _
  | succ m =>
    obtain ⟨g, rfl⟩ := hf
    exact ⟨relToQCochainInt U V m g, relToQCochainInt_coboundary U V m g⟩

/-- The `mapQ` compatibility: the cocycle inclusion carries the coboundary subgroup into the coboundary
subgroup. -/
theorem relToQCocycleInt_submoduleOf_le (U V : Set ↑M) (n : ℕ) :
    (relCoboundaryRangeInt (U ∪ V) n).submoduleOf (LinearMap.ker (relCoboundaryIntₗ (U ∪ V) n)) ≤
      Submodule.comap (relToQCocycleInt U V n)
        ((qCoboundaryRangeInt U V n).submoduleOf (LinearMap.ker (qCoboundaryIntₗ U V n))) := by
  intro z hz
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
    relToQCocycleInt_coe] at hz ⊢
  exact relToQCochainInt_mem_qCoboundaryRange U V n _ hz

/-- **The dual excision map** `dualExcisionInt : RelativeCohomologyInt(U∪V) n →ₗ QCohomologyInt U V n`, the
cohomology dual of the small-chains excision. Cochain inclusion `relCochainsInt(U∪V) ↪ mvUnionCochainsInt`
descended via `Submodule.mapQ`. -/
noncomputable def dualExcisionInt (U V : Set ↑M) (n : ℕ) :
    RelativeCohomologyInt (U ∪ V) n →ₗ[ℤ] QCohomologyInt U V n :=
  Submodule.mapQ _ _ (relToQCocycleInt U V n) (relToQCocycleInt_submoduleOf_le U V n)

/-- **Computation rule**: `dualExcisionInt [z]_{U∪V} = [incl z]_Q`. -/
@[simp] theorem dualExcisionInt_mk (U V : Set ↑M) (n : ℕ)
    (z : LinearMap.ker (relCoboundaryIntₗ (U ∪ V) n)) :
    dualExcisionInt U V n (RelativeCohomologyInt.mk (U ∪ V) n z)
      = QCohomologyInt.mk U V n (relToQCocycleInt U V n z) :=
  rfl

/-- **The dual excision map is surjective** (degrees `≥ 1`): every `Q`-cohomology class is the excision of a
genuine `(U∪V)`-relative class. This is the `(B)`-node `exists_lift_cochain` — a `Q`-cocycle `g` (vanishing
on `mvUnion`, `δg = 0`) becomes, after subtracting a `Q`-coboundary `δH`, a cochain vanishing on ALL of
`C(U∪V)`, i.e. a genuine `relCochainsInt(U∪V)` cocycle representing the same `Q`-class. -/
theorem dualExcisionInt_surjective (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    Function.Surjective (dualExcisionInt U V (n + 1)) := by
  intro qc
  obtain ⟨gz, rfl⟩ := QCohomologyInt.mk_surjective U V (n + 1) qc
  set g : SingularCochainInt M (n + 1) := (gz.1 : SingularCochainInt M (n + 1)) with hg
  have hcocy : coboundary M (n + 1) g = 0 := by
    have h := gz.2
    rw [LinearMap.mem_ker] at h
    have := congrArg (fun x : mvUnionCochainsInt U V (n + 2) => (x : SingularCochainInt M (n + 2))) h
    simpa only [qCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] using this
  obtain ⟨H, hHmv, hHrel⟩ := exists_lift_cochain U V hU hV n g gz.1.2 hcocy
  have hwmem : g - coboundary M n H ∈ relCochainsInt (U ∪ V) (n + 1) := hHrel
  have hwcocy : (⟨g - coboundary M n H, hwmem⟩ : relCochainsInt (U ∪ V) (n + 1))
      ∈ LinearMap.ker (relCoboundaryIntₗ (U ∪ V) (n + 1)) := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show coboundaryₗ M (n + 1) (g - coboundary M n H) = 0
    rw [map_sub]
    show coboundary M (n + 1) g - coboundary M (n + 1) (coboundary M n H) = 0
    rw [hcocy, coboundary_comp_coboundary, sub_zero]
  refine ⟨RelativeCohomologyInt.mk (U ∪ V) (n + 1) ⟨⟨g - coboundary M n H, hwmem⟩, hwcocy⟩, ?_⟩
  rw [dualExcisionInt_mk]
  -- both `Q`-classes: their reps differ by `-δH`, a `Q`-coboundary.
  refine (Submodule.Quotient.eq _).2 ⟨-⟨H, hHmv⟩, ?_⟩
  apply Subtype.ext
  show coboundaryₗ M n (-H) = (g - coboundary M n H) - g
  rw [map_neg]
  show -coboundary M n H = (g - coboundary M n H) - g
  abel

/-- **The dual excision map is injective** (degrees `≥ 2`): a `(U∪V)`-relative cocycle `z` that becomes a
`Q`-coboundary (`z = δg` with `g` vanishing only on `mvUnion`) is already a genuine `relCochainsInt(U∪V)`
coboundary. The class of `g` in `Hom(K)` is a `K`-cocycle (`δg = z` vanishes on `subspaceChains(U∪V) ⊇ K`);
the K-complex acyclicity `hom_K_cocycle_eq_coboundary` gives `kg = h ∘ dK`; extending `h` to `H` through the
split retract of `piMapInt`, `g − δH` vanishes on all of `C(U∪V)` and `δ(g − δH) = z`. -/
theorem dualExcisionInt_injective (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    Function.Injective (dualExcisionInt U V (n + 2)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro zc hzc
  obtain ⟨z, rfl⟩ := RelativeCohomologyInt.mk_surjective (U ∪ V) (n + 2) zc
  rw [dualExcisionInt_mk, QCohomologyInt.mk_eq_zero_iff] at hzc
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype, qCoboundaryRangeInt,
    LinearMap.mem_range] at hzc
  -- `g : mvUnionCochains(n+1)` with `coboundary g = z` (as absolute cochains)
  obtain ⟨g, hg⟩ := hzc
  set gc : SingularCochainInt M (n + 1) := (g : SingularCochainInt M (n + 1)) with hgc
  have hgz : coboundary M (n + 1) gc = (z : SingularCochainInt M (n + 2)) := by
    have := congrArg (fun x : mvUnionCochainsInt U V (n + 2) => (x : SingularCochainInt M (n + 2))) hg
    simpa only [qCoboundaryIntₗ_coe, relToQCocycleInt_coe, relToQCochainInt_coe] using this
  -- `qg : Q(n+1) → ℤ` descends `⟨g, ·⟩`; `kg = qg ∘ subtype : K(n+1) → ℤ` is a K-cocycle.
  have hgvan : ∀ c ∈ mvUnionChainsInt U V (n + 1), Finsupp.linearCombination ℤ gc c = 0 := by
    intro c hc; rw [← kronecker_eq_linearCombination]; exact g.2 c hc
  set qg : QChainInt U V (n + 1) →ₗ[ℤ] ℤ :=
    Submodule.liftQ (mvUnionChainsInt U V (n + 1)) (Finsupp.linearCombination ℤ gc) hgvan with hqg
  have hqg_mk : ∀ c, qg (QChainInt.mk U V (n + 1) c) = kronecker gc c := by
    intro c; rw [hqg, kronecker_eq_linearCombination]; rfl
  set kg : ↥(LinearMap.ker (piMapInt U V (n + 1))) →ₗ[ℤ] ℤ :=
    qg.comp (LinearMap.ker (piMapInt U V (n + 1))).subtype with hkg
  have hkgcocy : kg.comp (dK U V (n + 1)) = 0 := by
    apply LinearMap.ext; intro k'
    rw [LinearMap.comp_apply, LinearMap.zero_apply, hkg, LinearMap.comp_apply,
      Submodule.subtype_apply, dK_coe]
    obtain ⟨c', hc'⟩ := Submodule.Quotient.mk_surjective _ (k' : QChainInt U V (n + 2))
    rw [show (k' : QChainInt U V (n + 2)) = QChainInt.mk U V (n + 2) c' from hc'.symm,
      qBoundaryInt_mk, hqg_mk, ← kronecker_coboundary_chainBoundary, hgz]
    -- `c'` is a subspace-`(U∪V)` chain (since `k' ∈ ker piMapInt`), and `z` vanishes there.
    have hc'mem : (k' : QChainInt U V (n + 2)) ∈ LinearMap.ker (piMapInt U V (n + 2)) := k'.2
    rw [show (k' : QChainInt U V (n + 2)) = QChainInt.mk U V (n + 2) c' from hc'.symm,
      LinearMap.mem_ker, piMapInt_mk, RelativeChainInt.mk_eq_zero_iff] at hc'mem
    exact z.1.2 c' hc'mem
  obtain ⟨h, hh⟩ := hom_K_cocycle_eq_coboundary U V hU hV n kg hkgcocy
  -- extend `h` to `H : Cⁿ` through the split retract of `piMapInt` (as in `exists_lift_cochain`).
  haveI : Module.Free ℤ (RelativeChainInt (U ∪ V) n) := free_relChainUnion U V n
  obtain ⟨sec, hsec⟩ := LinearMap.exists_rightInverse_of_surjective (piMapInt U V n)
    (LinearMap.range_eq_top.mpr (piMapInt_surjective U V n))
  have hretr_mem : ∀ x, (LinearMap.id - sec.comp (piMapInt U V n) :
      QChainInt U V n →ₗ[ℤ] QChainInt U V n) x ∈ LinearMap.ker (piMapInt U V n) := by
    intro x
    rw [LinearMap.mem_ker]
    erw [LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.comp_apply, map_sub]
    have hgy : piMapInt U V n (sec (piMapInt U V n x)) = piMapInt U V n x := by
      simpa using LinearMap.congr_fun hsec (piMapInt U V n x)
    rw [hgy, sub_self]
  set retr : QChainInt U V n →ₗ[ℤ] ↥(LinearMap.ker (piMapInt U V n)) :=
    (LinearMap.id - sec.comp (piMapInt U V n)).codRestrict _ hretr_mem with hretr
  have hretr_sub : ∀ k : ↥(LinearMap.ker (piMapInt U V n)), retr (k : QChainInt U V n) = k := by
    intro k
    apply Subtype.ext
    have hk0 : piMapInt U V n (k : QChainInt U V n) = 0 := LinearMap.mem_ker.mp k.2
    simp only [hretr, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_coe, id_eq,
      LinearMap.comp_apply, hk0, map_zero, sub_zero]
  set H : SingularCochainInt M n := fun σ => h (retr (QChainInt.mk U V n (Finsupp.single σ 1))) with hH
  have hHc : ∀ c : SingularChainInt M n, kronecker H c = h (retr (QChainInt.mk U V n c)) := by
    have hlin : Finsupp.linearCombination ℤ H
        = (h ∘ₗ retr ∘ₗ (mvUnionChainsInt U V n).mkQ) := by
      apply Finsupp.lhom_ext'
      intro σ
      apply LinearMap.ext_ring
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.linearCombination_single,
        one_smul, hH]
      rfl
    intro c
    rw [kronecker_eq_linearCombination, hlin]
    rfl
  -- `g − δH` vanishes on `C(U∪V)` (degree `n+1`), so it is a genuine `(U∪V)`-relative cochain.
  have hwmem : gc - coboundary M n H ∈ relCochainsInt (U ∪ V) (n + 1) := by
    intro c hc
    have hmem : QChainInt.mk U V (n + 1) c ∈ LinearMap.ker (piMapInt U V (n + 1)) := by
      rw [LinearMap.mem_ker, piMapInt_mk, RelativeChainInt.mk_eq_zero_iff]; exact hc
    set k_c : ↥(LinearMap.ker (piMapInt U V (n + 1))) := ⟨QChainInt.mk U V (n + 1) c, hmem⟩ with hkc
    have hgcval : kronecker gc c = h (dK U V n k_c) := by
      have hcf := LinearMap.congr_fun hh k_c
      rw [hkg, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.comp_apply] at hcf
      rw [show (k_c : QChainInt U V (n + 1)) = QChainInt.mk U V (n + 1) c from rfl, hqg_mk] at hcf
      exact hcf
    have hbdry : (dK U V n k_c : QChainInt U V n) = QChainInt.mk U V n (chainBoundary M n c) := by
      rw [dK_coe]; rfl
    have hdHval : kronecker (coboundary M n H) c = h (dK U V n k_c) := by
      rw [kronecker_coboundary_chainBoundary, hHc]
      congr 1
      rw [← hbdry, hretr_sub]
    have hsub : kronecker (gc - coboundary M n H) c
        = kronecker gc c - kronecker (coboundary M n H) c := by
      rw [sub_eq_add_neg, ← neg_one_zsmul (coboundary M n H), kronecker_add_left,
        kronecker_smul_left, neg_one_zsmul, ← sub_eq_add_neg]
    rw [hsub, hgcval, hdHval, sub_self]
  -- `z = δ(g − δH)` with `g − δH ∈ relCochainsInt(U∪V)`, so `[z] = 0`.
  refine (RelativeCohomologyInt.mk_eq_zero_iff (U ∪ V) (n + 2) z).2 ?_
  simp only [relCoboundaryRangeInt, LinearMap.mem_range]
  refine ⟨⟨gc - coboundary M n H, hwmem⟩, ?_⟩
  apply Subtype.ext
  show coboundary M (n + 1) (gc - coboundary M n H) = (z : SingularCochainInt M (n + 2))
  rw [show coboundary M (n + 1) (gc - coboundary M n H)
      = coboundaryₗ M (n + 1) (gc - coboundary M n H) from rfl, map_sub]
  show coboundary M (n + 1) gc - coboundary M (n + 1) (coboundary M n H)
      = (z : SingularCochainInt M (n + 2))
  rw [hgz, coboundary_comp_coboundary, sub_zero]

/-- **The dual excision isomorphism** `RelativeCohomologyInt(U∪V) (n+2) ≃ₗ QCohomologyInt U V (n+2)` — the
cohomology dual of the small-chains excision `iotaEquivInt`, bijective by `dualExcisionInt_surjective`
(degree `≥ 1`) + `dualExcisionInt_injective` (degree `≥ 2`). The connecting map of the relative-cohomology
Mayer–Vietoris LES factors through `(dualExcisionEquivInt).symm`. -/
noncomputable def dualExcisionEquivInt (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    RelativeCohomologyInt (U ∪ V) (n + 2) ≃ₗ[ℤ] QCohomologyInt U V (n + 2) :=
  LinearEquiv.ofBijective (dualExcisionInt U V (n + 2))
    ⟨dualExcisionInt_injective U V hU hV n, dualExcisionInt_surjective U V hU hV (n + 1)⟩

@[simp] theorem dualExcisionEquivInt_apply (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (x : RelativeCohomologyInt (U ∪ V) (n + 2)) :
    dualExcisionEquivInt U V hU hV n x = dualExcisionInt U V (n + 2) x :=
  rfl

end SKEFTHawking.SingularQCohomologyExcisionInt
