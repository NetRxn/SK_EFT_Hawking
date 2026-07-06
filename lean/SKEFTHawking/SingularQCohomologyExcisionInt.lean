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

open SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeMVInt
open SKEFTHawking.SingularQCohomologyInt
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

end SKEFTHawking.SingularQCohomologyExcisionInt
