import Mathlib
import SKEFTHawking.SingularCapHomology
import SKEFTHawking.SingularCapChainIncl
import SKEFTHawking.SingularRelativePairing
import SKEFTHawking.SingularRelativeCup

/-!
# Phase 5q.H Track 2 — the relative cap product on homology and the descended cap–cup adjunction

The absolute cap product on homology `SingularCapHomology.capH : Hᵏ(X) → H_{k+m+1}(X) → H_{m+1}(X)`
and the absolute descended cap–cup adjunction `SingularCupCapHomology.kroneckerH_capH_cupRightGeneralH`
(`⟨a ∪ b, z⟩ = ⟨b, a ⌢ z⟩`) both have RELATIVE mirrors, capping an **absolute** cochain `a ∈ Hᵏ(X)`
against a **relative** chain `z ∈ H_n(X, S)`:

  `capRelH k m : Hᵏ(X) → H_{k+m+1}(X, S) → H_{m+1}(X, S)`,   `⟨a ∪ b, z⟩ = ⟨b, a ⌢ z⟩`  (relative K).

This is the **(A) layer** of the cylinder cap-cross projection wall (`…CylinderCapCrossProj`): with it
the residual pairing `⟨a ∪ b, [M] × [I,∂I]⟩ = ⟨b, ((α a) ⌢ [M]) × [I,∂I]⟩` collapses (adjunction on the
LHS) to the honest homology-class identity `a ⌢ ([M] × [I,∂I]) = ((α a) ⌢ [M]) × [I,∂I]` — the pure
Eilenberg–Zilber cap-cross projection, with the entire `.mu`/pairing/adjunction layer discharged.

## The construction (mirror of `SingularCapHomology`)

The key twist over the absolute case is that capping an absolute cochain `a` against a **subspace
chain** lands in the subspace chains again (`cap_mem_subspaceChains`): the Alexander–Whitney *back*
face — which `cap` keeps — of a subspace simplex is a subspace simplex (`SingularCapChainIncl.cap_chainIncl`).
So `cap a` descends through the relative-chain quotient (`capRelChain`), and the standard
cocycle-chain-map (`cap_cocycle_chainMap`) and cap-Leibniz (`cap_leibniz`) descents carry over to the
relative complex — a relative cocycle caps a relative cycle to a relative cycle, and a coboundary caps a
relative cycle to a relative boundary + subspace chain (relatively null).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.SingularCapChainIncl
open SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularRelativeCup

namespace SKEFTHawking.SingularRelativeCapHomology

variable {X : TopCat} {S : Set X} {k m : ℕ}

/-! ## §1. Capping an absolute cochain preserves the subspace chains -/

/-- **Capping an absolute cochain against a subspace chain stays in the subspace chains.** For any
absolute `a : Cᵏ(X)` and `c ∈ C_{k+m}(S) = subspaceChains S (k+m)`, `a ⌢ c ∈ C_m(S)`. On a subspace
simplex `chainIncl S d`, `a ⌢ (chainIncl d) = chainIncl ((pullbackCochain a) ⌢ d)`
(`SingularCapChainIncl.cap_chainIncl`) — the *back* face `cap` keeps is again a subspace simplex. -/
theorem cap_mem_subspaceChains (a : SingularCochain X k) {c : SingularChain X (k + m)}
    (hc : c ∈ subspaceChains S (k + m)) : cap (m := m) a c ∈ subspaceChains S m := by
  rw [subspaceChains, LinearMap.mem_range] at hc
  obtain ⟨d, rfl⟩ := hc
  exact ⟨cap (SingularCapChainIncl.pullbackCochain S k a) d,
    (SingularCapChainIncl.cap_chainIncl (S := S) a d).symm⟩

/-! ## §2. The relative cap at the chain level and its relative chain-map property -/

/-- **The relative cap chain map** for a fixed absolute cochain `a : Cᵏ(X)`:
`a ⌢ · : C_{k+m}(X, S) → C_m(X, S)`, `[c] ↦ [a ⌢ c]`, well-defined by `cap_mem_subspaceChains`. -/
noncomputable def capRelChain (a : SingularCochain X k) :
    RelativeChain S (k + m) →ₗ[ZMod 2] RelativeChain S m :=
  Submodule.mapQ (subspaceChains S (k + m)) (subspaceChains S m) (cap (m := m) a)
    (fun _ hc => cap_mem_subspaceChains a hc)

@[simp] theorem capRelChain_mk (a : SingularCochain X k) (c : SingularChain X (k + m)) :
    capRelChain (S := S) (m := m) a (RelativeChain.mk S (k + m) c)
      = RelativeChain.mk S m (cap a c) :=
  rfl

/-- **The relative cap of a cocycle is a relative chain map**: for an absolute cocycle `a` (`δa = 0`),
`∂(a ⌢ z) = a ⌢ (∂z)` on relative chains (descends `cap_cocycle_chainMap`). -/
theorem capRelChain_relBoundary (a : LinearMap.ker (coboundaryₗ X k))
    (z : RelativeChain S (k + m + 1)) :
    relBoundary S m (capRelChain (m := m + 1) a.1 z)
      = capRelChain (m := m) a.1 (relBoundary S (k + m) z) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact congrArg (Submodule.Quotient.mk)
    (cap_cocycle_chainMap a.1 (LinearMap.mem_ker.mp a.2) c)

/-! ## §3. Descending the chain argument to relative homology (for a fixed cocycle) -/

/-- For a fixed absolute cocycle `a`, `capRelChain a` sends relative `(k+m+1)`-cycles to relative
`(m+1)`-cycles (`∂(a ⌢ z) = a ⌢ (∂z) = 0` in `C(X, S)`). -/
noncomputable def capRelCyclesₗ (a : LinearMap.ker (coboundaryₗ X k)) :
    relCycles S (k + m + 1) →ₗ[ZMod 2] relCycles S (m + 1) :=
  LinearMap.restrict (capRelChain (m := m + 1) a.1) (fun z hz => by
    show capRelChain (m := m + 1) a.1 z ∈ LinearMap.ker (relBoundary S m)
    rw [LinearMap.mem_ker, capRelChain_relBoundary,
      show relBoundary S (k + m) z = 0 from LinearMap.mem_ker.mp hz, map_zero])

@[simp] theorem capRelCyclesₗ_coe (a : LinearMap.ker (coboundaryₗ X k)) (z : relCycles S (k + m + 1)) :
    (capRelCyclesₗ (m := m) a z : RelativeChain S (m + 1))
      = capRelChain (m := m + 1) a.1 (z : RelativeChain S (k + m + 1)) :=
  LinearMap.restrict_coe_apply _ _ _

/-- For a fixed absolute cocycle `a`, `capRelChain a` descends to a `ℤ/2`-linear map on relative
homology `H_{k+m+1}(X,S) → H_{m+1}(X,S)`. -/
noncomputable def capRelHomology (a : LinearMap.ker (coboundaryₗ X k)) :
    RelativeHomology S (k + m + 1) →ₗ[ZMod 2] RelativeHomology S (m + 1) :=
  Submodule.mapQ _ _ (capRelCyclesₗ a) (by
    rintro ⟨z, hz⟩ hzb
    rw [Submodule.mem_comap]
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at hzb
    obtain ⟨w, hw⟩ := hzb
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype, capRelCyclesₗ_coe]
    refine ⟨capRelChain (m := m + 2) a.1 w, ?_⟩
    rw [capRelChain_relBoundary]
    exact congrArg (capRelChain (m := m + 1) a.1) hw)

@[simp] theorem capRelHomology_mk (a : LinearMap.ker (coboundaryₗ X k)) (z : relCycles S (k + m + 1)) :
    capRelHomology (m := m) a (RelativeHomology.mk S (k + m + 1) z)
      = RelativeHomology.mk S (m + 1) (capRelCyclesₗ a z) :=
  Submodule.mapQ_apply _ _ _ _

/-! ## §4. Linearity in the cochain and the cohomology-argument descent -/

/-- `capRelCyclesₗ` is additive in the cochain. -/
theorem capRelCyclesₗ_add (a a' : LinearMap.ker (coboundaryₗ X k)) (z : relCycles S (k + m + 1)) :
    capRelCyclesₗ (m := m) (a + a') z = capRelCyclesₗ a z + capRelCyclesₗ a' z := by
  apply Subtype.ext
  simp only [Submodule.coe_add, capRelCyclesₗ_coe]
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z : RelativeChain S (k + m + 1))
  rw [← hc]
  show Submodule.Quotient.mk (cap (m := m + 1) (a.1 + a'.1) c)
    = Submodule.Quotient.mk (cap (m := m + 1) a.1 c) + Submodule.Quotient.mk (cap (m := m + 1) a'.1 c)
  rw [cap_add_cochain]
  exact map_add (Submodule.mkQ (subspaceChains S (m + 1))) _ _

/-- `capRelCyclesₗ` commutes with the `ℤ/2`-action in the cochain. -/
theorem capRelCyclesₗ_smul (s : ZMod 2) (a : LinearMap.ker (coboundaryₗ X k))
    (z : relCycles S (k + m + 1)) :
    capRelCyclesₗ (m := m) (s • a) z = s • capRelCyclesₗ a z := by
  apply Subtype.ext
  simp only [SetLike.val_smul, capRelCyclesₗ_coe]
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z : RelativeChain S (k + m + 1))
  rw [← hc]
  show Submodule.Quotient.mk (cap (m := m + 1) (s • a.1) c)
    = s • Submodule.Quotient.mk (cap (m := m + 1) a.1 c)
  rw [cap_smul_cochain]
  exact map_smul (Submodule.mkQ (subspaceChains S (m + 1))) _ _

/-- `capRelHomology` is additive in the cochain. -/
theorem capRelHomology_add (a a' : LinearMap.ker (coboundaryₗ X k)) :
    capRelHomology (S := S) (m := m) (a + a') = capRelHomology a + capRelHomology a' := by
  ext x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show capRelHomology (a + a') (RelativeHomology.mk S (k + m + 1) z)
    = capRelHomology a (RelativeHomology.mk S (k + m + 1) z)
      + capRelHomology a' (RelativeHomology.mk S (k + m + 1) z)
  rw [capRelHomology_mk, capRelHomology_mk, capRelHomology_mk, capRelCyclesₗ_add]
  rfl

/-- `capRelHomology` commutes with the `ℤ/2`-action in the cochain. -/
theorem capRelHomology_smul (s : ZMod 2) (a : LinearMap.ker (coboundaryₗ X k)) :
    capRelHomology (S := S) (m := m) (s • a) = s • capRelHomology a := by
  ext x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show capRelHomology (s • a) (RelativeHomology.mk S (k + m + 1) z)
    = s • capRelHomology a (RelativeHomology.mk S (k + m + 1) z)
  rw [capRelHomology_mk, capRelHomology_mk, capRelCyclesₗ_smul]
  rfl

/-- The map `a ↦ capRelHomology a`, packaged `ℤ/2`-linear in the cochain. -/
noncomputable def capRelHomologyₗ :
    LinearMap.ker (coboundaryₗ X k) →ₗ[ZMod 2]
      (RelativeHomology S (k + m + 1) →ₗ[ZMod 2] RelativeHomology S (m + 1)) where
  toFun := capRelHomology
  map_add' := capRelHomology_add
  map_smul' := capRelHomology_smul

/-- Degree-cast transport of subspace-chain membership through `chainBoundary`. -/
private theorem chainBoundary_cast_mem {a b : ℕ} (z : SingularChain X (a + 1))
    (e : a + 1 = b + 1) (eb : a = b) (hz : chainBoundary X a z ∈ subspaceChains S a) :
    chainBoundary X b (e ▸ z) ∈ subspaceChains S b := by
  subst eb
  rw [show e = rfl from rfl]
  simpa using hz

/-- **The cohomology-argument descent (relative form).** For a `j`-cochain `g`, its coboundary `δg`
caps a relative `(j+1+m+1)`-cycle representative `z` (with `∂z ∈ C(S)`) to a relative `(m+1)`-boundary:
`cap_leibniz` gives `(δg) ⌢ z = ∂(g ⌢ z) + g ⌢ (∂z)`, the first summand a (relative) boundary, the
second a subspace chain (`cap_mem_subspaceChains`, since `∂z ∈ C(S)`) — so the relative class of
`(δg) ⌢ z` is a relative boundary. The relative mirror of
`SingularCapHomology.cap_coboundary_cycle_mem_boundaries`. -/
theorem cap_coboundary_relCycle_mem_relBoundaries {j : ℕ} (g : SingularCochain X j)
    (z : SingularChain X (j + 1 + m + 1))
    (hz : chainBoundary X (j + 1 + m) z ∈ subspaceChains S (j + 1 + m)) :
    RelativeChain.mk S (m + 1) (cap (m := m + 1) (coboundary X j g) z) ∈ relBoundaries S (m + 1) := by
  have e : j + 1 + m + 1 = j + (m + 1) + 1 := by omega
  have h : j + (m + 1) + 1 = j + 1 + (m + 1) := by omega
  have hleib := cap_leibniz (a := g) (c := e ▸ z) (m := m + 1) h
  have hcancel : (h ▸ (e ▸ z) : SingularChain X (j + 1 + (m + 1))) = z := by
    rw [eqRec_eq_cast, eqRec_eq_cast, cast_cast, cast_eq]
  rw [hcancel] at hleib
  have hsub : chainBoundary X (j + (m + 1)) (e ▸ z) ∈ subspaceChains S (j + (m + 1)) :=
    chainBoundary_cast_mem (a := j + 1 + m) (b := j + (m + 1)) z e (by omega) hz
  have hgsub : cap (m := m + 1) g (chainBoundary X (j + (m + 1)) (e ▸ z)) ∈ subspaceChains S (m + 1) :=
    cap_mem_subspaceChains g hsub
  have addcc : ∀ (B C : SingularChain X (m + 1)), B + C + C = B := fun B C => by
    rw [add_assoc, ZModModule.add_self, add_zero]
  have hcapeq : cap (m := m + 1) (coboundary X j g) z
      = chainBoundary X (m + 1) (cap (m := m + 2) g (e ▸ z))
        + cap (m := m + 1) g (chainBoundary X (j + (m + 1)) (e ▸ z)) := by
    simp only [hleib]
    exact (addcc _ _).symm
  refine ⟨RelativeChain.mk S (m + 2) (cap (m := m + 2) g (e ▸ z)), ?_⟩
  rw [relBoundary_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  simp only [hcapeq]
  rw [show chainBoundary X (m + 1) (cap (m := m + 2) g (e ▸ z))
        - (chainBoundary X (m + 1) (cap (m := m + 2) g (e ▸ z))
          + cap (m := m + 1) g (chainBoundary X (j + (m + 1)) (e ▸ z)))
      = cap (m := m + 1) g (chainBoundary X (j + (m + 1)) (e ▸ z)) from by
        rw [sub_add_eq_sub_sub, sub_self, zero_sub,
          neg_eq_of_add_eq_zero_left (ZModModule.add_self _)]]
  exact hgsub

/-- **The relative cap product on (co)homology** `capRelH k m : Hᵏ(X) → H_{k+m+1}(X, S) → H_{m+1}(X, S)`
— capping an **absolute** cohomology class against a **relative** homology class. The relative mirror of
`SingularCapHomology.capH`. -/
noncomputable def capRelH (k m : ℕ) :
    Cohomology X k →ₗ[ZMod 2]
      RelativeHomology S (k + m + 1) →ₗ[ZMod 2] RelativeHomology S (m + 1) :=
  Submodule.liftQ _ capRelHomologyₗ (by
    intro a ha
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
    rw [LinearMap.mem_ker]
    ext x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.zero_apply]
    show capRelHomology a (RelativeHomology.mk S (k + m + 1) z) = 0
    rw [capRelHomology_mk, RelativeHomology.mk_eq_zero_iff]
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z : RelativeChain S (k + m + 1))
    have hcmk : (z : RelativeChain S (k + m + 1)) = RelativeChain.mk S (k + m + 1) c := hc.symm
    have hzc : chainBoundary X (k + m) c ∈ subspaceChains S (k + m) := by
      have hz2 : relBoundary S (k + m) (z : RelativeChain S (k + m + 1)) = 0 :=
        LinearMap.mem_ker.mp z.2
      rw [hcmk, relBoundary_mk, RelativeChain.mk_eq_zero_iff] at hz2
      exact hz2
    have hval : (capRelCyclesₗ (m := m) a z : RelativeChain S (m + 1))
        = RelativeChain.mk S (m + 1) (cap (m := m + 1) a.1 c) := by
      rw [capRelCyclesₗ_coe, hcmk]; rfl
    rw [hval]
    cases k with
    | zero =>
        rw [show coboundaryRange X 0 = (⊥ : Submodule (ZMod 2) (SingularCochain X 0)) from rfl,
          Submodule.mem_bot] at ha
        rw [show (a.1 : SingularCochain X 0) = 0 from ha, cap_zero_cochain,
          show RelativeChain.mk S (m + 1) (0 : SingularChain X (m + 1)) = 0 from by
            rw [RelativeChain.mk_eq_zero_iff]; exact Submodule.zero_mem _]
        exact Submodule.zero_mem _
    | succ j =>
        rw [show coboundaryRange X (j + 1) = LinearMap.range (coboundaryₗ X j) from rfl] at ha
        obtain ⟨g, hg⟩ := ha
        rw [← hg]
        exact cap_coboundary_relCycle_mem_relBoundaries g c hzc)

@[simp] theorem capRelH_mk_mk (a : LinearMap.ker (coboundaryₗ X k)) (z : relCycles S (k + m + 1)) :
    capRelH (S := S) k m (Cohomology.mk X k a) (RelativeHomology.mk S (k + m + 1) z)
      = RelativeHomology.mk S (m + 1) (capRelCyclesₗ a z) :=
  rfl

/-! ## §5. The relative descended cap–cup adjunction `⟨a ∪ b, z⟩ = ⟨b, a ⌢ z⟩` -/

/-- **The relative descended cap–cup adjunction** `⟨a ∪ b, z⟩ = ⟨b, a ⌢ z⟩` for an absolute left factor
`a ∈ Hᵏ(X)`, a relative right factor `b ∈ H^{m+1}(X, S)`, and a relative class `z ∈ H_{k+m+1}(X, S)`.
Descends the chain-level `SingularCapChainIncl.kronecker_cup_cap` through the relative quotients — the
relative mirror of `SingularCupCapHomology.kroneckerH_capH_cupRightGeneralH`. The left cup factor is
carried as the class `Cohomology.mk X k a` via the relative right-general cup `relCupRightGeneralH`. -/
theorem relKroneckerH_relCupRightGeneralH (a : LinearMap.ker (coboundaryₗ X k))
    (b : RelativeCohomology S (m + 1)) (z : RelativeHomology S (k + m + 1)) :
    relKroneckerH S (relCupRightGeneralH (k := k) (m := m + 1) a b) z
      = relKroneckerH S b (capRelH k m (Cohomology.mk X k a) z) := by
  obtain ⟨fb, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  obtain ⟨zc, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨zchain, hzchain⟩ := Submodule.Quotient.mk_surjective _ (zc : RelativeChain S (k + m + 1))
  show relKroneckerH S (relCupRightGeneralH (k := k) (m := m + 1) a (RelativeCohomology.mk S (m + 1) fb))
        (RelativeHomology.mk S (k + m + 1) zc)
      = relKroneckerH S (RelativeCohomology.mk S (m + 1) fb)
          (capRelH k m (Cohomology.mk X k a) (RelativeHomology.mk S (k + m + 1) zc))
  rw [relCupRightGeneralH_apply_mk, capRelH_mk_mk]
  show relKroneckerH S (RelativeCohomology.mk S (k + m + 1) (relCupCocycleₗ a fb))
        (RelativeHomology.mk S (k + m + 1) zc)
      = relKroneckerH S (RelativeCohomology.mk S (m + 1) fb)
          (RelativeHomology.mk S (m + 1) (capRelCyclesₗ a zc))
  rw [relKroneckerH_mk_mk, relKroneckerH_mk_mk]
  have h1 : (zc : RelativeChain S (k + m + 1)) = RelativeChain.mk S (k + m + 1) zchain := hzchain.symm
  have h2 : (capRelCyclesₗ (m := m) a zc : RelativeChain S (m + 1))
      = RelativeChain.mk S (m + 1) (cap (m := m + 1) a.1 zchain) := by
    rw [capRelCyclesₗ_coe, h1]; rfl
  rw [h1, h2, relKronecker_mk, relKronecker_mk]
  show kronecker (cup a.1 (fb.1 : SingularCochain X (m + 1))) zchain
      = kronecker (fb.1 : SingularCochain X (m + 1)) (cap a.1 zchain)
  exact SingularCapChainIncl.kronecker_cup_cap a.1 (fb.1 : SingularCochain X (m + 1)) zchain

end SKEFTHawking.SingularRelativeCapHomology
