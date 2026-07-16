/-
# Phase 5q.H close-out (#187) — the INTEGRAL cohomology pair-LES connecting map `δ` and the
# `im ι* = ker δ` middle exactness, on the annihilator model over `ℤ`

The integral mirror of `SingularRelativeCohomDelta.deltaRelH`. On this substrate's annihilator model
(`relCochainsInt S` = integral cochains killing the subspace chains `= im C_•(S;ℤ)`) the pair
connecting map has a light description as a **δ-image class**: the connecting map
`δ : Hⁿ(∂W;ℤ) → Hⁿ⁺¹(W,∂W;ℤ)` sends the class of a boundary cocycle — presented by any absolute lift
`z ∈ Cⁿ(W;ℤ)` whose coboundary `δz` annihilates the subcomplex (`δz ∈ relCochainsInt S (n+1)`) — to
`[δz] ∈ Hⁿ⁺¹(W,∂W;ℤ)`. (The lift exists because the restriction `Cⁿ(W) ↠ Cⁿ(∂W)` is surjective, the
annihilator-model dual of the subcomplex injection.)

This module banks, for a generic pair `(X, S)`, over `ℤ`:

* **§1 `deltaRelHInt`** (piece 1) — the δ-image class `[δz] ∈ Hⁿ⁺¹(X,S;ℤ)`, degree-general (`δⁿ`), with
  its additivity/`ℤ`-linearity in the lift and its `deltaRelCocycleInt` cocycle-packaging.
* **§2 the pair-LES middle exactness** `im ι* = ker δ` (piece 2). On lifts:
  `deltaRelHInt z h = 0 ↔ z` differs from an absolute cocycle by a relative cochain
  (`deltaRelHInt_eq_zero_iff`), i.e. the boundary class `[z|∂W]` is `δ`-killed **iff** it is the
  restriction of an absolute class (`= im ι*`). The two containment halves:
  `im ι* ⊆ ker δ` is `deltaRelHInt_of_cocycle_eq_zero` (an absolute cocycle has `δz = 0`, so `[δz] = 0`);
  `ker δ ⊆ im ι*` is the substantive snake-chase inside `deltaRelHInt_eq_zero_iff`.

This is the shared Int pair-LES substrate for the σ-descent, dA's hcob, and the trace's Wu functional
vanishings — the `#185`-inventoried architectural gap's core `δ`+exactness over `ℤ`. It is built on the
genuine integral relative cochain complex (`RelativeCohomologyInt`, `SingularEuclideanCapIsoInt`), NOT on
the `Fin n → ℝ` lattice model of the downstream consumers (that identification is the separate `⊗ℝ`
wiring layer).

Dimension discipline (for the consumers): `W` 5-dim, `∂W` 4-dim; `δ` in degrees `2 → 3`
(`n = 2` here); the mixed pairing against `[W,∂W]` lives in the Kronecker layer, not this module.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SingularEuclideanCapIsoInt
import SKEFTHawking.SingularRelativeUCInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeUCInt

namespace SKEFTHawking.SingularRelativeCohomDeltaInt

noncomputable section

variable {X : TopCat} {S : Set X}

/-! ## §1. The integral δ-image class -/

/-- The integral coboundary `δz` of an absolute cochain, packaged as a **relative cocycle** when it
annihilates the subcomplex (the cocycle condition is `δ² = 0`). Integral mirror of
`SingularRelativeCohomDelta.deltaRelCocycle`. -/
def deltaRelCocycleInt {n : ℕ} (z : SingularCochainInt X n)
    (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) :
    LinearMap.ker (relCoboundaryIntₗ S (n + 1)) :=
  ⟨⟨coboundaryₗ X n z, h⟩, LinearMap.mem_ker.mpr (Subtype.ext (by
    rw [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero]
    exact coboundary_comp_coboundary X n z))⟩

@[simp] theorem deltaRelCocycleInt_coe {n : ℕ} (z : SingularCochainInt X n)
    (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) :
    ((deltaRelCocycleInt z h : LinearMap.ker (relCoboundaryIntₗ S (n + 1))) :
      SingularCochainInt X (n + 1)) = coboundaryₗ X n z := rfl

/-- **The integral δ-image class** `[δz] ∈ Hⁿ⁺¹(X,S;ℤ)` — the cohomology pair connecting-map image on
the annihilator model over `ℤ`. -/
def deltaRelHInt {n : ℕ} (z : SingularCochainInt X n)
    (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) : RelativeCohomologyInt S (n + 1) :=
  RelativeCohomologyInt.mk S (n + 1) (deltaRelCocycleInt z h)

/-! ## §2. Middle exactness `im ι* = ker δ` on the lift model -/

/-- **`im ι* ⊆ ker δ`** — an absolute cocycle's boundary class is `δ`-killed. If `z` is an absolute
cocycle (`δz = 0`, so trivially relative), its δ-image class vanishes. -/
theorem deltaRelHInt_of_cocycle_eq_zero {n : ℕ} (z : SingularCochainInt X n)
    (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) (hz : coboundaryₗ X n z = 0) :
    deltaRelHInt z h = 0 := by
  rw [deltaRelHInt, RelativeCohomologyInt.mk_eq_zero_iff,
    show (↑(deltaRelCocycleInt z h) : relCochainsInt S (n + 1)) = 0 from
      Subtype.ext (by rw [deltaRelCocycleInt_coe]; exact hz)]
  exact Submodule.zero_mem _

/-- **The pair-LES middle exactness `im ι* = ker δ`, on lifts.** The δ-image class `[δz]` vanishes
**iff** the lift `z` differs from an absolute cocycle by a relative cochain — i.e. iff the boundary
class `[z|∂W] ∈ Hⁿ(∂W;ℤ)` is the restriction `ι*` of an absolute class in `Hⁿ(W;ℤ)`. The `←`
direction is `im ι* ⊆ ker δ`; the `→` direction is the substantive `ker δ ⊆ im ι*` snake-chase. -/
theorem deltaRelHInt_eq_zero_iff {n : ℕ} (z : SingularCochainInt X n)
    (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) :
    deltaRelHInt z h = 0 ↔
      ∃ z' : SingularCochainInt X n, coboundaryₗ X n z' = 0 ∧ z - z' ∈ relCochainsInt S n := by
  rw [deltaRelHInt, RelativeCohomologyInt.mk_eq_zero_iff]
  show (↑(deltaRelCocycleInt z h) : relCochainsInt S (n + 1)) ∈
      relCoboundaryRangeInt S (n + 1) ↔ _
  rw [show relCoboundaryRangeInt S (n + 1) = LinearMap.range (relCoboundaryIntₗ S n) from rfl,
    LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨z - (w : SingularCochainInt X n), ?_, ?_⟩
    · have hw' : coboundaryₗ X n (w : SingularCochainInt X n) = coboundaryₗ X n z := by
        have := Subtype.ext_iff.mp hw
        rwa [relCoboundaryIntₗ_coe, deltaRelCocycleInt_coe] at this
      rw [map_sub, hw', sub_self]
    · rw [sub_sub_cancel]
      exact w.2
  · rintro ⟨z', hz', hmem⟩
    refine ⟨⟨z - z', hmem⟩, ?_⟩
    apply Subtype.ext
    rw [relCoboundaryIntₗ_coe, deltaRelCocycleInt_coe]
    show coboundaryₗ X n (z - z') = coboundaryₗ X n z
    rw [map_sub, hz', sub_zero]

/-- A **relative** lift has vanishing δ-image class: if `z ∈ relCochainsInt S n`, then `[δz] = 0`
(take the absolute cocycle `0`; `z - 0 = z` is relative). The well-definedness engine — `δ` factors
through the restriction `z ↦ z|∂W`. -/
theorem deltaRelHInt_relCochain_eq_zero {n : ℕ} (z : SingularCochainInt X n)
    (hz : z ∈ relCochainsInt S n)
    (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) :
    deltaRelHInt z h = 0 :=
  (deltaRelHInt_eq_zero_iff z h).mpr ⟨0, map_zero _, by rwa [sub_zero]⟩

/-! ## §3. `ℤ`-linearity of the δ-image class in the lift -/

/-- **Additivity of `δ` in the lift.** `[δ(z₁+z₂)] = [δz₁] + [δz₂]` — the δ-image class is additive.
This is what makes the pair connecting map `δ` a genuine `ℤ`-linear map on `Hⁿ(∂W;ℤ)` (the lift class
`[z|∂W]` depends `ℤ`-linearly on `z`, `deltaRelHInt_relCochain_eq_zero` handling well-definedness). -/
theorem deltaRelHInt_add {n : ℕ} (z₁ z₂ : SingularCochainInt X n)
    (h₁ : coboundaryₗ X n z₁ ∈ relCochainsInt S (n + 1))
    (h₂ : coboundaryₗ X n z₂ ∈ relCochainsInt S (n + 1)) :
    deltaRelHInt (z₁ + z₂) (by rw [map_add]; exact Submodule.add_mem _ h₁ h₂)
      = deltaRelHInt z₁ h₁ + deltaRelHInt z₂ h₂ := by
  have hsum : deltaRelCocycleInt (z₁ + z₂) (by rw [map_add]; exact Submodule.add_mem _ h₁ h₂)
      = deltaRelCocycleInt z₁ h₁ + deltaRelCocycleInt z₂ h₂ :=
    Subtype.ext (Subtype.ext (by rw [deltaRelCocycleInt_coe]; exact map_add _ _ _))
  rw [deltaRelHInt, deltaRelHInt, deltaRelHInt, hsum, RelativeCohomologyInt.mk,
    RelativeCohomologyInt.mk, RelativeCohomologyInt.mk]
  exact Submodule.Quotient.mk_add _

/-- **`ℤ`-homogeneity of `δ` in the lift.** `[δ(s • z)] = s • [δz]`. -/
theorem deltaRelHInt_smul {n : ℕ} (s : ℤ) (z : SingularCochainInt X n)
    (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) :
    deltaRelHInt (s • z) (by rw [map_smul]; exact Submodule.smul_mem _ s h)
      = s • deltaRelHInt z h := by
  have hsm : deltaRelCocycleInt (s • z) (by rw [map_smul]; exact Submodule.smul_mem _ s h)
      = s • deltaRelCocycleInt z h :=
    Subtype.ext (Subtype.ext (by rw [deltaRelCocycleInt_coe]; exact map_smul _ _ _))
  rw [deltaRelHInt, deltaRelHInt, hsm, RelativeCohomologyInt.mk, RelativeCohomologyInt.mk]
  exact Submodule.Quotient.mk_smul _ _ _

/-! ## §4. The `δ ⊣ ∂` adjunction against the relative Kronecker pairing -/

/-- **The connecting-map / boundary adjunction** `⟨δ[z|∂W], [c]⟩ = ⟨z, ∂c⟩`. The relative Kronecker
pairing (`SingularRelativeUCInt.relKroneckerHInt`, piece 3 — the mixed cohomology×homology pairing
whose free-part nondegeneracy is the integral relative UCT) of the δ-image class `deltaRelHInt z h`
against a relative `(n+1)`-cycle `[c]` equals the absolute Kronecker of the lift `z` against the
boundary `∂c` (which lives in the subspace, `c` being a relative cycle). This is the algebraic core
of the substrate's PD-intertwining `hadj` — the `rest2 ⊣ delta` compatibility — in the pairing's
native language: `δ` is adjoint to `∂` under Kronecker. Reuses `relKroneckerInt_relBoundary`'s engine
via `kronecker_coboundary_chainBoundary`. -/
theorem relKroneckerHInt_deltaRelHInt {n : ℕ} (z : SingularCochainInt X n)
    (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1))
    (c : SingularChainInt X (n + 1))
    (hc : RelativeChainInt.mk S (n + 1) c ∈ relCyclesInt S (n + 1)) :
    relKroneckerHInt S (deltaRelHInt z h)
        (RelHomologyInt.mk S (n + 1) ⟨RelativeChainInt.mk S (n + 1) c, hc⟩)
      = kronecker z (chainBoundary X n c) := by
  rw [deltaRelHInt, relKroneckerHInt_mk_mk, relKroneckerInt_mk, deltaRelCocycleInt_coe]
  exact kronecker_coboundary_chainBoundary z c

/-! ## §5. The pair-restriction map `j*` and the `im δ = ker j*` exactness -/

/-- A relative cocycle, forgotten to an absolute cocycle over `ℤ` (`relCochainsInt ↪ SingularCochainInt`
on cocycles): `a ↦ a` as a cochain, still a cocycle since `δ_rel a = 0 ⟺ δ a = 0`. Integral mirror of
`SingularRelativeAbsCompat.relToAbsCocycleₗ`. -/
noncomputable def relToAbsCocycleIntₗ {m : ℕ} :
    LinearMap.ker (relCoboundaryIntₗ S m) →ₗ[ℤ] LinearMap.ker (coboundaryₗ X m) :=
  (((relCochainsInt S m).subtype.comp (LinearMap.ker (relCoboundaryIntₗ S m)).subtype)).codRestrict
    (LinearMap.ker (coboundaryₗ X m))
    (fun a => LinearMap.mem_ker.mpr (relCocycleInt_coboundary_zero S a))

@[simp] theorem relToAbsCocycleIntₗ_coe {m : ℕ} (a : LinearMap.ker (relCoboundaryIntₗ S m)) :
    ((relToAbsCocycleIntₗ a : LinearMap.ker (coboundaryₗ X m)) : SingularCochainInt X m) = a.1.1 := rfl

/-- **The integral absolutification / pair-restriction map** `j* : Hᵐ(X, S; ℤ) → Hᵐ(X; ℤ)`,
`[a] ↦ [a]`. Well-defined: `relToAbsCocycleIntₗ` carries relative cocycles to absolute cocycles, and
relative coboundaries (`δ_rel β`) to absolute coboundaries (`δ β`). The forgetful `j*` leg of the pair
long exact sequence, over `ℤ`. Integral mirror of `SingularRelativeAbsCompat.relToAbs`. -/
noncomputable def relToAbsInt {m : ℕ} : RelativeCohomologyInt S m →ₗ[ℤ] Cohomology X m :=
  Submodule.liftQ _ ((Submodule.mkQ _).comp relToAbsCocycleIntₗ)
    (by
      intro a ha
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
      cases m with
      | zero =>
          rw [show relCoboundaryRangeInt S 0 = (⊥ : Submodule ℤ (relCochainsInt S 0)) from rfl,
            Submodule.mem_bot] at ha
          rw [show coboundaryRange X 0 = (⊥ : Submodule ℤ (SingularCochainInt X 0)) from rfl,
            Submodule.mem_bot]
          rw [show ((relToAbsCocycleIntₗ a : LinearMap.ker (coboundaryₗ X 0)) : SingularCochainInt X 0)
              = a.1.1 from rfl, show a.1 = 0 from ha]
          rfl
      | succ j =>
          rw [show relCoboundaryRangeInt S (j + 1) = LinearMap.range (relCoboundaryIntₗ S j) from rfl]
            at ha
          rw [show coboundaryRange X (j + 1) = LinearMap.range (coboundaryₗ X j) from rfl]
          obtain ⟨β, hβ⟩ := ha
          refine ⟨β.1, ?_⟩
          rw [relToAbsCocycleIntₗ_coe]
          have := congrArg Subtype.val hβ
          rwa [relCoboundaryIntₗ_coe] at this)

@[simp] theorem relToAbsInt_mk {m : ℕ} (a : LinearMap.ker (relCoboundaryIntₗ S m)) :
    relToAbsInt (RelativeCohomologyInt.mk S m a) = Cohomology.mk X m (relToAbsCocycleIntₗ a) := rfl

/-- **Exactness at `Hⁿ⁺¹(X,S;ℤ)` — `ker j* ⊆ im δ`.** A relative class killed by the pair restriction
`j* = relToAbsInt` is a δ-image. On the cylinder / suspension degrees `j*` vanishes, so every class is a
δ-image — the `ker j* ⊆ im δ` half the suspension atoms consume, now over `ℤ`. Integral mirror of
`SingularRelativeCohomDelta.exists_deltaRelH_of_relToAbs_eq_zero`. -/
theorem exists_deltaRelHInt_of_relToAbsInt_eq_zero {n : ℕ} (b : RelativeCohomologyInt S (n + 1))
    (hb : relToAbsInt b = 0) :
    ∃ (z : SingularCochainInt X n) (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)),
      b = deltaRelHInt z h := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [show (Submodule.Quotient.mk a : RelativeCohomologyInt S (n + 1))
      = RelativeCohomologyInt.mk S (n + 1) a from rfl, relToAbsInt_mk] at hb
  have h2 := (Submodule.Quotient.mk_eq_zero _).mp hb
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
    show coboundaryRange X (n + 1) = LinearMap.range (coboundaryₗ X n) from rfl] at h2
  obtain ⟨z, hz⟩ := h2
  have hz' : coboundaryₗ X n z = a.1.1 := hz.trans (relToAbsCocycleIntₗ_coe a)
  refine ⟨z, by rw [hz']; exact a.1.2, ?_⟩
  exact congrArg (RelativeCohomologyInt.mk S (n + 1)) (Subtype.ext (Subtype.ext hz'.symm))

/-- **`im δ ⊆ ker j*`** — the δ-image class is `j*`-killed. `j*[δz] = [δz]` in `Hⁿ⁺¹(X;ℤ)` is zero
because `δz` is an absolute coboundary. Together with `exists_deltaRelHInt_of_relToAbsInt_eq_zero` this
is the full exactness `im δ = ker j*` at `Hⁿ⁺¹(X,S;ℤ)`. -/
theorem relToAbsInt_deltaRelHInt_eq_zero {n : ℕ} (z : SingularCochainInt X n)
    (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) :
    relToAbsInt (deltaRelHInt z h) = 0 := by
  rw [deltaRelHInt, relToAbsInt_mk, Cohomology.mk]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
    show coboundaryRange X (n + 1) = LinearMap.range (coboundaryₗ X n) from rfl,
    relToAbsCocycleIntₗ_coe, deltaRelCocycleInt_coe]
  exact ⟨z, rfl⟩

end

end SKEFTHawking.SingularRelativeCohomDeltaInt
