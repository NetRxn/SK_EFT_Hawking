/-
# The interval pair class `H₁(I, ∂I; ℤ/2) ≅ ℤ/2` — the interval factor of the cross product

The mod-2 relative fundamental class of the pair `(I, ∂I)` where `I = unitInterval = [0,1]` and
`∂I = {⊥, ⊤} = {0, 1}`. This is the interval factor of the honest product route
`[W, ∂W] = [M] × [I, ∂I]` (the `SingularRelativeCrossProduct` engine bakes `[I, ∂I]` in as the
identity `1`-simplex / prism); the standalone class here is the reusable interval infrastructure the
eventual interior local-Künneth discharge consumes.

## What this banks (all kernel-pure, no `sorry`/axiom)

* **§1 — `I` is acyclic**: the straight-line contraction to `0` gives `Hₙ₊₁(I; ℤ/2) = 0`
  (`homology_interval_eq_zero`); in particular `H₁(I) = 0`.
* **§2 — `∂I` is two points**: `H₀(∂I; ℤ/2)` is `2`-dimensional (`{⊥}` clopen in `{⊥,⊤}`, each a
  point with `H₀ ≅ ℤ/2` — `SingularDisjointUnionHn.splitHnEquiv`).
* **§3 — the pair rank**: via the generic `finrank_relHom_of_homIncl_surj` (pair-LES rank–nullity),
  `dim H₁(I, ∂I) = dim H₀(∂I) − dim H₀(I) = 2 − 1 = 1`, hence `H₁(I, ∂I) ≅ ℤ/2`
  (`intervalPairClassEquiv`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.SingularH0PathConnected
import SKEFTHawking.SingularDisjointUnionHn
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularH0 SKEFTHawking.SingularH0PathConnected
open SKEFTHawking.SingularDisjointUnionHn

namespace SKEFTHawking.SingularIntervalPairClass

noncomputable section

/-- **The interval `I = [0,1]` as a `TopCat`.** -/
abbrev ICat : TopCat := TopCat.of unitInterval

/-! ## §1. `I` is acyclic — the straight-line contraction to `0` -/

/-- **The straight-line contraction** `H : I × I → I`, `(x, t) ↦ (1 - t)·x`, contracting `I` to `0`. -/
def intervalContraction : C(↑ICat × unitInterval, ↑ICat) where
  toFun p := ⟨(1 - (p.2 : ℝ)) * (p.1 : ℝ), by
    constructor <;>
      nlinarith [unitInterval.nonneg p.2, unitInterval.le_one p.2,
        unitInterval.nonneg p.1, unitInterval.le_one p.1]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop

@[simp] theorem slice_intervalContraction_zero :
    slice intervalContraction 0 = ContinuousMap.id ↑ICat := by
  ext x
  show (1 - ((0 : unitInterval) : ℝ)) * (x : ℝ) = (x : ℝ)
  simp

@[simp] theorem slice_intervalContraction_one :
    slice intervalContraction 1 = ContinuousMap.const ↑ICat (⟨0, by norm_num, by norm_num⟩) := by
  ext x
  show (1 - ((1 : unitInterval) : ℝ)) * (x : ℝ) = (0 : ℝ)
  simp

/-- **`I` is acyclic in positive degrees** `Hₙ₊₁(I; ℤ/2) = 0`: every cycle is a boundary, from the
straight-line contraction to `0`. -/
theorem homology_interval_eq_zero (n : ℕ) (y : Homology ICat (n + 1)) : y = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  exact Submodule.mem_comap.mpr
    (cycle_mem_boundaries_of_contraction intervalContraction ⟨0, by norm_num, by norm_num⟩
      slice_intervalContraction_zero slice_intervalContraction_one
      (z : SingularChain ICat (n + 1)) (LinearMap.mem_ker.mp z.2))

/-- **`I` is path-connected** (convex), so `H₀(I; ℤ/2) ≅ ℤ/2` — the base of the pair-rank count. -/
instance instPathConnectedICat : PathConnectedSpace ↑ICat :=
  isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by norm_num, by norm_num⟩)

/-- **`dim H₀(I; ℤ/2) = 1`** (`I` path-connected). -/
theorem finrank_homology_interval_zero : Module.finrank (ZMod 2) (Homology ICat 0) = 1 := by
  rw [LinearEquiv.finrank_eq (homologyZeroPathConnectedEquiv (X := ICat)), Module.finrank_self]

/-! ## §2. `∂I = {⊥,⊤}` is two points: `dim H₀(∂I; ℤ/2) = 2` -/

/-- **The interval boundary** `∂I = {⊥, ⊤} = {0, 1}` as a subset of `I`. -/
abbrev bdI : Set ↑ICat := {⊥, ⊤}

instance instNonemptyBotPt : Nonempty ↑(sub ({p : ↑(sub bdI) | (p : ↑ICat) = ⊥})) :=
  ⟨⟨⟨⊥, Set.mem_insert _ _⟩, rfl⟩⟩

instance instNonemptyTopPt :
    Nonempty ↑(sub (({p : ↑(sub bdI) | (p : ↑ICat) = ⊥})ᶜ)) :=
  ⟨⟨⟨⊤, Set.mem_insert_of_mem _ rfl⟩, top_ne_bot⟩⟩

instance instSubsingletonBotPt :
    Subsingleton ↑(sub ({p : ↑(sub bdI) | (p : ↑ICat) = ⊥})) :=
  ⟨fun a b => Subtype.ext (Subtype.ext (a.2.trans b.2.symm))⟩

instance instSubsingletonTopPt :
    Subsingleton ↑(sub (({p : ↑(sub bdI) | (p : ↑ICat) = ⊥})ᶜ)) := by
  refine ⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩
  have ha : ((a.1 : ↑(sub bdI)) : ↑ICat) = ⊤ :=
    Set.mem_singleton_iff.mp ((a.1.2).resolve_left a.2)
  have hb : ((b.1 : ↑(sub bdI)) : ↑ICat) = ⊤ :=
    Set.mem_singleton_iff.mp ((b.1.2).resolve_left b.2)
  rw [ha, hb]

/-- **`H₀(∂I; ℤ/2) ≅ ℤ/2 ⊕ ℤ/2`**: `∂I` is a two-point discrete space; the `⊥`-point is clopen,
splitting `H₀(∂I) ≅ H₀(⊥) ⊕ H₀(⊤) ≅ ℤ/2 ⊕ ℤ/2` (`SingularDisjointUnionHn.splitHnEquiv`). -/
noncomputable def intervalBdEquiv : Homology (sub bdI) 0 ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
  (splitHnEquiv (⟨isClosed_discrete _, isOpen_discrete _⟩ :
      IsClopen ({p : ↑(sub bdI) | (p : ↑ICat) = ⊥})) 0).symm.trans
    (LinearEquiv.prodCongr
      (homologyZeroPathConnectedEquiv (X := sub ({p : ↑(sub bdI) | (p : ↑ICat) = ⊥})))
      (homologyZeroPathConnectedEquiv (X := sub (({p : ↑(sub bdI) | (p : ↑ICat) = ⊥})ᶜ))))

instance instFiniteHomologyBdI : FiniteDimensional (ZMod 2) (Homology (sub bdI) 0) :=
  intervalBdEquiv.symm.finiteDimensional

/-- **`dim H₀(∂I; ℤ/2) = 2`**. -/
theorem finrank_homology_bdI : Module.finrank (ZMod 2) (Homology (sub bdI) 0) = 2 := by
  rw [LinearEquiv.finrank_eq intervalBdEquiv, Module.finrank_prod, Module.finrank_self]

/-! ## §3. The pair rank `dim H₁(I, ∂I) = 1` and the class `H₁(I, ∂I) ≅ ℤ/2` -/

/-- **`homIncl : H₁(∂I) → H₁(I)` is surjective** — trivially, since `H₁(I) = 0`. -/
theorem homIncl_bdI_one_surjective : Function.Surjective (homIncl bdI 1) :=
  fun y => ⟨0, by rw [map_zero]; exact (homology_interval_eq_zero 0 y).symm⟩

/-- **`homIncl : H₀(∂I) → H₀(I)` is surjective**: the `⊥`-boundary point's class maps to the
generator of `H₀(I) ≅ ℤ/2` (augmentation `1`), so — as `H₀(I)` is `1`-dimensional — the map is onto.
This is "every path-component of `I` meets `∂I`" (`I` connected, `∂I` nonempty). -/
theorem homIncl_bdI_zero_surjective : Function.Surjective (homIncl bdI 0) := by
  set z₀ : cycles (sub bdI) 0 :=
    ⟨Finsupp.single (constSimplex (⟨⊥, Set.mem_insert _ _⟩ : ↑(sub bdI)) 0) 1, Submodule.mem_top⟩
    with hz₀
  set y₀ : Homology (sub bdI) 0 := Homology.mk (sub bdI) 0 z₀ with hy₀
  have hy1 : augH ICat (homIncl bdI 0 y₀) = 1 := by
    rw [hy₀, homIncl_mk, augH_mk]
    show augmentation ICat (chainIncl bdI 0 (z₀ : SingularChain (sub bdI) 0)) = 1
    rw [hz₀, chainIncl_single, augmentation_single]
  have hbij : Function.Bijective (augH ICat) :=
    (homologyZeroPathConnectedEquiv (X := ICat)).bijective
  intro y
  refine ⟨(augH ICat y) • y₀, hbij.injective ?_⟩
  simp only [map_smul, hy1, smul_eq_mul, mul_one]

/-- **`dim H₁(I, ∂I; ℤ/2) = 1`**: the pair-LES rank–nullity
(`finrank_relHom_of_homIncl_surj`) gives `dim H₁(I, ∂I) = dim H₀(∂I) − dim H₀(I) = 2 − 1 = 1`. -/
theorem finrank_intervalPair : Module.finrank (ZMod 2) (RelativeHomology bdI 1) = 1 := by
  rw [PoincareLefschetzRelFundClassCylinderSuspension.finrank_relHom_of_homIncl_surj bdI 0
      instFiniteHomologyBdI homIncl_bdI_zero_surjective homIncl_bdI_one_surjective,
    finrank_homology_bdI, finrank_homology_interval_zero]

instance instFiniteIntervalPair : FiniteDimensional (ZMod 2) (RelativeHomology bdI 1) :=
  FiniteDimensional.of_finrank_eq_succ finrank_intervalPair

/-- **The interval pair class** `H₁(I, ∂I; ℤ/2) ≅ ℤ/2` — the mod-2 relative fundamental class of the
pair `(I, ∂I)`, the interval factor of `[W, ∂W] = [M] × [I, ∂I]`. -/
noncomputable def intervalPairClassEquiv :
    RelativeHomology bdI 1 ≃ₗ[ZMod 2] ZMod 2 :=
  LinearEquiv.ofFinrankEq _ _ (by rw [finrank_intervalPair, Module.finrank_self])

end

end SKEFTHawking.SingularIntervalPairClass
