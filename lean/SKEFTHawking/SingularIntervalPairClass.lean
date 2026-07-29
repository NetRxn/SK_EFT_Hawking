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
import SKEFTHawking.PoincareLefschetzRelFundClass
import SKEFTHawking.SingularCohomologyPairRestrict
import SKEFTHawking.SingularSubHomSumEnd
import SKEFTHawking.SingularRelativeFunctoriality
import SKEFTHawking.SingularRelativeMV

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularH0 SKEFTHawking.SingularH0PathConnected
open SKEFTHawking.SingularDisjointUnionHn
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularCohomologyPairRestrict
open SKEFTHawking.SingularSubHomSumEnd
open SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularRelativeMV

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

/-! ## §4. The interval **local** class at an interior point, `H₁(I, I∖{t}; ℤ/2) ≅ ℤ/2`

The local analogue of `intervalPairClassEquiv`: for an interior point `t ∉ ∂I`, `I ∖ {t}` splits
into the two convex clopen pieces `[0,t)` and `(t,1]` (`belowT`/`aboveT`), giving
`dim H₀(I∖{t}) = 2` by the same clopen-split route as `∂I`; the pair-rank count then gives
`dim H₁(I, I∖{t}) = 2 - 1 = 1`. -/

/-- The "below `t`" piece of `I ∖ {t}`: `{x ∈ I | x < t}`. -/
def belowT (t : ↑ICat) : Set ↑ICat := {x | (x : ℝ) < (t : ℝ)}

/-- The "above `t`" piece of `I ∖ {t}`: `{x ∈ I | t < x}`. -/
def aboveT (t : ↑ICat) : Set ↑ICat := {x | (t : ℝ) < (x : ℝ)}

theorem isOpen_belowT (t : ↑ICat) : IsOpen (belowT t) :=
  isOpen_Iio.preimage continuous_subtype_val

theorem isOpen_aboveT (t : ↑ICat) : IsOpen (aboveT t) :=
  isOpen_Ioi.preimage continuous_subtype_val

theorem belowT_subset_compl_singleton (t : ↑ICat) : belowT t ⊆ ({t}ᶜ : Set ↑ICat) :=
  fun _ hx hxt => absurd (congrArg (fun y : ↑ICat => (y : ℝ)) hxt) (ne_of_lt hx)

theorem aboveT_subset_compl_singleton (t : ↑ICat) : aboveT t ⊆ ({t}ᶜ : Set ↑ICat) :=
  fun _ hx hxt => absurd (congrArg (fun y : ↑ICat => (y : ℝ)) hxt) (ne_of_gt hx)

/-- **The "below `t`" piece of the punctured interval** `I ∖ {t}`, as a subset of the subspace
`sub ({t}ᶜ)`: the preimage of `belowT t` under the inclusion `I∖{t} ↪ I`. -/
def leftOfT (t : ↑ICat) : Set ↑(sub ({t}ᶜ : Set ↑ICat)) :=
  (fun p => (p : ↑ICat)) ⁻¹' belowT t

theorem isOpen_leftOfT (t : ↑ICat) : IsOpen (leftOfT t) :=
  (isOpen_belowT t).preimage continuous_subtype_val

/-- **The complement of `leftOfT t` in `I∖{t}` is `aboveT t`** (pulled back): every point of
`I∖{t}` is either below or above `t`, by trichotomy on the real coordinate. -/
theorem leftOfT_compl (t : ↑ICat) :
    (leftOfT t)ᶜ = (fun p : ↑(sub ({t}ᶜ : Set ↑ICat)) => (p : ↑ICat)) ⁻¹' aboveT t := by
  ext p
  have hp : (p : ↑ICat) ≠ t := p.2
  have hpR : ((p : ↑ICat) : ℝ) ≠ (t : ℝ) := fun h => hp (Subtype.ext h)
  simp only [leftOfT, Set.mem_compl_iff, Set.mem_preimage, belowT, aboveT, Set.mem_setOf_eq]
  rcases lt_or_gt_of_ne hpR with h | h
  · simp [not_lt.mpr h.le, h]
  · simp [not_lt_of_gt h, h]

theorem isOpen_leftOfT_compl (t : ↑ICat) : IsOpen (leftOfT t)ᶜ := by
  rw [leftOfT_compl]
  exact (isOpen_aboveT t).preimage continuous_subtype_val

/-- **`leftOfT t` is clopen in `I ∖ {t}`**: open by construction (preimage of the open `belowT t`),
closed because its complement is the preimage of the open `aboveT t`. -/
theorem isClopen_leftOfT (t : ↑ICat) : IsClopen (leftOfT t) :=
  ⟨isOpen_compl_iff.mp (isOpen_leftOfT_compl t), isOpen_leftOfT t⟩

theorem belowT_eq_preimage_Ico (t : ↑ICat) :
    belowT t = (fun x : ↑ICat => (x : ℝ)) ⁻¹' (Set.Ico (0 : ℝ) (t : ℝ)) := by
  ext x
  simp [belowT, Set.mem_Ico, unitInterval.nonneg x]

theorem aboveT_eq_preimage_Ioc (t : ↑ICat) :
    aboveT t = (fun x : ↑ICat => (x : ℝ)) ⁻¹' (Set.Ioc (t : ℝ) (1 : ℝ)) := by
  ext x
  simp [aboveT, Set.mem_Ioc, unitInterval.le_one x]

/-- **`belowT t` is path-connected** (`[0,t)` is convex, hence path-connected in `ℝ`; pulled back
along the inclusion `I ↪ ℝ`). -/
theorem isPathConnected_belowT (t : ↑ICat) (ht0 : (0 : ℝ) < (t : ℝ)) :
    IsPathConnected (belowT t) := by
  rw [belowT_eq_preimage_Ico]
  exact ((convex_Ico (0 : ℝ) (t : ℝ)).isPathConnected ⟨0, le_refl 0, ht0⟩).preimage_coe
    (fun x hx => ⟨hx.1, hx.2.le.trans (unitInterval.le_one t)⟩)

/-- **`aboveT t` is path-connected** (`(t,1]` is convex, hence path-connected in `ℝ`; pulled back
along the inclusion `I ↪ ℝ`). -/
theorem isPathConnected_aboveT (t : ↑ICat) (ht1 : (t : ℝ) < 1) :
    IsPathConnected (aboveT t) := by
  rw [aboveT_eq_preimage_Ioc]
  exact ((convex_Ioc (t : ℝ) (1 : ℝ)).isPathConnected ⟨1, ht1, le_refl 1⟩).preimage_coe
    (fun x hx => ⟨(unitInterval.nonneg t).trans hx.1.le, hx.2⟩)

/-- **`sub (leftOfT t)` is path-connected**: `leftOfT t` is the pullback of the path-connected
`belowT t` along `I∖{t} ↪ I`. -/
theorem pathConnectedSpace_leftOfT (t : ↑ICat) (ht0 : (0 : ℝ) < (t : ℝ)) :
    PathConnectedSpace ↑(sub (leftOfT t)) :=
  isPathConnected_iff_pathConnectedSpace.mp
    ((isPathConnected_belowT t ht0).preimage_coe (belowT_subset_compl_singleton t))

/-- **`sub (leftOfT t)ᶜ` is path-connected**: `(leftOfT t)ᶜ = ` the pullback of the path-connected
`aboveT t` along `I∖{t} ↪ I`. -/
theorem pathConnectedSpace_leftOfT_compl (t : ↑ICat) (ht1 : (t : ℝ) < 1) :
    PathConnectedSpace ↑(sub (leftOfT t)ᶜ) := by
  rw [leftOfT_compl]
  exact isPathConnected_iff_pathConnectedSpace.mp
    ((isPathConnected_aboveT t ht1).preimage_coe (aboveT_subset_compl_singleton t))

/-- **An interior point (`t ∉ ∂I`) has real coordinate strictly between `0` and `1`.** -/
theorem lt_and_lt_of_not_mem_bdI (t : ↑ICat) (ht : t ∉ bdI) :
    (0 : ℝ) < (t : ℝ) ∧ (t : ℝ) < 1 := by
  simp only [bdI, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
  obtain ⟨h0, h1⟩ := ht
  refine ⟨lt_of_le_of_ne (unitInterval.nonneg t) ?_, lt_of_le_of_ne (unitInterval.le_one t) ?_⟩
  · exact fun h => h0 (Subtype.ext (h.symm.trans (Set.Icc.coe_bot 0 1).symm))
  · exact fun h => h1 (Subtype.ext (h.trans (Set.Icc.coe_top 0 1).symm))

/-- **`H₀(I∖{t}; ℤ/2) ≅ ℤ/2 ⊕ ℤ/2`** for an interior point `t ∉ ∂I`: the clopen split
`I∖{t} = belowT t ⊔ aboveT t` into two convex (hence path-connected) pieces. -/
noncomputable def intervalLocalBdEquiv (t : ↑ICat) (ht0 : (0 : ℝ) < (t : ℝ))
    (ht1 : (t : ℝ) < 1) :
    Homology (sub ({t}ᶜ : Set ↑ICat)) 0 ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) := by
  haveI := pathConnectedSpace_leftOfT t ht0
  haveI := pathConnectedSpace_leftOfT_compl t ht1
  exact (splitHnEquiv (isClopen_leftOfT t) 0).symm.trans
    (LinearEquiv.prodCongr (homologyZeroPathConnectedEquiv (X := sub (leftOfT t)))
      (homologyZeroPathConnectedEquiv (X := sub (leftOfT t)ᶜ)))

-- v4.32 rejects this as an `instance`: `ht` is neither instance-implicit nor present in the
-- return type, so synthesis could never have inferred it. Kind change only.
theorem instFiniteHomologyCompl (t : ↑ICat) (ht : t ∉ bdI) :
    FiniteDimensional (ZMod 2) (Homology (sub ({t}ᶜ : Set ↑ICat)) 0) :=
  (intervalLocalBdEquiv t (lt_and_lt_of_not_mem_bdI t ht).1
    (lt_and_lt_of_not_mem_bdI t ht).2).symm.finiteDimensional

/-- **`dim H₀(I∖{t}; ℤ/2) = 2`** for an interior point `t ∉ ∂I`. -/
theorem finrank_homology_compl_singleton (t : ↑ICat) (ht0 : (0 : ℝ) < (t : ℝ))
    (ht1 : (t : ℝ) < 1) :
    Module.finrank (ZMod 2) (Homology (sub ({t}ᶜ : Set ↑ICat)) 0) = 2 := by
  rw [LinearEquiv.finrank_eq (intervalLocalBdEquiv t ht0 ht1), Module.finrank_prod,
    Module.finrank_self]

/-! ## §5. The interval local generator `H₁(I, I∖{t}; ℤ/2) ≅ ℤ/2` -/

/-- **`homIncl : H₁(S) → H₁(I)` is surjective for any `S`** — trivially, since `H₁(I) = 0`. -/
theorem homIncl_one_surjective (S : Set ↑ICat) : Function.Surjective (homIncl S 1) :=
  fun y => ⟨0, by rw [map_zero]; exact (homology_interval_eq_zero 0 y).symm⟩

/-- **`homIncl : H₀(S) → H₀(I)` is surjective whenever `S` is nonempty**: the class of a point of
`S` maps to the augmentation generator `1`, so — as `H₀(I)` is `1`-dimensional — the map is onto.
The point-parametrised generalisation of `homIncl_bdI_zero_surjective`. -/
theorem homIncl_zero_surjective_of_mem {S : Set ↑ICat} {p : ↑ICat} (hp : p ∈ S) :
    Function.Surjective (homIncl S 0) := by
  set z₀ : cycles (sub S) 0 :=
    ⟨Finsupp.single (constSimplex (⟨p, hp⟩ : ↑(sub S)) 0) 1, Submodule.mem_top⟩ with hz₀
  set y₀ : Homology (sub S) 0 := Homology.mk (sub S) 0 z₀ with hy₀
  have hy1 : augH ICat (homIncl S 0 y₀) = 1 := by
    rw [hy₀, homIncl_mk, augH_mk]
    show augmentation ICat (chainIncl S 0 (z₀ : SingularChain (sub S) 0)) = 1
    rw [hz₀, chainIncl_single, augmentation_single]
  have hbij : Function.Bijective (augH ICat) :=
    (homologyZeroPathConnectedEquiv (X := ICat)).bijective
  intro y
  refine ⟨(augH ICat y) • y₀, hbij.injective ?_⟩
  simp only [map_smul, hy1, smul_eq_mul, mul_one]

/-- **`⊥ ∈ I ∖ {t}`** for an interior point `t ∉ ∂I` (`t ≠ ⊥`). -/
theorem bot_mem_compl_singleton {t : ↑ICat} (ht : t ∉ bdI) : (⊥ : ↑ICat) ∈ ({t}ᶜ : Set ↑ICat) := by
  simp only [bdI, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
  exact fun h => ht.1 h.symm

/-- **`dim H₁(I, I∖{t}; ℤ/2) = 1`** for an interior point `t ∉ ∂I`: the pair-LES rank–nullity count,
mirroring `finrank_intervalPair` with `∂I` replaced by the punctured-interval `{t}ᶜ`. -/
theorem finrank_intervalLocalPair (t : ↑ICat) (ht : t ∉ bdI) :
    Module.finrank (ZMod 2) (RelativeHomology ({t}ᶜ : Set ↑ICat) 1) = 1 := by
  obtain ⟨ht0, ht1⟩ := lt_and_lt_of_not_mem_bdI t ht
  rw [PoincareLefschetzRelFundClassCylinderSuspension.finrank_relHom_of_homIncl_surj
      ({t}ᶜ) 0 (instFiniteHomologyCompl t ht)
      (homIncl_zero_surjective_of_mem (bot_mem_compl_singleton ht))
      (homIncl_one_surjective ({t}ᶜ)),
    finrank_homology_compl_singleton t ht0 ht1, finrank_homology_interval_zero]

-- v4.32 rejects this as an `instance`: `ht` is neither instance-implicit nor present in the
-- return type, so synthesis could never have inferred it. Kind change only.
theorem instFiniteIntervalLocalPair (t : ↑ICat) (ht : t ∉ bdI) :
    FiniteDimensional (ZMod 2) (RelativeHomology ({t}ᶜ : Set ↑ICat) 1) :=
  FiniteDimensional.of_finrank_eq_succ (finrank_intervalLocalPair t ht)

/-- **The interval LOCAL generator** `H₁(I, I∖{t}; ℤ/2) ≅ ℤ/2` at an interior point `t ∉ ∂I` — the
local analogue of `intervalPairClassEquiv`, in the exact `gen` shape `RestrictsToRelGen`/
`HasRelFundClass` (`PoincareLefschetzRelFundClass`) consume: an interior local-homology iso
`RelativeHomology ({x}ᶜ) _ ≃ₗ ZMod 2`. This is the reusable building block the interior
local-Künneth (the interval factor of `cylGen`) will cross against `M`'s own local generator. -/
noncomputable def intervalLocalGenEquiv {t : ↑ICat} (ht : t ∉ bdI) :
    RelativeHomology ({t}ᶜ : Set ↑ICat) 1 ≃ₗ[ZMod 2] ZMod 2 :=
  haveI := instFiniteIntervalLocalPair t ht
  LinearEquiv.ofFinrankEq _ _ (by rw [finrank_intervalLocalPair t ht, Module.finrank_self])

/-! ## §6. The restriction fact: `[I,∂I]` restricts to the local generator at every interior point -/

/-- **In a `1`-dimensional `ℤ/2`-vector space, `x` is the chosen generator `e.symm 1` of a linear
iso `e` to `ZMod 2` iff `x ≠ 0`** — `ZMod 2` has only the two elements `0, 1`, so the (unique)
nonzero element is forced to be the generator. Reduces "restricts to the generator" to "the
restriction map is nonzero". -/
theorem eq_symm_one_iff_ne_zero {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (e : V ≃ₗ[ZMod 2] ZMod 2) {x : V} : x = e.symm 1 ↔ x ≠ 0 := by
  rw [ne_eq, ← map_eq_zero_iff e e.injective, e.eq_symm_apply]
  rcases (by decide : ∀ p : ZMod 2, p = 0 ∨ p = 1) (e x) with h | h <;> simp [h]

/-- **A constant simplex at a subspace point pushes forward to the constant simplex at its image**:
`chainIncl S n (single (constSimplex ⟨p,hp⟩ n) 1) = single (constSimplex p n) 1`. The chain-level
bridge identifying the subspace-chain and ambient-chain descriptions of a basepoint class. -/
theorem chainIncl_constSimplex {X : TopCat} (S : Set ↑X) {p : ↑X} (hp : p ∈ S) (n : ℕ) :
    chainIncl S n (Finsupp.single (constSimplex (⟨p, hp⟩ : ↥S) n) 1)
      = Finsupp.single (constSimplex p n) 1 := by
  rw [← mapChain_subInclCM, mapChain_single, mapSimplex_constSimplex]
  rfl

/-- **`⊤ ∈ I ∖ {t}`** for an interior point `t ∉ ∂I` (`t ≠ ⊤`). -/
theorem top_mem_compl_singleton {t : ↑ICat} (ht : t ∉ bdI) : (⊤ : ↑ICat) ∈ ({t}ᶜ : Set ↑ICat) := by
  simp only [bdI, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
  exact fun h => ht.2 h.symm

/-- **A path `⊥ ⤳ ⊤` in `I`** (exists since `ICat` is path-connected). -/
noncomputable def bdPath : Path (⊥ : ↑ICat) (⊤ : ↑ICat) := PathConnectedSpace.somePath ⊥ ⊤

/-- **The identity `1`-simplex chain**: the singular `1`-simplex of `bdPath`, as a `1`-chain of `I`.
Its boundary is `[⊤] + [⊥]` — the chain-level witness that `[I,∂I]` is realised by "the interval
traversed once", the honest geometric content behind the restriction fact below. -/
noncomputable def bdPathChain : SingularChain ICat 1 := Finsupp.single (pathSimplex bdPath) 1

theorem chainBoundary_bdPathChain :
    chainBoundary ICat 0 bdPathChain
      = Finsupp.single (constSimplex (⊤ : ↑ICat) 0) 1 + Finsupp.single (constSimplex (⊥ : ↑ICat) 0) 1 :=
  chainBoundary_pathSimplex bdPath

/-- `∂(bdPathChain)` lies in the subspace chains of `∂I` — `bdPathChain` is a relative `1`-cycle of
`(I, ∂I)`. -/
theorem chainBoundary_bdPathChain_mem_subspaceChains_bdI :
    chainBoundary ICat 0 bdPathChain ∈ subspaceChains bdI 0 := by
  rw [chainBoundary_bdPathChain]
  refine ⟨Finsupp.single (constSimplex (⟨⊤, Set.mem_insert_of_mem _ rfl⟩ : ↥bdI) 0) 1
      + Finsupp.single (constSimplex (⟨⊥, Set.mem_insert _ _⟩ : ↥bdI) 0) 1, ?_⟩
  rw [map_add, chainIncl_constSimplex, chainIncl_constSimplex]

/-- `∂(bdPathChain)` lies in the subspace chains of `I ∖ {t}` — `bdPathChain` is also a relative
`1`-cycle of `(I, I∖{t})`, for any interior point `t`. -/
theorem chainBoundary_bdPathChain_mem_subspaceChains_compl {t : ↑ICat} (ht : t ∉ bdI) :
    chainBoundary ICat 0 bdPathChain ∈ subspaceChains ({t}ᶜ : Set ↑ICat) 0 := by
  rw [chainBoundary_bdPathChain]
  refine ⟨Finsupp.single (constSimplex (⟨⊤, top_mem_compl_singleton ht⟩ : ↥({t}ᶜ : Set ↑ICat)) 0) 1
      + Finsupp.single (constSimplex (⟨⊥, bot_mem_compl_singleton ht⟩ : ↥({t}ᶜ : Set ↑ICat)) 0) 1, ?_⟩
  rw [map_add, chainIncl_constSimplex, chainIncl_constSimplex]

theorem bdPathChain_mem_relCycleLift_bdI : bdPathChain ∈ relCycleLift bdI 0 :=
  Submodule.mem_comap.mpr chainBoundary_bdPathChain_mem_subspaceChains_bdI

theorem bdPathChain_mem_relCycleLift_compl {t : ↑ICat} (ht : t ∉ bdI) :
    bdPathChain ∈ relCycleLift ({t}ᶜ : Set ↑ICat) 0 :=
  Submodule.mem_comap.mpr (chainBoundary_bdPathChain_mem_subspaceChains_compl ht)

/-- **`restrictBd` reinterprets the same chain under a bigger subspace**: `relIncl` (of which
`restrictBd` is an instance) commutes with `relCycleToHom` on a shared chain lift-witness — the
identity map doesn't move the chain, only the ambient subspace changes. -/
theorem relIncl_relCycleToHom {S T : Set ↑ICat} (h : S ⊆ T) (n : ℕ) (c : SingularChain ICat (n + 1))
    (hcS : c ∈ relCycleLift S n) (hcT : c ∈ relCycleLift T n) :
    relIncl h (n + 1) (relCycleToHom S n ⟨c, hcS⟩) = relCycleToHom T n ⟨c, hcT⟩ := by
  rw [relCycleToHom_apply, relCycleToHom_apply, relIncl]
  show RelativeHomology.map (ContinuousMap.id ↑ICat) (fun _ hx => h hx) (n + 1)
      (RelativeHomology.mk (S := S) (n + 1) ⟨RelativeChain.mk S (n + 1) c, _⟩) = _
  rw [RelativeHomology.mk, RelativeHomology.mk, RelativeHomology.map_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  rw [relCyclesMap_coe, relMapChain_mk, mapChain_id]

/-- **The interval class as a chain-level witness**: the class of `bdPathChain` in `H₁(I,∂I)`. -/
noncomputable def zGen : RelativeHomology bdI 1 :=
  relCycleToHom bdI 0 ⟨bdPathChain, bdPathChain_mem_relCycleLift_bdI⟩

/-- **`restrictBd` applied to `zGen` is the same chain-level witness rel `I∖{t}`.** -/
theorem restrictBd_zGen (t : ↑ICat) (ht : t ∉ bdI) :
    restrictBd bdI ht 1 zGen
      = relCycleToHom ({t}ᶜ : Set ↑ICat) 0 ⟨bdPathChain, bdPathChain_mem_relCycleLift_compl ht⟩ :=
  relIncl_relCycleToHom (Set.subset_compl_singleton_iff.mpr ht) 0 bdPathChain _ _

/-- **The connecting-map extraction of `bdPathChain` rel `I∖{t}`** is exactly the pushed-forward
`⊤ + ⊥` basepoint chain (chain-level, via injectivity of `chainIncl`). -/
theorem boundaryExtract_bdPathChain_compl {t : ↑ICat} (ht : t ∉ bdI) :
    boundaryExtract ({t}ᶜ : Set ↑ICat) 0 ⟨bdPathChain, bdPathChain_mem_relCycleLift_compl ht⟩
      = Finsupp.single (constSimplex (⟨⊤, top_mem_compl_singleton ht⟩ : ↥({t}ᶜ : Set ↑ICat)) 0) 1
        + Finsupp.single (constSimplex (⟨⊥, bot_mem_compl_singleton ht⟩ : ↥({t}ᶜ : Set ↑ICat)) 0) 1 := by
  apply chainIncl_injective ({t}ᶜ : Set ↑ICat) 0
  rw [chainIncl_boundaryExtract, chainBoundary_bdPathChain, map_add, chainIncl_constSimplex,
    chainIncl_constSimplex]

theorem bot_mem_leftOfT {t : ↑ICat} (ht : t ∉ bdI) :
    (⟨⊥, bot_mem_compl_singleton ht⟩ : ↥({t}ᶜ : Set ↑ICat)) ∈ leftOfT t := by
  show ((⊥ : ↑ICat) : ℝ) < (t : ℝ)
  rw [Set.Icc.coe_bot]
  exact (lt_and_lt_of_not_mem_bdI t ht).1

theorem top_mem_leftOfT_compl {t : ↑ICat} (ht : t ∉ bdI) :
    (⟨⊤, top_mem_compl_singleton ht⟩ : ↥({t}ᶜ : Set ↑ICat)) ∈ (leftOfT t)ᶜ := by
  show ¬ ((⊤ : ↑ICat) : ℝ) < (t : ℝ)
  rw [Set.Icc.coe_top]
  exact not_lt.mpr (lt_and_lt_of_not_mem_bdI t ht).2.le

/-- The `⊥`-basepoint class of `sub (leftOfT t)`. -/
noncomputable def aGen {t : ↑ICat} (ht : t ∉ bdI) : Homology (sub (leftOfT t)) 0 :=
  Homology.mk (sub (leftOfT t)) 0
    ⟨Finsupp.single (constSimplex
      (⟨⟨⊥, bot_mem_compl_singleton ht⟩, bot_mem_leftOfT ht⟩ : ↥(leftOfT t)) 0) 1,
      Submodule.mem_top⟩

/-- The `⊤`-basepoint class of `sub (leftOfT t)ᶜ`. -/
noncomputable def bGen {t : ↑ICat} (ht : t ∉ bdI) : Homology (sub (leftOfT t)ᶜ) 0 :=
  Homology.mk (sub (leftOfT t)ᶜ) 0
    ⟨Finsupp.single (constSimplex
      (⟨⟨⊤, top_mem_compl_singleton ht⟩, top_mem_leftOfT_compl ht⟩ : ↥(leftOfT t)ᶜ) 0) 1,
      Submodule.mem_top⟩

theorem splitHn_aGen_bGen {t : ↑ICat} (ht : t ∉ bdI) :
    splitHn (leftOfT t) 0 (aGen ht, bGen ht)
      = Homology.mk (sub ({t}ᶜ : Set ↑ICat)) 0
          ⟨Finsupp.single (constSimplex (⟨⊤, top_mem_compl_singleton ht⟩ :
              ↥({t}ᶜ : Set ↑ICat)) 0) 1
            + Finsupp.single (constSimplex (⟨⊥, bot_mem_compl_singleton ht⟩ :
              ↥({t}ᶜ : Set ↑ICat)) 0) 1, Submodule.mem_top⟩ := by
  show homIncl (leftOfT t) 0 (aGen ht) + homIncl (leftOfT t)ᶜ 0 (bGen ht)
      = Homology.mk (sub ({t}ᶜ : Set ↑ICat)) 0 _
  rw [aGen, bGen, homIncl_mk, homIncl_mk, chainIncl_constSimplex, chainIncl_constSimplex,
    add_comm]
  rfl

/-- **The `⊤+⊥` class rel `I∖{t}` is nonzero**: it splits (via `splitHnEquiv`) as `(aGen, bGen)`,
whose first component `aGen` already has nonzero augmentation `1` — so `aGen ≠ 0`, hence the pair
`(aGen, bGen) ≠ 0`, hence (injectivity of `splitHnEquiv`) the original class is `≠ 0`. This is the
chain-level heart of the restriction fact: the local generator is detected by the split. -/
theorem homIncl_target_ne_zero {t : ↑ICat} (ht : t ∉ bdI) :
    Homology.mk (sub ({t}ᶜ : Set ↑ICat)) 0
      ⟨Finsupp.single (constSimplex (⟨⊤, top_mem_compl_singleton ht⟩ :
          ↥({t}ᶜ : Set ↑ICat)) 0) 1
        + Finsupp.single (constSimplex (⟨⊥, bot_mem_compl_singleton ht⟩ :
          ↥({t}ᶜ : Set ↑ICat)) 0) 1, Submodule.mem_top⟩ ≠ 0 := by
  intro hz
  have hpair : (splitHnEquiv (isClopen_leftOfT t) 0).symm
      (Homology.mk (sub ({t}ᶜ : Set ↑ICat)) 0
        ⟨Finsupp.single (constSimplex (⟨⊤, top_mem_compl_singleton ht⟩ :
            ↥({t}ᶜ : Set ↑ICat)) 0) 1
          + Finsupp.single (constSimplex (⟨⊥, bot_mem_compl_singleton ht⟩ :
            ↥({t}ᶜ : Set ↑ICat)) 0) 1, Submodule.mem_top⟩)
      = (aGen ht, bGen ht) :=
    (LinearEquiv.symm_apply_eq _).mpr (splitHn_aGen_bGen ht).symm
  rw [hz, map_zero] at hpair
  have haGen : aGen ht = 0 := congrArg Prod.fst hpair.symm
  have h1 : augH (sub (leftOfT t)) (aGen ht) = 1 := by
    rw [aGen, augH_mk, augmentation_single]
  rw [haGen, map_zero] at h1
  exact one_ne_zero h1.symm

/-- **`restrictBd bdI ht 1 zGen` is nonzero**: it connects (via `connecting`) to the nonzero
`⊤+⊥` class rel `I∖{t}`, and a linear map sends `0 ↦ 0`, so its argument must be nonzero too. -/
theorem restrictBd_zGen_ne_zero {t : ↑ICat} (ht : t ∉ bdI) : restrictBd bdI ht 1 zGen ≠ 0 := by
  intro hz
  refine homIncl_target_ne_zero ht ?_
  rw [← boundaryExtract_bdPathChain_compl ht, ← connectingLift_apply,
    ← connecting_relCycleToHom, ← restrictBd_zGen t ht, hz, map_zero]

/-- **`zGen` is nonzero**: `restrictBd` (a linear map) sends `0 ↦ 0`, so a class with nonzero
image must itself be nonzero. -/
theorem zGen_ne_zero {t : ↑ICat} (ht : t ∉ bdI) : zGen ≠ 0 := by
  intro hz
  exact restrictBd_zGen_ne_zero ht (by rw [hz, map_zero])

/-- **The restriction fact**: the interval pair class `[I,∂I]` restricts to the interior local
generator at every interior point `t ∉ ∂I`. Both `intervalPairClassEquiv` and `intervalLocalGenEquiv`
are `1`-dimensional `ℤ/2`-vector-space isomorphisms, so this reduces (via `eq_symm_one_iff_ne_zero`)
to the chain-level fact that `restrictBd` sends the nonzero chain-witness `zGen` to a nonzero class —
the honest geometric content that "the interval traversed once" restricts to the local generator. -/
theorem intervalPairClass_restricts {t : ↑ICat} (ht : t ∉ bdI) :
    restrictBd bdI ht 1 (intervalPairClassEquiv.symm 1) = (intervalLocalGenEquiv ht).symm 1 := by
  have hzGen : zGen = intervalPairClassEquiv.symm 1 :=
    (eq_symm_one_iff_ne_zero intervalPairClassEquiv).mpr (zGen_ne_zero ht)
  rw [← hzGen]
  exact (eq_symm_one_iff_ne_zero (intervalLocalGenEquiv ht)).mpr (restrictBd_zGen_ne_zero ht)

/-! ## §7. Packaging — the interval local-class datum for the interior local-Künneth consumer -/

/-- **The interval local-class package** at an interior point `t ∉ ∂I`: the local generator
`H₁(I, I∖{t}; ℤ/2) ≅ ℤ/2` together with the proof that the global interval class `[I,∂I]` restricts
to it. This is the reusable shape the interior local-Künneth (the interval factor of `cylGen`,
crossed against `M`'s own local generator) consumes — both facts of this brick, bundled by point. -/
structure IntervalLocalClass (t : ↑ICat) (ht : t ∉ bdI) where
  /-- The interior local-homology iso `H₁(I, I∖{t}; ℤ/2) ≅ ℤ/2`. -/
  gen : RelativeHomology ({t}ᶜ : Set ↑ICat) 1 ≃ₗ[ZMod 2] ZMod 2
  /-- `[I,∂I]` restricts to `gen`'s generator at `t`. -/
  restricts : restrictBd bdI ht 1 (intervalPairClassEquiv.symm 1) = gen.symm 1

/-- **The canonical interval local-class package**, built from `intervalLocalGenEquiv` and
`intervalPairClass_restricts`. -/
noncomputable def intervalLocalClass (t : ↑ICat) (ht : t ∉ bdI) : IntervalLocalClass t ht :=
  ⟨intervalLocalGenEquiv ht, intervalPairClass_restricts ht⟩

end

end SKEFTHawking.SingularIntervalPairClass
