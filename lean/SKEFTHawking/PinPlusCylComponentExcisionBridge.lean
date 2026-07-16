import Mathlib
import SKEFTHawking.PinPlusCylComponentHomeo
import SKEFTHawking.PinPlusCylComponentManifold
import SKEFTHawking.SingularRelativeDisjointUnionDetect
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU

/-!
# Phase 5q.H — THE EXCISION BRIDGE: per-component detection from the CONNECTED class (route (b))

The keystone the #137 wall-isolation report reduced the disconnected `D` field to: the
sub-cylinder→ambient open-embedding excision bridge. For a clopen component `C ⊆ M` (charted, closed,
nonempty, **connected**) the CONNECTED cylinder engine supplies a relative fundamental class `μ_C` on
`cylW ↥C` that restricts to the interior generator at every interior point
(`…CrossLocalAlphaU.hasRelFundClass_cylGen`, valid because `↥C` is preconnected). We transport `μ_C`
back to the ambient piece `U = C ×ˢ univ ⊆ cylW M` through the piece homeomorphism `pieceHomeo`
(`↥U ≃ₜ cylW ↥C`), obtaining `αU`, and show that `αU`'s INTRINSIC local restriction inside `sub U` is
nonzero at every interior point of `U`.

Combined with `SingularRelativeDisjointUnionDetect.restrictsToRelGenOn_of_relIncl_ne_zero` (which needs
only a nonzero intrinsic restriction, the `ℤ/2` local-homology uniqueness absorbing any generator
mismatch), this yields the per-piece detection witness `RestrictsToRelGenOn` that the disconnected
engine consumer `cylinderRelFundClassDatum_of_clopenSplit` requires — with NO homeomorphism-transport
of the Lefschetz–Wu datum (the standing wall), only the transport of a single relative homology class
and the naturality of local restriction under a pair map (`relIncl_map`).

The transport nonzero-ness is pure naturality: `relIncl (…) αU = RelativeHomology.map e.symm
(restrictBd (∂cylW ↥C) μ_C)`, the connected restriction `restrictBd … μ_C = (cylGen …).symm 1 ≠ 0`,
and `RelativeHomology.map` of a homeomorphism is injective (`map_bijective_of_comp_id`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.SingularRelativeExcisionRestrict
open SKEFTHawking.SingularRelativeDisjointUnionFundClass
open SKEFTHawking.SingularRelativeDisjointUnionDetect
open SKEFTHawking.PinPlusCylComponentHomeo

namespace SKEFTHawking.PinPlusCylComponentExcisionBridge

noncomputable section

variable {m' : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-! ## §1. The boundary is governed by the interval coordinate (routed through `cyl_boundary_eq`). -/

/-- **The cylinder boundary membership is the interval-endpoint condition** (any charted base). Via
`cyl_boundary_eq` (`∂ = univ ×ˢ {⊥,⊤}`); NO unfolding of the concrete `ModelWithCorners.boundary`.
Reused at both `M` and the component base `↥C`. -/
theorem mem_cylBoundary_iff (p : cylW M) :
    p ∈ (cylModel m').boundary (cylW M) ↔ p.2 ∈ ({⊥, ⊤} : Set (Set.Icc (0 : ℝ) 1)) := by
  rw [cyl_boundary_eq]
  simp [Set.mem_prod]

/-! ## §2. The per-component detection witness via the transported connected class. -/

/-- **The boundary correspondence**: `(pieceHomeo C).symm` maps `∂(cylW ↥C)` into `restr S U`
(`U = C ×ˢ univ`, `S = ∂(cylW M)`). Both boundaries are the interval-endpoint condition
(`mem_cylBoundary_iff`), and the homeo preserves the interval coordinate (`pieceHomeo_symm_apply`). -/
theorem boundary_mapsTo (C : Set M) [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) ↥C] :
    Set.MapsTo (pieceHomeo C).symm ((cylModel m').boundary (cylW ↥C))
      (restr (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))
        (C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)))) := by
  intro q hq
  rw [mem_cylBoundary_iff] at hq
  rw [restr, Set.mem_preimage]
  rw [mem_cylBoundary_iff]
  exact hq

/-- **The image of a `ℤ/2`-generator under an INJECTIVE relative-homology pushforward is nonzero**
(whnf-safe, generator-agnostic). For a pair map `φ` inducing an injective `RelativeHomology.map` and
ANY local iso `E : Hₙ(X, A) ≅ ℤ/2`, `map φ (E.symm 1)` is nonzero (`E.symm 1 ≠ 0` since `1 ≠ 0`). The
abstract `E` is supplied by goal-directed unification, so the sealed `cylGen` is never unfolded. -/
theorem map_symm_one_ne_zero {X Y : TopCat} (φ : C(↑X, ↑Y)) {A : Set ↑X} {B : Set ↑Y}
    (hφ : Set.MapsTo φ A B) (n : ℕ) (hinj : Function.Injective (RelativeHomology.map φ hφ n))
    (E : RelativeHomology A n ≃ₗ[ZMod 2] ZMod 2) :
    RelativeHomology.map φ hφ n (E.symm 1) ≠ 0 := fun h =>
  one_ne_zero (E.symm.injective ((hinj (h.trans (map_zero _).symm)).trans (map_zero _).symm))

/-- The forward piece pair map `cylW ↥C → sub U` (the `pieceHomeo.symm` direction), **explicitly typed
over the TopCat coercions** so its `X = TopCat.of (cylW ↥C)`, `Y = sub U` are pinned — the ascription
that bridges the raw-subtype homeo into `RelativeHomology.map` (as `chartStagePairEquiv` does) and
avoids the `↑(TopCat.of ·)`-inversion whnf. -/
def pieceFwd (C : Set M) :
    C(↑(TopCat.of (cylW ↥C)),
      ↑(sub (X := TopCat.of (cylW M)) (C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1))))) :=
  ⟨(pieceHomeo C).symm, (pieceHomeo C).symm.continuous⟩

/-- The backward piece pair map `sub U → cylW ↥C` (the `pieceHomeo` direction), the left inverse of
`pieceFwd` used for injectivity. -/
def pieceBwd (C : Set M) :
    C(↑(sub (X := TopCat.of (cylW M)) (C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)))),
      ↑(TopCat.of (cylW ↥C))) :=
  ⟨pieceHomeo C, (pieceHomeo C).continuous⟩

variable [T2Space M] [CompactSpace M]

/-- **THE EXCISION BRIDGE — per-component detection.** For a clopen, nonempty, **connected** piece
`C ⊆ M`, the ambient cylinder piece `U = C ×ˢ univ` carries a class `αU` (the transport of the
connected class `μ_C` of `cylW ↥C` through `pieceHomeo`) whose excision `excisionMap S U αU` detects
the interior generator on `U` — the folded `RestrictsToRelGenOn` witness the disconnected engine
consumer needs. -/
theorem restrictsToRelGenOn_component [T1Space (cylW M)]
    (C : Set M) (hC : IsClopen C) [Nonempty ↥C] [PreconnectedSpace ↥C] [T1Space (cylW ↥C)] :
    ∃ αU : RelativeHomology
        (restr (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))
          (C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)))) (m' + 1 + 2),
      RestrictsToRelGenOn (X := TopCat.of (cylW M)) (m := m' + 1)
        ((cylModel m').boundary (cylW M)) (cylGen (M := M) (m' := m'))
        (· ∈ (C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)) : Set ↑(TopCat.of (cylW M))))
        (excisionMap (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))
          (C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1))) (m' + 1 + 2) αU) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) ↥C :=
    TopologicalSpace.Opens.instChartedSpace ⟨C, hC.isOpen⟩
  haveI : CompactSpace ↥C := isCompact_iff_compactSpace.mp hC.isClosed.isCompact
  obtain ⟨μC, hμC⟩ :=
    SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU.hasRelFundClass_cylGen
      (M := ↥C) (m' := m')
  -- the transported class `αU` (over the pinned pair map `pieceFwd`)
  refine ⟨RelativeHomology.map (pieceFwd C) (boundary_mapsTo C) (m' + 1 + 2) μC, ?_⟩
  apply restrictsToRelGenOn_of_relIncl_ne_zero (hC.isOpen.prod isOpen_univ)
  intro x hx hxU
  -- the corresponding interior point `y = pieceHomeo C ⟨x, hxU⟩` of `cylW ↥C`
  set y : cylW ↥C := pieceHomeo C ⟨x, hxU⟩ with hy_def
  have hy : y ∉ (cylModel m').boundary (cylW ↥C) := by
    rw [mem_cylBoundary_iff]; rw [mem_cylBoundary_iff] at hx; exact hx
  -- the local pair map maps `{y}ᶜ` into `restr {x}ᶜ U` (homeo bijectivity)
  have hφT : Set.MapsTo (pieceHomeo C).symm ({y}ᶜ : Set (cylW ↥C))
      (restr (X := TopCat.of (cylW M)) ({x}ᶜ)
        (C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)))) := by
    intro q hq
    rw [restr, Set.mem_preimage, Set.mem_compl_singleton_iff]
    intro hcontra
    have h1 : (pieceHomeo C).symm q = ⟨x, hxU⟩ := Subtype.ext hcontra
    exact hq (Set.mem_singleton_iff.mpr
      (by rw [hy_def, ← h1, (pieceHomeo C).apply_symm_apply]))
  -- the reverse local map, for injectivity of the forward transport
  have hφTinv : Set.MapsTo (pieceHomeo C) (restr (X := TopCat.of (cylW M)) ({x}ᶜ)
        (C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)))) ({y}ᶜ : Set (cylW ↥C)) := by
    intro p hp
    rw [restr, Set.mem_preimage, Set.mem_compl_singleton_iff] at hp
    rw [Set.mem_compl_singleton_iff]
    intro hcontra
    apply hp
    have h1 : p = (pieceHomeo C).symm y := by rw [← hcontra, (pieceHomeo C).symm_apply_apply]
    rw [h1, hy_def, (pieceHomeo C).symm_apply_apply]
  -- naturality: `relIncl (…) αU = map (pieceFwd C) hφT (restrictBd ∂ hy μC)`
  rw [← relIncl_map (pieceFwd C)
      (Set.subset_compl_singleton_iff.mpr hy) (boundary_mapsTo C) hφT
      (restr_mono _ (Set.subset_compl_singleton_iff.mpr hx)) (m' + 1 + 2) μC]
  -- `pieceFwd` is injective (`pieceBwd` is a left inverse via the homeo comp-identities)
  have hinj := (RelativeHomology.map_bijective_of_comp_id (pieceFwd C) (pieceBwd C) hφT hφTinv
    (ContinuousMap.ext fun z => (pieceHomeo C).apply_symm_apply z)
    (ContinuousMap.ext fun z => (pieceHomeo C).symm_apply_apply z) (m' + 1 + 2)).1
  -- the connected restriction is `(cylGen …).symm 1`; its transport is nonzero (injective).
  -- Unfold `restrictBd` in `hμC y hy` (never re-mentioning the sealed `cylGen`) so `rw` matches the
  -- `relIncl` form `relIncl_map` produced — avoiding the whnf explosion of re-elaborating `cylGen`.
  have hval := hμC y hy
  simp only [restrictBd] at hval
  rw [hval]
  exact map_symm_one_ne_zero (pieceFwd C) hφT (m' + 1 + 2) hinj _

end

end SKEFTHawking.PinPlusCylComponentExcisionBridge
