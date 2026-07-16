import Mathlib
import SKEFTHawking.SingularRelativeCoverMV

/-!
# Phase 5q.H — THE COVER-MV TRANSPORT LAYER (discharging the glue detections from piece engines)

The relative cover-MV glue (`SingularRelativeCoverMV.lean`) reduces the connected `[W,∂W]` existence
witness to per-zone local nonvanishing facts about concrete chains. This module supplies the generic
machinery that discharges those facts from the PIECE engines (the cylinder engine's classes, the
handle model, the collar product chain):

* `exists_relClassOf_rep` — every relative homology class is the class of an almost-cycle chain, so
  a piece engine's abstract class (e.g. `hasRelFundClass_cylGen`'s witness) yields a concrete
  representative CHAIN to feed the glue datum;
* `relClassOf_rep_ne_zero_of_restrictsToRelGen` — a representative chain of a class restricting to
  the interior generators has NONZERO local class at every interior point (the producer of the
  glue's per-zone detection inputs on the piece's own carrier);
* `relMap_relClassOf` + `relClassOf_map_ne_zero_of_comp_id` — `relClassOf` is natural in continuous
  pair-maps, and nonvanishing transports across a pair-homeomorphism (e.g. the closed embedding
  `fromCyl : M × I ≃ₜ range fromCyl` of the capstone's cylinder core);
* `mem_interior_left_of_cover` — a point off one closed core is interior to the other (the interior
  hypothesis of the excision bridge `relClassOf_chainIncl_ne_zero_of_interior` is free on a
  two-closed-core cover).

Together with the excision bridge these give the full discharge chain: piece class → representative
chain → intrinsic nonvanishing at interior points → transported across the piece embedding →
ambient local nonvanishing = the glue's `hdet` fields. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no `native_decide`, no
`maxHeartbeats`.
-/

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SingularRelativeCoverMV

namespace SKEFTHawking.SingularRelativeCoverMVTransport

variable {X : TopCat}

/-! ## §1. Representation — every class is the class of an almost-cycle chain -/

/-- **Every relative homology class is a `relClassOf`**: choosing a cycle representative and then a
chain representative exhibits any `α ∈ H_{m+2}(X, S)` as the class of an absolute chain with
`S`-small boundary. The producer of concrete chains from a piece engine's abstract class. -/
theorem exists_relClassOf_rep (S : Set ↑X) (m : ℕ) (α : RelativeHomology S (m + 2)) :
    ∃ (c : SingularChain X (m + 2))
      (hc : chainBoundary X (m + 1) c ∈ subspaceChains S (m + 1)),
      α = relClassOf S m c hc := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ α
  obtain ⟨c, hcz⟩ := Submodule.Quotient.mk_surjective _ (z : RelativeChain S (m + 2))
  replace hcz : RelativeChain.mk S (m + 2) c = (z : RelativeChain S (m + 2)) := hcz
  have hz0 : relBoundary S (m + 1) (z : RelativeChain S (m + 2)) = 0 := LinearMap.mem_ker.mp z.2
  have hc : chainBoundary X (m + 1) c ∈ subspaceChains S (m + 1) := by
    rw [← RelativeChain.mk_eq_zero_iff, ← relBoundary_mk, hcz, hz0]
  refine ⟨c, hc, ?_⟩
  show Submodule.Quotient.mk z = RelativeHomology.mk S (m + 2) (relCycleOf S m c hc)
  exact congrArg Submodule.Quotient.mk (Subtype.ext hcz.symm)

/-! ## §2. The detection producer — a generator-restricting class detects through its chain -/

/-- **The generator is nonzero**: a class restricting to the interior generator has nonzero local
restriction at every interior point (`(gen x hx).symm 1 ≠ 0` since `gen` is an iso and `1 ≠ 0`). -/
theorem restrictBd_ne_zero_of_restrictsToRelGen {S : Set ↑X} {m : ℕ}
    {gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2)}
    {α : RelativeHomology S (m + 2)} (hα : RestrictsToRelGen S gen α)
    (x : ↑X) (hx : x ∉ S) : restrictBd S hx (m + 2) α ≠ 0 := by
  rw [hα x hx]
  intro h0
  have h1 := congrArg (gen x hx) h0
  rw [LinearEquiv.apply_symm_apply, map_zero] at h1
  exact one_ne_zero h1

/-- **A fundamental-class representative chain detects at every interior point**: if the class of
`c` restricts to the interior generators, then the LOCAL class of the chain `c` itself is nonzero at
every `x ∉ S`. This is the producer of the glue's per-zone detection inputs on the piece's own
carrier (e.g. the cylinder engine's class through a chosen representative). -/
theorem relClassOf_rep_ne_zero_of_restrictsToRelGen {S : Set ↑X} {m : ℕ}
    {gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2)}
    (c : SingularChain X (m + 2))
    (hc : chainBoundary X (m + 1) c ∈ subspaceChains S (m + 1))
    (hα : RestrictsToRelGen S gen (relClassOf S m c hc)) (x : ↑X) (hx : x ∉ S) :
    relClassOf ({x}ᶜ) m c
      (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) hc) ≠ 0 := by
  rw [← restrictBd_relClassOf S hx m c hc]
  exact restrictBd_ne_zero_of_restrictsToRelGen hα x hx

/-! ## §3. Naturality and homeomorphism transport of almost-cycle classes -/

/-- **`relClassOf` is natural in continuous pair-maps**: the pushforward of the class of `c` is the
class of the pushed chain `mapChain f c`. -/
theorem relMap_relClassOf {Y : TopCat} (f : C(↑X, ↑Y)) {A : Set ↑X} {B : Set ↑Y}
    (hAB : Set.MapsTo f A B) (m : ℕ) (c : SingularChain X (m + 2))
    (hc : chainBoundary X (m + 1) c ∈ subspaceChains A (m + 1)) :
    RelativeHomology.map f hAB (m + 2) (relClassOf A m c hc)
      = relClassOf B m (mapChain f (m + 2) c)
          (by
            rw [chainBoundary_mapChain]
            exact mapChain_mem_subspaceChains f hAB (m + 1) _ hc) := by
  rw [relClassOf, relClassOf,
    show RelativeHomology.mk A (m + 2) (relCycleOf A m c hc)
      = Submodule.Quotient.mk (relCycleOf A m c hc) from rfl,
    RelativeHomology.map_mk]
  rfl

/-- **Nonvanishing of an almost-cycle class transports across a pair-homeomorphism**: for a
two-sided pair-inverse `(f, g)` (e.g. a piece embedding onto its range with its inverse), the class
of the pushed chain is nonzero whenever the intrinsic class is. -/
theorem relClassOf_map_ne_zero_of_comp_id {Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    {A : Set ↑X} {B : Set ↑Y} (hAB : Set.MapsTo f A B) (hBA : Set.MapsTo g B A)
    (hgf : g.comp f = ContinuousMap.id ↑X) (hfg : f.comp g = ContinuousMap.id ↑Y)
    (m : ℕ) (c : SingularChain X (m + 2))
    (hc : chainBoundary X (m + 1) c ∈ subspaceChains A (m + 1))
    (hne : relClassOf A m c hc ≠ 0) :
    relClassOf B m (mapChain f (m + 2) c)
      (by
        rw [chainBoundary_mapChain]
        exact mapChain_mem_subspaceChains f hAB (m + 1) _ hc) ≠ 0 := by
  rw [← relMap_relClassOf f hAB m c hc]
  intro h0
  exact hne
    ((RelativeHomology.map_bijective_of_comp_id f g hAB hBA hgf hfg (m + 2)).injective
      (h0.trans (map_zero (RelativeHomology.map f hAB (m + 2))).symm))

/-! ## §4. The interior hypothesis is free on a two-closed-core cover -/

/-- **A point off one closed core is interior to the other**: on a cover `CA ∪ CB = X` with `CB`
closed, `x ∉ CB` gives `x ∈ interior CA` (the open `CBᶜ` sits inside `CA`). The interior hypothesis
of the excision bridge `relClassOf_chainIncl_ne_zero_of_interior`, free on the glue's cores. -/
theorem mem_interior_left_of_cover {CA CB : Set ↑X} (hcover : ∀ y : ↑X, y ∈ CA ∨ y ∈ CB)
    (hCB : IsClosed CB) {x : ↑X} (hxB : x ∉ CB) : x ∈ interior CA :=
  interior_maximal (fun y hy => (hcover y).resolve_right hy) hCB.isOpen_compl hxB

end SKEFTHawking.SingularRelativeCoverMVTransport
