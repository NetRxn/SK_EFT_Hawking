/-
# Phase 5q.H close-out — THE CAPSTONE `hasClass` ATOM REDUCED to a two-piece partition-detection row

The deepest atom of the `CapstoneAmbientSupply` row (`PinPlusTraceCapstoneInhabit.lean`) is the trace
`[W,∂W]` existence witness

  `hasClass : HasRelFundClass (∂W) (interiorGenFamily … εtrace)`

on the CONSTRUCTED capstone carrier `W = (ktHandleAttachment …).carrier`. That carrier is a genuine
two-piece union `W = range fromCyl ∪ range fromHandle` (`HandleAttachment`,
`SingularSurgeryFoundation.lean`), the two pieces overlapping exactly on the glued seam `S` (the collar,
`range_fromCyl_inter_range_fromHandle`) — a COLLAR-overlap union, NOT a clopen partition.

**The reduction (§1 — the clopen-free binary partition assembly).** The disjoint-union engine's
sum-assembly `hasRelFundClass_of_clopen_split` (`SingularRelativeDisjointUnionFundClass.lean`) carries a
`_hU : IsClopen U` hypothesis that its proof never uses: the off-piece vanishing
`restrictBd_excisionMap_eq_zero` (`SingularRelativeDisjointUnionLocal.lean`) needs only `x ∉ B`, and the
two-way detection splits on the tautological partition `x ∈ U ∨ x ∈ Uᶜ`. Dropping the unused hypothesis
gives `hasRelFundClass_of_partition`: for ANY set `U ⊆ X`, a class detecting the interior generator on
`U` plus one detecting it on `Uᶜ` assemble to `HasRelFundClass`. This is exactly the collar-overlap form
— choose `U` = the closed cyl-range and `Uᶜ` = the open handle-minus-seam, and the seam (which lies in
`U`) is detected by the cyl side. No clopen/open hypothesis on the pieces; the partition `{U, Uᶜ}` is
automatic.

**The capstone supplier (§2).** `capstone_hasClass_of_partition` fires the folded brick at
`X := TopCat.of W`, `S := ∂W`, `gen := interiorGenFamily … εtrace`, `m := 3` — supplying the
`CapstoneAmbientSupply.hasClass` field from a set `U ⊆ W` and the two per-piece detection facts (folded
`RestrictsToRelGenOn`, the whnf-guarded form the concrete `ModelWithCorners.boundary` requires). So the
single-existence atom `hasClass` visibly shrinks to a transparent partition-detection row: the
cyl-side class + its detection on `U`, the handle-side class + its detection on `Uᶜ`. Neither residual is
a completeness Prop — each is an honest per-piece relative-generator detection (B's cylinder-like class,
Ha's `D⁵`-model local computation), the genuine geometric content of the relative Hatcher-3.27(b) MV
existence obligation. `CapstoneRelFundPartitionDatum` bundles the row; `.toHasClass` assembles it.

**Fences.** THE COLLAR FORK is respected: no general collar theorem is invoked — the two-piece union is
the constructed handle-attachment's own `range fromCyl`/`range fromHandle` decomposition, carried by
construction. `εtrace` is the canonical `finAddEquivProd` (no basis gauge). The interior generators are
the canonically-constructed `interiorGenFamily`, never a free basis.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularSurgeryTraceCapstone
import SKEFTHawking.PinPlusTraceRelFundReduce
import SKEFTHawking.PinPlusTraceCapstoneInhabit
import SKEFTHawking.SingularRelativeDisjointUnionFundClass
import SKEFTHawking.SingularRelativeDisjointUnionDetect

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.SingularRelativeDisjointUnionLocal
open SKEFTHawking.SingularRelativeDisjointUnionFundClass
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusTraceCapstoneInhabit

namespace SKEFTHawking.PinPlusTraceCapstoneRelFund

noncomputable section

/-! ## §1. The clopen-free binary partition assembly (general carrier-agnostic brick). -/

variable {X : TopCat}

/-- **The binary partition assembly of a relative fundamental class — CLOPEN-FREE.** For ANY set
`U ⊆ X` and subspace `S`, a class `αU` detecting the interior generator on `U` plus a class `αUc`
detecting it on `Uᶜ` (each phrased over the ambient via `excisionMap`) assemble to `HasRelFundClass S
gen`: the sum `excisionMap S U αU + excisionMap S Uᶜ αUc` restricts to the generator at every interior
point, because at `x ∈ U` the `Uᶜ`-summand dies (`restrictBd_excisionMap_eq_zero`, which needs only
`x ∉ Uᶜ`) and symmetrically at `x ∈ Uᶜ`. This is `hasRelFundClass_of_clopen_split` with its unused
`IsClopen U` hypothesis dropped — the assembly rests on the tautological partition `x ∈ U ∨ x ∈ Uᶜ`, not
on clopen-ness, so it applies to a COLLAR-overlap union where the geometric pieces are merely closed. -/
theorem hasRelFundClass_of_partition {m : ℕ} (U : Set ↑X) (S : Set ↑X)
    (gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2))
    (αU : RelativeHomology (restr S U) (m + 2))
    (αUc : RelativeHomology (restr S Uᶜ) (m + 2))
    (hdetU : ∀ (x : ↑X) (hx : x ∉ S), x ∈ U →
      restrictBd S hx (m + 2) (excisionMap S U (m + 2) αU) = (gen x hx).symm 1)
    (hdetUc : ∀ (x : ↑X) (hx : x ∉ S), x ∈ Uᶜ →
      restrictBd S hx (m + 2) (excisionMap S Uᶜ (m + 2) αUc) = (gen x hx).symm 1) :
    HasRelFundClass S gen := by
  refine ⟨excisionMap S U (m + 2) αU + excisionMap S Uᶜ (m + 2) αUc, ?_⟩
  intro x hx
  by_cases hxU : x ∈ U
  · rw [map_add, restrictBd_excisionMap_eq_zero hx (by simpa using hxU) (m + 2) αUc, add_zero]
    exact hdetU x hx hxU
  · rw [map_add, restrictBd_excisionMap_eq_zero hx hxU (m + 2) αU, zero_add]
    exact hdetUc x hx hxU

/-- **The binary partition assembly, folded form.** Identical to `hasRelFundClass_of_partition` with the
two per-piece detection hypotheses packaged as folded `RestrictsToRelGenOn` predicates — the whnf-guarded
statement the concrete `ModelWithCorners.boundary` of the trace carrier requires (the same wall
`hasRelFundClass_of_clopen_split_folded` guards against). -/
theorem hasRelFundClass_of_partition_folded {m : ℕ} (U : Set ↑X) (S : Set ↑X)
    (gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2))
    (αU : RelativeHomology (restr S U) (m + 2))
    (αUc : RelativeHomology (restr S Uᶜ) (m + 2))
    (hdetU : RestrictsToRelGenOn S gen (· ∈ U) (excisionMap S U (m + 2) αU))
    (hdetUc : RestrictsToRelGenOn S gen (· ∈ Uᶜ) (excisionMap S Uᶜ (m + 2) αUc)) :
    HasRelFundClass S gen :=
  hasRelFundClass_of_partition U S gen αU αUc hdetU hdetUc

end

/-! ## §2. The capstone `hasClass` supplier — the deepest atom reduced to a two-piece detection row. -/

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-- **The capstone `hasClass` per-atom supplier.** Fires the folded clopen-free binary assembly at
`X := TopCat.of W`, `S := ∂W`, `gen := interiorGenFamily … εtrace`, `m := 3` — producing the exact
`CapstoneAmbientSupply.hasClass` field (equivalently the `hasClass` argument of
`TraceRelFundLeaves.ofCapstone`) from a set `U ⊆ W` and the two folded per-piece detection facts. On the
CONSTRUCTED capstone `W = range fromCyl ∪ range fromHandle`, the intended instantiation is `U` = the
closed cyl-range (`fromCyl` image) with `Uᶜ` the open handle-minus-seam: the seam lies in `U`, detected
by the cyl side. Neither `hdetU` nor `hdetUc` is a completeness Prop — each is an honest per-piece
relative-generator detection (the cyl-side cylinder-like class on `U`, the `D⁵`-model local computation
on `Uᶜ`), the genuine geometric content of the relative Hatcher-3.27(b) MV existence obligation. The
detection facts are FOLDED (`RestrictsToRelGenOn`), the whnf-guarded form the concrete
`ModelWithCorners.boundary` of the trace carrier requires; the body infers `S`/`gen` from those
hypotheses' types (never re-elaborating the sealed heavy `capstoneB` term). -/
def capstone_hasClass_of_partition
    (U : Set ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W))
    (αU : RelativeHomology
        (restr (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) U) (3 + 2))
    (αUc : RelativeHomology
        (restr (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) Uᶜ) (3 + 2))
    (hdetU : letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
      RestrictsToRelGenOn (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (m := 3)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          ((𝓡 4).prod (𝓡∂ 1)) εtrace) (· ∈ U)
        (excisionMap
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) U (3 + 2) αU))
    (hdetUc : letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
      RestrictsToRelGenOn (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W) (m := 3)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          ((𝓡 4).prod (𝓡∂ 1)) εtrace) (· ∈ Uᶜ)
        (excisionMap
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) Uᶜ (3 + 2) αUc)) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
  hasRelFundClass_of_partition_folded U _ _ αU αUc hdetU hdetUc

end

end SKEFTHawking.PinPlusTraceCapstoneRelFund
