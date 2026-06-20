import Mathlib
import SKEFTHawking.SingularRelativeCohomologyMVConnecting
import SKEFTHawking.SingularCohomologySnake
import SKEFTHawking.SingularMvDeltaPartition
import SKEFTHawking.SingularRelMvDeltaPartition

/-!
# Phase 5q.F (w₂-foundation) — geometric cover-split realization of the cohomology MV connecting map

`SingularRelativeCohomologyMVConnecting.relCohomMvConnecting` is **Kronecker-defined** — the
`dualMap`-conjugate of the homology connecting `relMvDelta` through the perfect Kronecker pairing — so
it carries no explicit chain/cochain representative. Downstream the Poincaré-duality connecting-square
match must compute a cap against `relCohomMvConnecting g`, which is impossible while it is opaque (every
folding-back through the Kronecker dual is circular). This file gives it an **explicit geometric
representative**: the cohomology analogue of the committed homology lemma
`SingularMvDeltaPartition.mvDelta_cover_partition` (which computes `relMvDelta` of a cover-partitioned
cycle as the class of the seam-supported `∂zB`).

The explicit cocycle is `ξ := δφ = coboundary (cochainSplit U ω)`, the relative coboundary of the
**`U`-part of the function-level cover-split** of a representing cocycle `ω` of the source class
(`SingularCohomologySnake.cochainSplit` — subdivision-free, since cochains are functions).

Two forms, both kernel-pure, proved **non-circularly** (the chain-level identity `⟨ξ, c⟩ = ⟨ω, ∂_V c⟩`
is concrete, never routed back through the Kronecker self-reference):

* `relKroneckerH_relCohomMvConnecting_cover_partition` (pairing form, *unconditional*): pairing the
  connecting map against the class of a cover-partitioned cycle `c` (`∂c = u + w`, `u ∈ C(U)`,
  `w ∈ C(V)`) equals the chain-level `⟨δφ, c⟩`.
* `relCohomMvConnecting_eq_mk_coboundary_cochainSplit` (class form): `relCohomMvConnecting (mk ω)` IS the
  `(U∪V)`-class `[δφ]`, given the union-level membership `δφ ∈ relCochains (U∪V)` as a hypothesis. That
  membership is the small-simplices / subdivision content (a `(U∪V)`-chain need not split as `C(U)+C(V)`
  without subdivision; `cochainSplit` lives in `relCochains U ∩ relCochains V`), made explicit rather
  than hidden in the Kronecker dual.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularRelativeMV
  SKEFTHawking.SingularRelativeKroneckerEquiv SKEFTHawking.SingularCohomologySnake
  SKEFTHawking.SingularRelativeUC

namespace SKEFTHawking.SingularRelCohomMvConnectingGeom

variable {M : TopCat}

/-- **chain-level helper**: `⟨δφ, c⟩ = ⟨ω, w⟩` where `φ = cochainSplit U ω` is the `U`-part of the
cover-split of a `U∩V`-cocycle `ω`, and `∂c = u + w` with `u ∈ C(U)`, `w ∈ C(V)`. -/
theorem kronecker_coboundary_cochainSplit_eq (U V : Set ↑M) (N : ℕ)
    (ω : LinearMap.ker (relCoboundaryₗ (U ∩ V) (N + 1)))
    (c : SingularChain M (N + 2)) (u w : SingularChain M (N + 1))
    (hu : u ∈ subspaceChains U (N + 1)) (hw : w ∈ subspaceChains V (N + 1))
    (hbd : chainBoundary M (N + 1) c = u + w) :
    kronecker (coboundary M (N + 1) (cochainSplit U (N + 1) ω.1.1)) c
      = kronecker ω.1.1 w := by
  rw [kronecker_coboundary_chainBoundary, hbd, kronecker_add_right,
    cochainSplit_mem_relCochains U (N + 1) ω.1.1 u hu, zero_add]
  have h2 := cochainSplit_compl_mem_relCochains U V (N + 1) ω.1.1 ω.1.2 w hw
  rw [show (ω.1.1 - cochainSplit U (N + 1) ω.1.1)
      = ω.1.1 + cochainSplit U (N + 1) ω.1.1 from by rw [ZModModule.sub_eq_add],
    kronecker_add_left] at h2
  exact (eq_of_sub_eq_zero (by rw [ZModModule.sub_eq_add]; exact h2)).symm

/-- **Geometric cover-split realization of the cohomology MV connecting map (pairing form)**. The
Kronecker-defined `relCohomMvConnecting`, paired against the class of a cover-partitioned cycle `c`
(`∂c = u + w`, `u ∈ C(U)`, `w ∈ C(V)`), equals the chain-level Kronecker pairing of the EXPLICIT
seam-supported coboundary `δφ` against `c`, where `φ = cochainSplit U ω` is the `U`-part of the
function-level cover-split of a representing cocycle `ω`. This is the cohomology analogue of
`SingularRelMvDeltaPartition.relKroneckerH_relMvDelta_cover_partition`: it transports the abstract
`dualMap`-conjugate connecting map onto a concrete cochain (`δ` of the cover-split), so downstream
cap/cup computations have a representative to work with. -/
theorem relKroneckerH_relCohomMvConnecting_cover_partition (U V : Set ↑M) (hU : IsOpen U)
    (hV : IsOpen V) (N : ℕ) (ω : LinearMap.ker (relCoboundaryₗ (U ∩ V) (N + 1)))
    (c : SingularChain M (N + 1 + 1)) (u w : SingularChain M (N + 1))
    (hu : u ∈ subspaceChains U (N + 1)) (hw : w ∈ subspaceChains V (N + 1))
    (hbd : chainBoundary M (N + 1) c = u + w)
    (hwcyc : RelativeChain.mk (U ∩ V) (N + 1) w ∈ relCycles (U ∩ V) (N + 1))
    (hccyc : RelativeChain.mk (U ∪ V) (N + 1 + 1) c ∈ relCycles (U ∪ V) (N + 1 + 1)) :
    relKroneckerH (U ∪ V)
        (SKEFTHawking.SingularRelativeCohomologyMVConnecting.relCohomMvConnecting U V hU hV N
          (RelativeCohomology.mk (U ∩ V) (N + 1) ω))
        (RelativeHomology.mk (U ∪ V) (N + 1 + 1) ⟨RelativeChain.mk (U ∪ V) (N + 1 + 1) c, hccyc⟩)
      = kronecker (coboundary M (N + 1) (cochainSplit U (N + 1) ω.1.1)) c := by
  rw [SKEFTHawking.SingularRelativeCohomologyMVConnecting.relKroneckerH_relCohomMvConnecting,
    SKEFTHawking.SingularRelMvDeltaPartition.relMvDelta_cover_partition U V hU hV (N + 1) c u w hu hw
      hbd hwcyc, relKroneckerH_mk_mk, relKronecker_mk,
    kronecker_coboundary_cochainSplit_eq U V N ω c u w hu hw hbd]

/-- **Every relative `(U∪V)`-homology class has a cover-partitioned representative.** For `w` open `U, V`,
any `w' : Hₙ₊₁(M, U∪V)` is the class of a chain `c` whose boundary splits cover-subordinately
`∂c = u + w` (`u ∈ C(U)`, `w ∈ C(V)`). The cohomology-side dual of the homology cover-partition setup —
obtained by pulling `w'` back through the small-chains iso `iotaEquiv` to a `Q`-cycle and subdividing. -/
theorem exists_cover_partition_rep (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (N : ℕ)
    (w' : RelativeHomology (U ∪ V) (N + 1 + 1)) :
    ∃ (c : SingularChain M (N + 1 + 1)) (u w : SingularChain M (N + 1))
      (_ : u ∈ subspaceChains U (N + 1)) (_ : w ∈ subspaceChains V (N + 1))
      (_ : chainBoundary M (N + 1) c = u + w)
      (hccyc : RelativeChain.mk (U ∪ V) (N + 1 + 1) c ∈ relCycles (U ∪ V) (N + 1 + 1)),
      w' = RelativeHomology.mk (U ∪ V) (N + 1 + 1)
        ⟨RelativeChain.mk (U ∪ V) (N + 1 + 1) c, hccyc⟩ := by
  obtain ⟨q, rfl⟩ := iota_surjective U V hU hV (N + 1 + 1) w'
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z : QChain U V (N + 1 + 1))
  have hz0 : QChain.mk U V (N + 1) (chainBoundary M (N + 1) c) = 0 := by
    have := LinearMap.mem_ker.mp z.2
    rw [← hc] at this
    rw [← qBoundary_mk]; exact this
  have hbdun : chainBoundary M (N + 1) c ∈ mvUnionChains U V (N + 1) :=
    (QChain.mk_eq_zero_iff U V (N + 1) _).mp hz0
  obtain ⟨u, hu, w, hw, hsum⟩ := Submodule.mem_sup.1 hbdun
  refine ⟨c, u, w, hu, hw, hsum.symm, ?_, ?_⟩
  · rw [show relCycles (U ∪ V) (N + 1 + 1) = LinearMap.ker (relBoundary (U ∪ V) (N + 1)) from rfl,
      LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff]
    exact mvUnionChains_le_subspaceChains_union U V (N + 1) hbdun
  · rw [show (Submodule.Quotient.mk z : QHomology U V (N + 1 + 1)) = QHomology.mk U V (N + 1 + 1) z
      from rfl, iota_mk]
    refine congrArg (RelativeHomology.mk (U ∪ V) (N + 1 + 1)) (Subtype.ext ?_)
    show piMap U V (N + 1 + 1) (z : QChain U V (N + 1 + 1)) = RelativeChain.mk (U ∪ V) (N + 1 + 1) c
    rw [← hc, show (Submodule.Quotient.mk c : QChain U V (N + 1 + 1)) = QChain.mk U V (N + 1 + 1) c
      from rfl, piMap_mk]

/-- **Geometric cover-split realization of the cohomology MV connecting map (class form)**. Given that
the explicit seam-supported coboundary `δφ = δ(cochainSplit U ω)` of the cover-split of a representing
cocycle `ω` is a genuine relative `(U∪V)`-cochain (hypothesis `hmem` — the union-level membership is the
small-simplices/subdivision content the cover-split makes explicit), the Kronecker-defined
`relCohomMvConnecting (mk ω)` IS the relative-cohomology class of that explicit cocycle:
`relCohomMvConnecting (mk ω) = [δφ]_{U∪V}`. The proof is non-circular: by Kronecker non-degeneracy
(`relCohomology_eq_zero_of_relKroneckerH`) the two classes are equal iff they pair equally against every
`(U∪V)`-cycle; every such cycle has a cover-partitioned representative (`exists_cover_partition_rep`), on
which the pairing form `relKroneckerH_relCohomMvConnecting_cover_partition` reduces the connecting map to
the chain-level `⟨δφ, c⟩`. This is the explicit cochain representative the connecting-square cap/cup
computation needs in place of the opaque `Quotient.mk_surjective` rep of `relCohomMvConnecting`. -/
theorem relCohomMvConnecting_eq_mk_coboundary_cochainSplit (U V : Set ↑M) (hU : IsOpen U)
    (hV : IsOpen V) (N : ℕ) (ω : LinearMap.ker (relCoboundaryₗ (U ∩ V) (N + 1)))
    (hmem : coboundary M (N + 1) (cochainSplit U (N + 1) ω.1.1) ∈ relCochains (U ∪ V) (N + 2))
    (hcoc : (⟨coboundary M (N + 1) (cochainSplit U (N + 1) ω.1.1), hmem⟩ : relCochains (U ∪ V) (N + 2))
      ∈ LinearMap.ker (relCoboundaryₗ (U ∪ V) (N + 2))) :
    SKEFTHawking.SingularRelativeCohomologyMVConnecting.relCohomMvConnecting U V hU hV N
        (RelativeCohomology.mk (U ∩ V) (N + 1) ω)
      = RelativeCohomology.mk (U ∪ V) (N + 2)
          ⟨⟨coboundary M (N + 1) (cochainSplit U (N + 1) ω.1.1), hmem⟩, hcoc⟩ := by
  refine sub_eq_zero.mp (relCohomology_eq_zero_of_relKroneckerH (U ∪ V) _ (fun w' => ?_))
  rw [map_sub, LinearMap.sub_apply]
  obtain ⟨c, u, w, hu, hw, hbd, hccyc, rfl⟩ := exists_cover_partition_rep U V hU hV N w'
  have hwcyc : RelativeChain.mk (U ∩ V) (N + 1) w ∈ relCycles (U ∩ V) (N + 1) := by
    rw [show relCycles (U ∩ V) (N + 1) = LinearMap.ker (relBoundary (U ∩ V) N) from rfl,
      LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff]
    -- `∂w = ∂(∂c - u) = ∂u ∈ C(U)`, and `∂w ∈ C(V)`, so `∂w ∈ C(U∩V)`.
    have hwu : chainBoundary M N w = chainBoundary M N u := by
      have h0 : chainBoundary M N (chainBoundary M (N + 1) c) = 0 :=
        chainBoundary_chainBoundary_apply M N c
      rw [hbd, map_add] at h0
      exact eq_of_sub_eq_zero (by rw [ZModModule.sub_eq_add, add_comm]; exact h0)
    rw [← SingularExcision.subspaceChains_inf]
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [hwu]; exact chainBoundary_mem_subspaceChains U N u hu
    · exact chainBoundary_mem_subspaceChains V N w hw
  rw [relKroneckerH_relCohomMvConnecting_cover_partition U V hU hV N ω c u w hu hw hbd hwcyc hccyc,
    relKroneckerH_mk_mk, relKronecker_mk, sub_self]

end SKEFTHawking.SingularRelCohomMvConnectingGeom
