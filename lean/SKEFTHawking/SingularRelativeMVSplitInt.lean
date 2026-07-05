/-
# Phase 5q.H (E1 integral topology) — the relative-homology MV chain SES SPLITS (integral)

The on-main relative-homology MV chain SES
  `0 → RC(U∩V) →^Diag RC(U)⊕RC(V) →^Sum QChainInt → 0`
(with third term `QChainInt U V n = C(M) / (C(U)+C(V))`; `relMvChainDiagInt_injective` +
`relMvChain_exactInt` + `relMvChainSumInt_surjective`) **SPLITS**, because `QChainInt` is PROJECTIVE — it
is a coordinate quotient (`mvUnionChainsInt = supported(range simplexInclU ∪ range simplexInclV)`), so
`supported_quotient_projective` applies. A section `σ` of `Sum` is obtained by lifting `id` through it
(`Module.projective_lifting_property`).

This is the field-UC-free enabler for the relative-cohomology Mayer–Vietoris exactness over ℤ: a SPLIT
chain SES stays exact under `Hom(−, ℤ)`, dualizing to the relative-cohomology MV — no UCT, no finrank, no
torsion (the mod-2 route needs ℤ/2 a field).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularRelativeMVInt
import SKEFTHawking.SingularChainQuotientProjectiveInt

open Opposite
open SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeMVInt SKEFTHawking.SingularChainQuotientProjectiveInt
open SKEFTHawking.SingularRelativeHomologyMod2 (simplexIncl)

namespace SKEFTHawking.SingularRelativeMVSplitInt

variable {M : TopCat}

/-- The integral subspace chains are a `Finsupp.supported` (coordinate) submodule:
`subspaceChainsInt S n = supported(range simplexIncl)`. -/
theorem subspaceChainsInt_eq_supported (S : Set ↑M) (n : ℕ) :
    subspaceChainsInt S n = Finsupp.supported ℤ ℤ (Set.range (simplexIncl S n)) := by
  rw [subspaceChainsInt, show chainIncl S n = Finsupp.lmapDomain ℤ ℤ (simplexIncl S n) from rfl,
    Finsupp.range_lmapDomain, Finsupp.supported_eq_span_single, ← Set.range_comp]
  rfl

/-- **The MV third term `QChainInt = C/(C(U)+C(V))` is projective** (a coordinate quotient). -/
theorem qChainInt_projective (U V : Set ↑M) (n : ℕ) :
    Module.Projective ℤ (QChainInt U V n) := by
  refine supported_quotient_projective n
    (Set.range (simplexIncl U n) ∪ Set.range (simplexIncl V n)) (mvUnionChainsInt U V n) ?_
  rw [mvUnionChainsInt, subspaceChainsInt_eq_supported, subspaceChainsInt_eq_supported,
    Submodule.add_eq_sup, ← Finsupp.supported_union]

/-- **The MV chain-`Sum` map has a section** (the SES splits): a linear `σ : QChainInt → RC(U)⊕RC(V)`
with `Sum ∘ σ = id`, from the projectivity of `QChainInt` lifting `id` through the surjection `Sum`. -/
theorem relMvChainSumInt_split (U V : Set ↑M) (n : ℕ) :
    ∃ σ : QChainInt U V n →ₗ[ℤ] (RelativeChainInt U n × RelativeChainInt V n),
      (relMvChainSumInt U V n).comp σ = LinearMap.id := by
  haveI := qChainInt_projective U V n
  exact Module.projective_lifting_property (relMvChainSumInt U V n) LinearMap.id
    (relMvChainSumInt_surjective U V n)

end SKEFTHawking.SingularRelativeMVSplitInt
