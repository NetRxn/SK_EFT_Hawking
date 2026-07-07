/-
# Phase 5q.H (E1 integral topology) — the small-chains submodule is a basis-subset (`Finsupp.supported`)

Foundation for the cohomology Mayer–Vietoris middle-exactness node `(B)` via the **degreewise-split
SES** route (the `SingularRelativeCohomologyMVInt` docstring's own recommendation), instead of rebuilding
the per-simplex subdivision operator from scratch: the relative-HOMOLOGY MV is already fully built at ℤ
with the honest union end (`SingularRelativeMVInt.relMvInt_exact_middle'`, the small-chains excision iso
`iotaEquivInt`), so the cohomology `(B)` is its DUAL, obtained by dualising the degreewise-split chain SES.

The enabling structural fact: `subspaceChainsInt S n = LinearMap.range (chainIncl S n)` and `chainIncl`
is `Finsupp.mapDomain` along the INJECTIVE `simplexIncl`, so `subspaceChainsInt S n` is exactly the
**coordinate-support** submodule `Finsupp.supported ℤ ℤ {τ | range τ ⊆ S}` — a span of a SUBSET of the
singleton basis. Hence `mvUnionChainsInt = supported (P_U ∪ P_V)` is a basis-subset submodule, a direct
summand of `SingularChainInt`, and the MV chain SES splits degreewise (so `Hom(−,ℤ)` keeps it exact — no
universal-coefficient / torsion issue).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `native_decide`, no `maxHeartbeats`, no axiom.
-/
import Mathlib
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularRelativeMVInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.SingularRelativeMVInt

namespace SKEFTHawking.SingularSmallChainsSplitInt

variable {X : TopCat}

/-- The **support predicate** on singular `n`-simplices of `X`: `τ`'s image lands in `S`. -/
def SmallSimplices (S : Set X) (n : ℕ) :
    Set ((TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :=
  {τ | Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) ⊆ S}

/-- **The subspace chains are a coordinate-support submodule.** `subspaceChainsInt S n =
Finsupp.supported ℤ ℤ {τ | range τ ⊆ S}` — the span of the singleton basis simplices whose image lies in
`S`. Both inclusions are the support characterisation (`range_of_mem_subspaceChainsInt` /
`mem_subspaceChainsInt_of_support`). This exhibits `subspaceChainsInt S n` as a basis-subset submodule. -/
theorem subspaceChainsInt_eq_supported (S : Set X) (n : ℕ) :
    subspaceChainsInt S n = Finsupp.supported ℤ ℤ (SmallSimplices S n) := by
  ext c
  rw [Finsupp.mem_supported]
  constructor
  · intro hc τ hτ
    exact range_of_mem_subspaceChainsInt hc (Finset.mem_coe.mp hτ)
  · intro hc
    exact mem_subspaceChainsInt_of_support (fun τ hτ => hc (Finset.mem_coe.mpr hτ))

/-- **The MV small chains are the basis-subset submodule on `P_U ∪ P_V`.** `mvUnionChainsInt U V n =
Finsupp.supported ℤ ℤ (SmallSimplices U n ∪ SmallSimplices V n)` — `C(U)+C(V)` is spanned by the singleton
basis simplices whose image lies in `U` or in `V`. Immediate from `subspaceChainsInt_eq_supported` and
`Finsupp.supported_union` (`+` on submodules is `⊔`). -/
theorem mvUnionChainsInt_eq_supported (U V : Set X) (n : ℕ) :
    mvUnionChainsInt U V n
      = Finsupp.supported ℤ ℤ (SmallSimplices U n ∪ SmallSimplices V n) := by
  rw [mvUnionChainsInt, Submodule.add_eq_sup, subspaceChainsInt_eq_supported,
    subspaceChainsInt_eq_supported, Finsupp.supported_union]

/-- **A coordinate-support submodule is a direct summand**: `IsCompl (supported s) (supported sᶜ)` —
disjoint (`s ∩ sᶜ = ∅`) and codisjoint (`s ∪ sᶜ = univ`). The building block of every degreewise splitting
below. -/
theorem isCompl_supported_compl {α : Type*} (s : Set α) :
    IsCompl (Finsupp.supported ℤ ℤ s) (Finsupp.supported ℤ ℤ sᶜ) :=
  ⟨Finsupp.disjoint_supported_supported isCompl_compl.disjoint,
    Finsupp.codisjoint_supported_supported isCompl_compl.codisjoint⟩

/-- **The MV chain SES splits degreewise.** `mvUnionChainsInt U V n` is a direct summand of
`SingularChainInt M n`, complemented by the basis-subset submodule on the LARGE simplices
`(P_U ∪ P_V)ᶜ`. This is the field-free, torsion-safe splitting that makes `Hom(−, ℤ)` preserve exactness
of the relative MV chain SES — the enabling input for the cohomology MV middle-exactness `(B)`. -/
theorem isCompl_mvUnionChainsInt (U V : Set X) (n : ℕ) :
    IsCompl (mvUnionChainsInt U V n)
      (Finsupp.supported ℤ ℤ (SmallSimplices U n ∪ SmallSimplices V n)ᶜ) := by
  rw [mvUnionChainsInt_eq_supported]
  exact isCompl_supported_compl _

/-- **The quotient by a coordinate-support submodule is free.** `(α →₀ ℤ) ⧸ supported s ≅ supported sᶜ ≅
(↥sᶜ →₀ ℤ)`, which is a free ℤ-module. The reusable engine behind the freeness of every relative chain
group on a set built from the simplex-support predicate. -/
theorem free_quotient_supported {α : Type*} (s : Set α) :
    Module.Free ℤ ((α →₀ ℤ) ⧸ Finsupp.supported ℤ ℤ s) :=
  Module.Free.of_equiv
    ((Submodule.quotientEquivOfIsCompl _ _ (isCompl_supported_compl s)).trans
      (Finsupp.supportedEquivFinsupp sᶜ)).symm

/-- **`Q_n = C(M)/(C(U)+C(V))` is a free ℤ-module** — the third term of the relative MV chain SES. Since
`Q_n` is free, the SES `0 → K → Q → C(M,U∪V) → 0` (`iotaInt`) splits degreewise, so `Hom(−, ℤ)` keeps it
exact. -/
theorem free_qChain (U V : Set X) (n : ℕ) :
    Module.Free ℤ (SingularChainInt X n ⧸ mvUnionChainsInt U V n) := by
  rw [mvUnionChainsInt_eq_supported]
  exact free_quotient_supported _

/-- **`C(M, U∪V)_n = C(M)/C(U∪V)` is a free ℤ-module** — the base of the relative MV chain SES. Freeness is
exactly what lets the surjection onto it split, making the whole SES degreewise split and its `Hom(−, ℤ)`
dual exact (the torsion-safe input to the cohomology MV middle exactness `(B)`). -/
theorem free_relChainUnion (U V : Set X) (n : ℕ) :
    Module.Free ℤ (RelativeChainInt (U ∪ V) n) := by
  show Module.Free ℤ (SingularChainInt X n ⧸ subspaceChainsInt (U ∪ V) n)
  rw [subspaceChainsInt_eq_supported]
  exact free_quotient_supported _

/-- **`RelativeChainInt S n = C(M)/C(S)` is a free ℤ-module for ANY `S`** — the arbitrary-set
generalization of `free_relChainUnion` (both are the same coordinate-support quotient
`subspaceChainsInt_eq_supported`). The foundation of the boundary/homology freeness story: relative
chains on any subspace are free, so their submodules are submodules of a free ℤ-module. -/
theorem free_relChainInt (S : Set X) (n : ℕ) :
    Module.Free ℤ (RelativeChainInt S n) := by
  show Module.Free ℤ (SingularChainInt X n ⧸ subspaceChainsInt S n)
  rw [subspaceChainsInt_eq_supported]
  exact free_quotient_supported _

end SKEFTHawking.SingularSmallChainsSplitInt
