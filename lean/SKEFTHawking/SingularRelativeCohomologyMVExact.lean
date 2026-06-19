import Mathlib
import SKEFTHawking.SingularRelativeCohomologyMV

/-!
# Phase 5q.F (brick 72c-PD5b-exact) — relative cohomology Mayer–Vietoris, the gluing identity

Toward middle exactness of the relative cohomology MV sequence
  `Hᵏ(M|A∪B) --Δ--> Hᵏ(M|A) ⊕ Hᵏ(M|B) --Σ--> Hᵏ(M|A∩B)`.

The cochain-level load-bearing gluing identity for the contravariant MV is the **dual of the
homology MV intersection identity** `subspaceChains A ⊓ subspaceChains B = subspaceChains (A∩B)`.
Over `ℤ/2`, `relCochains S n` is the annihilator of `subspaceChains S n`, so the meet of two
relative-cochain annihilators is the annihilator of the *sum* of the subspace chains
`subspaceChains U + subspaceChains V` (`mvUnionChains U V` from `SingularRelativeMV`): a cochain
vanishing on `U`-chains AND on `V`-chains is exactly a cochain vanishing on `C(U)+C(V)`. This is the
cochain-level "compatible-pair = `Q`-cochain" statement underlying the cohomology MV gluing.

Note the easy inclusion only: `relCochains (U∪V) n ≤ relCochains U n ⊓ relCochains V n`. Equality
FAILS in general (the dual of `mvUnionChains U V n ≤ subspaceChains (U∪V) n`, a strict `≤`); closing
the cohomology gluing to a genuine `Q`-cochain iso requires the contravariant small-simplices /
excision apparatus (the dual of `SingularRelativeMV.iotaEquiv`), a separate multi-brick program.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularMayerVietoris
  SKEFTHawking.SingularRelativeMV

namespace SKEFTHawking.SingularRelativeCohomologyMVExact

variable {M : TopCat}

/-! ## §1. The cochain-level MV gluing identity (dual of `subspaceChains_inf`) -/

/-- **The cochain MV intersection identity** (`ℤ/2`): a cochain lies in both `relCochains U n` and
`relCochains V n` iff it vanishes on the union chains `mvUnionChains U V n = C(U) + C(V)`. The
contravariant dual of the homology MV identity
`subspaceChains U ⊓ subspaceChains V = subspaceChains (U∩V)`: `relCochains S n` is the annihilator
of `subspaceChains S n`, so the meet of two annihilators is the annihilator of the sum. -/
theorem mem_relCochains_inf_iff (U V : Set ↑M) (n : ℕ) (f : SingularCochain M n) :
    f ∈ relCochains U n ⊓ relCochains V n ↔ ∀ c ∈ mvUnionChains U V n, kronecker f c = 0 := by
  rw [Submodule.mem_inf, mem_relCochains, mem_relCochains]
  constructor
  · rintro ⟨hU, hV⟩ c hc
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hc
    rw [kronecker_add_right, hU u hu, hV v hv, add_zero]
  · intro h
    exact ⟨fun c hc => h c (Submodule.mem_sup_left hc),
      fun c hc => h c (Submodule.mem_sup_right hc)⟩

/-- **The meet of relative cochains as the union-chains annihilator** (`ℤ/2`): the carrier set of
`relCochains U n ⊓ relCochains V n` is exactly the cochains vanishing on
`mvUnionChains U V n = C(U) + C(V)`. The set-level restatement of `mem_relCochains_inf_iff`; the
relative-cochain meet is the annihilator of the union chains. -/
theorem relCochains_inf_eq_annihilator (U V : Set ↑M) (n : ℕ) :
    (relCochains U n ⊓ relCochains V n : Set (SingularCochain M n))
      = { f : SingularCochain M n | ∀ c ∈ mvUnionChains U V n, kronecker f c = 0 } := by
  ext f
  exact mem_relCochains_inf_iff U V n f

/-- **The easy MV inclusion on cochains** (`ℤ/2`): a relative cochain on the union `U∪V` restricts
to a relative cochain on each of `U`, `V`, i.e.
`relCochains (U∪V) n ≤ relCochains U n ⊓ relCochains V n`.
The contravariant dual of the (strict, in general) `mvUnionChains U V n ≤ subspaceChains (U∪V) n`
(`SingularRelativeMV.mvUnionChains_le_subspaceChains_union`): a cochain killing the larger
`subspaceChains (U∪V) n` kills the smaller `C(U) + C(V)`. Equality FAILS in general — closing the
cohomology gluing to a `Q`-cochain iso is the dual small-simplices / excision program. -/
theorem relCochains_union_le_inf (U V : Set ↑M) (n : ℕ) :
    relCochains (U ∪ V) n ≤ relCochains U n ⊓ relCochains V n := by
  intro f hf
  rw [mem_relCochains_inf_iff]
  intro c hc
  exact (mem_relCochains (U ∪ V) n f).1 hf c (mvUnionChains_le_subspaceChains_union U V n hc)

end SKEFTHawking.SingularRelativeCohomologyMVExact
