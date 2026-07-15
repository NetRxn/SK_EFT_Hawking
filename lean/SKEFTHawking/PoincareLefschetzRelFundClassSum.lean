/-
# Phase 5q.H (W-A addClosure, layer 3) — the block-sum relative fundamental class over `⊔`

Constructs a concrete `PoincareLefschetzWuBlockAssembly.SumRelFundClass A B S₁ S₂` term — the sole
remaining interface of the disjoint-union `addClosure`. From relative fundamental-class data on each
summand pair `(A, S₁)`, `(B, S₂)`, the block-sum class `[W₁,∂W₁] ⊔ [W₂,∂W₂]` (via the homology
pushforwards `RelativeHomology.map inl/inr`) is a relative fundamental class on the union pair, whose
`μ` is the μ-block sum `⟨inl*·, [W₁,∂W₁]⟩ + ⟨inr*·, [W₂,∂W₂]⟩`.

The two load-bearing algebraic facts:
* **The relative Kronecker adjunction** `⟨ω, f_* α⟩ = ⟨f* ω, α⟩` (`relKroneckerH_relCohomPullback`) —
  the relative analogue of `SingularKroneckerFunctoriality.kroneckerH_Homology_map`, descended from the
  chain-level `SingularCohomologyFunctoriality.kronecker_cochainPullback`.
* **The block-sum μ** (`blockSumCls_mu`) — bilinearity of the pairing + the adjunction give the
  `sumD_mu` identity directly.

The interior local-generation (`gen`/`restricts`) fields of the union datum are supplied by relative
excision at interior points of the sum (`SingularExcisionIso.excisionEquiv`): at `inl a` the local
homology `Hₙ(A⊔B, {inl a}ᶜ) ≅ Hₙ(A, {a}ᶜ)` (the `B`-component is whole, contributing `H(B,B) = 0`),
transporting `D₁.gen a`; symmetrically at `inr b`. The construction carries `[T1Space]` on each
carrier (points closed ⟹ the excision cover condition), discharged from the manifold instances at the
bordism level.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzWuBlockAssembly
import SKEFTHawking.SingularRelativeFunctoriality
import SKEFTHawking.SingularKroneckerFunctoriality
import SKEFTHawking.SingularExcisionIso

namespace SKEFTHawking.PoincareLefschetzRelFundClassSum

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularKroneckerFunctoriality
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularCohomologyDisjointSum
open SKEFTHawking.SingularRelativeCohomologyDisjointSum
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzWuBlockAssembly

/-! ## §1. The relative Kronecker adjunction (naturality of the pairing along a pair map). -/

/-- **Chain-level relative Kronecker adjunction** `⟨f, φ_# w⟩ = ⟨φ* f, w⟩`: the relative pairing of a
relative cochain against the relative-chain pushforward equals the pairing of the relative cochain
pullback against the chain. Descends the absolute `kronecker_cochainPullback`. -/
theorem relKronecker_relMapChain {X Y : TopCat} (φ : C(↑X, ↑Y)) {SX : Set ↑X} {SY : Set ↑Y}
    (hφ : Set.MapsTo φ SX SY) {n : ℕ} (f : relCochains SY n) (w : RelativeChain SX n) :
    relKronecker SY f (relMapChain φ hφ n w) = relKronecker SX (relCochainPullback φ hφ n f) w := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  show relKronecker SY f (RelativeChain.mk SY n (mapChain φ n c))
      = relKronecker SX (relCochainPullback φ hφ n f) (RelativeChain.mk SX n c)
  rw [relKronecker_mk, relKronecker_mk, relCochainPullback_coe, kronecker_cochainPullback]

/-- **The relative Kronecker adjunction** `⟨ω, f_* α⟩_Y = ⟨f* ω, α⟩_X` for a map of pairs
`φ : (X, SX) → (Y, SY)`: pairing a relative cohomology class `ω ∈ Hⁿ(Y, SY)` against the homology
pushforward `f_* α` equals pairing the cohomology pullback `f* ω` against `α`. The relative analogue
of `kroneckerH_Homology_map`; descends the chain-level adjunction `relKronecker_relMapChain`. -/
theorem relKroneckerH_relCohomPullback {X Y : TopCat} (φ : C(↑X, ↑Y)) {SX : Set ↑X} {SY : Set ↑Y}
    (hφ : Set.MapsTo φ SX SY) {N : ℕ} (ω : RelativeCohomology SY (N + 1))
    (α : RelativeHomology SX (N + 1)) :
    relKroneckerH SY ω (RelativeHomology.map φ hφ (N + 1) α)
      = relKroneckerH SX (relCohomPullback φ hφ (N + 1) ω) α := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ ω
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ α
  rw [RelativeHomology.map_mk]
  exact relKronecker_relMapChain φ hφ a.1 z.1

/-! ## §2. The block-sum class and the μ-block-sum (the `sumD_mu` identity). -/

variable {A B : TopCat} {S₁ : Set ↑A} {S₂ : Set ↑B}

/-- **The block-sum relative fundamental class** `[W₁,∂W₁] ⊔ [W₂,∂W₂] ∈ H₅(A⊔B, S₁⊔S₂)`: the sum of
the homology pushforwards of the two summand classes along the disjoint-union inclusions of pairs. -/
noncomputable def blockSumCls (D₁ : RelFundClassDatum (m := 3) S₁)
    (D₂ : RelFundClassDatum (m := 3) S₂) : RelativeHomology (sumSet A B S₁ S₂) 5 :=
  RelativeHomology.map (inlMap A B) (mapsTo_inl A B S₁ S₂) 5 D₁.cls
    + RelativeHomology.map (inrMap A B) (mapsTo_inr A B S₁ S₂) 5 D₂.cls

/-- **The μ of the block sum IS the block sum of the μ's** (`sumD_mu`): the Kronecker functional of the
block-sum class against `z` decomposes as `⟨inl*z, [W₁,∂W₁]⟩ + ⟨inr*z, [W₂,∂W₂]⟩` — bilinearity plus
the relative Kronecker adjunction (`relKroneckerH_relCohomPullback`). -/
theorem blockSumCls_mu (D₁ : RelFundClassDatum (m := 3) S₁) (D₂ : RelFundClassDatum (m := 3) S₂)
    (z : RelativeCohomology (sumSet A B S₁ S₂) 5) :
    relKroneckerH (sumSet A B S₁ S₂) z (blockSumCls D₁ D₂)
      = D₁.mu (relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) 5 z)
        + D₂.mu (relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) 5 z) := by
  rw [blockSumCls, map_add,
    relKroneckerH_relCohomPullback (N := 4) (inlMap A B) (mapsTo_inl A B S₁ S₂),
    relKroneckerH_relCohomPullback (N := 4) (inrMap A B) (mapsTo_inr A B S₁ S₂),
    D₁.mu_apply, D₂.mu_apply]

end SKEFTHawking.PoincareLefschetzRelFundClassSum
