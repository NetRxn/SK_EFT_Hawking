import Mathlib
import SKEFTHawking.SingularLocalDualityK
import SKEFTHawking.SingularCapChainIncl
import SKEFTHawking.SingularRelativePairing
import SKEFTHawking.SingularRightCapBoundary
import SKEFTHawking.SingularExcisionIso

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6f-c2) — the duality chain is a genuine `sub K`-cap

`pullbackDualityₗ S K z hzK a` (the `sub K`-chain whose `chainIncl` is the absolute cap `a.1.1 ⌢ z`) is
**literally the `sub K`-cap** `(pullbackCochain K a.1.1) ⌢ z_sub` of the pulled-back cochain with the
`sub K`-representative `z_sub = (subspaceChainsEquiv K).symm ⟨z, hzK⟩` of the `K`-supported cycle `z`. Both
have the same `chainIncl` (`= a.1.1 ⌢ z`, by `chainIncl_pullbackDualityₗ` and the cap-chainIncl naturality
`SingularCapChainIncl.cap_chainIncl`), so `chainIncl`-injectivity identifies them.

This is the step that makes the Poincaré-duality cap a `sub K`-level cap product, so the Kronecker pairing
`⟨a', relativeDualityK … (mk a)⟩_{sub K}` becomes a cup pairing via `kronecker_cup_cap` at `X := sub K`
(the connecting-square cap×Kronecker bridge) — with no cochain representative of `relCohomMvConnecting`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularLocalDualityK SKEFTHawking.SingularCapChainIncl
  SKEFTHawking.SingularSubspaceChainsEquiv SKEFTHawking.SingularRelativePairing
  SKEFTHawking.SingularRightCapBoundary SKEFTHawking.SingularRelativeCap
  SKEFTHawking.SingularExcisionIso

namespace SKEFTHawking.SingularCapSubKDuality

variable {X : TopCat}

/-- **The duality chain is a `sub K`-cap**: `pullbackDualityₗ S K z hzK a = (pullbackCochain K a.1.1) ⌢ z_sub`
with `z_sub = (subspaceChainsEquiv K).symm ⟨z, hzK⟩`. Both `chainIncl` to `a.1.1 ⌢ z`. -/
theorem pullbackDualityₗ_eq_subcap {k m : ℕ} {S K : Set ↑X} (z : SingularChain X (k + m + 1))
    (hzK : z ∈ subspaceChains K (k + m + 1))
    (a : LinearMap.ker (relCoboundaryₗ S k)) :
    pullbackDualityₗ S K z hzK a
      = cap (pullbackCochain K k a.1.1) ((subspaceChainsEquiv K (k + m + 1)).symm ⟨z, hzK⟩) := by
  apply chainIncl_injective K (m + 1)
  rw [chainIncl_pullbackDualityₗ, ← cap_chainIncl]
  exact congrArg (cap a.1.1) (chainIncl_subspaceChainsEquiv_symm K (k + m + 1) ⟨z, hzK⟩).symm

/-- **The sub-`K` Kronecker cup bridge**: pairing a `sub K`-cohomology cocycle `a'` against the
Poincaré-duality image `relativeDualityK S K z [a]` equals pairing the cup `(pullbackCochain K a) ∪ a'`
against the `sub K`-representative `z_sub = (subspaceChainsEquiv K).symm ⟨z,hzK⟩` of the fundamental
cycle. Chains together `relativeDualityK_mk` (the image is `[pullbackDualityₗ]`), c2
(`pullbackDualityₗ_eq_subcap`: that chain IS the sub-`K`-cap `(pullbackCochain K a) ⌢ z_sub`), and
`kronecker_cup_cap` at `Y := sub K`. This converts the connecting-square cap pairing into a cup pairing
with **no cochain representative of `relCohomMvConnecting`** — the move that dodged the original block. -/
theorem kroneckerH_relativeDualityK_mk_eq_cup {k m : ℕ} {S K : Set ↑X}
    (z : SingularChain X (k + m + 1)) (hzK : z ∈ subspaceChains K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (a : LinearMap.ker (relCoboundaryₗ S k))
    (a' : LinearMap.ker (coboundaryₗ (sub K) (m + 1))) :
    kroneckerH (X := sub K) (m + 1) (Submodule.Quotient.mk a')
        (relativeDualityK S K k m z hzK hzS (RelativeCohomology.mk S k a))
      = kronecker (cup (pullbackCochain K k a.1.1) a'.1)
          ((subspaceChainsEquiv K (k + m + 1)).symm ⟨z, hzK⟩) := by
  rw [relativeDualityK_mk]
  show kroneckerH (X := sub K) (m + 1) (Submodule.Quotient.mk a')
      (Submodule.Quotient.mk _) = _
  rw [kroneckerH_mk_mk]
  show kronecker a'.1 (pullbackDualityₗ S K z hzK a) = _
  rw [pullbackDualityₗ_eq_subcap, ← kronecker_cup_cap]

/-- **Kronecker–chainIncl naturality** (the adjoint of `cap_chainIncl`): pairing the pulled-back cochain
`pullbackCochain S k a` against a `sub S`-chain `c` equals pairing the ambient cochain `a` against its
inclusion `chainIncl S k c`. On a basis `sub S`-simplex `τ` both are `a(simplexIncl S k τ)`. This moves a
`sub S`-level Kronecker pairing up to the ambient pairing — used to land the connecting-square RHS pairing
in the *relative* Kronecker `relKronecker S a c = kronecker a.1 c`. -/
theorem kronecker_pullbackCochain {k : ℕ} {S : Set ↑X} (a : SingularCochain X k)
    (c : SingularChain (sub S) k) :
    kronecker (pullbackCochain S k a) c = kronecker a (chainIncl S k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, kronecker_apply, Finsupp.sum_zero_index]
  | add c d hc hd => rw [kronecker_add_right, map_add, kronecker_add_right, hc, hd]
  | single τ s => rw [chainIncl_single, kronecker_single, kronecker_single, pullbackCochain_apply]

/-- **The RHS connecting-square pairing, reduced to an ambient `ω`-pairing**: pairing a `sub K`-cocycle
`a'` against the PD image `relativeDualityK S K z [ω]` equals pairing the *relative* cochain `ω` (ambient
rep `ω.1.1`) against the inclusion of the **right cap** `(a' ⌢ʳ z_sub)`. Chains c3
(`kroneckerH_relativeDualityK_mk_eq_cup`, the cup bridge) → `kronecker_cup_rcap` (extract the left factor
`pullbackCochain ω`) → `kronecker_pullbackCochain` (R2a, lift to the ambient). The `ω`-on-the-left form is
what lets `relKroneckerH_relCohomMvConnecting` fire when `ω = relCohomMvConnecting …` (via
`relKronecker_mk`, once the capped chain is recognised as a relative cycle). -/
theorem kroneckerH_relativeDualityK_mk_eq_rcap {k m : ℕ} {S K : Set ↑X}
    (z : SingularChain X (k + m + 1)) (hzK : z ∈ subspaceChains K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (ω : LinearMap.ker (relCoboundaryₗ S k))
    (a' : LinearMap.ker (coboundaryₗ (sub K) (m + 1))) :
    kroneckerH (X := sub K) (m + 1) (Submodule.Quotient.mk a')
        (relativeDualityK S K k m z hzK hzS (RelativeCohomology.mk S k ω))
      = kronecker ω.1.1
          (chainIncl K k (rcap a'.1 ((subspaceChainsEquiv K (k + m + 1)).symm ⟨z, hzK⟩))) := by
  rw [kroneckerH_relativeDualityK_mk_eq_cup, kronecker_cup_rcap, kronecker_pullbackCochain]

/-- `chainIncl` commutes with a degree cast (transport along a degree equality). -/
theorem chainIncl_cast {p q : ℕ} {K : Set ↑X} (h : p = q) (w : SingularChain (sub K) p) :
    chainIncl K q (cast (congrArg (SingularChain (sub K)) h) w)
      = cast (congrArg (SingularChain X) h) (chainIncl K p w) := by cases h; rfl

/-- `chainBoundary` commutes with a degree cast (transport along a degree equality of the index). -/
theorem chainBoundary_cast_succ {p q : ℕ} (h : p = q) (w : SingularChain X (p + 1)) :
    chainBoundary X q (cast (congrArg (fun n => SingularChain X (n + 1)) h) w)
      = cast (congrArg (SingularChain X) h) (chainBoundary X p w) := by cases h; rfl

/-- Membership in `subspaceChains S` is preserved under a degree cast. -/
theorem subspaceChains_mem_cast {p q : ℕ} {S : Set ↑X} (h : p = q) {c : SingularChain X p}
    (hc : c ∈ subspaceChains S p) : cast (congrArg (SingularChain X) h) c ∈ subspaceChains S q := by
  cases h; exact hc

/-- **Right-cap–chainIncl naturality** (the right-cap mirror of `cap_chainIncl`):
`b ⌢ʳ (chainIncl c) = chainIncl ((pullbackCochain b) ⌢ʳ c)`. On a basis `sub K`-simplex `τ`, both sides
are `b(simplexIncl (backₗ τ)) • [simplexIncl (frontₖ τ)]` (`frontFace`/`backFace` commute with
`simplexIncl`). Pushes the inclusion *inside* a right cap, so an ambient `K`-supported chain's right cap
can be recognised as the inclusion of a `sub K`-level right cap. -/
theorem rcap_chainIncl {k l : ℕ} {K : Set ↑X} (b : SingularCochain X l)
    (c : SingularChain (sub K) (k + l)) :
    rcap b (chainIncl K (k + l) c) = chainIncl K k (rcap (pullbackCochain K l b) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => rw [map_add, map_add, map_add, map_add, hc, hd]
  | single τ s =>
      rw [chainIncl_single, rcap_single_smul, rcap_single_smul, rcapBasis, rcapBasis,
        pullbackCochain_apply, frontFace_simplexIncl, backFace_simplexIncl, map_smul, map_smul,
        chainIncl_single]

/-- **The generic relative cap–Kronecker bridge**: the `sub K`-cohomology pairing of `a'` against the
PD image equals the *relative* `S`-pairing of `ω` against the relative homology class
`[chainIncl (a' ⌢ʳ z_sub)]`. Lifts R2b's RHS into the relative Kronecker pairing so the
relative-cohomology MV-connecting adjunction can fire. The rel-cycle witness `hWcyc` is taken as a
hypothesis (discharged separately by `chainIncl_rcap_mem_relCycles`). -/
theorem kroneckerH_relativeDualityK_mk_eq_relKroneckerH {k m : ℕ} {S K : Set ↑X}
    (z : SingularChain X (k + 1 + m + 1)) (hzK : z ∈ subspaceChains K (k + 1 + m + 1))
    (hzS : chainBoundary X (k + 1 + m) z ∈ subspaceChains S (k + 1 + m))
    (ω : LinearMap.ker (relCoboundaryₗ S (k + 1)))
    (a' : LinearMap.ker (coboundaryₗ (sub K) (m + 1)))
    (hWcyc : RelativeChain.mk S (k + 1)
        (chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z, hzK⟩)))
      ∈ relCycles S (k + 1)) :
    kroneckerH (X := sub K) (m + 1) (Submodule.Quotient.mk a')
        (relativeDualityK S K (k + 1) m z hzK hzS (RelativeCohomology.mk S (k + 1) ω))
      = relKroneckerH S (RelativeCohomology.mk S (k + 1) ω)
          (RelativeHomology.mk S (k + 1)
            ⟨RelativeChain.mk S (k + 1)
              (chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z, hzK⟩))),
              hWcyc⟩) := by
  rw [kroneckerH_relativeDualityK_mk_eq_rcap, relKroneckerH_mk_mk, relKronecker_mk]

/-- **The rel-cycle witness for the cap–Kronecker bridge**: `chainIncl K (a' ⌢ʳ z_sub)` is a *relative*
`(k+1)`-cycle of the pair `(X, S)`. Reason: its boundary equals `chainIncl K (a' ⌢ʳ ∂z_sub)` (since `a'`
is a cocycle, `⌢ʳ` is a chain map; `chainIncl` is a chain map), and `chainIncl K (∂z_sub) = ∂z` is
`S`-supported (`hzS`). Pushing the inclusion inside the right cap (`rcap_chainIncl`) identifies the
boundary with an *ambient* right cap `(pullbackCochain a') ⌢ʳ ∂z` of an `S`-supported chain, which is
`S`-supported by `rcap_mem_subspaceChains`. Discharges `hWcyc` at call sites of
`kroneckerH_relativeDualityK_mk_eq_relKroneckerH`. -/
theorem chainIncl_rcap_mem_relCycles {k m : ℕ} {S K : Set ↑X}
    (z : SingularChain X (k + 1 + m + 1)) (hzK : z ∈ subspaceChains K (k + 1 + m + 1))
    (hzS : chainBoundary X (k + 1 + m) z ∈ subspaceChains S (k + 1 + m))
    (a' : LinearMap.ker (coboundaryₗ (sub K) (m + 1))) :
    RelativeChain.mk S (k + 1)
        (chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z, hzK⟩)))
      ∈ relCycles S (k + 1) := by
  rw [show relCycles S (k + 1) = LinearMap.ker (relBoundary S k) from rfl, LinearMap.mem_ker,
    relBoundary_mk, RelativeChain.mk_eq_zero_iff, ← chainIncl_chainBoundary,
    chainIncl_mem_subspaceChains_iff S K]
  -- Now goal lives entirely inside `sub K`: `∂_{sub K}(rcap a' zsub) ∈ subspaceChains (val⁻¹'S) k`.
  -- Base degree equality `k+1+m = k+(m+1)`; the chain cast is `congrArg (·+1)` of it.
  have e0 : k + 1 + m = k + (m + 1) := by omega
  have key := rcap_cocycle_chainMap (k := k) (l := m + 1) a'.1 (LinearMap.mem_ker.mp a'.2)
    (congrArg (· + 1) e0 ▸ (subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z, hzK⟩)
  simp only [eqRec_eq_cast, cast_cast, cast_eq] at key
  rw [key]
  -- `rcap` preserves `(val⁻¹'S)`-support, reducing to `∂_{sub K} (cast zsub) ∈ subspaceChains (val⁻¹'S)`.
  apply rcap_mem_subspaceChains (Subtype.val ⁻¹' S) a'.1
  -- Reflect back to ambient `S`-support of `∂(chainIncl (cast zsub)) = cast ∂z`, which is `hzS`.
  rw [← chainIncl_mem_subspaceChains_iff S K, chainIncl_chainBoundary, chainIncl_cast,
    chainIncl_subspaceChainsEquiv_symm, chainBoundary_cast_succ]
  · exact subspaceChains_mem_cast e0 hzS
  · omega
  · omega

end SKEFTHawking.SingularCapSubKDuality
