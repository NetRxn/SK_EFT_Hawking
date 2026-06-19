import Mathlib
import SKEFTHawking.SingularRelativeHomologyMod2

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-pullback) — the subspace-chains pullback equiv

The inclusion-induced chain map `chainIncl S n : C_n(S) → C_n(X)` is **injective**
(`chainIncl_injective`) with image exactly `subspaceChains S n` (by definition). Hence its
**corestriction** to `subspaceChains S n` is a linear **isomorphism**
  `subspaceChainsEquiv : C_n(sub S) ≃ₗ subspaceChains S n`,
the canonical linear **pullback** of an `S`-supported absolute chain to a genuine chain of the
subspace `sub S`.

This is the piece that turns the `K`-supported duality cycle `a ⌢ z_K ∈ subspaceChains K`
(`SingularCapSupport`) into a class in the homology of the **compact `K` itself**,
`H_{n-k}(sub K)` — the *varying* duality target `D_K : Hᵏ(M|K) → H_{n-k}(K)` that fits the
Mayer–Vietoris `5`-lemma ladder.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2

namespace SKEFTHawking.SingularSubspaceChainsEquiv

variable {X : TopCat} (S : Set X)

/-- The corestriction of `chainIncl S n` to its range `subspaceChains S n` — a linear map
`C_n(sub S) → subspaceChains S n`, surjective by construction (`subspaceChains = range chainIncl`)
and injective (`chainIncl_injective`). -/
noncomputable def chainInclCorestrict (n : ℕ) :
    SingularChain (sub S) n →ₗ[ZMod 2] subspaceChains S n :=
  (chainIncl S n).codRestrict (subspaceChains S n) (fun c => ⟨c, rfl⟩)

@[simp] theorem chainInclCorestrict_coe (n : ℕ) (c : SingularChain (sub S) n) :
    (chainInclCorestrict S n c : SingularChain X n) = chainIncl S n c := rfl

/-- **The subspace-chains pullback equiv** `C_n(sub S) ≃ₗ subspaceChains S n`: the corestriction of the
injective inclusion-induced chain map onto its image. The linear inverse of `chainIncl S n` on the
`S`-supported chains. -/
noncomputable def subspaceChainsEquiv (n : ℕ) :
    SingularChain (sub S) n ≃ₗ[ZMod 2] subspaceChains S n :=
  LinearEquiv.ofBijective (chainInclCorestrict S n)
    ⟨fun a b hab => chainIncl_injective S n (Subtype.ext_iff.mp hab),
      fun s => by obtain ⟨c, hc⟩ := s.2; exact ⟨c, Subtype.ext hc⟩⟩

@[simp] theorem subspaceChainsEquiv_coe (n : ℕ) (c : SingularChain (sub S) n) :
    (subspaceChainsEquiv S n c : SingularChain X n) = chainIncl S n c := rfl

/-- **The pullback inverts `chainIncl`**: applying the inclusion to the pulled-back chain recovers the
underlying `S`-supported absolute chain. The defining property of `subspaceChainsEquiv.symm`. -/
@[simp] theorem chainIncl_subspaceChainsEquiv_symm (n : ℕ) (s : subspaceChains S n) :
    chainIncl S n ((subspaceChainsEquiv S n).symm s) = (s : SingularChain X n) := by
  conv_rhs => rw [← (subspaceChainsEquiv S n).apply_symm_apply s]
  rfl

/-- **Pullback of an `S`-supported boundary with an `S`-supported bounding chain is a `sub S` boundary.**
If an `S`-supported `(n+1)`-chain `c` is the boundary `c = ∂d` of an **`S`-supported** `(n+2)`-chain `d`,
then the pulled-back chain `(subspaceChainsEquiv S (n+1)).symm ⟨c⟩` is a boundary of the subspace `sub S`:
its bounding `(n+2)`-chain is the pullback of `d`. (`chainIncl` is an injective chain map, so the
boundary identity transfers through the pullback.) This is what turns the cap-of-a-relative-coboundary —
which is `S`-supported *and* bounds the `S`-supported cap-of-the-cochain — into a genuine boundary of
`H_{n-k}(sub S)`, giving well-definedness of the `H(sub S)`-valued duality map modulo coboundaries. -/
theorem subspaceChainsEquiv_symm_mem_boundaries (n : ℕ) (c : SingularChain X (n + 1))
    (hc : c ∈ subspaceChains S (n + 1)) (d : SingularChain X (n + 2))
    (hd : d ∈ subspaceChains S (n + 2)) (hbd : chainBoundary X (n + 1) d = c) :
    (subspaceChainsEquiv S (n + 1)).symm ⟨c, hc⟩ ∈ boundaries (sub S) (n + 1) := by
  refine ⟨(subspaceChainsEquiv S (n + 2)).symm ⟨d, hd⟩, ?_⟩
  apply chainIncl_injective S (n + 1)
  rw [chainIncl_chainBoundary, chainIncl_subspaceChainsEquiv_symm,
    chainIncl_subspaceChainsEquiv_symm]
  exact hbd

end SKEFTHawking.SingularSubspaceChainsEquiv
