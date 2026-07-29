import Mathlib
import SKEFTHawking.SingularLocalDualityK

/-!
# Phase 5q.G (G1 PD-induction, the ₀-family) — the `H₀(sub K)`-valued bottom duality map

The **bottom-degree** analogue of `SingularLocalDualityK.relativeDualityK`: the duality map
`D_K⁰ : Hᵏ⁺¹(M, M∖K) → H₀(sub K)`, `[a] ↦ [a ⌢ z_K]`, for `z_K` a `K`-supported fundamental
cycle of degree `k+1` (the cap at `m = 0`: a `(k+1)`-cochain against a `(k+1)`-chain gives a
`0`-chain). The main family's `(m+1)`-indexed target `Homology (sub K) (m+1)` structurally cannot
express `H₀`; this ₀-family fills the bottom vertical of the Poincaré-duality 5-lemma ladder
(the `(3,0)`-center's pos4/pos5 verticals — L2 notebook, 32nd–34th pushes).

Design notes: at the bottom degree the `cap_leibniz` cast `k+0+1 = k+1+0` is `rfl` (both sides
reduce to `k+1`) — no cast transport anywhere; `cycles Y 0 = ⊤`, so every cycle obligation is
trivial; the cocycle degree `k+1` is always a successor, so the coboundary-range case split of the
main family's `liftQ` well-definedness has no `k = 0` branch.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativeCap SKEFTHawking.SingularRelativeDuality
  SKEFTHawking.SingularCapSupport SKEFTHawking.SingularSubspaceChainsEquiv

namespace SKEFTHawking.SingularLocalDualityKBot

variable {X : TopCat} (S K : Set ↑X)

/-- **Bottom boundary-transfer**: a `K`-supported `0`-chain bounded by a `K`-supported `1`-chain
pulls back to a boundary of `sub K` (the `n = 0` analogue of
`subspaceChainsEquiv_symm_mem_boundaries`). -/
theorem subspaceChainsEquiv_symm_mem_boundaries₀ (c : SingularChain X 0)
    (hc : c ∈ subspaceChains S 0) (d : SingularChain X 1)
    (hd : d ∈ subspaceChains S 1) (hbd : chainBoundary X 0 d = c) :
    (subspaceChainsEquiv S 0).symm ⟨c, hc⟩ ∈ boundaries (sub S) 0 := by
  refine ⟨(subspaceChainsEquiv S 1).symm ⟨d, hd⟩, ?_⟩
  apply chainIncl_injective S 0
  rw [SingularRelativeHomologyMod2.chainIncl_chainBoundary, chainIncl_subspaceChainsEquiv_symm,
    chainIncl_subspaceChainsEquiv_symm]
  exact hbd

/-- **Bottom coboundary witness** (the `m = 0` analogue of `cap_relCoboundary_K_witness`): a
relative coboundary `δg` caps the degree-`(k+1)` cycle `z` to the boundary of the `K`-supported
`1`-chain `g ⌢ z`. The `cap_leibniz` cast is `rfl` at the bottom. -/
theorem cap_relCoboundary_K_witness₀ {k : ℕ} (g : SingularCochain X k)
    (hg : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))),
      g (simplexIncl S k τ) = 0)
    (z : SingularChain X (k + 1)) (hzK : z ∈ subspaceChains K (k + 1))
    (hzS : chainBoundary X k z ∈ subspaceChains S k) :
    ∃ d : SingularChain X 1, d ∈ subspaceChains K 1 ∧
      chainBoundary X 0 d = cap (m := 0) (coboundary X k g) z := by
  refine ⟨cap (m := 1) g z, cap_mem_subspaceChains K g hzK, ?_⟩
  have hleib := cap_leibniz (a := g) (c := z) (m := 0) rfl
  have hmid : cap (m := 0) g (chainBoundary X (k + 0) z) = 0 :=
    cap_subspaceChain_eq_zero S g hg hzS
  rw [hmid, add_zero] at hleib
  exact hleib

/-- The bottom cap `a ↦ a ⌢ z` of a relative cocycle (`(k+1)`-cochain × `(k+1)`-chain → `0`-chain). -/
noncomputable def capCochainₗ₀ {k : ℕ} (z : SingularChain X (k + 1)) :
    LinearMap.ker (relCoboundaryₗ S (k + 1)) →ₗ[ZMod 2] SingularChain X 0 :=
  ((capₗ (k + 1) 0).flip z).comp
    ((relCochains S (k + 1)).subtype.comp (LinearMap.ker (relCoboundaryₗ S (k + 1))).subtype)

@[simp] theorem capCochainₗ₀_apply {k : ℕ} (z : SingularChain X (k + 1))
    (a : LinearMap.ker (relCoboundaryₗ S (k + 1))) :
    capCochainₗ₀ S z a = cap (m := 0) a.1.1 z := rfl

/-- The bottom cap valued in the `K`-supported `0`-chains (cap-locality). -/
noncomputable def capSubKₗ₀ {k : ℕ} (z : SingularChain X (k + 1))
    (hzK : z ∈ subspaceChains K (k + 1)) :
    LinearMap.ker (relCoboundaryₗ S (k + 1)) →ₗ[ZMod 2] subspaceChains K 0 :=
  (capCochainₗ₀ S z).codRestrict (subspaceChains K 0)
    (fun a => cap_mem_subspaceChains K a.1.1 hzK)

@[simp] theorem capSubKₗ₀_coe {k : ℕ} (z : SingularChain X (k + 1))
    (hzK : z ∈ subspaceChains K (k + 1)) (a : LinearMap.ker (relCoboundaryₗ S (k + 1))) :
    (capSubKₗ₀ S K z hzK a : SingularChain X 0) = cap (m := 0) a.1.1 z := rfl

/-- The bottom pulled-back duality chain, a genuine `0`-chain of the subspace `K`. -/
noncomputable def pullbackDualityₗ₀ {k : ℕ} (z : SingularChain X (k + 1))
    (hzK : z ∈ subspaceChains K (k + 1)) :
    LinearMap.ker (relCoboundaryₗ S (k + 1)) →ₗ[ZMod 2] SingularChain (sub K) 0 :=
  (subspaceChainsEquiv K 0).symm.toLinearMap.comp (capSubKₗ₀ S K z hzK)

@[simp] theorem chainIncl_pullbackDualityₗ₀ {k : ℕ} (z : SingularChain X (k + 1))
    (hzK : z ∈ subspaceChains K (k + 1)) (a : LinearMap.ker (relCoboundaryₗ S (k + 1))) :
    chainIncl K 0 (pullbackDualityₗ₀ S K z hzK a) = cap (m := 0) a.1.1 z := by
  rw [pullbackDualityₗ₀, LinearMap.comp_apply, LinearEquiv.coe_coe,
    chainIncl_subspaceChainsEquiv_symm, capSubKₗ₀_coe]

/-- The bottom cycle-level duality map `a ↦ [a ⌢ z]_{sub K} ∈ H₀(sub K)` (every `0`-chain is a
cycle: `cycles _ 0 = ⊤`). -/
noncomputable def relDualityKₗ₀ {k : ℕ} (z : SingularChain X (k + 1))
    (hzK : z ∈ subspaceChains K (k + 1)) :
    LinearMap.ker (relCoboundaryₗ S (k + 1)) →ₗ[ZMod 2] Homology (sub K) 0 :=
  (Submodule.mkQ _).comp
    ((pullbackDualityₗ₀ S K z hzK).codRestrict (cycles (sub K) 0)
      (fun _ => Submodule.mem_top))

@[simp] theorem relDualityKₗ₀_apply {k : ℕ} (z : SingularChain X (k + 1))
    (hzK : z ∈ subspaceChains K (k + 1)) (a : LinearMap.ker (relCoboundaryₗ S (k + 1))) :
    relDualityKₗ₀ S K z hzK a
      = Homology.mk (sub K) 0 ⟨pullbackDualityₗ₀ S K z hzK a, Submodule.mem_top⟩ := rfl

/-- **The bottom `H₀(sub K)`-valued duality map** `D_K⁰ : Hᵏ⁺¹(M, M∖K) → H₀(sub K)`,
`[a] ↦ [a ⌢ z]` — the ₀-family's endpoint, well-defined modulo relative coboundaries via the
bottom witness `cap_relCoboundary_K_witness₀` + the bottom boundary-transfer. -/
noncomputable def relativeDualityK₀ (k : ℕ) (z : SingularChain X (k + 1))
    (hzK : z ∈ subspaceChains K (k + 1))
    (hzS : chainBoundary X k z ∈ subspaceChains S k) :
    RelativeCohomology S (k + 1) →ₗ[ZMod 2] Homology (sub K) 0 :=
  Submodule.liftQ _ (relDualityKₗ₀ S K z hzK) (by
    intro a ha
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
    rw [LinearMap.mem_ker, relDualityKₗ₀_apply]
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
    rw [show relCoboundaryRange S (k + 1) = LinearMap.range (relCoboundaryₗ S k) from rfl] at ha
    obtain ⟨g, hg⟩ := ha
    have hcob : (a.1.1 : SingularCochain X (k + 1)) = coboundary X k g.1 := by
      rw [← hg, relCoboundaryₗ_coe]
    obtain ⟨d, hdK, hbd⟩ :=
      cap_relCoboundary_K_witness₀ S K g.1 (relCochain_vanish S g) z hzK hzS
    have hc : cap (m := 0) a.1.1 z ∈ subspaceChains K 0 :=
      cap_mem_subspaceChains K a.1.1 hzK
    have hpb : pullbackDualityₗ₀ S K z hzK a
        = (subspaceChainsEquiv K 0).symm ⟨cap (m := 0) a.1.1 z, hc⟩ := rfl
    rw [hpb]
    have hbd' : chainBoundary X 0 d = cap (m := 0) a.1.1 z := by rw [hbd, hcob]
    exact subspaceChainsEquiv_symm_mem_boundaries₀ K (cap (m := 0) a.1.1 z) hc d hdK hbd')

/-- **Computation rule for `D_K⁰`**: `[a] ↦ [a ⌢ z]_{sub K}`. -/
@[simp] theorem relativeDualityK₀_mk (k : ℕ) (z : SingularChain X (k + 1))
    (hzK : z ∈ subspaceChains K (k + 1))
    (hzS : chainBoundary X k z ∈ subspaceChains S k)
    (a : LinearMap.ker (relCoboundaryₗ S (k + 1))) :
    relativeDualityK₀ S K k z hzK hzS (RelativeCohomology.mk S (k + 1) a)
      = Homology.mk (sub K) 0 ⟨pullbackDualityₗ₀ S K z hzK a, Submodule.mem_top⟩ :=
  rfl

end SKEFTHawking.SingularLocalDualityKBot
