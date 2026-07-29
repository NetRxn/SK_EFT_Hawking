/-
# Phase 5q.H (E1 integral topology) — the `H₀(sub K)`-valued bottom duality map (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularLocalDualityKBot`. The **bottom-degree** analogue of
`relativeDualityKInt`: the duality map `D_K⁰ : Hᵏ⁺¹(M, M∖K; ℤ) → H₀(sub K; ℤ)`, `[a] ↦ [a ⌢ z_K]`, for
`z_K` a `K`-supported fundamental cycle of degree `k+1` (the cap at `m = 0`: a `(k+1)`-cochain against a
`(k+1)`-chain gives a `0`-chain). The main family's `(m+1)`-indexed target structurally cannot express
`H₀`; this ₀-family fills the bottom vertical of the PD 5-lemma ladder.

Design notes (as in the mod-2): at the bottom the `capInt_leibniz` cast `k+0+1 = k+1+0` is `rfl`;
`cycles _ 0 = ⊤`, so every cycle obligation is trivial; the cocycle degree `k+1` is always a successor,
so the coboundary-range case split has no `k = 0` branch. The one genuine ℤ-difference is the sign
(`capInt_leibniz` carries `(-1)^{k+1}`), so the witness is `(-1)^{k+1} • (g ⌢ z)` (as in the main D_K
witness).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularLocalDualityKInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCapSupportInt

namespace SKEFTHawking.SingularLocalDualityKBotInt

variable {X : TopCat} (S K : Set ↑X)

/-- **Bottom boundary-transfer** (`n = 0` analogue of `inclRangeEquiv_symm_mem_boundariesInt`). -/
theorem inclRangeEquiv_symm_mem_boundaries₀Int (c : SingularChainInt X 0)
    (hc : c ∈ subspaceChainsInt S 0) (d : SingularChainInt X 1)
    (hd : d ∈ subspaceChainsInt S 1) (hbd : chainBoundary X 0 d = c) :
    (inclRangeEquiv S 0).symm ⟨c, hc⟩ ∈ boundaries (sub S) 0 := by
  refine ⟨(inclRangeEquiv S 1).symm ⟨d, hd⟩, ?_⟩
  apply chainIncl_injective S 0
  rw [chainIncl_chainBoundary, chainIncl_inclRangeEquiv_symm, chainIncl_inclRangeEquiv_symm]
  exact hbd

/-- **Bottom coboundary witness** (`m = 0` analogue of `capInt_relCoboundary_K_witness`): a relative
coboundary `δg` caps the degree-`(k+1)` cycle `z` to `∂` of the `K`-supported `1`-chain `(-1)^{k+1} •
(g ⌢ z)` (the sign making `(-1)^{2k+2} = 1` cancel; the leibniz `∂z`-term vanishes on `S`). -/
theorem capInt_relCoboundary_K_witness₀ {k : ℕ} (g : SingularCochainInt X k)
    (hg : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))),
      g (simplexIncl S k τ) = 0)
    (z : SingularChainInt X (k + 1)) (hzK : z ∈ subspaceChainsInt K (k + 1))
    (hzS : chainBoundary X k z ∈ subspaceChainsInt S k) :
    ∃ d : SingularChainInt X 1, d ∈ subspaceChainsInt K 1 ∧
      chainBoundary X 0 d = capInt (m := 0) (coboundary X k g) z := by
  refine ⟨(-1 : ℤ) ^ (k + 1) • capInt (m := 1) g z,
    Submodule.smul_mem _ _ (capInt_mem_subspaceChainsInt K g hzK), ?_⟩
  rw [map_smul]
  have hleib := capInt_leibniz (m := 0) (a := g) (c := z) (rfl : k + 0 + 1 = k + 1 + 0)
  have hmid : capInt (m := 0) g (chainBoundary X (k + 0) z) = 0 :=
    capInt_subspaceChainInt_eq_zero S g hg hzS
  rw [hmid, smul_zero, add_zero] at hleib
  rw [hleib, smul_smul, ← pow_add]
  have hev : Even ((k + 1) + (k + 1)) := ⟨k + 1, by ring⟩
  rw [hev.neg_one_pow, one_smul]

/-- The bottom cap `a ↦ a ⌢ z` of a relative cocycle (`(k+1)`-cochain × `(k+1)`-chain → `0`-chain). -/
noncomputable def capCochainIntₗ₀ {k : ℕ} (z : SingularChainInt X (k + 1)) :
    LinearMap.ker (relCoboundaryIntₗ S (k + 1)) →ₗ[ℤ] SingularChainInt X 0 :=
  ((capIntₗ (k + 1) 0).flip z).comp
    ((relCochainsInt S (k + 1)).subtype.comp (LinearMap.ker (relCoboundaryIntₗ S (k + 1))).subtype)

@[simp] theorem capCochainIntₗ₀_apply {k : ℕ} (z : SingularChainInt X (k + 1))
    (a : LinearMap.ker (relCoboundaryIntₗ S (k + 1))) :
    capCochainIntₗ₀ S z a = capInt (m := 0) a.1.1 z := rfl

/-- The bottom cap valued in the `K`-supported `0`-chains (cap-locality). -/
noncomputable def capSubKIntₗ₀ {k : ℕ} (z : SingularChainInt X (k + 1))
    (hzK : z ∈ subspaceChainsInt K (k + 1)) :
    LinearMap.ker (relCoboundaryIntₗ S (k + 1)) →ₗ[ℤ] subspaceChainsInt K 0 :=
  (capCochainIntₗ₀ S z).codRestrict (subspaceChainsInt K 0)
    (fun a => capInt_mem_subspaceChainsInt K a.1.1 hzK)

@[simp] theorem capSubKIntₗ₀_coe {k : ℕ} (z : SingularChainInt X (k + 1))
    (hzK : z ∈ subspaceChainsInt K (k + 1)) (a : LinearMap.ker (relCoboundaryIntₗ S (k + 1))) :
    (capSubKIntₗ₀ S K z hzK a : SingularChainInt X 0) = capInt (m := 0) a.1.1 z := rfl

/-- The bottom pulled-back duality chain, a genuine `0`-chain of the subspace `K`. -/
noncomputable def pullbackDualityIntₗ₀ {k : ℕ} (z : SingularChainInt X (k + 1))
    (hzK : z ∈ subspaceChainsInt K (k + 1)) :
    LinearMap.ker (relCoboundaryIntₗ S (k + 1)) →ₗ[ℤ] SingularChainInt (sub K) 0 :=
  (inclRangeEquiv K 0).symm.toLinearMap.comp (capSubKIntₗ₀ S K z hzK)

@[simp] theorem chainIncl_pullbackDualityIntₗ₀ {k : ℕ} (z : SingularChainInt X (k + 1))
    (hzK : z ∈ subspaceChainsInt K (k + 1)) (a : LinearMap.ker (relCoboundaryIntₗ S (k + 1))) :
    chainIncl K 0 (pullbackDualityIntₗ₀ S K z hzK a) = capInt (m := 0) a.1.1 z := by
  rw [pullbackDualityIntₗ₀, LinearMap.comp_apply, LinearEquiv.coe_coe,
    chainIncl_inclRangeEquiv_symm, capSubKIntₗ₀_coe]

/-- The bottom cycle-level duality map `a ↦ [a ⌢ z]_{sub K} ∈ H₀(sub K)` (`cycles _ 0 = ⊤`). -/
noncomputable def relDualityKIntₗ₀ {k : ℕ} (z : SingularChainInt X (k + 1))
    (hzK : z ∈ subspaceChainsInt K (k + 1)) :
    LinearMap.ker (relCoboundaryIntₗ S (k + 1)) →ₗ[ℤ] Homology (sub K) 0 :=
  (Submodule.mkQ _).comp
    ((pullbackDualityIntₗ₀ S K z hzK).codRestrict (cycles (sub K) 0)
      (fun _ => Submodule.mem_top))

@[simp] theorem relDualityKIntₗ₀_apply {k : ℕ} (z : SingularChainInt X (k + 1))
    (hzK : z ∈ subspaceChainsInt K (k + 1)) (a : LinearMap.ker (relCoboundaryIntₗ S (k + 1))) :
    relDualityKIntₗ₀ S K z hzK a
      = Homology.mk (sub K) 0 ⟨pullbackDualityIntₗ₀ S K z hzK a, Submodule.mem_top⟩ := rfl

/-- **The bottom `H₀(sub K)`-valued duality map** `D_K⁰ : Hᵏ⁺¹(M, M∖K; ℤ) → H₀(sub K; ℤ)`,
`[a] ↦ [a ⌢ z]`, well-defined modulo relative coboundaries via `capInt_relCoboundary_K_witness₀`. -/
noncomputable def relativeDualityK₀Int (k : ℕ) (z : SingularChainInt X (k + 1))
    (hzK : z ∈ subspaceChainsInt K (k + 1))
    (hzS : chainBoundary X k z ∈ subspaceChainsInt S k) :
    RelativeCohomologyInt S (k + 1) →ₗ[ℤ] Homology (sub K) 0 :=
  Submodule.liftQ _ (relDualityKIntₗ₀ S K z hzK) (by
    intro a ha
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
    rw [LinearMap.mem_ker, relDualityKIntₗ₀_apply]
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
    rw [show relCoboundaryRangeInt S (k + 1) = LinearMap.range (relCoboundaryIntₗ S k) from rfl] at ha
    obtain ⟨g, hg⟩ := ha
    have hcob : (a.1.1 : SingularCochainInt X (k + 1)) = coboundary X k g.1 := by
      rw [← hg, relCoboundaryIntₗ_coe]
    obtain ⟨d, hdK, hbd⟩ :=
      capInt_relCoboundary_K_witness₀ S K g.1 (relCochainInt_vanish S g) z hzK hzS
    have hc : capInt (m := 0) a.1.1 z ∈ subspaceChainsInt K 0 :=
      capInt_mem_subspaceChainsInt K a.1.1 hzK
    have hpb : pullbackDualityIntₗ₀ S K z hzK a
        = (inclRangeEquiv K 0).symm ⟨capInt (m := 0) a.1.1 z, hc⟩ := rfl
    rw [hpb]
    have hbd' : chainBoundary X 0 d = capInt (m := 0) a.1.1 z := by rw [hbd, hcob]
    exact inclRangeEquiv_symm_mem_boundaries₀Int K (capInt (m := 0) a.1.1 z) hc d hdK hbd')

/-- **Computation rule for `D_K⁰`**: `[a] ↦ [a ⌢ z]_{sub K}`. -/
@[simp] theorem relativeDualityK₀Int_mk (k : ℕ) (z : SingularChainInt X (k + 1))
    (hzK : z ∈ subspaceChainsInt K (k + 1))
    (hzS : chainBoundary X k z ∈ subspaceChainsInt S k)
    (a : LinearMap.ker (relCoboundaryIntₗ S (k + 1))) :
    relativeDualityK₀Int S K k z hzK hzS (RelativeCohomologyInt.mk S (k + 1) a)
      = Homology.mk (sub K) 0 ⟨pullbackDualityIntₗ₀ S K z hzK a, Submodule.mem_top⟩ :=
  rfl

end SKEFTHawking.SingularLocalDualityKBotInt
