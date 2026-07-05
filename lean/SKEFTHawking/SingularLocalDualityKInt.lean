/-
# Phase 5q.H (E1 integral topology) — the integral `H(sub K)`-valued local duality map `D_K`

Integral (`ZMod 2 → ℤ`) mirror of `SingularLocalDualityK`. The framework-correct Poincaré-duality map
for the Mayer–Vietoris induction lands in the homology of the **compact `K` itself** (which *varies* with
`K`), not the fixed absolute `H_{n-k}(M; ℤ)`:
  `D_K : Hᵏ(M, M∖K; ℤ) → H_{n-k}(sub K; ℤ)`,    `[a] ↦ [a ⌢ z_K]`,
for `z_K` a fundamental cycle **supported in `K`** (`z ∈ subspaceChainsInt K`) whose boundary lies in
`M∖K`. The integral cap of a relative cocycle with `z_K` is an absolute cycle (`capInt_relCycle_isCycleInt`)
**and** supported in `K` (`capInt_mem_subspaceChainsInt`), so it pulls back (`inclRangeEquiv`) to a genuine
cycle of `sub K`, giving a class in `H_{n-k}(sub K; ℤ)`.

**The one genuine ℤ-difference vs the mod-2 mirror:** `capInt_leibniz` carries SIGNS,
`∂(a ⌢ c) = (-1)^{k+1}•(δa ⌢ c) + (-1)^k•(a ⌢ ∂c)`, where the mod-2 `cap_leibniz` is sign-free. So the
`K`-supported bounding-chain witness uses `d := (-1)^{j+1} • (g ⌢ z)`, not the bare `g ⌢ z`: then
`∂d = (-1)^{j+1}•(-1)^{j+1}•(δg ⌢ z) = (δg ⌢ z)` since `((-1)^{j+1})² = 1`, and the `K`-support survives
the `• `. Everything else is a direct name-swap mirror.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularEuclideanCapIsoInt
import SKEFTHawking.SingularCapSupportInt
import SKEFTHawking.SingularSubspaceChainsEquivInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCapSupportInt

namespace SKEFTHawking.SingularLocalDualityKInt

variable {X : TopCat} (S K : Set X)

/-! ## §1. Degree-cast helpers (integral mirror of `SingularLocalDualityK`'s private versions) -/

private theorem chainBoundary_castInt {a b : ℕ} (z : SingularChainInt X (a + 1))
    (e : a + 1 = b + 1) (eb : a = b) :
    chainBoundary X b (e ▸ z) = eb ▸ chainBoundary X a z := by
  subst eb; rw [show e = rfl from rfl]

private theorem subspaceChains_castInt {a b : ℕ} (c : SingularChainInt X a) (eb : a = b)
    (hc : c ∈ subspaceChainsInt K a) : (eb ▸ c) ∈ subspaceChainsInt K b := by
  subst eb; exact hc

/-! ## §2. The `K`-supported bounding-chain witness (with the ℤ sign adjustment) -/

/-- **The `K`-supported witness for the relative-coboundary cap** (integral). For a `j`-cochain `g`
vanishing on `S` and a fundamental cycle `z` **supported in `K`** with `∂z ∈ subspaceChainsInt S`, the
cap `(δg) ⌢ z` is `∂` of the `K`-supported chain `d = (-1)^{j+1} • (g ⌢ z)` (the sign making the two
copies of `(-1)^{j+1}` from `capInt_leibniz` cancel, `((-1)^{j+1})² = 1`). -/
theorem capInt_relCoboundary_K_witness {j m : ℕ} (g : SingularCochainInt X j)
    (hg : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk j))),
      g (simplexIncl S j τ) = 0)
    (z : SingularChainInt X (j + 1 + m + 1))
    (hzK : z ∈ subspaceChainsInt K (j + 1 + m + 1))
    (hzS : chainBoundary X (j + 1 + m) z ∈ subspaceChainsInt S (j + 1 + m)) :
    ∃ d : SingularChainInt X (m + 2), d ∈ subspaceChainsInt K (m + 2) ∧
      chainBoundary X (m + 1) d = capInt (m := m + 1) (coboundary X j g) z := by
  have e : j + 1 + m + 1 = j + (m + 1) + 1 := by omega
  refine ⟨(-1 : ℤ) ^ (j + 1) • capInt (m := m + 2) g (e ▸ z), ?_, ?_⟩
  · -- `K`-support: `g ⌢ (e ▸ z)` with `e ▸ z` still `K`-supported (cap-locality), then `• `-closed.
    exact Submodule.smul_mem _ _
      (capInt_mem_subspaceChainsInt K g (subspaceChains_castInt K z e hzK))
  · -- The boundary identity, with the sign cancellation.
    rw [map_smul]
    have h : j + (m + 1) + 1 = j + 1 + (m + 1) := by omega
    have hleib := capInt_leibniz (a := g) (c := e ▸ z) h
    have ed : j + 1 + m = j + (m + 1) := by omega
    have hmid : capInt (m := m + 1) g (chainBoundary X (j + (m + 1)) (e ▸ z)) = 0 := by
      apply capInt_subspaceChainInt_eq_zero S g hg
      rw [chainBoundary_castInt z e ed]
      exact subspaceChains_castInt S _ ed hzS
    rw [hmid, smul_zero, add_zero] at hleib
    have hcancel : (h ▸ (e ▸ z) : SingularChainInt X (j + 1 + (m + 1))) = z := by
      rw [eqRec_eq_cast, eqRec_eq_cast, cast_cast, cast_eq]
    rw [hcancel] at hleib
    -- `hleib : ∂(g ⌢ (e▸z)) = (-1)^{j+1} • (δg ⌢ z)`; combine the two signs.
    rw [hleib, smul_smul, ← pow_add]
    have hev : Even ((j + 1) + (j + 1)) := ⟨j + 1, by ring⟩
    rw [hev.neg_one_pow, one_smul]

/-! ## §3. The `H(sub K)`-valued duality map -/

/-- The cap `a ↦ a ⌢ z` of a relative cocycle, valued in the `K`-supported `(m+1)`-chains
`subspaceChainsInt K (m+1)` (cap-locality). -/
noncomputable def capSubKIntₗ {k m : ℕ} (z : SingularChainInt X (k + m + 1))
    (hzK : z ∈ subspaceChainsInt K (k + m + 1)) :
    LinearMap.ker (relCoboundaryIntₗ S k) →ₗ[ℤ] subspaceChainsInt K (m + 1) :=
  (capCochainIntₗ S z).codRestrict (subspaceChainsInt K (m + 1))
    (fun a => capInt_mem_subspaceChainsInt K a.1.1 hzK)

@[simp] theorem capSubKIntₗ_coe {k m : ℕ} (z : SingularChainInt X (k + m + 1))
    (hzK : z ∈ subspaceChainsInt K (k + m + 1)) (a : LinearMap.ker (relCoboundaryIntₗ S k)) :
    (capSubKIntₗ S K z hzK a : SingularChainInt X (m + 1)) = capInt a.1.1 z := rfl

/-- The pulled-back duality chain `a ↦ (a ⌢ z)` pulled back into `C(sub K; ℤ)` via `inclRangeEquiv`. -/
noncomputable def pullbackDualityIntₗ {k m : ℕ} (z : SingularChainInt X (k + m + 1))
    (hzK : z ∈ subspaceChainsInt K (k + m + 1)) :
    LinearMap.ker (relCoboundaryIntₗ S k) →ₗ[ℤ] SingularChainInt (sub K) (m + 1) :=
  (inclRangeEquiv K (m + 1)).symm.toLinearMap.comp (capSubKIntₗ S K z hzK)

/-- `chainIncl` recovers the absolute cap from the pulled-back duality chain. -/
@[simp] theorem chainIncl_pullbackDualityIntₗ {k m : ℕ} (z : SingularChainInt X (k + m + 1))
    (hzK : z ∈ subspaceChainsInt K (k + m + 1)) (a : LinearMap.ker (relCoboundaryIntₗ S k)) :
    chainIncl K (m + 1) (pullbackDualityIntₗ S K z hzK a) = capInt a.1.1 z := by
  rw [pullbackDualityIntₗ, LinearMap.comp_apply, LinearEquiv.coe_coe,
    chainIncl_inclRangeEquiv_symm, capSubKIntₗ_coe]

/-- The pulled-back duality chain is a **cycle of `sub K`**: `chainIncl` is an injective chain map and
the absolute cap `a ⌢ z` is an absolute cycle (`capInt_relCycle_isCycleInt`). -/
theorem pullbackDualityIntₗ_mem_cycles {k m : ℕ} (z : SingularChainInt X (k + m + 1))
    (hzK : z ∈ subspaceChainsInt K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m))
    (a : LinearMap.ker (relCoboundaryIntₗ S k)) :
    pullbackDualityIntₗ S K z hzK a ∈ cycles (sub K) (m + 1) := by
  have hcyc : chainBoundary X m (capInt a.1.1 z) = 0 :=
    capInt_relCycle_isCycleInt S a.1.1 (relCochainInt_vanish S a.1)
      (relCocycleInt_coboundary_zero S a) hzS
  show chainBoundary (sub K) m (pullbackDualityIntₗ S K z hzK a) = 0
  apply chainIncl_injective K m
  rw [chainIncl_chainBoundary, chainIncl_pullbackDualityIntₗ, hcyc, map_zero]

/-- The cycle-level `H(sub K)`-valued duality map `a ↦ [a ⌢ z]_{sub K}`. -/
noncomputable def relDualityKIntₗ {k m : ℕ} (z : SingularChainInt X (k + m + 1))
    (hzK : z ∈ subspaceChainsInt K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m)) :
    LinearMap.ker (relCoboundaryIntₗ S k) →ₗ[ℤ] Homology (sub K) (m + 1) :=
  ((boundaries (sub K) (m + 1)).submoduleOf (cycles (sub K) (m + 1))).mkQ.comp
    ((pullbackDualityIntₗ S K z hzK).codRestrict (cycles (sub K) (m + 1))
      (pullbackDualityIntₗ_mem_cycles S K z hzK hzS))

@[simp] theorem relDualityKIntₗ_apply {k m : ℕ} (z : SingularChainInt X (k + m + 1))
    (hzK : z ∈ subspaceChainsInt K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m))
    (a : LinearMap.ker (relCoboundaryIntₗ S k)) :
    relDualityKIntₗ S K z hzK hzS a
      = Homology.mk (sub K) (m + 1) ⟨pullbackDualityIntₗ S K z hzK a,
          pullbackDualityIntₗ_mem_cycles S K z hzK hzS a⟩ := rfl

/-- **The integral `H(sub K)`-valued relative Poincaré-duality map** `D_K : Hᵏ(M, S; ℤ) → H_{m+1}(sub K;
ℤ)`, `[a] ↦ [a ⌢ z_K]`, for a fundamental cycle `z_K` **supported in `K`** whose boundary lies in
`S = M∖K`. Well-defined: a relative cocycle caps `z_K` to a `K`-supported absolute cycle that pulls back
to a cycle of `sub K` (`pullbackDualityIntₗ_mem_cycles`); a relative coboundary `δg` caps `z_K` to
`(-1)^{j+1}•∂(g ⌢ z_K)` whose `K`-supported bounding chain is `capInt_relCoboundary_K_witness`, so the
pullback is a `sub K` boundary (`inclRangeEquiv_symm_mem_boundariesInt`). Integral mirror of
`SingularLocalDualityK.relativeDualityK`; the fixed-target `relativeDualityInt` is `incl ∘ D_K`. -/
noncomputable def relativeDualityKInt (k m : ℕ) (z : SingularChainInt X (k + m + 1))
    (hzK : z ∈ subspaceChainsInt K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m)) :
    RelativeCohomologyInt S k →ₗ[ℤ] Homology (sub K) (m + 1) :=
  Submodule.liftQ _ (relDualityKIntₗ S K z hzK hzS) (by
    intro a ha
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
    rw [LinearMap.mem_ker, relDualityKIntₗ_apply]
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
    cases k with
    | zero =>
        rw [show relCoboundaryRangeInt S 0 = (⊥ : Submodule ℤ (relCochainsInt S 0)) from rfl,
          Submodule.mem_bot] at ha
        have h0 : (a.1.1 : SingularCochainInt X 0) = 0 := by rw [ha]; rfl
        have hz0 : capInt a.1.1 z = (0 : SingularChainInt X (m + 1)) := by
          rw [h0, ← capIntₗ_apply, map_zero]; rfl
        have hpb : pullbackDualityIntₗ S K z hzK a = 0 := by
          apply chainIncl_injective K (m + 1)
          rw [chainIncl_pullbackDualityIntₗ, hz0, map_zero]
        rw [hpb]
        exact Submodule.zero_mem _
    | succ j =>
        rw [show relCoboundaryRangeInt S (j + 1) = LinearMap.range (relCoboundaryIntₗ S j) from rfl]
          at ha
        obtain ⟨g, hg⟩ := ha
        have hcob : (a.1.1 : SingularCochainInt X (j + 1)) = coboundary X j g.1 := by
          rw [← hg, relCoboundaryIntₗ_coe]
        obtain ⟨d, hdK, hbd⟩ :=
          capInt_relCoboundary_K_witness S K g.1 (relCochainInt_vanish S g) z hzK hzS
        have hc : capInt a.1.1 z ∈ subspaceChainsInt K (m + 1) :=
          capInt_mem_subspaceChainsInt K a.1.1 hzK
        have hpb : pullbackDualityIntₗ S K z hzK a
            = (inclRangeEquiv K (m + 1)).symm ⟨capInt a.1.1 z, hc⟩ := rfl
        rw [hpb]
        have hbd' : chainBoundary X (m + 1) d = capInt a.1.1 z := by rw [hbd, hcob]
        exact inclRangeEquiv_symm_mem_boundariesInt K m (capInt a.1.1 z) hc d hdK hbd')

/-- **Computation rule for `D_K`**: `[a] ↦ [a ⌢ z]_{sub K}`. -/
@[simp] theorem relativeDualityKInt_mk (k m : ℕ) (z : SingularChainInt X (k + m + 1))
    (hzK : z ∈ subspaceChainsInt K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m))
    (a : LinearMap.ker (relCoboundaryIntₗ S k)) :
    relativeDualityKInt S K k m z hzK hzS (RelativeCohomologyInt.mk S k a)
      = Homology.mk (sub K) (m + 1) ⟨pullbackDualityIntₗ S K z hzK a,
          pullbackDualityIntₗ_mem_cycles S K z hzK hzS a⟩ :=
  rfl

end SKEFTHawking.SingularLocalDualityKInt
