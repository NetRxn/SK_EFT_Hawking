import Mathlib
import SKEFTHawking.SingularRelativeDuality
import SKEFTHawking.SingularCapSupport
import SKEFTHawking.SingularSubspaceChainsEquiv

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-Dk) — the `H(K)`-valued duality map `D_K`

The framework-correct Poincaré-duality map for the Mayer–Vietoris induction lands in the homology of
the **compact `K` itself** (which *varies* with `K`), not the fixed absolute `H_{n-k}(M)`:
  `D_K : Hᵏ(M, M∖K) → H_{n-k}(sub K)`,    `[a] ↦ [a ⌢ z_K]`,
for `z_K` a fundamental cycle **supported in `K`** (`z ∈ subspaceChains K`) whose boundary lies in
`M∖K`. The cap of a relative cocycle with `z_K` is an absolute cycle (`cap_relCycle_isCycle`) **and**
supported in `K` (`cap_mem_subspaceChains`), so it pulls back (`subspaceChainsEquiv`) to a genuine cycle
of `sub K`, giving a class in `H_{n-k}(sub K)`.

This is the duality target that makes the 5-lemma ladder work: both rows
  `Hᵏ(M|A∩B) → Hᵏ(M|A)⊕Hᵏ(M|B) → Hᵏ(M|A∪B)` (top, rel cohomology MV)
  `H_{n-k}(A∩B) → H_{n-k}(A)⊕H_{n-k}(B) → H_{n-k}(A∪B)` (bottom, singular homology MV of the compacts)
vary with `K`. The fixed-target `SingularRelativeDuality.relativeDuality` is the composite
`(incl : H(K) → H(M)) ∘ D_K`.

Well-definedness modulo relative coboundaries uses the cap-locality of the **cochain's** cap: a relative
coboundary `δg` caps `z_K` to `∂(g ⌢ z_K)` where `g ⌢ z_K` is *also* `K`-supported
(`cap_mem_subspaceChains`), so the boundary pulls back to a `sub K` boundary
(`subspaceChainsEquiv_symm_mem_boundaries`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativeCap SKEFTHawking.SingularRelativeDuality
  SKEFTHawking.SingularCapSupport SKEFTHawking.SingularSubspaceChainsEquiv

namespace SKEFTHawking.SingularLocalDualityK

variable {X : TopCat} (S K : Set X)

/-! ## §1. Degree-cast helpers (local, mirroring `SingularRelativeDuality`'s private versions) -/

private theorem chainBoundary_cast {a b : ℕ} (z : SingularChain X (a + 1))
    (e : a + 1 = b + 1) (eb : a = b) :
    chainBoundary X b (e ▸ z) = eb ▸ chainBoundary X a z := by
  subst eb; rw [show e = rfl from rfl]

private theorem subspaceChains_cast {a b : ℕ} (c : SingularChain X a) (eb : a = b)
    (hc : c ∈ subspaceChains K a) : (eb ▸ c) ∈ subspaceChains K b := by
  subst eb; exact hc

/-! ## §2. The `K`-supported bounding-chain witness -/

/-- **The `K`-supported witness for the relative-coboundary cap.** For a `j`-cochain `g` vanishing on
`S` and a fundamental cycle `z` **supported in `K`** with `∂z ∈ subspaceChains S`, the cap
`(δg) ⌢ z = ∂(g ⌢ z)` where the bounding `(m+2)`-chain `g ⌢ z` is **also `K`-supported**
(`cap_mem_subspaceChains`). Strengthens `SingularRelativeDuality.cap_relCoboundary_mem_boundaries`
(which only records the absolute-boundary fact) by exposing the `K`-supported bounding chain — exactly
what `subspaceChainsEquiv_symm_mem_boundaries` needs to descend to a `sub K` boundary. -/
theorem cap_relCoboundary_K_witness {j m : ℕ} (g : SingularCochain X j)
    (hg : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk j))),
      g (simplexIncl S j τ) = 0)
    (z : SingularChain X (j + 1 + m + 1))
    (hzK : z ∈ subspaceChains K (j + 1 + m + 1))
    (hzS : chainBoundary X (j + 1 + m) z ∈ subspaceChains S (j + 1 + m)) :
    ∃ d : SingularChain X (m + 2), d ∈ subspaceChains K (m + 2) ∧
      chainBoundary X (m + 1) d = cap (m := m + 1) (coboundary X j g) z := by
  have e : j + 1 + m + 1 = j + (m + 1) + 1 := by omega
  refine ⟨cap (m := m + 2) g (e ▸ z), ?_, ?_⟩
  · -- `K`-support: `g ⌢ (e ▸ z)` with `e ▸ z` still `K`-supported (cap-locality).
    refine cap_mem_subspaceChains K g ?_
    exact subspaceChains_cast K z e hzK
  · -- The boundary identity, verbatim `cap_relCoboundary_mem_boundaries`.
    have h : j + (m + 1) + 1 = j + 1 + (m + 1) := by omega
    have hleib := cap_leibniz (a := g) (c := e ▸ z) (m := m + 1) h
    have ed : j + 1 + m = j + (m + 1) := by omega
    have hmid : cap (m := m + 1) g (chainBoundary X (j + (m + 1)) (e ▸ z)) = 0 := by
      apply cap_subspaceChain_eq_zero S g hg
      rw [chainBoundary_cast z e ed]
      exact subspaceChains_cast S _ ed hzS
    rw [hmid, add_zero] at hleib
    have hcancel : (h ▸ (e ▸ z) : SingularChain X (j + 1 + (m + 1))) = z := by
      rw [eqRec_eq_cast, eqRec_eq_cast, cast_cast, cast_eq]
    rw [hcancel] at hleib
    -- `hleib : ∂(g ⌢ z) = (δg) ⌢ z`; the goal is the same (degrees `m+1` defeq).
    exact hleib

/-! ## §3. The `H(sub K)`-valued duality map -/

/-- The cap `a ↦ a ⌢ z` of a relative cocycle, valued in the `K`-supported `(m+1)`-chains
`subspaceChains K (m+1)` (cap-locality, `cap_mem_subspaceChains`). -/
noncomputable def capSubKₗ {k m : ℕ} (z : SingularChain X (k + m + 1))
    (hzK : z ∈ subspaceChains K (k + m + 1)) :
    LinearMap.ker (relCoboundaryₗ S k) →ₗ[ZMod 2] subspaceChains K (m + 1) :=
  (capCochainₗ S z).codRestrict (subspaceChains K (m + 1))
    (fun a => cap_mem_subspaceChains K a.1.1 hzK)

@[simp] theorem capSubKₗ_coe {k m : ℕ} (z : SingularChain X (k + m + 1))
    (hzK : z ∈ subspaceChains K (k + m + 1)) (a : LinearMap.ker (relCoboundaryₗ S k)) :
    (capSubKₗ S K z hzK a : SingularChain X (m + 1)) = cap a.1.1 z := rfl

/-- The pulled-back duality chain `a ↦ (a ⌢ z) pulled back into `C(sub K)` — the `K`-supported cap
transported through the pullback equiv `subspaceChainsEquiv` to a genuine chain of the subspace `K`. -/
noncomputable def pullbackDualityₗ {k m : ℕ} (z : SingularChain X (k + m + 1))
    (hzK : z ∈ subspaceChains K (k + m + 1)) :
    LinearMap.ker (relCoboundaryₗ S k) →ₗ[ZMod 2] SingularChain (sub K) (m + 1) :=
  (subspaceChainsEquiv K (m + 1)).symm.toLinearMap.comp (capSubKₗ S K z hzK)

/-- `chainIncl` recovers the absolute cap from the pulled-back duality chain. -/
@[simp] theorem chainIncl_pullbackDualityₗ {k m : ℕ} (z : SingularChain X (k + m + 1))
    (hzK : z ∈ subspaceChains K (k + m + 1)) (a : LinearMap.ker (relCoboundaryₗ S k)) :
    chainIncl K (m + 1) (pullbackDualityₗ S K z hzK a) = cap a.1.1 z := by
  rw [pullbackDualityₗ, LinearMap.comp_apply, LinearEquiv.coe_coe,
    chainIncl_subspaceChainsEquiv_symm, capSubKₗ_coe]

/-- The pulled-back duality chain is a **cycle of `sub K`**: `chainIncl` is an injective chain map and
the absolute cap `a ⌢ z` is an absolute cycle (`cap_relCycle_isCycle`). -/
theorem pullbackDualityₗ_mem_cycles {k m : ℕ} (z : SingularChain X (k + m + 1))
    (hzK : z ∈ subspaceChains K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (a : LinearMap.ker (relCoboundaryₗ S k)) :
    pullbackDualityₗ S K z hzK a ∈ cycles (sub K) (m + 1) := by
  have hcyc : chainBoundary X m (cap a.1.1 z) = 0 :=
    cap_relCycle_isCycle S a.1.1 (relCochain_vanish S a.1) (relCocycle_coboundary_zero S a) hzS
  show chainBoundary (sub K) m (pullbackDualityₗ S K z hzK a) = 0
  apply chainIncl_injective K m
  rw [chainIncl_chainBoundary, chainIncl_pullbackDualityₗ, hcyc, map_zero]

/-- The cycle-level `H(sub K)`-valued duality map `a ↦ [a ⌢ z]_{sub K}`. -/
noncomputable def relDualityKₗ {k m : ℕ} (z : SingularChain X (k + m + 1))
    (hzK : z ∈ subspaceChains K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m)) :
    LinearMap.ker (relCoboundaryₗ S k) →ₗ[ZMod 2] Homology (sub K) (m + 1) :=
  ((boundaries (sub K) (m + 1)).submoduleOf (cycles (sub K) (m + 1))).mkQ.comp
    ((pullbackDualityₗ S K z hzK).codRestrict (cycles (sub K) (m + 1))
      (pullbackDualityₗ_mem_cycles S K z hzK hzS))

@[simp] theorem relDualityKₗ_apply {k m : ℕ} (z : SingularChain X (k + m + 1))
    (hzK : z ∈ subspaceChains K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (a : LinearMap.ker (relCoboundaryₗ S k)) :
    relDualityKₗ S K z hzK hzS a
      = Homology.mk (sub K) (m + 1) ⟨pullbackDualityₗ S K z hzK a,
          pullbackDualityₗ_mem_cycles S K z hzK hzS a⟩ := rfl

/-- **The `H(sub K)`-valued relative Poincaré-duality map** `D_K : Hᵏ(M, S) → H_{m+1}(sub K)`,
`[a] ↦ [a ⌢ z_K]`, for a fundamental cycle `z_K` **supported in `K`** (`z ∈ subspaceChains K`) whose
boundary lies in `S = M∖K`. Well-defined: a relative cocycle caps `z_K` to a `K`-supported absolute
cycle that pulls back to a cycle of `sub K` (`pullbackDualityₗ_mem_cycles`); a relative coboundary `δg`
caps `z_K` to `∂(g ⌢ z_K)` whose bounding chain `g ⌢ z_K` is itself `K`-supported
(`cap_relCoboundary_K_witness`), so the pullback is a `sub K` boundary
(`subspaceChainsEquiv_symm_mem_boundaries`). This is the *varying*-target duality map of the
Mayer–Vietoris `5`-lemma ladder; `SingularRelativeDuality.relativeDuality` is `incl ∘ D_K`. -/
noncomputable def relativeDualityK (k m : ℕ) (z : SingularChain X (k + m + 1))
    (hzK : z ∈ subspaceChains K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m)) :
    RelativeCohomology S k →ₗ[ZMod 2] Homology (sub K) (m + 1) :=
  Submodule.liftQ _ (relDualityKₗ S K z hzK hzS) (by
    intro a ha
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
    rw [LinearMap.mem_ker, relDualityKₗ_apply]
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
    cases k with
    | zero =>
        rw [show relCoboundaryRange S 0 = (⊥ : Submodule (ZMod 2) (relCochains S 0)) from rfl,
          Submodule.mem_bot] at ha
        have h0 : (a.1.1 : SingularCochain X 0) = 0 := by rw [ha]; rfl
        -- `cap 0 z = 0`, so the pulled-back chain is `0`, a boundary.
        have hz0 : cap a.1.1 z = (0 : SingularChain X (m + 1)) := by
          rw [h0, ← capₗ_apply, map_zero]; rfl
        have hpb : pullbackDualityₗ S K z hzK a = 0 := by
          apply chainIncl_injective K (m + 1)
          rw [chainIncl_pullbackDualityₗ, hz0, map_zero]
        rw [hpb]
        exact Submodule.zero_mem _
    | succ j =>
        rw [show relCoboundaryRange S (j + 1) = LinearMap.range (relCoboundaryₗ S j) from rfl] at ha
        obtain ⟨g, hg⟩ := ha
        have hcob : (a.1.1 : SingularCochain X (j + 1)) = coboundary X j g.1 := by
          rw [← hg, relCoboundaryₗ_coe]
        -- The `K`-supported bounding chain witness for the coboundary cap.
        obtain ⟨d, hdK, hbd⟩ := cap_relCoboundary_K_witness S K g.1 (relCochain_vanish S g) z hzK hzS
        -- The pulled-back duality chain is a `sub K` boundary, via the transfer lemma.
        have hc : cap a.1.1 z ∈ subspaceChains K (m + 1) := cap_mem_subspaceChains K a.1.1 hzK
        have hpb : pullbackDualityₗ S K z hzK a
            = (subspaceChainsEquiv K (m + 1)).symm ⟨cap a.1.1 z, hc⟩ := rfl
        rw [hpb]
        -- Rewrite `cap a.1.1 z = cap (δg) z` so the witness `d` bounds it.
        have hbd' : chainBoundary X (m + 1) d = cap a.1.1 z := by rw [hbd, hcob]
        exact subspaceChainsEquiv_symm_mem_boundaries K m (cap a.1.1 z) hc d hdK hbd')

/-- **Computation rule for `D_K`**: `[a] ↦ [a ⌢ z]_{sub K}`. -/
@[simp] theorem relativeDualityK_mk (k m : ℕ) (z : SingularChain X (k + m + 1))
    (hzK : z ∈ subspaceChains K (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (a : LinearMap.ker (relCoboundaryₗ S k)) :
    relativeDualityK S K k m z hzK hzS (RelativeCohomology.mk S k a)
      = Homology.mk (sub K) (m + 1) ⟨pullbackDualityₗ S K z hzK a,
          pullbackDualityₗ_mem_cycles S K z hzK hzS a⟩ :=
  rfl

end SKEFTHawking.SingularLocalDualityK
