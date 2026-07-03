import Mathlib
import SKEFTHawking.RP4Transfer

/-!
# Phase 5q.G (B-arc, M2-e) — the Smith long exact sequence of the antipodal double cover

The chain-level short exact sequence `0 → Cₙ(ℝP⁴) →τ Cₙ(S⁴) →π Cₙ(ℝP⁴) → 0` (M2-d) descends
to the **Smith long exact sequence** in mod-2 homology. The snake construction is made concrete
by the **plus-lift linear section** `s` of `π_#` (`σ ↦ liftPlus σ`, extended linearly — a
section of modules, *not* a chain map; its failure to commute with `∂` *is* the connecting
homomorphism): for a cycle `z` of `ℝP⁴`, the chain `∂(s z)` is killed by `π_#`
(`π∂s = ∂πs = ∂z = 0`), hence lies in `range τ = ker π_#`, and its unique `τ`-preimage is the
connecting value. No quotient chain complex is needed — `τ`-injectivity replaces it.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.RP4PointSet SKEFTHawking.RP4Covering SKEFTHawking.RP4Transfer
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.RP4SmithLES

/-! ## §1. The plus-lift section of `π_#` -/

/-- **The plus-lift linear section** `s : Cₙ(ℝP⁴) → Cₙ(S⁴)`, `σ ↦ liftPlus σ` extended linearly.
A module section of `π_#` (`mapChain_plusSection`) but *not* a chain map — the defect
`∂ ∘ s − s ∘ ∂` generates the Smith connecting homomorphism. -/
noncomputable def plusSection (n : ℕ) :
    SingularChain (TopCat.of RP4) n →ₗ[ZMod 2] SingularChain (TopCat.of S4) n :=
  Finsupp.linearCombination (ZMod 2) (fun σ => Finsupp.single (liftPlus σ) 1)

@[simp] theorem plusSection_single {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) (a : ZMod 2) :
    plusSection n (Finsupp.single σ a) = Finsupp.single (liftPlus σ) a := by
  rw [plusSection, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- `π_# ∘ s = id` — the plus-lift is a genuine module section of the pushforward. -/
theorem mapChain_plusSection {n : ℕ} (c : SingularChain (TopCat.of RP4) n) :
    mapChain mkC n (plusSection n c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add c d hc hd => rw [map_add, map_add, hc, hd]
  | single σ a => rw [plusSection_single, mapChain_single, mapSimplex_liftPlus]

/-! ## §2. The boundary extraction (the concrete snake) -/

/-- The transfer as a linear equivalence onto its range (`τ` is injective, M2-d). -/
noncomputable def transferEquivRange (n : ℕ) :
    SingularChain (TopCat.of RP4) n ≃ₗ[ZMod 2] LinearMap.range (transferChain n) :=
  LinearEquiv.ofInjective (transferChain n) (transferChain_injective n)

@[simp] theorem transferEquivRange_apply {n : ℕ} (c : SingularChain (TopCat.of RP4) n) :
    (transferEquivRange n c : SingularChain (TopCat.of S4) n) = transferChain n c := rfl

/-- For a cycle `z` of `ℝP⁴`, the boundary of its plus-lift is killed by `π_#`. -/
theorem mapChain_chainBoundary_plusSection {k : ℕ} (z : cycles (TopCat.of RP4) (k + 1)) :
    mapChain mkC k (chainBoundary (TopCat.of S4) k (plusSection (k + 1) z.1)) = 0 := by
  rw [← chainBoundary_mapChain, mapChain_plusSection]
  exact LinearMap.mem_ker.mp z.2

/-- `∂(s z) ∈ range τ` — the snake membership, through `ker π_# = range τ`. -/
theorem chainBoundary_plusSection_mem_range {k : ℕ} (z : cycles (TopCat.of RP4) (k + 1)) :
    chainBoundary (TopCat.of S4) k (plusSection (k + 1) z.1)
      ∈ LinearMap.range (transferChain k) := by
  rw [← ker_mapChain_eq_range_transferChain]
  exact LinearMap.mem_ker.mpr (mapChain_chainBoundary_plusSection z)

/-- **The Smith boundary extraction**: the unique `τ`-preimage of `∂(s z)` — the chain-level
connecting map, linear in the cycle. -/
noncomputable def smithExtract (k : ℕ) :
    cycles (TopCat.of RP4) (k + 1) →ₗ[ZMod 2] SingularChain (TopCat.of RP4) k :=
  (transferEquivRange k).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (transferChain k))
      ((chainBoundary (TopCat.of S4) k) ∘ₗ (plusSection (k + 1)) ∘ₗ
        (cycles (TopCat.of RP4) (k + 1)).subtype)
      (fun z => chainBoundary_plusSection_mem_range z)

/-- The defining property of the extraction: `τ(smithExtract z) = ∂(s z)`. -/
theorem transferChain_smithExtract {k : ℕ} (z : cycles (TopCat.of RP4) (k + 1)) :
    transferChain k (smithExtract k z)
      = chainBoundary (TopCat.of S4) k (plusSection (k + 1) z.1) := by
  have h := congrArg (Subtype.val)
    ((transferEquivRange k).apply_symm_apply
      ⟨chainBoundary (TopCat.of S4) k (plusSection (k + 1) z.1),
        chainBoundary_plusSection_mem_range z⟩)
  rw [transferEquivRange_apply] at h
  exact h

/-- **The extraction is a cycle**: `τ(∂ extract) = ∂(τ extract) = ∂∂(s z) = 0` and `τ` is
injective. -/
theorem smithExtract_mem_cycles {k : ℕ} (z : cycles (TopCat.of RP4) (k + 1)) :
    smithExtract k z ∈ cycles (TopCat.of RP4) k := by
  cases k with
  | zero => exact Submodule.mem_top
  | succ m =>
      show smithExtract (m + 1) z ∈ LinearMap.ker (chainBoundary (TopCat.of RP4) m)
      rw [LinearMap.mem_ker]
      apply transferChain_injective m
      rw [map_zero, ← chainBoundary_transferChain, transferChain_smithExtract]
      exact LinearMap.congr_fun (chainBoundary_comp_chainBoundary (TopCat.of S4) m) _

/-! ## §3. Descent to homology — the Smith connecting homomorphism -/

/-- **The extraction kills boundaries** (snake well-definedness): if `z = ∂w`, the defect
`s(∂w) + ∂(s w)` is killed by `π_#`, so it is `τ v` for some `v`, and then
`∂(s z) = ∂(τ v) = τ(∂ v)` exhibits the extraction as the boundary `∂ v`. -/
theorem smithExtract_mem_boundaries {k : ℕ} (z : cycles (TopCat.of RP4) (k + 1))
    (hz : z.1 ∈ boundaries (TopCat.of RP4) (k + 1)) :
    smithExtract k z ∈ boundaries (TopCat.of RP4) k := by
  obtain ⟨w, hw⟩ := hz
  have hker : mapChain mkC (k + 1) (plusSection (k + 1) z.1
      + chainBoundary (TopCat.of S4) (k + 1) (plusSection (k + 1 + 1) w)) = 0 := by
    rw [map_add, mapChain_plusSection, ← chainBoundary_mapChain, mapChain_plusSection, hw,
      ← two_smul (ZMod 2) z.1, show (2 : ZMod 2) = 0 by decide, zero_smul]
  have hmem : plusSection (k + 1) z.1
      + chainBoundary (TopCat.of S4) (k + 1) (plusSection (k + 1 + 1) w)
      ∈ LinearMap.range (transferChain (k + 1)) := by
    rw [← ker_mapChain_eq_range_transferChain]
    exact LinearMap.mem_ker.mpr hker
  obtain ⟨v, hv⟩ := hmem
  refine ⟨v, ?_⟩
  apply transferChain_injective k
  have hdd : chainBoundary (TopCat.of S4) k (chainBoundary (TopCat.of S4) (k + 1)
      (plusSection (k + 1 + 1) w)) = 0 :=
    LinearMap.congr_fun (chainBoundary_comp_chainBoundary (TopCat.of S4) k) _
  rw [transferChain_smithExtract, ← chainBoundary_transferChain, hv, map_add, hdd, add_zero]

/-- The extraction as a map into `k`-homology, on `(k+1)`-cycles. -/
noncomputable def smithConnectingLift (k : ℕ) :
    cycles (TopCat.of RP4) (k + 1) →ₗ[ZMod 2] Homology (TopCat.of RP4) k :=
  (Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (cycles (TopCat.of RP4) k) (smithExtract k)
    (fun z => smithExtract_mem_cycles z)

theorem smithConnectingLift_apply {k : ℕ} (z : cycles (TopCat.of RP4) (k + 1)) :
    smithConnectingLift k z
      = Homology.mk (TopCat.of RP4) k ⟨smithExtract k z, smithExtract_mem_cycles z⟩ := rfl

/-- **The Smith connecting homomorphism** `∂ : H_{k+1}(ℝP⁴; ℤ/2) → H_k(ℝP⁴; ℤ/2)` —
`[z] ↦ [τ⁻¹(∂(s z))]`, descended through the homology quotient. -/
noncomputable def smithConnecting (k : ℕ) :
    Homology (TopCat.of RP4) (k + 1) →ₗ[ZMod 2] Homology (TopCat.of RP4) k :=
  Submodule.liftQ _ (smithConnectingLift k) (by
    intro z hz
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hz
    rw [LinearMap.mem_ker, smithConnectingLift_apply]
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
    exact smithExtract_mem_boundaries z hz)

/-- The connecting map computes on classes: `∂[z] = [τ⁻¹(∂(s z))]`. -/
theorem smithConnecting_mk {k : ℕ} (z : cycles (TopCat.of RP4) (k + 1)) :
    smithConnecting k (Homology.mk (TopCat.of RP4) (k + 1) z)
      = Homology.mk (TopCat.of RP4) k ⟨smithExtract k z, smithExtract_mem_cycles z⟩ :=
  Submodule.liftQ_apply _ _ _

end SKEFTHawking.RP4SmithLES
