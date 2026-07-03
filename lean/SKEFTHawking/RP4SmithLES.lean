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

/-! ## §4. The induced transfer `τ_* : Hₙ(ℝP⁴) → Hₙ(S⁴)`

`π_*` is the tower's `Homology.map mkC` (continuous-map functoriality); `τ_*` must be
hand-rolled — the transfer is a chain map not induced by any continuous map. -/

/-- The transfer preserves cycles. -/
theorem transferChain_mem_cycles {n : ℕ} {z : SingularChain (TopCat.of RP4) n}
    (hz : z ∈ cycles (TopCat.of RP4) n) : transferChain n z ∈ cycles (TopCat.of S4) n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
      show transferChain (m + 1) z ∈ LinearMap.ker (chainBoundary (TopCat.of S4) m)
      rw [LinearMap.mem_ker, chainBoundary_transferChain, LinearMap.mem_ker.mp hz, map_zero]

/-- The transfer preserves boundaries. -/
theorem transferChain_mem_boundaries {n : ℕ} {w : SingularChain (TopCat.of RP4) n}
    (hw : w ∈ boundaries (TopCat.of RP4) n) :
    transferChain n w ∈ boundaries (TopCat.of S4) n := by
  obtain ⟨u, rfl⟩ := hw
  exact ⟨transferChain (n + 1) u, chainBoundary_transferChain n u⟩

/-- The transfer on cycles `Zₙ(ℝP⁴) → Zₙ(S⁴)`. -/
noncomputable def transferCycles (n : ℕ) :
    cycles (TopCat.of RP4) n →ₗ[ZMod 2] cycles (TopCat.of S4) n :=
  (transferChain n).restrict (fun _ hz => transferChain_mem_cycles hz)

@[simp] theorem transferCycles_coe {n : ℕ} (z : cycles (TopCat.of RP4) n) :
    (transferCycles n z : SingularChain (TopCat.of S4) n)
      = transferChain n (z : SingularChain (TopCat.of RP4) n) := rfl

/-- **The homology transfer** `τ_* : Hₙ(ℝP⁴; ℤ/2) → Hₙ(S⁴; ℤ/2)`. -/
noncomputable def homTransfer (n : ℕ) :
    Homology (TopCat.of RP4) n →ₗ[ZMod 2] Homology (TopCat.of S4) n :=
  Submodule.mapQ _ _ (transferCycles n) (by
    rintro ⟨z, hz⟩ hzb
    rw [Submodule.mem_comap]
    exact transferChain_mem_boundaries hzb)

@[simp] theorem homTransfer_mk {n : ℕ} (z : cycles (TopCat.of RP4) n) :
    homTransfer n (Homology.mk (TopCat.of RP4) n z)
      = Homology.mk (TopCat.of S4) n (transferCycles n z) :=
  Submodule.mapQ_apply _ _ _ _

/-! ## §5. The six exactness facts of the Smith triangle

`… → Hₙ(ℝP⁴) →τ* Hₙ(S⁴) →π* Hₙ(ℝP⁴) →∂ Hₙ₋₁(ℝP⁴) → …` -/

private theorem mk_eq_zero_iff' {X : TopCat} {n : ℕ} (z : cycles X n) :
    Homology.mk X n z = 0 ↔ (z : SingularChain X n) ∈ boundaries X n := by
  refine (Submodule.Quotient.mk_eq_zero _).trans ?_
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]

/-- **`π_* ∘ τ_* = 0`** — descends the chain identity `π_# ∘ τ = 0`. -/
theorem homMap_homTransfer {n : ℕ} (w : Homology (TopCat.of RP4) n) :
    Homology.map mkC n (homTransfer n w) = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  show Homology.map mkC n (homTransfer n (Homology.mk (TopCat.of RP4) n z)) = 0
  rw [homTransfer_mk, Homology.map_mk, mk_eq_zero_iff', cyclesMap_coe, transferCycles_coe,
    mapChain_transferChain]
  exact Submodule.zero_mem _

/-- **Exactness at `Hₙ(S⁴)`**: `ker π_* = im τ_*`. Snake content: if `π_# y = ∂d`, correct `y` by
the boundary `∂(s d)` — the corrected cycle is killed by `π_#`, hence is `τ w`, and `[τ w] = [y]`. -/
theorem exact_homTransfer_homMap (n : ℕ) :
    Function.Exact (homTransfer n) (Homology.map mkC n) := by
  intro y₀
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y₀
  constructor
  · intro h
    have hb : mapChain mkC n (y : SingularChain (TopCat.of S4) n)
        ∈ boundaries (TopCat.of RP4) n := by
      have h2 : Homology.map mkC n (Homology.mk (TopCat.of S4) n y) = 0 := h
      rw [Homology.map_mk, mk_eq_zero_iff', cyclesMap_coe] at h2
      exact h2
    obtain ⟨d, hd⟩ := hb
    have hker : mapChain mkC n ((y : SingularChain (TopCat.of S4) n)
        + chainBoundary (TopCat.of S4) n (plusSection (n + 1) d)) = 0 := by
      rw [map_add, ← chainBoundary_mapChain, mapChain_plusSection, hd,
        ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]
    have hmem : (y : SingularChain (TopCat.of S4) n)
        + chainBoundary (TopCat.of S4) n (plusSection (n + 1) d)
        ∈ LinearMap.range (transferChain n) := by
      rw [← ker_mapChain_eq_range_transferChain]
      exact LinearMap.mem_ker.mpr hker
    obtain ⟨w, hw⟩ := hmem
    have hwcyc : w ∈ cycles (TopCat.of RP4) n := by
      cases n with
      | zero => exact Submodule.mem_top
      | succ m =>
          show w ∈ LinearMap.ker (chainBoundary (TopCat.of RP4) m)
          rw [LinearMap.mem_ker]
          apply transferChain_injective m
          have hdd : chainBoundary (TopCat.of S4) m (chainBoundary (TopCat.of S4) (m + 1)
              (plusSection (m + 1 + 1) d)) = 0 :=
            LinearMap.congr_fun (chainBoundary_comp_chainBoundary (TopCat.of S4) m) _
          rw [map_zero, ← chainBoundary_transferChain, hw, map_add, hdd, add_zero,
            LinearMap.mem_ker.mp y.2]
    refine ⟨Homology.mk (TopCat.of RP4) n ⟨w, hwcyc⟩, ?_⟩
    rw [homTransfer_mk]
    refine (Submodule.Quotient.eq _).mpr ?_
    rw [Submodule.submoduleOf, Submodule.mem_comap]
    show transferChain n w - (y : SingularChain (TopCat.of S4) n)
      ∈ boundaries (TopCat.of S4) n
    rw [hw]
    have hcanc : (y : SingularChain (TopCat.of S4) n)
        + chainBoundary (TopCat.of S4) n (plusSection (n + 1) d)
        - (y : SingularChain (TopCat.of S4) n)
        = chainBoundary (TopCat.of S4) n (plusSection (n + 1) d) := by abel
    rw [hcanc]
    exact ⟨plusSection (n + 1) d, rfl⟩
  · rintro ⟨w, hw⟩
    rw [← hw]
    exact homMap_homTransfer w

/-- **`∂ ∘ π_* = 0`**: for an `S⁴`-cycle `c`, the defect `s(π_# c) + c` is killed by `π_#`, hence
is `τ u`; then `∂(s(π_# c)) = τ(∂u)` exhibits the extraction as the boundary `∂u`. -/
theorem smithConnecting_homMap {k : ℕ} (y : Homology (TopCat.of S4) (k + 1)) :
    smithConnecting k (Homology.map mkC (k + 1) y) = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  show smithConnecting k (Homology.map mkC (k + 1) (Homology.mk (TopCat.of S4) (k + 1) c)) = 0
  rw [Homology.map_mk, smithConnecting_mk, mk_eq_zero_iff']
  have hker : mapChain mkC (k + 1)
      (plusSection (k + 1) (mapChain mkC (k + 1) (c : SingularChain (TopCat.of S4) (k + 1)))
        + (c : SingularChain (TopCat.of S4) (k + 1))) = 0 := by
    rw [map_add, mapChain_plusSection, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide,
      zero_smul]
  have hmem : plusSection (k + 1)
      (mapChain mkC (k + 1) (c : SingularChain (TopCat.of S4) (k + 1)))
      + (c : SingularChain (TopCat.of S4) (k + 1))
      ∈ LinearMap.range (transferChain (k + 1)) := by
    rw [← ker_mapChain_eq_range_transferChain]
    exact LinearMap.mem_ker.mpr hker
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, ?_⟩
  apply transferChain_injective k
  rw [transferChain_smithExtract, ← chainBoundary_transferChain, hu, map_add,
    LinearMap.mem_ker.mp c.2, add_zero]
  rfl

/-- **Exactness at the `π_*`-target `Hₖ₊₁(ℝP⁴)`**: `ker ∂ = im π_*`. Snake content: if the
extraction is `∂v`, then `s z + τ v` is an `S⁴`-cycle pushing forward to `z` on the nose. -/
theorem exact_homMap_smithConnecting (k : ℕ) :
    Function.Exact (Homology.map mkC (k + 1)) (smithConnecting k) := by
  intro x₀
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x₀
  constructor
  · intro h
    have hb : smithExtract k z ∈ boundaries (TopCat.of RP4) k := by
      have h2 : smithConnecting k (Homology.mk (TopCat.of RP4) (k + 1) z) = 0 := h
      rw [smithConnecting_mk, mk_eq_zero_iff'] at h2
      exact h2
    obtain ⟨v, hv⟩ := hb
    have hycyc : plusSection (k + 1) (z : SingularChain (TopCat.of RP4) (k + 1))
        + transferChain (k + 1) v ∈ cycles (TopCat.of S4) (k + 1) := by
      show _ ∈ LinearMap.ker (chainBoundary (TopCat.of S4) k)
      rw [LinearMap.mem_ker, map_add, chainBoundary_transferChain, hv,
        ← transferChain_smithExtract, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide,
        zero_smul]
    refine ⟨Homology.mk (TopCat.of S4) (k + 1) ⟨_, hycyc⟩, ?_⟩
    rw [Homology.map_mk]
    refine congrArg (Homology.mk (TopCat.of RP4) (k + 1)) (Subtype.ext ?_)
    rw [cyclesMap_coe]
    show mapChain mkC (k + 1) (plusSection (k + 1) (z : SingularChain (TopCat.of RP4) (k + 1))
      + transferChain (k + 1) v) = (z : SingularChain (TopCat.of RP4) (k + 1))
    rw [map_add, mapChain_plusSection, mapChain_transferChain, add_zero]
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact smithConnecting_homMap y

/-- **`τ_* ∘ ∂ = 0`**: `τ(extract z) = ∂(s z)` is a boundary on the nose. -/
theorem homTransfer_smithConnecting {k : ℕ} (x : Homology (TopCat.of RP4) (k + 1)) :
    homTransfer k (smithConnecting k x) = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show homTransfer k (smithConnecting k (Homology.mk (TopCat.of RP4) (k + 1) z)) = 0
  rw [smithConnecting_mk, homTransfer_mk, mk_eq_zero_iff']
  show transferChain k (smithExtract k z) ∈ boundaries (TopCat.of S4) k
  rw [transferChain_smithExtract]
  exact ⟨plusSection (k + 1) (z : SingularChain (TopCat.of RP4) (k + 1)), rfl⟩

/-- **Exactness at the `∂`-target `Hₖ(ℝP⁴)`**: `ker τ_* = im ∂`. Snake content: if `τ w = ∂u`,
then `π_# u` is a cycle whose extraction differs from `w` by the boundary `∂t` of the defect. -/
theorem exact_smithConnecting_homTransfer (k : ℕ) :
    Function.Exact (smithConnecting k) (homTransfer k) := by
  intro w₀
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w₀
  constructor
  · intro h
    have hb : transferChain k (w : SingularChain (TopCat.of RP4) k)
        ∈ boundaries (TopCat.of S4) k := by
      have h2 : homTransfer k (Homology.mk (TopCat.of RP4) k w) = 0 := h
      rw [homTransfer_mk, mk_eq_zero_iff'] at h2
      exact h2
    obtain ⟨u, hu⟩ := hb
    have hzcyc : mapChain mkC (k + 1) u ∈ cycles (TopCat.of RP4) (k + 1) := by
      show _ ∈ LinearMap.ker (chainBoundary (TopCat.of RP4) k)
      rw [LinearMap.mem_ker, chainBoundary_mapChain, hu, mapChain_transferChain]
    refine ⟨Homology.mk (TopCat.of RP4) (k + 1) ⟨_, hzcyc⟩, ?_⟩
    rw [smithConnecting_mk]
    have hker : mapChain mkC (k + 1) (plusSection (k + 1) (mapChain mkC (k + 1) u) + u) = 0 := by
      rw [map_add, mapChain_plusSection, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide,
        zero_smul]
    have hmem : plusSection (k + 1) (mapChain mkC (k + 1) u) + u
        ∈ LinearMap.range (transferChain (k + 1)) := by
      rw [← ker_mapChain_eq_range_transferChain]
      exact LinearMap.mem_ker.mpr hker
    obtain ⟨t, ht⟩ := hmem
    have hext : smithExtract k ⟨_, hzcyc⟩
        = chainBoundary (TopCat.of RP4) k t + (w : SingularChain (TopCat.of RP4) k) := by
      apply transferChain_injective k
      rw [transferChain_smithExtract, map_add, ← chainBoundary_transferChain, ht, map_add, hu,
        add_assoc, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul, add_zero]
    refine (Submodule.Quotient.eq _).mpr ?_
    rw [Submodule.submoduleOf, Submodule.mem_comap]
    show smithExtract k ⟨_, hzcyc⟩ - (w : SingularChain (TopCat.of RP4) k)
      ∈ boundaries (TopCat.of RP4) k
    rw [hext]
    have hcanc : chainBoundary (TopCat.of RP4) k t + (w : SingularChain (TopCat.of RP4) k)
        - (w : SingularChain (TopCat.of RP4) k) = chainBoundary (TopCat.of RP4) k t := by abel
    rw [hcanc]
    exact ⟨t, rfl⟩
  · rintro ⟨x, hx⟩
    rw [← hx]
    exact homTransfer_smithConnecting x

end SKEFTHawking.RP4SmithLES
