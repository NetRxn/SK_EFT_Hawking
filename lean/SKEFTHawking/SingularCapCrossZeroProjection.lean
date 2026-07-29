/-
# The degree-0-target cap `Hᵏ × Hₖ → H₀` and the degree-0-target cap-cross projection

Brick N2b of the `hBbord` → P23-nondeg → `hcompat` keystone (Phase 5q.H). The homology cap product
`SingularCapHomology.capH : Hᵏ(X) → H_{k+m+1}(X) → H_{m+1}(X)` always outputs degree `m+1 ≥ 1`; the
final application `H²(M) ⌢ H₂(M) → H₀(M)` needs the **degree-0-target corner**. This module builds

  `capHZero (k : ℕ) : Hᵏ(X) → Hₖ(X) → H₀(X)`   (`Hᵏ ⌢ Hₖ → H₀`)

(`cycles X 0 = ⊤`, so the target cycle condition is trivial) and, gated on the same normalization
residual `PrismDegNull` + absolute `fst_*` injectivity as `SingularCapCrossProjection`, the
degree-0-target cap-cross projection

  `(π* u) ⌢ ([z] × [I,∂I]) = (u ⌢ [z]) × [I,∂I]`   with the RHS the degree-0 cross `crossHZero`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SingularCapCrossZero
import SKEFTHawking.SingularCapCrossProjection
import SKEFTHawking.SingularCapHomology

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularKroneckerFunctoriality
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularPrism
open SKEFTHawking.SingularHomotopyInvariance (slice endMap_eq_mapChain)
open SKEFTHawking.SingularCapMapChain
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.SingularRelativeCapHomology
open SKEFTHawking.SingularCapCrossProjection
open SKEFTHawking.SingularCapCrossZero

namespace SKEFTHawking.SingularCapCrossZeroProjection

variable {X : TopCat} {j k m : ℕ}

/-! ## §1. The degree-0-target absolute cap `Hᵏ ⌢ Hₖ → H₀` -/

/-- **The cohomology-argument descent, degree-0 target.** For a `j`-cochain `g`, its coboundary `δg`
caps a `(j+1)`-**cycle** `z` (`∂z = 0`) to a `0`-**boundary**: `cap_leibniz` gives
`(δg) ⌢ z = ∂(g ⌢ z) + g ⌢ (∂z) = ∂(g ⌢ z)`, a boundary. The `m+1 = 0` corner of
`SingularCapHomology.cap_coboundary_cycle_mem_boundaries`; the cap-leibniz degrees collapse to `rfl`. -/
theorem cap_coboundary_cycle_mem_boundaries_zero (g : SingularCochain X j)
    (z : SingularChain X (j + 1)) (hz : chainBoundary X j z = 0) :
    cap (m := 0) (coboundary X j g) z ∈ boundaries X 0 := by
  refine ⟨cap (m := 1) g z, ?_⟩
  have hleib := cap_leibniz (a := g) (c := z) (m := 0) rfl
  rw [show ((rfl : j + 0 + 1 = j + 1 + 0) ▸ z : SingularChain X (j + 1 + 0)) = z from rfl,
    show chainBoundary X (j + 0) z = chainBoundary X j z from rfl, hz, map_zero, add_zero] at hleib
  exact hleib

/-- For a fixed `k`-cocycle `a`, `cap a` sends `k`-cycles to `0`-cycles (`cycles X 0 = ⊤`, trivial).
Packaged `ℤ/2`-linearly `Zₖ → Z₀`. -/
noncomputable def capZeroCyclesₗ (a : LinearMap.ker (coboundaryₗ X k)) :
    cycles X k →ₗ[ZMod 2] cycles X 0 :=
  LinearMap.restrict (cap (m := 0) a.1) (fun _ _ => Submodule.mem_top)

@[simp] theorem capZeroCyclesₗ_coe (a : LinearMap.ker (coboundaryₗ X k)) (z : cycles X k) :
    (capZeroCyclesₗ a z : SingularChain X 0) = cap (m := 0) a.1 (z : SingularChain X k) :=
  LinearMap.restrict_coe_apply _ _ _

/-- For a fixed `k`-cocycle `a`, `cap a` descends to `Hₖ(X) → H₀(X)`: it sends boundaries to
boundaries, `a ⌢ ∂w = ∂(a ⌢ w)` (`cap_cocycle_chainMap` at `m = 0`). -/
noncomputable def capZeroHomology (a : LinearMap.ker (coboundaryₗ X k)) :
    Homology X k →ₗ[ZMod 2] Homology X 0 :=
  Submodule.mapQ _ _ (capZeroCyclesₗ a) (by
    rintro ⟨z, hz⟩ hzb
    rw [Submodule.mem_comap]
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hzb
    obtain ⟨w, hw⟩ := hzb
    refine ⟨cap (m := 1) a.1 w, ?_⟩
    show chainBoundary X 0 (cap (m := 1) a.1 w) = cap (m := 0) a.1 z
    rw [cap_cocycle_chainMap (m := 0) a.1 (LinearMap.mem_ker.mp a.2) w]
    exact congrArg (cap a.1) hw)

@[simp] theorem capZeroHomology_mk (a : LinearMap.ker (coboundaryₗ X k)) (z : cycles X k) :
    capZeroHomology a (Homology.mk X k z) = Homology.mk X 0 (capZeroCyclesₗ a z) :=
  Submodule.mapQ_apply _ _ _ _

theorem capZeroCyclesₗ_add (a a' : LinearMap.ker (coboundaryₗ X k)) (z : cycles X k) :
    capZeroCyclesₗ (a + a') z = capZeroCyclesₗ a z + capZeroCyclesₗ a' z := by
  apply Subtype.ext
  simp only [capZeroCyclesₗ_coe, Submodule.coe_add]
  exact cap_add_cochain (k := k) (m := 0) a.1 a'.1 z.1

theorem capZeroCyclesₗ_smul (s : ZMod 2) (a : LinearMap.ker (coboundaryₗ X k)) (z : cycles X k) :
    capZeroCyclesₗ (s • a) z = s • capZeroCyclesₗ a z := by
  apply Subtype.ext
  simp only [capZeroCyclesₗ_coe, SetLike.val_smul]
  exact cap_smul_cochain (k := k) (m := 0) s a.1 z.1

theorem capZeroHomology_add (a a' : LinearMap.ker (coboundaryₗ X k)) :
    capZeroHomology (a + a') = capZeroHomology a + capZeroHomology a' := by
  ext x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show capZeroHomology (a + a') (Homology.mk X k z)
    = capZeroHomology a (Homology.mk X k z) + capZeroHomology a' (Homology.mk X k z)
  rw [capZeroHomology_mk, capZeroHomology_mk, capZeroHomology_mk, ← Homology.mk_add, capZeroCyclesₗ_add]

theorem capZeroHomology_smul (s : ZMod 2) (a : LinearMap.ker (coboundaryₗ X k)) :
    capZeroHomology (s • a) = s • capZeroHomology a := by
  ext x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show capZeroHomology (s • a) (Homology.mk X k z) = s • capZeroHomology a (Homology.mk X k z)
  rw [capZeroHomology_mk, capZeroHomology_mk, ← Homology.mk_smul, capZeroCyclesₗ_smul]

/-- `a ↦ capZeroHomology a`, packaged `ℤ/2`-linear in the cochain. -/
noncomputable def capZeroHomologyₗ :
    LinearMap.ker (coboundaryₗ X k) →ₗ[ZMod 2] (Homology X k →ₗ[ZMod 2] Homology X 0) where
  toFun := capZeroHomology
  map_add' := capZeroHomology_add
  map_smul' := capZeroHomology_smul

/-- **The degree-0-target cap product on (co)homology** `capHZero k : Hᵏ(X) → Hₖ(X) → H₀(X)` — capping
a `k`-cocycle class against a `k`-cycle class into `H₀`. The `m+1 = 0` corner of
`SingularCapHomology.capH`; well-defined modulo coboundaries by
`cap_coboundary_cycle_mem_boundaries_zero`. -/
noncomputable def capHZero (k : ℕ) :
    Cohomology X k →ₗ[ZMod 2] Homology X k →ₗ[ZMod 2] Homology X 0 :=
  Submodule.liftQ _ capZeroHomologyₗ (by
    intro a ha
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
    rw [LinearMap.mem_ker]
    ext x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.zero_apply]
    show capZeroHomology a (Homology.mk X k z) = 0
    rw [capZeroHomology_mk, Homology.mk_eq_zero]
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply, capZeroCyclesₗ_coe]
    cases k with
    | zero =>
        rw [show coboundaryRange X 0 = (⊥ : Submodule (ZMod 2) (SingularCochain X 0)) from rfl,
          Submodule.mem_bot] at ha
        rw [show (a.1 : SingularCochain X 0) = 0 from ha,
          show cap (m := 0) (0 : SingularCochain X 0) z.1 = 0 from by
            rw [← capₗ_apply, map_zero, LinearMap.zero_apply]]
        exact Submodule.zero_mem _
    | succ j =>
        have hzc : chainBoundary X j z.1 = 0 :=
          LinearMap.mem_ker.mp (z.2 : z.1 ∈ LinearMap.ker (chainBoundary X j))
        rw [show coboundaryRange X (j + 1) = LinearMap.range (coboundaryₗ X j) from rfl] at ha
        obtain ⟨g, hg⟩ := ha
        rw [← hg]
        exact cap_coboundary_cycle_mem_boundaries_zero g z.1 hzc)

@[simp] theorem capHZero_mk_mk (a : LinearMap.ker (coboundaryₗ X k)) (z : cycles X k) :
    capHZero k (Cohomology.mk X k a) (Homology.mk X k z) = Homology.mk X 0 (capZeroCyclesₗ a z) :=
  rfl

/-! ## §2. The degree-0-target equal-boundary and pushforward lemmas -/

variable {M : TopCat}

/-- **The boundary of `P := (fst^* g) ⌢ (prism graphHom z)`, degree-0 target** (`g` a `(k+1)`-cocycle,
`z` a `(k+1)`-cycle): `∂ P = end₁(g ⌢ z) + end₀(g ⌢ z)`. The `m+1 = 0` corner of
`SingularCapCrossProjection.boundary_cap_pullback_prismOp`. -/
theorem boundary_cap_pullback_prismOp_zero (g : SingularCochain M (k + 1))
    (hg : coboundaryₗ M (k + 1) g = 0) (z : SingularChain M (k + 1))
    (hz : chainBoundary M k z = 0) :
    chainBoundary (cyl M) 0
        (cap (m := 1) (pullbackCochainMap (fstCyl M) (k + 1) g) (prismOp (graphHom M) (k + 1) z))
      = mapChain (slice (graphHom M) 1) 0 (cap (m := 0) g z)
        + mapChain (slice (graphHom M) 0) 0 (cap (m := 0) g z) := by
  have hcoc := coboundary_pullback_fstCyl_eq_zero g hg
  have hkey : chainBoundary (cyl M) (k + 1) (prismOp (graphHom M) (k + 1) z)
      = endMap (graphHom M) 1 (k + 1) z + endMap (graphHom M) 0 (k + 1) z := by
    have h := prism_chainHomotopy (graphHom M) (n := k) z
    rw [hz, map_zero, add_zero] at h
    exact h
  rw [cap_cocycle_chainMap (m := 0) (pullbackCochainMap (fstCyl M) (k + 1) g) hcoc, hkey, map_add,
    cap_pullback_endMap (m := 0) g 1 z, cap_pullback_endMap (m := 0) g 0 z]

/-- **The boundary of `Q := prism graphHom (g ⌢ z)`, degree-0 target**: `∂ Q = end₁(g ⌢ z) + end₀(g ⌢ z)`.
Immediate from the degree-0 prism homotopy (`g ⌢ z` is a `0`-chain). -/
theorem boundary_prismOp_cap_zero (g : SingularCochain M (k + 1))
    (z : SingularChain M (k + 1)) :
    chainBoundary (cyl M) 0 (prismOp (graphHom M) 0 (cap (m := 0) g z))
      = mapChain (slice (graphHom M) 1) 0 (cap (m := 0) g z)
        + mapChain (slice (graphHom M) 0) 0 (cap (m := 0) g z) := by
  rw [prism_chainHomotopy_zero, endMap_eq_mapChain, endMap_eq_mapChain]

/-- **`fst_#` of `P`, degree-0 target** is `g ⌢ (prism projHom z)`. The `m+1 = 0` corner of
`SingularCapCrossProjection.mapChain_cap_pullback_prismOp`. -/
theorem mapChain_cap_pullback_prismOp_zero (g : SingularCochain M (k + 1))
    (z : SingularChain M (k + 1)) :
    mapChain (fstCyl M) 1
        (cap (m := 1) (pullbackCochainMap (fstCyl M) (k + 1) g) (prismOp (graphHom M) (k + 1) z))
      = cap (m := 1) g (prismOp (projHom M) (k + 1) z) := by
  rw [← cap_mapChain]
  congr 1
  exact mapChain_prismOp (fstCyl M) (graphHom M) (k + 1) z

/-- **`fst_#` of `Q`, degree-0 target** is `prism projHom (g ⌢ z)`. Pure `mapChain_prismOp`. -/
theorem mapChain_prismOp_cap_zero (g : SingularCochain M (k + 1))
    (z : SingularChain M (k + 1)) :
    mapChain (fstCyl M) 1 (prismOp (graphHom M) 0 (cap (m := 0) g z))
      = prismOp (projHom M) 0 (cap (m := 0) g z) :=
  mapChain_prismOp (fstCyl M) (graphHom M) 0 (cap (m := 0) g z)

/-- **The degree-0-target normalization residual `PrismDegNullZero`**: the base-level difference
`(g ⌢ prism projHom z) + prism projHom (g ⌢ z)` is an absolute `1`-boundary of `M`. The `m+1 = 0`
corner of `SingularCapCrossProjection.PrismDegNull`; the single classical residual (singular
normalization) of the degree-0-target cap-cross projection. -/
def PrismDegNullZero (g : SingularCochain M (k + 1)) (z : SingularChain M (k + 1)) : Prop :=
  cap (m := 1) g (prismOp (projHom M) (k + 1) z) + prismOp (projHom M) 0 (cap (m := 0) g z)
      ∈ boundaries M 1

/-- **`P + Q` is an absolute `1`-boundary of `M × I`, degree-0 target**, from `PrismDegNullZero` and
`fst_*` injectivity (at degree `1`). The `m+1 = 0` corner of
`SingularCapCrossProjection.cap_pullback_prismOp_add_mem_boundaries`. -/
theorem cap_pullback_prismOp_add_mem_boundaries_zero
    (g : LinearMap.ker (coboundaryₗ M (k + 1))) (z : cycles M (k + 1))
    (hfstinj : Function.Injective (Homology.map (fstCyl M) 1))
    (hnull : PrismDegNullZero g.1 z.1) :
    cap (m := 1) (pullbackCochainMap (fstCyl M) (k + 1) g.1) (prismOp (graphHom M) (k + 1) z.1)
        + prismOp (graphHom M) 0 (cap (m := 0) g.1 z.1)
      ∈ boundaries (cyl M) 1 := by
  have hgc : coboundaryₗ M (k + 1) g.1 = 0 := g.2
  have hz : chainBoundary M k z.1 = 0 := z.2
  have hcyc : chainBoundary (cyl M) 0
      (cap (m := 1) (pullbackCochainMap (fstCyl M) (k + 1) g.1) (prismOp (graphHom M) (k + 1) z.1)
        + prismOp (graphHom M) 0 (cap (m := 0) g.1 z.1)) = 0 := by
    rw [map_add, boundary_cap_pullback_prismOp_zero g.1 hgc z.1 hz, boundary_prismOp_cap_zero g.1 z.1]
    exact ZModModule.add_self _
  set d : SingularChain (cyl M) 1 :=
    cap (m := 1) (pullbackCochainMap (fstCyl M) (k + 1) g.1) (prismOp (graphHom M) (k + 1) z.1)
      + prismOp (graphHom M) 0 (cap (m := 0) g.1 z.1) with hd
  have hpush : mapChain (fstCyl M) 1 d
      = cap (m := 1) g.1 (prismOp (projHom M) (k + 1) z.1)
        + prismOp (projHom M) 0 (cap (m := 0) g.1 z.1) := by
    rw [hd, map_add, mapChain_cap_pullback_prismOp_zero, mapChain_prismOp_cap_zero]
  have hmap0 : Homology.map (fstCyl M) 1 (Homology.mk (cyl M) 1 ⟨d, hcyc⟩) = 0 := by
    rw [Homology.map_mk, Homology.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap,
      Submodule.coe_subtype, cyclesMap_coe, hpush]
    exact hnull
  have hd0 : Homology.mk (cyl M) 1 ⟨d, hcyc⟩ = 0 :=
    hfstinj (by rw [hmap0, map_zero])
  rw [Homology.mk_eq_zero] at hd0
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at hd0
  exact hd0

/-! ## §3. The degree-0-target cap-cross projection, from `PrismDegNullZero` -/

/-- **The degree-0-target cap-cross projection, from `PrismDegNullZero`.** For a `(k+1)`-cocycle `g`
and `(k+1)`-cycle `z` on `M`, the pulled-back cap of the prism cross equals the degree-0 cross of the
base cap: `(fst^* [g]) ⌢ ([z] × [I,∂I]) = ([g] ⌢ [z]) × [I,∂I]`, with the base cap landing in `H₀(M)`
(`capHZero`) and the RHS the degree-0 cross `crossHZero`. Gated on `PrismDegNullZero` (singular
normalization) and `fst_*` injectivity at degree `1`. The `m+1 = 0` corner of
`SingularCapCrossProjection.capRelH_crossH_of_prismDegNull`. -/
theorem capRelH_crossHZero_of_prismDegNullZero {S : Set ↑(cyl M)}
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) S)
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) S)
    (hfstinj : Function.Injective (Homology.map (fstCyl M) 1))
    (g : LinearMap.ker (coboundaryₗ M (k + 1))) (z : cycles M (k + 1))
    (hnull : PrismDegNullZero g.1 z.1) :
    capRelH (S := S) (k + 1) 0
        (Cohomology.mk (cyl M) (k + 1)
          ⟨pullbackCochainMap (fstCyl M) (k + 1) g.1, coboundary_pullback_fstCyl_eq_zero g.1 g.2⟩)
        (crossH h1 h0 k (Homology.mk M (k + 1) z))
      = crossHZero h1 h0 (capHZero (k + 1) (Cohomology.mk M (k + 1) g) (Homology.mk M (k + 1) z)) := by
  rw [crossH_mk]
  erw [capRelH_mk_mk]
  rw [capHZero_mk_mk, crossHZero_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub]
  have hval1 : (capRelCyclesₗ (m := 0)
        ⟨pullbackCochainMap (fstCyl M) (k + 1) g.1, coboundary_pullback_fstCyl_eq_zero g.1 g.2⟩
        (crossRelCycle h1 h0 k z) : RelativeChain S 1)
      = RelativeChain.mk S 1
        (cap (m := 1) (pullbackCochainMap (fstCyl M) (k + 1) g.1)
          (prismOp (graphHom M) (k + 1) z.1)) := by
    rw [capRelCyclesₗ_coe]; rfl
  have hval2 : ((⟨crossChainZeroLM (S := S)
          ((capZeroCyclesₗ g z : cycles M 0) : SingularChain M 0),
          crossChainZeroLM_mem_relCycles h1 h0 _⟩ : relCycles S 1) : RelativeChain S 1)
      = RelativeChain.mk S 1 (prismOp (graphHom M) 0 (cap (m := 0) g.1 z.1)) := rfl
  rw [hval1, hval2]
  have hchar : ∀ (a b : RelativeChain S 1), a - b = a + b := fun a b => by
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (ZModModule.add_self b)]
  have hcomb : RelativeChain.mk S 1
        (cap (m := 1) (pullbackCochainMap (fstCyl M) (k + 1) g.1) (prismOp (graphHom M) (k + 1) z.1))
      + RelativeChain.mk S 1 (prismOp (graphHom M) 0 (cap (m := 0) g.1 z.1))
      = RelativeChain.mk S 1
        (cap (m := 1) (pullbackCochainMap (fstCyl M) (k + 1) g.1) (prismOp (graphHom M) (k + 1) z.1)
          + prismOp (graphHom M) 0 (cap (m := 0) g.1 z.1)) := rfl
  rw [hchar, hcomb]
  exact relBoundaries_mk_of_boundaries _
    (cap_pullback_prismOp_add_mem_boundaries_zero g z hfstinj hnull)

end SKEFTHawking.SingularCapCrossZeroProjection
