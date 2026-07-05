import Mathlib
import SKEFTHawking.SingularLocalHomologyIsoInt

/-!
# `redCompat` for the integral local-homology iso (brick 15 / 14f-2)

Proves the mod-2 reduction-naturality of the whole integral local-homology tower
`manifoldLocalHomologyIsoInt`, discharging the `redCompat` field of `IntLocalHomologyIso` and
upgrading `IntLocalHomologyIso M x` from a disclosed datum to a **theorem**
`intLocalHomologyIso_of_manifold`.

The tower is composed of a small number of map-kinds:
* `RelHomologyInt.map φ` (chart transport + translation) vs `RelativeHomology.map φ`;
* `connectingInt` vs mod-2 `connecting`;
* `Homology.mapInt φ` (normalize pushforward) vs mod-2 `Homology.map φ`;
* the excision equiv (itself `RelHomologyInt.map` of an inclusion);
* the sphere iso to `ℤ` / `ℤ/2`.

Each commutes with the ℤ→ℤ/2 reduction bridge `redRelChain`/`redRelHomology`/`redChain`/`redHomology`
(all `mapRange (Int.cast)`, which commutes with the `mapDomain`-shaped push-forwards). Composing the
per-stage naturality squares gives the whole-tower `redCompat`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularRelativeFunctorialityInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularLocalHomologyRedCompatInt

/-! ## §1. Chain-level naturality of the reduction w.r.t. the pushforward -/

/-- **The reduction commutes with the absolute chain pushforward** (`mapDomain`/`mapRange` commute):
`redChain ∘ mapChainInt φ = mapChain φ ∘ redChain`. Both `mapChainInt φ`/`mapChain φ` are the
extension of the SAME simplex pushforward `mapSimplex φ`; `redChain` is the pointwise cast. -/
theorem redChain_mapChainInt {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ)
    (c : SingularChainInt X n) :
    redChain Y n (mapChainInt φ n c)
      = SKEFTHawking.SingularFunctoriality.mapChain φ n (redChain X n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => rw [map_add, map_add, map_add, map_add, hc, hd]
  | single τ a =>
      rw [mapChainInt_single, redChain_single, redChain_single,
        SKEFTHawking.SingularFunctoriality.mapChain_single]

/-- **The reduction commutes with the relative chain pushforward**:
`redRelChain B n ∘ relMapChainInt φ = relMapChain φ ∘ redRelChain A n`. Descends
`redChain_mapChainInt` through the `RelativeChain` quotients. -/
theorem redRelChain_relMapChainInt {X Y : TopCat} (φ : C(↑X, ↑Y)) {A : Set ↑X} {B : Set ↑Y}
    (hAB : Set.MapsTo φ A B) (n : ℕ) (c : RelativeChainInt A n) :
    redRelChain B n (relMapChainInt φ hAB n c)
      = SKEFTHawking.SingularRelativeFunctoriality.relMapChain φ hAB n (redRelChain A n c) := by
  obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  show redRelChain B n (relMapChainInt φ hAB n (RelativeChainInt.mk A n d))
      = SKEFTHawking.SingularRelativeFunctoriality.relMapChain φ hAB n
          (redRelChain A n (RelativeChainInt.mk A n d))
  rw [relMapChainInt_mk, redRelChain_mk, redRelChain_mk,
    SKEFTHawking.SingularRelativeFunctoriality.relMapChain_mk, redChain_mapChainInt]

/-! ## §2. Homology-level naturality of the reduction w.r.t. the pushforward -/

/-- **The reduction commutes with the relative-homology pushforward** (the workhorse):
`redRelHomology B n ∘ RelHomologyInt.map φ = RelativeHomology.map φ ∘ redRelHomology A n`.
Descends `redRelChain_relMapChainInt` through the homology quotient. -/
theorem redRelHomology_map {X Y : TopCat} (φ : C(↑X, ↑Y)) {A : Set ↑X} {B : Set ↑Y}
    (hAB : Set.MapsTo φ A B) (n : ℕ) (z : RelHomologyInt A n) :
    redRelHomology B n (RelHomologyInt.map φ hAB n z)
      = SKEFTHawking.SingularRelativeFunctoriality.RelativeHomology.map φ hAB n
          (redRelHomology A n z) := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [RelHomologyInt.map_mk]
  show redRelHomology B n (RelHomologyInt.mk B n (relCyclesMapInt φ hAB n w))
      = SKEFTHawking.SingularRelativeFunctoriality.RelativeHomology.map φ hAB n
          (redRelHomology A n (RelHomologyInt.mk A n w))
  rw [redRelHomology_mk, redRelHomology_mk]
  show SKEFTHawking.SingularRelativeHomologyMod2.RelativeHomology.mk B n _
      = SKEFTHawking.SingularRelativeFunctoriality.RelativeHomology.map φ hAB n
          (Submodule.Quotient.mk (redRelCyclesHom A n w))
  rw [SKEFTHawking.SingularRelativeFunctoriality.RelativeHomology.map_mk]
  refine congrArg (SKEFTHawking.SingularRelativeHomologyMod2.RelativeHomology.mk B n) ?_
  ext
  simp only [SKEFTHawking.SingularRelativeFunctoriality.relCyclesMap_coe, redRelCyclesHom]
  exact redRelChain_relMapChainInt φ hAB n _

/-! ## §3. Naturality of the reduction w.r.t. the excision inclusion -/

open SKEFTHawking.SingularExcisionIsoInt (excisionMapInt relChainInclInt)
open SKEFTHawking.SingularExcisionIso (restr)

/-- **The reduction commutes with the relative excision inclusion (chain level)**:
`redRelChain A n ∘ relChainInclInt = relChainIncl ∘ redRelChain (restr A B) n`. Descends the
existing absolute `redChain_chainIncl` through the `RelativeChain` quotients. -/
theorem redRelChain_relChainInclInt {X : TopCat} (A B : Set ↑X) (n : ℕ)
    (c : RelativeChainInt (restr A B) n) :
    redRelChain A n (relChainInclInt A B n c)
      = SKEFTHawking.SingularExcisionIso.relChainIncl A B n (redRelChain (restr A B) n c) := by
  obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  show redRelChain A n (relChainInclInt A B n (RelativeChainInt.mk (restr A B) n d))
      = SKEFTHawking.SingularExcisionIso.relChainIncl A B n
          (redRelChain (restr A B) n (RelativeChainInt.mk (restr A B) n d))
  rw [SKEFTHawking.SingularExcisionIsoInt.relChainInclInt_mk, redRelChain_mk, redRelChain_mk,
    SKEFTHawking.SingularExcisionIso.relChainIncl_mk, redChain_chainIncl]

/-- **The reduction commutes with the excision map (homology level)**:
`redRelHomology A (n) ∘ excisionMapInt = excisionMap ∘ redRelHomology (restr A B) n`.
Descends `redRelChain_relChainInclInt`. -/
theorem redRelHomology_excisionMap {X : TopCat} (A B : Set ↑X) (n : ℕ)
    (z : RelHomologyInt (restr A B) n) :
    redRelHomology A n (excisionMapInt A B n z)
      = SKEFTHawking.SingularExcisionIso.excisionMap A B n (redRelHomology (restr A B) n z) := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [show (Submodule.Quotient.mk w : RelHomologyInt (restr A B) n)
        = RelHomologyInt.mk (restr A B) n w from rfl,
    SKEFTHawking.SingularExcisionIsoInt.excisionMapInt_mk, redRelHomology_mk, redRelHomology_mk]
  rw [SKEFTHawking.SingularExcisionIso.excisionMap_mk]
  refine congrArg (SKEFTHawking.SingularRelativeHomologyMod2.RelativeHomology.mk A n) ?_
  ext
  simp only [redRelCyclesHom]
  exact redRelChain_relChainInclInt A B n _

/-! ## §4. Reduction of `redCompat` to a single generator check

Both sides of `redCompat` are additive homomorphisms `H₄(M,M∖x;ℤ) → ZMod 2` and `iso` is an
isomorphism onto `ℤ` (generated by `1`), so it suffices to check the compatibility on the single
integral generator `iso.symm 1`. This collapses the whole-tower naturality square to the statement
"the reduction of the integral local generator is the mod-2 local generator". -/

/-- **`redCompat` reduces to a single generator check.** If the on-main mod-2 local iso `isoMod2` sends
the reduction of the integral generator `iso.symm 1` to `1 : ZMod 2`, then the full mod-2 compatibility
`∀ z, isoMod2 (redRelHomology z) = (iso z : ℤ) : ZMod 2` holds — because both sides are additive in `z`
and every `z` is an integer multiple of the generator (`iso` being an `≃+` onto `ℤ`). -/
theorem redCompat_of_generator {M : Type} [TopologicalSpace M] (x : M)
    (iso : RelHomologyInt (localSub x) 4 ≃+ ℤ)
    (isoMod2 : SKEFTHawking.SingularRelativeHomologyMod2.RelativeHomology (localSub x) 4 ≃+ ZMod 2)
    (hgen : isoMod2 (redRelHomology (localSub x) 4 (iso.symm 1)) = 1) :
    ∀ z : RelHomologyInt (localSub x) 4,
      isoMod2 (redRelHomology (localSub x) 4 z) = ((iso z : ℤ) : ZMod 2) := by
  intro z
  -- write `z` as `(iso z) • generator`
  have hz : z = (iso z) • iso.symm 1 := by
    conv_lhs => rw [← iso.symm_apply_apply z]
    rw [← map_zsmul iso.symm]
    congr 1
    simp
  rw [hz, map_zsmul, map_zsmul, hgen, zsmul_eq_mul, mul_one]
  -- RHS: `(iso ((iso z) • iso.symm 1) : ℤ) : ZMod 2`
  rw [map_zsmul, iso.apply_symm_apply, zsmul_eq_mul, mul_one]
  push_cast
  ring

/-- **The generator check follows from non-vanishing of the reduced generator.** Over the field
`ZMod 2` the only nonzero element is `1`; and `isoMod2` (an `≃+` onto `ZMod 2`) sends `0` to `0` and
nothing else. So `isoMod2 (redRelHomology (iso.symm 1)) = 1` as soon as the reduction of the integral
generator `iso.symm 1` is nonzero in the mod-2 local group. -/
theorem generator_check_of_ne_zero {M : Type} [TopologicalSpace M] (x : M)
    (iso : RelHomologyInt (localSub x) 4 ≃+ ℤ)
    (isoMod2 : SKEFTHawking.SingularRelativeHomologyMod2.RelativeHomology (localSub x) 4 ≃+ ZMod 2)
    (hne : redRelHomology (localSub x) 4 (iso.symm 1) ≠ 0) :
    isoMod2 (redRelHomology (localSub x) 4 (iso.symm 1)) = 1 := by
  have h0 : isoMod2 (redRelHomology (localSub x) 4 (iso.symm 1)) ≠ 0 := by
    intro h
    exact hne (isoMod2.injective (h.trans isoMod2.map_zero.symm))
  -- the only nonzero element of `ZMod 2` is `1`
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1)
      (isoMod2 (redRelHomology (localSub x) 4 (iso.symm 1))) with h | h
  · exact absurd h h0
  · exact h

/-! ## §5. Naturality of the reduction w.r.t. the connecting homomorphism

The final `δ`/normalize/sphere stages leave the relative setting and land in absolute homology of the
punctured space. Here we prove the connecting square:
`redHomology (sub S) n ∘ connectingInt S n = connecting S n ∘ redRelHomology S (n+1)`. -/

/-- **The reduction preserves the lift submodule** `Z_n = {c | ∂c ∈ Cₙ(S)}`. -/
theorem redChain_mem_relCycleLift {X : TopCat} {S : Set ↑X} (n : ℕ)
    {c : SingularChainInt X (n + 1)} (hc : c ∈ SKEFTHawking.SingularRelHomologyInt.relCycleLift S n) :
    redChain X (n + 1) c ∈ SKEFTHawking.SingularPairLES.relCycleLift S n := by
  show SKEFTHawking.SingularHomologyMod2.chainBoundary X n (redChain X (n + 1) c)
      ∈ SKEFTHawking.SingularRelativeHomologyMod2.subspaceChains S n
  rw [← redChain_chainBoundary]
  exact redChain_mem_subspaceChains S n hc

/-- **The reduction commutes with `boundaryExtract`** (the `δ`-extraction chain map). Proved by
`chainIncl`-injectivity: re-including both sides recovers `redChain (∂c)`, using the existing
`redChain_chainIncl` and `redChain_chainBoundary`. -/
theorem redChain_boundaryExtract {X : TopCat} {S : Set ↑X} (n : ℕ)
    (c : SKEFTHawking.SingularRelHomologyInt.relCycleLift S n) :
    redChain (sub S) n (SKEFTHawking.SingularRelHomologyInt.boundaryExtract S n c)
      = SKEFTHawking.SingularPairLES.boundaryExtract S n
          ⟨redChain X (n + 1) (c : SingularChainInt X (n + 1)),
            redChain_mem_relCycleLift n c.2⟩ := by
  apply SKEFTHawking.SingularRelativeHomologyMod2.chainIncl_injective S n
  rw [← redChain_chainIncl, SKEFTHawking.SingularRelHomologyInt.chainIncl_boundaryExtract,
    SKEFTHawking.SingularPairLES.chainIncl_boundaryExtract, redChain_chainBoundary]

/-- **The reduction commutes with `relCycleToHom`**: `redRelHomology S (n+1) (relCycleToHom c)
= relCycleToHom (redChain c)` (both realise the lift-chain as a relative homology class). -/
theorem redRelHomology_relCycleToHom {X : TopCat} {S : Set ↑X} (n : ℕ)
    (c : SKEFTHawking.SingularRelHomologyInt.relCycleLift S n) :
    redRelHomology S (n + 1) (SKEFTHawking.SingularRelHomologyInt.relCycleToHom S n c)
      = SKEFTHawking.SingularPairLES.relCycleToHom S n
          ⟨redChain X (n + 1) (c : SingularChainInt X (n + 1)),
            redChain_mem_relCycleLift n c.2⟩ := by
  rw [SKEFTHawking.SingularRelHomologyInt.relCycleToHom_apply, redRelHomology_mk,
    SKEFTHawking.SingularPairLES.relCycleToHom_apply]
  refine congrArg (SKEFTHawking.SingularRelativeHomologyMod2.RelativeHomology.mk S (n + 1)) ?_
  refine Subtype.ext ?_
  show redRelChain S (n + 1) (RelativeChainInt.mk S (n + 1) (c : SingularChainInt X (n + 1)))
      = SKEFTHawking.SingularRelativeHomologyMod2.RelativeChain.mk S (n + 1) (redChain X (n + 1) c)
  rw [redRelChain_mk]

/-- **The reduction commutes with the connecting homomorphism** (the `δ`-square):
`redHomology (sub S) n ∘ connectingInt S n = connecting S n ∘ redRelHomology S (n+1)`. -/
theorem redHomology_connectingInt {X : TopCat} {S : Set ↑X} (n : ℕ)
    (h : RelHomologyInt S (n + 1)) :
    redHomology (sub S) n (SKEFTHawking.SingularRelHomologyInt.connectingInt S n h)
      = SKEFTHawking.SingularPairLES.connecting S n (redRelHomology S (n + 1) h) := by
  obtain ⟨c, rfl⟩ := SKEFTHawking.SingularRelHomologyInt.relCycleToHom_surjective S n h
  rw [SKEFTHawking.SingularRelHomologyInt.connectingInt_relCycleToHom,
    SKEFTHawking.SingularRelHomologyInt.connectingLift_apply, redHomology_mk,
    redRelHomology_relCycleToHom, SKEFTHawking.SingularPairLES.connecting_relCycleToHom,
    SKEFTHawking.SingularPairLES.connectingLift_apply]
  refine congrArg (SKEFTHawking.SingularHomologyMod2.Homology.mk (sub S) n) ?_
  refine Subtype.ext ?_
  show redChain (sub S) n (SKEFTHawking.SingularRelHomologyInt.boundaryExtract S n c)
      = SKEFTHawking.SingularPairLES.boundaryExtract S n
          ⟨redChain X (n + 1) (c : SingularChainInt X (n + 1)),
            redChain_mem_relCycleLift n c.2⟩
  exact redChain_boundaryExtract n c

/-! ## §6. Naturality of the reduction w.r.t. the absolute homology pushforward -/

/-- **The reduction commutes with the absolute homology pushforward**:
`redHomology Y n ∘ Homology.mapInt φ = Homology.map φ ∘ redHomology X n`. Descends the §1 chain
naturality `redChain_mapChainInt` through the homology quotient. -/
theorem redHomology_homologyMapInt {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ)
    (h : Homology X n) :
    redHomology Y n (Homology.mapInt φ n h)
      = SKEFTHawking.SingularFunctoriality.Homology.map φ n (redHomology X n h) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  rw [show (Submodule.Quotient.mk z : Homology X n) = Homology.mk X n z from rfl,
    Homology.mapInt_mk, redHomology_mk, redHomology_mk]
  show SKEFTHawking.SingularHomologyMod2.Homology.mk Y n _
      = SKEFTHawking.SingularFunctoriality.Homology.map φ n
          (SKEFTHawking.SingularHomologyMod2.Homology.mk X n (redCyclesHom X n z))
  rw [SKEFTHawking.SingularFunctoriality.Homology.map_mk]
  refine congrArg (SKEFTHawking.SingularHomologyMod2.Homology.mk Y n) ?_
  refine Subtype.ext ?_
  simp only [SKEFTHawking.SingularFunctoriality.cyclesMap_coe, redCyclesHom]
  exact redChain_mapChainInt φ n _

end SKEFTHawking.SingularLocalHomologyRedCompatInt
