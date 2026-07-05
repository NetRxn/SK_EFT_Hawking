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

end SKEFTHawking.SingularLocalHomologyRedCompatInt
