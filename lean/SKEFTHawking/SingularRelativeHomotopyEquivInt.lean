/-
# Pair homotopy equivalences induce isomorphisms on **integral** relative homology

`SingularRelativeHomotopyInvariance` proves, over `ℤ/2`, that a homotopy equivalence *of pairs*
induces a bijection on relative homology (`RelativeHomology.map_bijective_of_homotopyEquiv_pair`).
The integral tree stopped one step short: it has the pair homotopy invariance
(`relHomologyInt_map_eq_of_homotopic_pair`) and the strict-inverse corollary
(`RelHomologyInt.map_bijective_of_comp_id`, requiring `g ∘ f = id` **on the nose**), but not the
homotopy-equivalence version. That gap is what forces every "this pair deformation-retracts onto
that one" step to be re-argued by hand, or to be dodged with a strict retraction that does not
exist.

This module closes it. The proof is pure functoriality: relative-chain functoriality
(`relMapChainInt_comp`, `relMapChainInt_id`) lifted to homology (§1), then the two pair homotopies
fed through `relHomologyInt_map_eq_of_homotopic_pair` (§2). No new geometry, no chain homotopy — the
signed prism operator was already built by `SingularRelativeHomotopyInvarianceInt`.

The `≃ₗ` packaging (§3) is the form downstream computations want: a deformation retraction of a pair
`(X, A)` onto `(Y, B)` transports the whole relative group.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularRelativeHomotopyInvarianceInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeFunctorialityInt
open SKEFTHawking.SingularRelativeHomotopyInvarianceInt (relHomologyInt_map_eq_of_homotopic_pair)
open SKEFTHawking.SingularHomotopyInvariance (slice)

namespace SKEFTHawking.SingularRelativeHomotopyEquivInt

noncomputable section

/-! ## §1. Functoriality of `RelHomologyInt.map` -/

/-- **Functoriality**: the induced map of a composite of maps of pairs is the composite of the
induced maps. -/
theorem relHomologyInt_map_comp {X Y Z : TopCat} {A : Set ↑X} {B : Set ↑Y} {C : Set ↑Z}
    (φ : C(↑X, ↑Y)) (hAB : Set.MapsTo φ A B) (ψ : C(↑Y, ↑Z)) (hBC : Set.MapsTo ψ B C) (n : ℕ)
    (x : RelHomologyInt A n) :
    RelHomologyInt.map (ψ.comp φ) (hBC.comp hAB) n x
      = RelHomologyInt.map ψ hBC n (RelHomologyInt.map φ hAB n x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [RelHomologyInt.map_mk, RelHomologyInt.map_mk, RelHomologyInt.map_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  simp only [relCyclesMapInt_coe]
  exact relMapChainInt_comp φ hAB ψ hBC n (z : RelativeChainInt A n)

/-- **Identity**: the identity map of pairs induces the identity. -/
theorem relHomologyInt_map_id {X : TopCat} {A : Set ↑X} (n : ℕ) (x : RelHomologyInt A n) :
    RelHomologyInt.map (ContinuousMap.id ↑X) (Set.mapsTo_id A) n x = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [RelHomologyInt.map_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  simp only [relCyclesMapInt_coe]
  exact relMapChainInt_id n (z : RelativeChainInt A n)

/-! ## §2. A pair homotopy equivalence induces an isomorphism -/

/-- **A pair homotopy equivalence induces an isomorphism on integral relative homology**
(degree `≥ 1`). Given maps of pairs `f : (X, A) → (Y, B)` and `g : (Y, B) → (X, A)` together with
homotopies *through maps of pairs* `g ∘ f ≃ id_{(X,A)}` (`Hgf` keeps `A × I` inside `A`) and
`f ∘ g ≃ id_{(Y,B)}` (`Hfg` keeps `B × I` inside `B`), the induced map
`Hₙ₊₁(X, A; ℤ) → Hₙ₊₁(Y, B; ℤ)` is bijective.

The integral mirror of `SingularRelativeHomotopyInvariance.RelativeHomology.map_bijective_of_
homotopyEquiv_pair`, and the strict-inverse hypothesis of
`SingularRelativeFunctorialityInt.RelHomologyInt.map_bijective_of_comp_id` relaxed to a homotopy. -/
theorem RelHomologyInt.map_bijective_of_homotopyEquiv_pair {X Y : TopCat}
    {A : Set ↑X} {B : Set ↑Y}
    (f : C(↑X, ↑Y)) (hf : Set.MapsTo f A B) (g : C(↑Y, ↑X)) (hg : Set.MapsTo g B A)
    (Hgf : C(↑X × unitInterval, ↑X)) (hgfH : ∀ a ∈ A, ∀ t : unitInterval, Hgf (a, t) ∈ A)
    (hgf0 : slice Hgf 0 = g.comp f) (hgf1 : slice Hgf 1 = ContinuousMap.id ↑X)
    (Hfg : C(↑Y × unitInterval, ↑Y)) (hfgH : ∀ b ∈ B, ∀ t : unitInterval, Hfg (b, t) ∈ B)
    (hfg0 : slice Hfg 0 = f.comp g) (hfg1 : slice Hfg 1 = ContinuousMap.id ↑Y) (n : ℕ) :
    Function.Bijective (RelHomologyInt.map f hf (n + 1)) := by
  have hL : ∀ x : RelHomologyInt A (n + 1),
      RelHomologyInt.map g hg (n + 1) (RelHomologyInt.map f hf (n + 1) x) = x := by
    intro x
    rw [← relHomologyInt_map_comp f hf g hg (n + 1) x,
      ← relHomologyInt_map_eq_of_homotopic_pair Hgf hgf0 hgf1 hgfH
        (fun a ha => hg (hf ha)) (Set.mapsTo_id A) n]
    exact relHomologyInt_map_id (n + 1) x
  have hR : ∀ y : RelHomologyInt B (n + 1),
      RelHomologyInt.map f hf (n + 1) (RelHomologyInt.map g hg (n + 1) y) = y := by
    intro y
    rw [← relHomologyInt_map_comp g hg f hf (n + 1) y,
      ← relHomologyInt_map_eq_of_homotopic_pair Hfg hfg0 hfg1 hfgH
        (fun b hb => hf (hg hb)) (Set.mapsTo_id B) n]
    exact relHomologyInt_map_id (n + 1) y
  exact ⟨fun a b hab => by rw [← hL a, ← hL b, hab], fun y => ⟨_, hR y⟩⟩

/-! ## §3. The `≃ₗ` packaging -/

/-- **Transport of the whole relative group along a pair homotopy equivalence.** -/
def relHomologyEquivInt {X Y : TopCat} {A : Set ↑X} {B : Set ↑Y}
    (f : C(↑X, ↑Y)) (hf : Set.MapsTo f A B) (g : C(↑Y, ↑X)) (hg : Set.MapsTo g B A)
    (Hgf : C(↑X × unitInterval, ↑X)) (hgfH : ∀ a ∈ A, ∀ t : unitInterval, Hgf (a, t) ∈ A)
    (hgf0 : slice Hgf 0 = g.comp f) (hgf1 : slice Hgf 1 = ContinuousMap.id ↑X)
    (Hfg : C(↑Y × unitInterval, ↑Y)) (hfgH : ∀ b ∈ B, ∀ t : unitInterval, Hfg (b, t) ∈ B)
    (hfg0 : slice Hfg 0 = f.comp g) (hfg1 : slice Hfg 1 = ContinuousMap.id ↑Y) (n : ℕ) :
    RelHomologyInt A (n + 1) ≃ₗ[ℤ] RelHomologyInt B (n + 1) :=
  LinearEquiv.ofBijective (RelHomologyInt.map f hf (n + 1))
    (RelHomologyInt.map_bijective_of_homotopyEquiv_pair f hf g hg Hgf hgfH hgf0 hgf1 Hfg hfgH
      hfg0 hfg1 n)

/-- **Vanishing transports**: if the source pair group vanishes so does the target's. The form the
two-piece decomposition of `SingularRelativeTripleSurjInt` consumes — a chart pair is shown acyclic
on a convenient model and the conclusion is moved to the pair actually appearing in the triple. -/
theorem relHomologyInt_eq_zero_of_homotopyEquiv_pair {X Y : TopCat} {A : Set ↑X} {B : Set ↑Y}
    (f : C(↑X, ↑Y)) (hf : Set.MapsTo f A B) (g : C(↑Y, ↑X)) (hg : Set.MapsTo g B A)
    (Hgf : C(↑X × unitInterval, ↑X)) (hgfH : ∀ a ∈ A, ∀ t : unitInterval, Hgf (a, t) ∈ A)
    (hgf0 : slice Hgf 0 = g.comp f) (hgf1 : slice Hgf 1 = ContinuousMap.id ↑X)
    (Hfg : C(↑Y × unitInterval, ↑Y)) (hfgH : ∀ b ∈ B, ∀ t : unitInterval, Hfg (b, t) ∈ B)
    (hfg0 : slice Hfg 0 = f.comp g) (hfg1 : slice Hfg 1 = ContinuousMap.id ↑Y) (n : ℕ)
    (hzero : ∀ x : RelHomologyInt A (n + 1), x = 0) :
    ∀ y : RelHomologyInt B (n + 1), y = 0 := by
  intro y
  obtain ⟨x, rfl⟩ := (RelHomologyInt.map_bijective_of_homotopyEquiv_pair f hf g hg Hgf hgfH hgf0
    hgf1 Hfg hfgH hfg0 hfg1 n).2 y
  rw [hzero x, map_zero]

end

end SKEFTHawking.SingularRelativeHomotopyEquivInt
