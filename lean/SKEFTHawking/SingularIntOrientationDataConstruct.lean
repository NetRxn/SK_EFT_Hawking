import Mathlib
import SKEFTHawking.SingularIntFundClassUnivInt
import SKEFTHawking.SingularRelativeEmptyInt
import SKEFTHawking.IntOrientationSection

/-!
# Constructing `IntOrientationData` from the oriented univ fundamental class (brick 18h)

The packaging that discharges `intOrientation_datum`: from the oriented univ fundamental class
`hasOrientedFundClassInt orient univ` (brick 18g, under the orientability `hballs`) plus the `±1`
section, build the disclosed `IntOrientationData M` (hence `IntOrientation M` via `intOrientationOfData`).

* `intFundClass` — the global `[M] ∈ H₄(M;ℤ)`, the univ witness transported from `H₄(M|univ) =
  H₄(M, ∅)` to `H₄(M)` via `relHomologyEmptyEquivInt` (`(univ)ᶜ = ∅`). Mirror of
  `SingularFundamentalClass.fundamentalClass`.
* `intFundClass_restricts` — `[M]` restricts at every point to the oriented local generator. Mirror of
  `fundamentalClass_restricts`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeFunctorialityInt
open SKEFTHawking.SingularIntFundamentalClassExist
open SKEFTHawking.IntOrientationSection (relInclInt relInclInt_trans restrictToPointInt
  restrictHomologyToPointInt orientedLocalGenerator)

namespace SKEFTHawking.SingularIntOrientationDataConstruct

/-- **mod-2 `homProj = relIncl ∘ relHomologyEmptyEquiv.symm`** (the mod-2 mirror of
`homProjInt_relHomologyEmptyEquivInt`), so mod-2 `restrictHomologyToPoint x = homProj {x}ᶜ`. -/
theorem homProj_relHomologyEmptyEquiv {X : TopCat} (S : Set ↑X) (n : ℕ)
    (w : SKEFTHawking.SingularRelativeHomologyMod2.RelativeHomology (∅ : Set ↑X) n) :
    SKEFTHawking.SingularPairLES.homProj S n
        (SKEFTHawking.SingularRelativeEmpty.relHomologyEmptyEquiv n w)
      = SKEFTHawking.SingularRelativeMV.relIncl (Set.empty_subset S) n w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [show (Submodule.Quotient.mk u :
        SKEFTHawking.SingularRelativeHomologyMod2.RelativeHomology (∅ : Set ↑X) n)
      = SKEFTHawking.SingularRelativeHomologyMod2.RelativeHomology.mk (∅ : Set ↑X) n u from rfl,
    SKEFTHawking.SingularRelativeEmpty.relHomologyEmptyEquiv_mk,
    SKEFTHawking.SingularPairLES.homProj_mk]
  simp only [SKEFTHawking.SingularRelativeMV.relIncl]
  congr 1
  apply Subtype.ext
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
    (u : SKEFTHawking.SingularRelativeHomologyMod2.RelativeChain (∅ : Set ↑X) n)
  simp only [SKEFTHawking.SingularRelativeFunctoriality.relCyclesMap_coe,
    SKEFTHawking.SingularRelativeEmpty.cyclesEmptyEquiv_coe, ← hc,
    show (Submodule.Quotient.mk c :
        SKEFTHawking.SingularRelativeHomologyMod2.RelativeChain (∅ : Set ↑X) n)
      = SKEFTHawking.SingularRelativeHomologyMod2.RelativeChain.mk (∅ : Set ↑X) n c from rfl,
    SKEFTHawking.SingularRelativeEmpty.chainEmptyEquiv_mk,
    SKEFTHawking.SingularRelativeFunctoriality.relMapChain_mk,
    SKEFTHawking.SingularFunctoriality.mapChain_id]

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- **The integral fundamental class `[M] ∈ H₄(M;ℤ)`** from the oriented univ witness: transport the
`hasOrientedFundClassInt orient univ` witness (living in `H₄(M|univ) = H₄(M, (univ)ᶜ)`, `(univ)ᶜ = ∅`)
to `H₄(M;ℤ)` via `relInclInt` (over `(univ)ᶜ ⊆ ∅`) then `relHomologyEmptyEquivInt`. The ℤ mirror of
`SingularFundamentalClass.fundamentalClass`. -/
noncomputable def intFundClass {orient : M → ℤ}
    (hUniv : hasOrientedFundClassInt orient (Set.univ : Set M)) :
    Homology (TopCat.of M) 4 :=
  SKEFTHawking.SingularRelativeEmptyInt.relHomologyEmptyEquivInt 4
    (relInclInt (Set.compl_univ (α := ↑(TopCat.of M))).subset 4 hUniv.choose)

/-- **The `homProjInt`/`relHomologyEmptyEquivInt` compatibility** — where mod-2 got this
definitionally, over ℤ `restrictHomologyToPointInt = homProjInt {y≠x}` needs it proved:
`homProjInt S (relHomologyEmptyEquivInt w) = relInclInt (∅ ⊆ S) w`. Both send the class of `u` to the
class of `u`'s underlying chain in `Hₙ(M, S; ℤ)`. -/
theorem homProjInt_relHomologyEmptyEquivInt {X : TopCat} (S : Set ↑X) (n : ℕ)
    (w : RelHomologyInt (∅ : Set ↑X) n) :
    homProjInt S n (SKEFTHawking.SingularRelativeEmptyInt.relHomologyEmptyEquivInt n w)
      = relInclInt (Set.empty_subset S) n w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [show (Submodule.Quotient.mk u : RelHomologyInt (∅ : Set ↑X) n)
        = RelHomologyInt.mk (∅ : Set ↑X) n u from rfl,
    SKEFTHawking.SingularRelativeEmptyInt.relHomologyEmptyEquivInt_mk, homProjInt_mk]
  simp only [relInclInt]
  congr 1
  apply Subtype.ext
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (u : RelativeChainInt (∅ : Set ↑X) n)
  simp only [relCyclesMapInt_coe, SKEFTHawking.SingularRelativeEmptyInt.cyclesEmptyEquivInt_coe, ← hc,
    show (Submodule.Quotient.mk c : RelativeChainInt (∅ : Set ↑X) n)
      = RelativeChainInt.mk (∅ : Set ↑X) n c from rfl,
    SKEFTHawking.SingularRelativeEmptyInt.chainEmptyEquivInt_mk, relMapChainInt_mk,
    SKEFTHawking.SingularFunctorialityInt.mapChainInt_id]

omit [Nonempty M] in
/-- **`[M]` restricts to the oriented local generator at every point** (the `restricts` field). Unfold
`restrictHomologyToPointInt = homProjInt {y≠x}` and `intFundClass`, apply the compat lemma, collapse the
`relInclInt` chain (`relInclInt_trans`), and match the univ witness's per-point value
(`hUniv.choose_spec`). The ℤ mirror of `SingularFundamentalClass.fundamentalClass_restricts`. -/
theorem intFundClass_restricts {orient : M → ℤ}
    (hUniv : hasOrientedFundClassInt orient (Set.univ : Set M)) (x : M) :
    restrictHomologyToPointInt (X := TopCat.of M) x 4 (intFundClass hUniv)
      = orientedLocalGenerator x (orient x) := by
  rw [← hUniv.choose_spec x (Set.mem_univ x), restrictHomologyToPointInt, intFundClass,
    homProjInt_relHomologyEmptyEquivInt, relInclInt_trans]
  rfl

omit [T2Space M] [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] in
/-- mod-2 `restrictHomologyToPoint x = homProj {x}ᶜ` (from `homProj_relHomologyEmptyEquiv` + the def
`restrictHomologyToPoint = relIncl ∘ relHomologyEmptyEquiv.symm`). -/
theorem restrictHomologyToPoint_eq_homProj (x : M)
    (m : SKEFTHawking.SingularHomologyMod2.Homology (TopCat.of M) 4) :
    SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint (X := TopCat.of M) x 4 m
      = SKEFTHawking.SingularPairLES.homProj ({x}ᶜ : Set ↑(TopCat.of M)) 4 m := by
  simp only [SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  rw [← homProj_relHomologyEmptyEquiv, LinearEquiv.apply_symm_apply]

omit [T2Space M] [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] in
/-- **The mod-2 point-restriction of a reduction is the reduction of the ℤ point-restriction** (Helper
B): `restrictHomologyToPoint x (redHomology c) = redRelHomology (restrictHomologyToPointInt x c)`. Via
`restrictHomologyToPoint = homProj` + `restrictHomologyToPointInt = homProjInt {y≠x}` + the reduction
naturality `redRelHomology_homProjInt`. -/
theorem restrictHomologyToPoint_redHomology (x : M) (c : Homology (TopCat.of M) 4) :
    SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint (X := TopCat.of M) x 4
        (redHomology (TopCat.of M) 4 c)
      = SKEFTHawking.SingularRelHomologyInt.redRelHomology
          ({y | y ≠ x} : Set ↑(TopCat.of M)) 4 (restrictHomologyToPointInt (X := TopCat.of M) x 4 c) := by
  rw [restrictHomologyToPoint_eq_homProj]
  simp only [restrictHomologyToPointInt]
  rw [SKEFTHawking.SingularLocalHomologyRedCompatInt.redRelHomology_homProjInt]
  rfl

/-- **The `redCompat` field**: the ℤ→ℤ/2 reduction of the integral `[M]` is the on-main mod-2 `[M]₂`.
Via the mod-2 local-degree isomorphism at a basepoint `x₀` (`localDegree_bijective`, needs
`[PreconnectedSpace M]`): it suffices that `localDegree x₀ (redHomology [M]) = 1 = localDegree x₀ [M]₂`.
The left value is `manifoldLocalIso x₀ (restrictHomologyToPoint x₀ (redHomology [M])) = manifoldLocalIso
x₀ (redRelHomology (restrictHomologyToPointInt x₀ [M]))` (Helper B) `= manifoldLocalIso x₀ (redRelHomology
(orientedLocalGenerator x₀ (orient x₀)))` (`intFundClass_restricts`), which is nonzero
(`redRelHomology_orientedLocalGenerator_ne_zero` + `manifoldLocalIso` injective), hence `= 1` in `ℤ/2`. -/
theorem redCompat_intFundClass [PreconnectedSpace M] {orient : M → ℤ}
    (hUniv : hasOrientedFundClassInt orient (Set.univ : Set M))
    (horient : ∀ x, orient x = 1 ∨ orient x = -1) :
    redHomology (TopCat.of M) 4 (intFundClass hUniv)
      = SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  -- Generator identification: `redRelHomology (orientedLocalGenerator x₀ ·) = manifoldLocalIso.symm 1`
  -- (stated over `{y ≠ x₀}` = `localSub x₀` to match Helper B syntactically).
  have h1 : SKEFTHawking.SingularChartBridge.manifoldLocalIso x₀
      (SKEFTHawking.SingularRelHomologyInt.redRelHomology
        ({y | y ≠ x₀} : Set ↑(TopCat.of M)) 4 (orientedLocalGenerator x₀ (orient x₀))) = 1 := by
    have hne := SKEFTHawking.IntOrientationSection.redRelHomology_orientedLocalGenerator_ne_zero
      x₀ (horient x₀)
    have hv : SKEFTHawking.SingularChartBridge.manifoldLocalIso x₀
        (SKEFTHawking.SingularRelHomologyInt.redRelHomology
          ({y | y ≠ x₀} : Set ↑(TopCat.of M)) 4 (orientedLocalGenerator x₀ (orient x₀))) ≠ 0 := by
      simp only [ne_eq, EmbeddingLike.map_eq_zero_iff]
      exact hne
    exact (by decide : ∀ w : ZMod 2, w ≠ 0 → w = 1) _ hv
  have hgenID : SKEFTHawking.SingularRelHomologyInt.redRelHomology
        ({y | y ≠ x₀} : Set ↑(TopCat.of M)) 4 (orientedLocalGenerator x₀ (orient x₀))
      = (SKEFTHawking.SingularChartBridge.manifoldLocalIso x₀).symm 1 := by
    rw [← h1, LinearEquiv.symm_apply_apply]
  -- Both `redHomology [M]` and `[M]₂` restrict at `x₀` to the same generator ⟹ their difference does
  -- restrict to `0` ⟹ they are equal (mod-2 uniqueness at a basepoint, `[PreconnectedSpace M]`).
  refine eq_of_sub_eq_zero
    (SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint_injective (x₀ := x₀) ?_)
  rw [map_sub, restrictHomologyToPoint_redHomology, intFundClass_restricts,
    SKEFTHawking.SingularFundamentalClass.fundamentalClass_restricts, hgenID, sub_self]

/-- **`IntOrientationData M` from an orientation** (`orient` a `±1` section realisable on every chart
ball, `[PreconnectedSpace M]`) — the packaging that discharges `intOrientation_datum`: `intFundClass` +
`intFundClass_restricts` + `redCompat_intFundClass`. Compose with `intOrientationOfData` for the disclosed
`IntOrientation M`. The `hballs` input is orientability (`hasOrientedFundClassInt orient` on every ball). -/
noncomputable def intOrientationDataOfOrientation [PreconnectedSpace M] (orient : M → ℤ)
    (horient : ∀ x, orient x = 1 ∨ orient x = -1)
    (hballs : ∀ (x : M) (ρ : ℝ), 0 ≤ ρ →
        Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ
          ⊆ (chartAt (EuclideanSpace ℝ (Fin 4)) x).target →
        hasOrientedFundClassInt orient ((chartAt (EuclideanSpace ℝ (Fin 4)) x).symm ''
          Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ)) :
    SKEFTHawking.SingularHomologyInt.IntOrientation M :=
  haveI hUniv := SKEFTHawking.SingularIntFundClassUnivInt.hasOrientedFundClassInt_univ orient hballs
  SKEFTHawking.IntOrientationSection.intOrientationOfData
    { orient := orient
      orient_unit := horient
      fundClass := intFundClass hUniv
      restricts := intFundClass_restricts hUniv
      redCompat := redCompat_intFundClass hUniv horient }

end SKEFTHawking.SingularIntOrientationDataConstruct
