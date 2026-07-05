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

/-!
## Remaining: `redCompat` + the `IntOrientationData` assembly

Sub-lemmas (1) `homProjInt_relHomologyEmptyEquivInt` and (2) `intFundClass_restricts` are DONE above.
The last field is **`redCompat`** (`redHomology [M] = mod-2 [M]₂`), then the structure assembles:

3. **`redCompat`** (needs `[PreconnectedSpace M]`): `redHomology 4 (intFundClass hUniv) =
   SingularFundamentalClass.fundamentalClass (m:=2)`. Both restrict (mod-2 `restrictHomologyToPoint`) at
   a basepoint `x₀` to the SAME generator, so their difference restricts to `0`, hence `= 0` by mod-2
   uniqueness `SingularFundamentalClass.restrictHomologyToPoint_injective` (@:235). The `redHomology` side
   uses the reduction naturality `SingularLocalHomologyRedCompatInt` (`redRelHomology∘homProjInt =
   homProj∘redHomology`, @:370) + `intFundClass_restricts` + the generator identification
   `redRelHomology (orientedLocalGenerator x s) = (manifoldLocalIso x).symm 1` (nonzero via
   `redRelHomology_orientedLocalGenerator_ne_zero`, unique in `ℤ/2` via `manifoldLocalIso` injectivity);
   the mod-2 side uses `fundamentalClass_restricts`.

Then `IntOrientationData M := ⟨orient, horient_unit, intFundClass hUniv, intFundClass_restricts, redCompat⟩`
and `intOrientationOfData` bridges to `IntOrientation M`, discharging `intOrientation_datum` given the
orientability input (`hballs` → `hUniv` via `hasOrientedFundClassInt_univ`).
-/

end SKEFTHawking.SingularIntOrientationDataConstruct
