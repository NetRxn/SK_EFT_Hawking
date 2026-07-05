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

/-!
## Remaining packaging steps (the final `IntOrientationData` discharge of `intOrientation_datum`)

`intFundClass` above IS the global `[M]`. Three sub-lemmas complete `IntOrientationData M`:

1. **`restrictHomologyToPointInt_eq`** (the missing compat): `restrictHomologyToPointInt x n c
   = relInclInt (∅ ⊆ {y≠x}) n ((relHomologyEmptyEquivInt n).symm c)`. Where mod-2 got this
   *definitionally* (its `restrictHomologyToPoint` WAS that composite), the integral
   `restrictHomologyToPointInt = homProjInt {y≠x}` needs it PROVED: `obtain ⟨z,rfl⟩ :=
   Submodule.Quotient.mk_surjective _ c` then compute both sides via `homProjInt_mk`,
   `relHomologyEmptyEquivInt_mk`/`cyclesEmptyEquivInt`, `RelHomologyInt.mk`.
2. **`intFundClass_restricts`** (`[M]` restricts to `orientedLocalGenerator x (orient x)`): with (1),
   `rw [restrictHomologyToPointInt_eq, ← hUniv.choose_spec x (mem_univ x), intFundClass,
   LinearEquiv.symm_apply_apply, relInclInt_trans]` (the mod-2 `fundamentalClass_restricts` shape).
3. **`redCompat`** (`redHomology [M] = mod-2 [M]₂`): both restrict to the SAME mod-2 generator at every
   point — `redHomology` side via `SingularLocalHomologyRedCompatInt` (`redRelHomology∘homProjInt =
   homProj∘redHomology`, @:370) + `redRelHomology_orientedLocalGenerator_ne_zero`; equality by mod-2
   uniqueness `SingularFundamentalClass.restrictHomologyToPoint_injective` (@:235, from
   `goodCompact_univ`).

Then `IntOrientationData M := ⟨orient, horient_unit, intFundClass hUniv, intFundClass_restricts, redCompat⟩`
and `intOrientationOfData` bridges to `IntOrientation M`, discharging `intOrientation_datum` given the
orientability input (`hballs` → `hUniv` via `hasOrientedFundClassInt_univ`).
-/

end SKEFTHawking.SingularIntOrientationDataConstruct
