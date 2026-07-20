import Mathlib
import SKEFTHawking.Carrollian.WittAlgebra

/-!
# Phase 6o′ Wave 1a′ C2 residual — the Virasoro central extension via `LieAlgebra.Extension`

The C2 module (`WittAlgebra.lean`) proved the Witt `LieAlgebra` and the standard Virasoro
2-cocycle `c(Lₘ, Lₙ) = δ_{m+n,0}·(m³−m)/12` together with **both** Chevalley–Eilenberg
obligations for the central extension:
* alternating (`wittCocycleAux_self` : `c(x,x) = 0`), and
* the 2-cocycle identity (`wittCocycleAux_isCocycle` : cyclic sum `c([x,y],z)+c([y,z],x)+c([z,x],y)=0`).

This module discharges the documented C2 residual: it packages that proven cocycle into Mathlib's
`LieAlgebra.Extension` framework, producing the **Virasoro algebra as an `Extension` object**
`0 → ℝ → Vir → Witt → 0`. Per the C0 verdict the central charge is a genuine cohomology class, not
a numerical value baked in.

The coefficient module is the trivial 1-dimensional module `ℝ` (`TrivialLieModule`, which supplies
`LieRingModule`/`LieModule`/`IsTrivial`). The two `Submodule`-membership obligations are exactly the
two proven lemmas: `mem_twoCochain_iff` = `wittCocycleAux_self`, and (for a trivial module)
`mem_twoCocycle_iff_of_trivial` = the 2-cocycle identity — here in the derivation form
`c(x,[y,z]) = c([x,y],z) + c(y,[x,z])`, obtained from the proven cyclic form via antisymmetry of
`c` and of the bracket (`wittCocycle_cocycle_mem`). No new mathematics.
-/

noncomputable section

namespace SKEFTHawking.Carrollian

open WittAlgebra (wittCocycle wittCocycleAux wittCocycleAux_self wittCocycleAux_isCocycle
  wittCocycleAux_skew wittBracketAux wittBracket_skew)

/-- The trivial 1-dimensional coefficient module `ℝ` for the central extension. -/
abbrev VirCoeff : Type := TrivialLieModule ℝ WittAlgebra ℝ

/-- **The Virasoro 2-cocycle identity in derivation (Leibniz) form** — `ℝ`-valued:
`c(x,[y,z]) = c([x,y],z) + c(y,[x,z])`. Derived from the proven cyclic form
`wittCocycleAux_isCocycle` via antisymmetry of `c` (`wittCocycleAux_skew`) and of the Witt bracket
(`wittBracket_skew`). This is the exact shape `mem_twoCocycle_iff_of_trivial` demands. -/
theorem wittCocycle_cocycle_mem (x y z : WittAlgebra) :
    wittCocycle x ⁅y, z⁆ = wittCocycle ⁅x, y⁆ z + wittCocycle y ⁅x, z⁆ := by
  simp only [WittAlgebra.bracket_def, WittAlgebra.wittCocycle]
  have hcyc := wittCocycleAux_isCocycle x y z
  have s1 := wittCocycleAux_skew x (wittBracketAux y z)
  have s2 := wittCocycleAux_skew y (wittBracketAux x z)
  have s3 : wittCocycleAux (wittBracketAux x z) y
      = - wittCocycleAux (wittBracketAux z x) y := by
    rw [wittBracket_skew x z, map_neg, LinearMap.neg_apply]
  linear_combination s1 - hcyc - s2 + s3

/-- `wittCocycle` as an element of the 2-cochain space (it is alternating). -/
def wittTwoCochain : ↥(LieModule.Cohomology.twoCochain ℝ WittAlgebra VirCoeff) :=
  ⟨wittCocycle, LieModule.Cohomology.mem_twoCochain_iff.mpr (fun x => wittCocycleAux_self x)⟩

/-- **The Virasoro 2-cocycle** as an element of `twoCocycle ℝ Witt ℝ`: the alternating cochain
`wittCocycle` satisfying the 2-cocycle identity (`wittCocycle_cocycle_mem`). -/
def wittTwoCocycle : ↥(LieModule.Cohomology.twoCocycle ℝ WittAlgebra VirCoeff) :=
  ⟨wittTwoCochain,
    (LieModule.Cohomology.mem_twoCocycle_iff_of_trivial ℝ WittAlgebra VirCoeff wittTwoCochain).mpr
      (fun x y z => wittCocycle_cocycle_mem x y z)⟩

/-- **The Virasoro algebra** — the central extension `ℝ ⊕ Witt` of `Vect(S¹)` carrying the twisted
bracket built from the proven Virasoro 2-cocycle (`LieAlgebra.ofTwoCocycle` supplies its
`LieRing`/`LieAlgebra ℝ` instances). This is the honest Virasoro Lie algebra assembled from the C2
cocycle layer. -/
def virasoroAlgebra : Type := LieAlgebra.ofTwoCocycle wittTwoCocycle

noncomputable instance : LieRing virasoroAlgebra :=
  inferInstanceAs (LieRing (LieAlgebra.ofTwoCocycle wittTwoCocycle))
noncomputable instance : LieAlgebra ℝ virasoroAlgebra :=
  inferInstanceAs (LieAlgebra ℝ (LieAlgebra.ofTwoCocycle wittTwoCocycle))

/-! ### The Virasoro central extension as an `Extension` object

The coefficient `VirCoeff` (`= ℝ`) is the trivial `Vect(S¹)`-module; to view the extension in
Mathlib's `LieAlgebra.Extension` framework it must additionally carry the abelian Lie-*algebra*
structure of the kernel — supplied by the commutator LieRing on the associative ring `ℝ`
(`LieRing.ofAssociativeRing`, abelian since `ℝ` is commutative). These agree definitionally with
the trivial-module instances used to build the cocycle (all reduce to `ℝ`'s own
`AddCommGroup`/`Module`), so no instance diamond arises. -/
noncomputable instance : LieRing VirCoeff := inferInstanceAs (LieRing ℝ)
noncomputable instance : LieAlgebra ℝ VirCoeff := inferInstanceAs (LieAlgebra ℝ ℝ)
instance : IsLieAbelian VirCoeff :=
  (commutative_ring_iff_abelian_lie_ring.mp ⟨mul_comm⟩ : IsLieAbelian ℝ)

/-- **The Virasoro algebra as a `LieAlgebra.Extension`** of the Witt algebra `Vect(S¹)` by the
trivial 1-dimensional coefficient `ℝ` — the central extension `0 → ℝ → Vir → Vect(S¹) → 0` built
from the proven Virasoro 2-cocycle. This is the full discharge of the C2 Extension-packaging
residual: `wittCocycle` is packaged into Mathlib's `LieAlgebra.Extension` framework, both
`Submodule`-membership obligations coming from the already-proven `wittCocycleAux_self` and
`wittCocycleAux_isCocycle`. -/
noncomputable def virasoroExtension : LieAlgebra.Extension ℝ VirCoeff WittAlgebra :=
  LieAlgebra.Extension.ofTwoCocycle wittTwoCocycle

end SKEFTHawking.Carrollian
