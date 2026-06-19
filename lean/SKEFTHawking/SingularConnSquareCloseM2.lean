import Mathlib
import SKEFTHawking.SingularConnSquareLHSExplicit
import SKEFTHawking.SingularOpenDualityConnLegdeltaCollapse
import SKEFTHawking.SingularLegWCapForm

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-M7) — the M2-direct hcore closure (non-circular)

The connecting-square per-`K` cycle core `hcore`
`subHomConnecting U V (p+1) (legW K g) = openDuality (legδ K g)` in `Homology (sub (U∩V)) (p+1)`,
closed by the **M2-direct route** — reducing *both legs to the same explicit homology class* via the
bottom-row Mayer–Vietoris cover-partition chain action (`SingularMvDeltaPartition.mvDelta_cover_partition`)
and the RHS single-stage collapse (`openDuality_legδ_eq_legW`), **without** routing the LHS through the
Kronecker-pairing/`absCohomConn` adjunction (which is circular: `absCohomConn` is Kronecker-defined).

This file builds the abstract reduction skeleton (`hcore_of_lhs_rhs_eq`) and the LHS-explicit form
(`subHomConnecting_legW_eq`), keeping the cover sets abstract to dodge the `whnf` heartbeat wall.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularSubHomologyMV
  SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularOpenDualityCycle
  SKEFTHawking.SingularCompactlySupportedOpen SKEFTHawking.SingularCompactsInOpen
  SKEFTHawking.SingularMayerVietorisLES SKEFTHawking.SingularMvDeltaPartition
  SKEFTHawking.SingularConnSquareLHSExplicit SKEFTHawking.SingularExcisionIso
  SKEFTHawking.SingularPairLES

namespace SKEFTHawking.SingularConnSquareCloseM2

variable {X : TopCat}

/-- **Seam-injectivity reduction of the connecting-square equation.** Two homology classes
`L, R : Homology (sub (U ∩ V)) n` are equal iff, after stripping the two seam isomorphisms `seamI` and
`seamHomologyEquiv` from `L` (whatever the chosen pre-images `cL, cR : Homology (sub (restr ..)) n` are),
the pre-images agree. Concretely: if `L = seamI (seamHomologyEquiv cL)` and `R = seamI (seamHomologyEquiv cR)`,
then `L = R ↔ cL = cR`. The seam isos are injective (they are `LinearEquiv`s), so the
connecting-square equation reduces to an equation in the doubly-nested seam representation
`Homology (sub (restr (val⁻¹U) (val⁻¹V))) n` — where the M2 `[∂zB]`-class lives. -/
theorem seam_eq_iff (U V : Set ↑X) (n : ℕ)
    (cL cR : Homology (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) n) :
    seamI U V n
        (seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n cL)
      = seamI U V n
          (seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n cR)
    ↔ cL = cR := by
  rw [(seamI U V n).injective.eq_iff,
    (seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n).injective.eq_iff]

section
variable [T2Space ↑X]

open SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularConnSquareLHSExplicit in
/-- **M2-direct `hcore` reduction to the seam-transported `mvConnecting` identity.** The
connecting-square per-`K` core
`subHomConnecting (legW K g) = legW J σR` (where the RHS `legW J σR` is the single-stage collapse of
`openDuality (legδ K g)`) holds **iff** the bottom-row MV connecting map of `legW K g` equals the
double-seam-transport of the RHS cap class. The proof rewrites the LHS by the M2-direct
`subHomConnecting_legW` (= `seamI ∘ seamHom ∘ mvConnecting`), writes the RHS as
`seamI (seamHom ((seamHom).symm ((seamI).symm (legW J σR))))` (both seam isos are equivs, so this is `rfl`),
and applies `seam_eq_iff`. This is the **non-circular** reduction: the LHS goes through
`mvConnecting` (the bottom-row MV connecting map's chain action, `mvConnecting_cover_partition`), **never**
through `kroneckerH_subHomConnecting_legW` / `absCohomConn`. -/
theorem subHomConnecting_legW_eq_legW_of_mvConnecting (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V)
    {k p : ℕ} (z₀ : SingularChain X (k + (p + 1) + 1))
    (hz₀ : chainBoundary X (k + (p + 1)) z₀ = 0)
    (K : CompactsIn (U ∪ V)) (g : cohomGW (U ∪ V) k K)
    (R : Homology (sub (U ∩ V)) (p + 1))
    (hmv : mvConnecting (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) (p + 1)
          (cover_preimage U V hU hV) (legW (m := p + 1) (hU.union hV) z₀ hz₀ K g)
        = (seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) (p + 1)).symm
            ((seamI U V (p + 1)).symm R)) :
    subHomConnecting U V hU hV (p + 1) (legW (m := p + 1) (hU.union hV) z₀ hz₀ K g) = R := by
  have hL := subHomConnecting_legW U V hU hV z₀ hz₀ K g
  rw [hL]
  rw [hmv, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end

/-- **M2-direct `hmv` discharge from a cover-partition + a seam-match.** The `mvConnecting` identity
`hmv` required by `subHomConnecting_legW_eq_legW_of_mvConnecting` is discharged, **without** spelling the
concrete `[∂zB]` boundary-extraction class in any statement type, by:
  * a cover-partition `hw : w = [chainIncl (val⁻¹U) zA + chainIncl (val⁻¹V) zB]` of the class `w`
    (`= legW K g`), and
  * the **seam-match** `hmatch`: the explicit `mvConnecting` of that partition (computed by
    `mvConnecting_cover_partition` = the `[∂zB]` class — appearing **only as a proof term** here) equals
    the double-seam-transport of the RHS class `R`.
The concrete `[∂zB]` class is bound as the `mvConnecting_cover_partition` output and matched against the
seam-RHS inside the proof, so the `boundaryExtract_mem_cycles (restr …)` membership proof never enters a
type (dodging the `whnf` wall). The genuine remaining geometric content is exactly `hmatch`. -/
theorem mvConnecting_eq_seamRHS_of_partition (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (w : Homology (sub (U ∪ V)) (n + 1)) (R : Homology (sub (U ∩ V)) n)
    (zA : SingularChain (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) (n + 1))
    (zB : SingularChain (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (n + 1))
    (hz_cyc : chainIncl (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (n + 1) zA
        + chainIncl (Subtype.val ⁻¹' V) (n + 1) zB ∈ cycles (sub (U ∪ V)) (n + 1))
    (hw : w = Homology.mk (sub (U ∪ V)) (n + 1) ⟨_, hz_cyc⟩)
    (c : Homology (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) n)
    (hcZ : mvConnecting (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
          (cover_preimage U V hU hV) (Homology.mk (sub (U ∪ V)) (n + 1) ⟨_, hz_cyc⟩) = c)
    (hmatch : c
        = (seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n).symm
            ((seamI U V n).symm R)) :
    mvConnecting (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
        (cover_preimage U V hU hV) w
      = (seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n).symm
          ((seamI U V n).symm R) := by
  subst hw
  rw [hcZ, hmatch]

end SKEFTHawking.SingularConnSquareCloseM2
