/-
# Manifold-level Rokhlin from [HM] alone — the `eight_dvd` interface field made redundant

`SmoothSpinManifold4` (in `SpinRokhlinInterface`) carries three pieces of interface data: the
even-unimodular intersection form (`even_unimod`), the algebraic bound `8 ∣ σ` (`eight_dvd`, an *assumed*
field), and the topological factor `2 ∣ σ/8` (`topo`). With theta-modularity discharging the definite case
of `8 ∣ σ` (`eight_dvd_latticeSig_of_definite`) and the reduction `eight_dvd_latticeSig_of_HM` composing it,
the `eight_dvd` field is now **derivable from `even_unimod`** given only the single global input [HM]
(indefinite even unimodular ⟹ primitive isotropic vector).

`rokhlin_of_HM` and `sixteen_convergence_of_HM` therefore obtain `16 ∣ σ(M)` — and the full convergence
statement — from the manifold's *genuine* data (`even_unimod` + `topo`) plus [HM], WITHOUT consulting the
`eight_dvd` field and WITHOUT any global Rokhlin hypothesis. Once [HM] lands as a theorem, the `eight_dvd`
field and the `hHM` parameter both drop, yielding the fully unconditional `16 ∣ σ`.

Dependency graph (anti-circularity): [Θ] = `eight_dvd_rank` (theta-modularity) and [HM] = Hilbert-symbol
Hasse–Minkowski — neither routes through ABP / a Rokhlin-equivalent input. Kernel-pure, no new axioms.
-/

import Mathlib
import SKEFTHawking.SpinRokhlinInterface
import SKEFTHawking.RokhlinFromHM

namespace SKEFTHawking

/-- **`16 ∣ σ(M)` for a smooth spin 4-manifold from [HM] alone.** Derives the algebraic bound `8 ∣ σ` from
the even-unimodular form via `eight_dvd_latticeSig_of_HM` (with the definite case supplied unconditionally by
theta-modularity), then combines with the topological factor — never reading the assumed `eight_dvd` field. -/
theorem SmoothSpinManifold4.rokhlin_of_HM (hHM : HasIsotropicVectorHyp) (M : SmoothSpinManifold4) :
    16 ∣ M.sig :=
  sixteen_dvd_latticeSig_of_HM_of_topo hHM M.form M.even_unimod M.topo

/-- **`sixteen_convergence` from [HM] alone.** The companion to `sixteen_convergence_unconditional` whose
`16 ∣ σ` conjunct depends only on the global input [HM] (and the manifolds' genuine even-unimodular +
topological data), not on the per-manifold `eight_dvd` interface field. -/
theorem sixteen_convergence_of_HM (hHM : HasIsotropicVectorHyp) :
    (∑ f : SMFermion, components f) = 16 ∧
    (16 : ZMod 16) = 0 ∧
    (∀ M : SmoothSpinManifold4, (16 : ℤ) ∣ M.sig) ∧
    (∑ f : SMFermion, components f) = (16 : ℕ) :=
  ⟨total_components_with_nu_R, by decide,
   fun M => M.rokhlin_of_HM hHM, total_components_with_nu_R⟩

end SKEFTHawking
