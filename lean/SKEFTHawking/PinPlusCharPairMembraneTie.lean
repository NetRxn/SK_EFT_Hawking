/-
# Phase 5q.H (W-A Round 4) — THE MEMBRANE TIE: the ACCEPTANCE TESTS.

**Where the tie itself lives (post-migration).** The tied structures — `GeoMembrane` (with `L`
COMPUTED as `ker bInc`), `CharPairBorTied`, `mkCharPairBorTied`, and all eight tied op witnesses —
were MIGRATED into `PinPlusCharPairData` §9.6 by the arm-4 re-gate migration, and the live carrier
`pinPlusCharPairData` consumes ONLY the tied form. This module `export`s the moved names (the old
fully-qualified names keep resolving) and holds the gate's ACCEPTANCE TESTS, which need the
exploit objects (`phiLin`, `q4`) from `PinPlusKTVacuityGateWD`.

**The gate finding the tie repairs** (`free-membrane-kernel-kills-nonsplit`, round 3): with
`CharPairBor.L` a FREE `Submodule` field, the e₈-graph Lagrangian `graphSub phiLin` inhabits a
`CharPairBor` on the UN-reversed double `σ₄ ⊔ σ₄` — collapsing `⟨[ℝP⁴]⟩` to `ℤ/8` and refuting
`KTNonSplit` (`doubleKillerBor`). The tie computes `L = ker mem.bInc`, and the acceptance tests
below verify the geometric discrimination:

* **The honest kernel KILLS the un-reversed double** (`untwisted_double_fails_taylor_on_cyl`):
  on the diagonal class the un-negated doubled form is `2·q₄(gen) ≠ 0`.
* **The e₈ Lagrangian is NOT a geometric kernel** (`e8_omits_diagonal`, `cylKernel_ne_e8`): it
  omits the diagonal every honest cylinder kernel contains.
* **Positive form** (`no_untwisted_double_via_geometric_membrane`): ANY membrane whose kernel
  realizes the honest cylinder geometry cannot host the un-reversed double.

**⚠ The residual (round 4.5, self-attacked in `PinPlusKTVacuityGateWD` §4.5).** `bInc` is still an
un-tethered linear-map field, so a SYNTHETIC datum (`doubleKillerBInc`, kernel = the e₈ graph)
replays the exploit on the tied carrier — the §5 refutations there PERSIST and the W-D binders
stay FROZEN. Discharge path: the geometric-realization strengthening
(`PinPlusCharPairMembraneGeoRealization.GeoRealizationData` / `GeoMembrane.ofGeometric`) + the
fresh re-gate.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTVacuityGateWD

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.BordismTheory SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusKTVacuityGateWD

namespace SKEFTHawking.PinPlusCharPairMembraneTie

/-! ## §1. Backward-compatible aliases — the tie core now lives in `PinPlusCharPairData` §9.6 -/

export SKEFTHawking.PinPlusCharPairData (GeoMembrane cylGeoMembrane cylGeoMembrane_L
  diagonal_mem_cylGeoMembrane negBorBInc negBorBInc_ker CharPairBorTied mkCharPairBorTied
  charPairCylBorTied charPairNegBorTied charPairRevBorTied)

/-! ## §2. THE ACCEPTANCE TEST — the e₈-graph Lagrangian cannot inhabit the tied `Bor` for the
un-reversed double via any GEOMETRIC membrane.

The gate's exit criterion (`free-membrane-kernel-kills-nonsplit`): `doubleKillerBor` must BREAK.
On the tied form there is no free `L` field — `L = ker mem.bInc` is COMPUTED. The exploit's
`graphSub phiLin` (e₈) is a metabolic Lagrangian of `q₄ ⊞ q₄` (it PASSES the Taylor leg), but it is
NOT the kernel of any cylinder membrane's boundary-inclusion — it OMITS the diagonal that every
honest cylinder kernel contains. And the honest cylinder kernel (the anti-diagonal), which the
geometry forces, FAILS the un-reversed double's Taylor leg. Both facts are decidable in `Fin 8`. -/

/-- The odd `ℝP⁴`-generator class `gen ∈ Fin 4 → ZMod 2` (a single `1`). `q₄(gen) = 1`, so
`q₄(gen) + q₄(gen) = 2 ≠ 0` — the un-reversed double's obstruction. -/
def gen4 : Fin 4 → ZMod 2 := fun i => if i = 0 then 1 else 0

/-- **The un-reversed double's joint form does NOT vanish on the diagonal `gen`** — the concrete
`2·q₄(gen) ≠ 0` fact (`q₄(gen) = 1`). This is why the geometric (anti-diagonal-containing) kernel
kills `σ₄ ⊔ σ₄`. -/
theorem q4_diag_ne_zero : (Z4Quadratic.orthSum q4 q4).q (Sum.elim gen4 gen4) ≠ 0 := by
  rw [plain_joint_forces_two_torsion_on_diagonal]; decide

/-- **THE HONEST CYLINDER KERNEL KILLS THE UN-REVERSED DOUBLE.** The geometric doubling membrane's
kernel `(cylGeoMembrane q₄).L` (the anti-diagonal) contains the diagonal class `Sum.elim gen gen`, on
which the un-negated doubled form is `2·q₄(gen) ≠ 0`. So the Taylor leg FAILS — no `CharPairBorTied`
for the un-reversed double can use the honest cylinder membrane. -/
theorem untwisted_double_fails_taylor_on_cyl :
    ¬ (∀ l ∈ (cylGeoMembrane q4).L, (Z4Quadratic.orthSum q4 q4).q l = 0) := by
  intro h
  exact q4_diag_ne_zero (h _ (diagonal_mem_cylGeoMembrane q4 gen4))

/-- **THE e₈ LAGRANGIAN OMITS THE DIAGONAL** — `graphSub phiLin` does not contain `Sum.elim gen gen`
(because `φ(gen) = gen + 𝟙 ≠ gen`). So the extended Hamming code can NEVER be the boundary-inclusion
kernel of a cylinder membrane: it fails the geometric half-lives–half-dies signature. -/
theorem e8_omits_diagonal : Sum.elim gen4 gen4 ∉ graphSub phiLin := by
  rw [mem_graphSub]
  intro h
  have hval : phiFun gen4 = gen4 := by
    have h' := h.symm
    -- v4.32: with `gen4` in the simp set it unfolds in `h'` but NOT in this goal, leaving the two
    -- sides at different spellings. Drop it — `phiLin` alone is what needs unfolding, and both
    -- sides then stay on `gen4`.
    simpa [phiLin] using h'
  revert hval; decide

/-- **THE TIE DISCRIMINATES**: the honest cylinder membrane's COMPUTED kernel is NOT the e₈ graph
(a decidable `Fin 8` distinction). The exploit's Lagrangian is metabolic but geometrically
unrealizable — exactly the gap the free-`L` field papered over. -/
theorem cylKernel_ne_e8 : (cylGeoMembrane q4).L ≠ graphSub phiLin := by
  intro h
  exact e8_omits_diagonal (h ▸ diagonal_mem_cylGeoMembrane q4 gen4)

/-- **ACCEPTANCE TEST — POSITIVE FORM.** On the tied carrier, ANY membrane whose kernel realizes the
honest cylinder geometry (contains the full diagonal — the mandatory half-lives–half-dies classes of
a genuine `Σ × [0,1]` membrane) CANNOT host the un-reversed double: its diagonal class violates the
Taylor leg. The e₈ graph evades this only by NOT containing the diagonal — i.e. by not being a
geometric kernel at all. Hence the free-`L` exploit is dead on the tie, and the synthetic-`bInc`
replay (§4.5 of the gate module) is forced to carry a membrane datum with NO geometric realization
— the named residual the realization strengthening closes. -/
theorem no_untwisted_double_via_geometric_membrane
    (m : GeoMembrane q4 q4) (hgeo : ∀ a, Sum.elim a a ∈ m.L)
    (htaylor : ∀ l ∈ m.L, (Z4Quadratic.orthSum q4 q4).q l = 0) : False :=
  q4_diag_ne_zero (htaylor _ (hgeo gen4))

end SKEFTHawking.PinPlusCharPairMembraneTie
