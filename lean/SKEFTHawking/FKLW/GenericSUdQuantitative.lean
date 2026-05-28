/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.6 — the generic SU(d) bundled-strict Solovay-Kitaev headline (canonical name)

The canonical Track-S culmination: the generic SU(d) quantitative Solovay-Kitaev headline,
`solovayKitaev_dawson_nielsen_quantitative_generic_sud_strict_constructive_tight`. This is the
d-generic analog of the SU(2) `solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight`
(Phase 6u), and the public-facing name under which the per-alphabet headlines instantiate.

For any SU(d) generating set whose word monoid is a free group and whose image is dense in SU(d),
the bundled-strict headline `SolovayKitaevHeadline_FreeGroup_SUd` holds — i.e. there is a single
algorithmic compile function achieving, at the SAME compile level, BOTH (F#4):

  * the **error bound** `‖ρ_hom(compile U ε) − U‖ ≤ ε`, and
  * the **concrete word-length bound** `(compile U ε).toWord.length ≤ c·log(1/ε)^(log 5/log(3/2))`.

It is "UNCONDITIONAL" in the Track-S sense: the (B) super-quadratic bound (S102/S139), the regime
guards, and the F#4 length-polylog conjunct are ALL discharged internally by the Phase 6y SU(d)
cascade; the only remaining inputs are the alphabet's intrinsic properties — its density in SU(d)
and its free-group word-length structure. The per-alphabet UNCONDITIONAL instances (e.g. SU(4)
trapped-ion, `trappedIonSU4_solovayKitaev_headline_unconditional`) close those inputs concretely.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" S.6 — generic SU(d) bundled-strict headline (canonical name).
Composes `skHeadline_FreeGroup_SUd_from_density_auto` (S.6 plumbing, 2026-05-28). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdPerAlphabetHeadlineFromWitness

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **S.6 — the generic SU(d) bundled-strict Solovay-Kitaev headline (canonical name).**

For any `GeneratingSet (n + 2)` whose word monoid is a free group (`h_eq`), whose image is dense
in SU(d) (`h_dense`), and which carries the free-group word-length structure (`h_wl`), the
bundled-strict headline `SolovayKitaevHeadline_FreeGroup_SUd` holds: a single algorithmic compile
function achieving BOTH the error bound `‖ρ_hom(compile U ε) − U‖ ≤ ε` AND the concrete word-length
bound `≤ c·log(1/ε)^(log 5/log(3/2))` at the same compile level (F#4).

The (B) super-quadratic bound, regime guards, and length-polylog conjunct are discharged internally
(Phase 6y SU(d) cascade); only the alphabet's density + free-group structure remain as inputs. The
d-generic analog of the Phase 6u SU(2) `solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight`. -/
theorem solovayKitaev_dawson_nielsen_quantitative_generic_sud_strict_constructive_tight
    {n : ℕ} {α : Type} [DecidableEq α] [Nonempty (Fin (n + 2))]
    (gs : GeneratingSet (n + 2)) (h_eq : gs.W = FreeGroup α)
    (h_dense : IsDenseInSUd_gs gs)
    (h_wl : WordLengthFreeGroupLike gs (fun w => (h_eq ▸ w : FreeGroup α).toWord.length)) :
    SolovayKitaevHeadline_FreeGroup_SUd gs h_eq :=
  skHeadline_FreeGroup_SUd_from_density_auto gs h_eq h_dense h_wl

end SKEFTHawking.FKLW.GenericSUd
