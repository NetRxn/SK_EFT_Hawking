/-
Phase 5q.B Waves B3/B4: smooth-spin 4-manifold interface and the wired `16 ∣ σ`

INTERFACE-FIRST (roadmap Wave B3). A closed smooth spin 4-manifold contributes exactly the
data the spectra-free Rokhlin derivation needs:
  • its intersection form is **even unimodular** (Wu's formula + Poincaré duality — topological),
  • the algebraic signature bound `8 ∣ σ` holds (van der Blij; the target of Wave B1, where it is to
    be *proved* from even-unimodularity via the classification `E₈^a ⊕ (−E₈)^b ⊕ H^c`), and
  • the extra factor of two `2 ∣ σ/8` (Â-genus even / Arf(q̄)=0 — the irreducible topological input,
    Atiyah–Singer index / Freedman–Kirby; this is what genuinely distinguishes smooth from
    topological, per Freedman's E₈ manifold).

The signature here is the genuine `latticeSig form` (`LatticeSignature.lean`), NOT a free integer
parameter: a manifold's signature *is* the signature of its intersection form. From these data,
`16 ∣ latticeSig form` is a kernel-pure THEOREM via `sixteen_dvd_latticeSig_of_eight_dvd_of_topo`
(= `rokhlin_from_serre_plus_topology` on `latticeSig`) — NO global Rokhlin hypothesis, NO new axiom.

DEPENDENCY GRAPH (anti-circularity): the derivation routes
  even-unimodular (Wu) ─┐
  8 ∣ σ (van der Blij) ──┼─→ (carried as `eight_dvd`)  ─┐
                         │                              ├─→ 16 ∣ σ
  2 ∣ σ/8 (Â even)  ──────────────────────────────────┘
It does NOT use Anderson–Brown–Peterson or Rokhlin's theorem itself as input (Rokhlin's theorem
*is* the conclusion `16 ∣ σ`); the `2 ∣ σ/8` field is the more primitive index-theoretic fact.

STATUS: the `eight_dvd` field is the Wave-B1 algebraic input, precisely isolated as `8 ∣ latticeSig form`.
The signature *calculus* discharging it from the classification normal form is COMPLETE
(`RokhlinClassification.lean`: generators `8∣σ`, block-sum/congruence/reindex closure); the only remaining
input is the classification's EXISTENCE statement (every even unimodular form is congruent to
`E₈^a ⊕ (−E₈)^b ⊕ H^c`), whose two irreducible pieces — Hasse–Minkowski (indefinite represents 0) and
theta-modularity (definite `8 ∣ rank`) — have no Mathlib substrate yet. The `topo` field is the genuinely
topological input. Until the existence statement lands, `eight_dvd` is the single tracked interface
hypothesis (not an axiom).

See docs/roadmaps/Phase5qB_SpectraFreeSpinBordism_Roadmap.md (Waves B3, B4) and
docs/roadmaps/Phase5qB_LabNotebook.md.
-/

import SKEFTHawking.AlgebraicRokhlin
import SKEFTHawking.LatticeSignature
import SKEFTHawking.RokhlinClassification
import SKEFTHawking.RokhlinBridge
import SKEFTHawking.RokhlinHMRankFour

namespace SKEFTHawking

/-- A closed smooth spin 4-manifold, carrying exactly the data the Rokhlin derivation consumes:
    its even-unimodular intersection form and the topological factor-of-two. Its signature is
    `latticeSig form` (see `SmoothSpinManifold4.sig`), not a free parameter.

    The algebraic bound `8 ∣ σ` is **no longer an interface field** — it is now a kernel-pure theorem
    (`eight_dvd_latticeSig`, via the discharged Hasse–Minkowski `hasIsotropicVector` + theta-modularity),
    so a smooth spin 4-manifold is determined by its (even-unimodular) form and the genuinely topological
    factor `2 ∣ σ/8` alone. -/
structure SmoothSpinManifold4 where
  /-- dimension of `H²(M; ℤ)` (rank of the intersection lattice). -/
  rank : ℕ
  /-- the intersection form on `H²(M; ℤ)`. -/
  form : Matrix (Fin rank) (Fin rank) ℤ
  /-- spin ⟹ the intersection form is even unimodular (Wu's formula + Poincaré duality). -/
  even_unimod : IsEvenUnimodular form
  /-- the topological factor of two: `2 ∣ σ/8` (Â-genus even / `Arf(q̄)=0`). -/
  topo : (2 : ℤ) ∣ latticeSig form / 8

/-- The signature `σ(M)` of a smooth spin 4-manifold is the genuine signature of its intersection form. -/
noncomputable def SmoothSpinManifold4.sig (M : SmoothSpinManifold4) : ℤ := latticeSig M.form

/-- The algebraic half: `8 ∣ σ` for a smooth spin 4-manifold — now an unconditional theorem (van der Blij,
    derived from even-unimodularity via the discharged [HM] input), not a carried hypothesis. -/
theorem SmoothSpinManifold4.eight_dvd_sig (M : SmoothSpinManifold4) : 8 ∣ M.sig :=
  eight_dvd_latticeSig M.rank M.form M.even_unimod

/-- **Rokhlin's theorem, wired:** `16 ∣ σ(M)` for every closed smooth spin 4-manifold — a kernel-pure
    theorem derived from the even-unimodular form and the topological factor alone, with no global Rokhlin
    hypothesis, no assumed `8 ∣ σ`, and no new axiom. -/
theorem SmoothSpinManifold4.rokhlin (M : SmoothSpinManifold4) : 16 ∣ M.sig :=
  sixteen_dvd_latticeSig M.form M.even_unimod M.topo

/-- **`sixteen_convergence` without the Rokhlin hypothesis.** The unconditional companion to
    `RokhlinBridge.sixteen_convergence_full`: the `16 ∣ σ` conjunct is now a *theorem*
    (`SmoothSpinManifold4.rokhlin`), not an assumed input. -/
theorem sixteen_convergence_unconditional :
    (∑ f : SMFermion, components f) = 16 ∧
    (16 : ZMod 16) = 0 ∧
    (∀ M : SmoothSpinManifold4, (16 : ℤ) ∣ M.sig) ∧
    (∑ f : SMFermion, components f) = (16 : ℕ) :=
  ⟨total_components_with_nu_R, by decide,
   fun M => M.rokhlin, total_components_with_nu_R⟩

end SKEFTHawking
