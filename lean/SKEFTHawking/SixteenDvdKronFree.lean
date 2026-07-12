/-
# Phase 5q.H (N4 CLOSED) — the σ÷16 legs with the `kron`/`hkron` binders ELIMINATED

The composed glue for gap-map node N4 (`ASSEMBLY_GAP_MAP_20260712.md` row N4): the σ÷16 legs
(`SixteenDvdOfOrientationSpin.sixteen_dvd_latticeSig_of_orientation_spin`,
`PinPlusCertSpinSeam.sixteen_dvd_latticeSig_of_orientation_certK`) consumed the H₂ integral
Kronecker duality as TWO binders — `kron : H₂ ≃ₗ Module.Dual ℤ H²` + the computation rule `hkron`.
The absolute integral UCT engine (`SingularAbsoluteUCInt`, the absolute port of the relative
`SingularRelativeUCInt` engine) discharges both from honest structural hypotheses, so this module
restates the legs with the binders GONE, replaced by the instance set:

* `Module.Free ℤ (H₁(M; ℤ))` — the `Ext = 0` topological input (`H₁` torsion-free);
* `Module.Projective ℤ (boundaries 0/1)` — universally true over the PID ℤ (submodules of free
  modules are free), Mathlib-gapped at infinite rank — the same instances the relative engine and
  `euclSourceIso` carry;
* `Module.Free ℤ (H₂(M; ℤ))` + `Module.Finite ℤ (H₂(M; ℤ))` — the reflexivity input for the flip
  direction, N5-adjacent (the finiteness tower discharging `intH2_basis_datum` produces exactly
  these).

N4 thereby stops being a separate open node: the Kronecker duality is now a THEOREM over
N5-adjacent finiteness/freeness data. No Erdős–Kaplansky-over-ℤ derivation is attempted anywhere
(settled fork `5qH-fg-ek-over-Z-blocked`: freeness/FG stay hypotheses).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularAbsoluteUCInt
import SKEFTHawking.SixteenDvdOfOrientationSpin
import SKEFTHawking.PinPlusCertSpinSeam

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.IntOrientationSection
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PoincareDualityWu (wuClass2)
open SKEFTHawking.PinPlusTiedData
open SKEFTHawking.SingularAbsoluteUCInt (kronH2OfFree kronH2OfFree_apply)

namespace SKEFTHawking.SixteenDvdKronFree

/-! ## §1. The orientation+spin σ÷16 leg, Kronecker-binder-free -/

section Spin

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- **`16 ∣ σ` at a plus-oriented closed charted SPIN 4-manifold — Kronecker binders eliminated.**
`sixteen_dvd_latticeSig_of_orientation_spin` with its `kron`/`hkron` inputs DISCHARGED by the
absolute integral UCT flip (`SingularAbsoluteUCInt.kronH2OfFree`). Remaining open inputs: the
basis `B` (N5), the spin certificate `hv2` (N6), E2's topological factor `htopo` (N2) — plus the
honest UCT instance set (`H₁` free, boundary projectivity, `H₂` finite free). N4 is closed as a
separate node. -/
theorem sixteen_dvd_latticeSig_of_orientation_spin_free (d : IntOrientationData M)
    (h1 : ∀ x, d.orient x = 1)
    [Module.Free ℤ (Homology (TopCat.of M) 1)]
    [Module.Projective ℤ (boundaries (TopCat.of M) 0)]
    [Module.Projective ℤ (boundaries (TopCat.of M) 1)]
    [Module.Free ℤ (Homology (TopCat.of M) 2)]
    [Module.Finite ℤ (Homology (TopCat.of M) 2)]
    (B : IntH2Basis (TopCat.of M))
    (hv2 : wuClass2 (poincareDual4Mid_of_closed (M := M)) = 0)
    (htopo : (2 : ℤ) ∣ latticeSig
      (interMatrix (intFundamentalClassOfHomology d.fundClass) B) / 8) :
    (16 : ℤ) ∣ latticeSig (interMatrix (intFundamentalClassOfHomology d.fundClass) B) :=
  SKEFTHawking.SixteenDvdOfOrientationSpin.sixteen_dvd_latticeSig_of_orientation_spin d h1
    (kronH2OfFree (TopCat.of M)) (kronH2OfFree_apply (TopCat.of M)) B hv2 htopo

end Spin

/-! ## §2. The carrier-certified σ÷16 leg, Kronecker-binder-free -/

section CertK

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
  {k : WithTop ℕ∞}

/-- **The σ÷16 leg fed by the carrier certificate — Kronecker binders eliminated.**
`sixteen_dvd_latticeSig_of_orientation_certK` (the N6 carrier hook: spin supplied by
`PinPlusCertK I s`) with the `kron`/`hkron` binders DISCHARGED by the absolute integral UCT flip.
A `TiedStr` caller passes `σ.cert`; the remaining open inputs are `B` (N5) and `htopo` (N2), over
the honest UCT instance set. -/
theorem sixteen_dvd_latticeSig_of_orientation_certK_free {s : SingularManifold PUnit k I}
    (hcert : PinPlusCertK I s) [T2Space s.M] [Nonempty s.M]
    (d : IntOrientationData s.M) (h1 : ∀ x, d.orient x = 1)
    [Module.Free ℤ (Homology (TopCat.of s.M) 1)]
    [Module.Projective ℤ (boundaries (TopCat.of s.M) 0)]
    [Module.Projective ℤ (boundaries (TopCat.of s.M) 1)]
    [Module.Free ℤ (Homology (TopCat.of s.M) 2)]
    [Module.Finite ℤ (Homology (TopCat.of s.M) 2)]
    (B : IntH2Basis (TopCat.of s.M))
    (htopo : (2 : ℤ) ∣ SKEFTHawking.latticeSig
      (interMatrix (intFundamentalClassOfHomology d.fundClass) B) / 8) :
    (16 : ℤ) ∣ SKEFTHawking.latticeSig
      (interMatrix (intFundamentalClassOfHomology d.fundClass) B) :=
  SKEFTHawking.PinPlusCertSpinSeam.sixteen_dvd_latticeSig_of_orientation_certK hcert d h1
    (kronH2OfFree (TopCat.of s.M)) (kronH2OfFree_apply (TopCat.of s.M)) B htopo

end CertK

end SKEFTHawking.SixteenDvdKronFree
