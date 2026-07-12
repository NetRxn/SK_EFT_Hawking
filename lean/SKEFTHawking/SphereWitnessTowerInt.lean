/-
# Phase 5q.H (N5) — the WITNESS TOWER: the sphere witnesses' integral instance packages

The σ÷16 legs are kron-free (`SixteenDvdKronFree`): at a witness `M` they consume EXACTLY the
instance set `[Module.Free ℤ H₁] [Module.Projective ℤ (boundaries 0/1)] [Module.Free ℤ H₂]
[Module.Finite ℤ H₂]` + the basis datum `B : IntH2Basis`. This module PRODUCES that package at the
first witnesses, from the in-tree integral sphere tower (`sphere_homology_middleInt` /
`sphere_homology_high` / `topSphereIsoInt`) — no new homology computation is performed; the tower
already exists and is only *packaged* here.

* §0 — the UNIVERSAL half: `Module.Free/Projective ℤ (boundaries X n)` for EVERY space and degree
  (Kaplansky via `boundariesInt_free`), registered as instances. Two of the leg's five instance
  obligations are hereby discharged at every witness forever — nothing space-specific about them.
* §1 — the S⁴ homology package: `H₁ = H₂ = H₃ = 0` (from `sphere_homology_middleInt` at `n = 4`),
  as `Subsingleton` + `Module.Free` + `Module.Finite` instances; `H₄ ≅ ℤ` instances transported
  across `topSphereIsoInt`.
* §2 — the S⁴ cohomology package: `H²(S⁴;ℤ) = 0` and `H³(S⁴;ℤ) = 0` via the absolute integral UCT
  (`ucIntEquivOfFree`: `Hⁿ ≅ Dual Hₙ = Dual 0 = 0`), the rank-0 basis datum
  `sphere4IntH2Basis : IntH2Basis (Sph 4)` (the FIRST in-tree discharge of an `intH2_basis_datum`
  instance at a concrete witness), and the bonus `H⁴(S⁴;ℤ) ≅ ℤ` (UCT + `topSphereIsoInt` dual).
* §3 — the S⁴ integration check: `kronH2OfFree (Sph 4)` type-checks with NO leftover hypotheses
  (`kronH2Sphere4`) — the σ÷16 leg's full instance set is closed at S⁴ — and the witness value
  `latticeSig (interMatrix fc sphere4IntH2Basis) = 0` (`b₂(S⁴) = 0`, so σ(S⁴) = 0 through the SAME
  `latticeSig ∘ interMatrix` pipeline the leg divides by 16).
* §4 — the S²×S² witness: the product (co)homology is NOT computed in-tree (no Künneth / product-MV;
  honest freeze, mirroring `SphereProductBounding`'s datum design). `SphereProdHData` carries the
  frozen H-data (H₁ free, H₂ finite free, a rank-2 basis of H²); given it, the leg's instance set
  closes (`kronH2SphereProd`), and the Gram pin `interMatrix fc B = sphereProdFormDatum` (= `Hyp`,
  the `II(S²×S²) = H` datum of `SphereProductBounding`) discharges the leg's geometric
  `IsEvenUnimodular` AND `htopo` hypotheses and pins σ = 0 at the witness.
* §5 — the END-TO-END N4∘N5 integration: the kron-free σ÷16 leg INSTANTIATED at `M = S⁴`
  (`sixteen_dvd_latticeSig_sphere4`) — Mathlib's sphere smooth-manifold instances supply the
  charted structure, this module's package supplies every instance binder; the remaining open
  inputs at the witness are exactly `d` (orientation, N-fundClass) and `hv2` (spin, N6) — `htopo`
  is discharged here (`sphere4_interMatrix_htopo`).

No Erdős–Kaplansky-over-ℤ derivation anywhere (settled fork `5qH-fg-ek-over-Z-blocked`): S⁴'s
freeness comes from COMPUTATION (the sphere tower), S²×S²'s stays a disclosed frozen datum.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSphereMiddleInt
import SKEFTHawking.SingularRelBoundariesProjectiveInt
import SKEFTHawking.SingularAbsoluteUCInt
import SKEFTHawking.IntersectionMatrixInt
import SKEFTHawking.GMRokhlinDischarge
import SKEFTHawking.SphereProductBounding
import SKEFTHawking.SingularLineMinusPointInt
import SKEFTHawking.SixteenDvdKronFree

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularAbsoluteUCInt
open SKEFTHawking.SingularRelBoundariesProjectiveInt (boundariesInt_free)
open SKEFTHawking.SingularSphereMiddleInt (sphere_homology_middleInt)
open SKEFTHawking.SingularLineMinusPointInt (topSphereIsoInt)

namespace SKEFTHawking.SphereWitnessTowerInt

/-! ## §0. The universal half: boundaries are free/projective at EVERY space and degree -/

/-- **Absolute boundaries are free — as an instance** (Kaplansky, `boundariesInt_free`): a submodule
of the free `Finsupp` chain module over the PID ℤ. Universal in the space and the degree. -/
instance boundariesFree (X : TopCat) (n : ℕ) : Module.Free ℤ (boundaries X n) :=
  boundariesInt_free n

/-- **Absolute boundaries are projective — as an instance**: free ⟹ projective. This is the pair of
`Module.Projective ℤ (boundaries X 0/1)` obligations of the kron-free σ÷16 legs, discharged at EVERY
witness at once. -/
instance boundariesProjective (X : TopCat) (n : ℕ) : Module.Projective ℤ (boundaries X n) :=
  Module.Projective.of_free

/-- **A subsingleton module is finite** (`⊤ = ⊥` is finitely generated). Mathlib has
`Module.Free.of_subsingleton` but no matching `Module.Finite` form at this generality. -/
theorem moduleFinite_of_subsingleton (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    [Subsingleton M] : Module.Finite R M :=
  ⟨by rw [Subsingleton.elim (⊤ : Submodule R M) ⊥]; exact Submodule.fg_bot⟩

/-! ## §1. The S⁴ homology package: `H₁ = H₂ = H₃ = 0`, `H₄ ≅ ℤ` -/

/-- **`H₁(S⁴;ℤ) = 0`** — the sphere tower's middle vanishing at `(j, n) = (1, 4)`. -/
theorem sphere4_homology_one_eq_zero : ∀ x : Homology (Sph 4) 1, x = 0 :=
  sphere_homology_middleInt 1 4 one_pos (by norm_num)

/-- **`H₂(S⁴;ℤ) = 0`** — middle vanishing at `(2, 4)`. The leg's `H₂` witness value: `b₂(S⁴) = 0`. -/
theorem sphere4_homology_two_eq_zero : ∀ x : Homology (Sph 4) 2, x = 0 :=
  sphere_homology_middleInt 2 4 two_pos (by norm_num)

/-- **`H₃(S⁴;ℤ) = 0`** — middle vanishing at `(3, 4)` (feeds the degree-4 UCT for `H⁴ ≅ ℤ`). -/
theorem sphere4_homology_three_eq_zero : ∀ x : Homology (Sph 4) 3, x = 0 :=
  sphere_homology_middleInt 3 4 (by norm_num) (by norm_num)

instance : Subsingleton (Homology (Sph 4) 1) :=
  subsingleton_of_forall_eq 0 sphere4_homology_one_eq_zero

instance : Subsingleton (Homology (Sph 4) 2) :=
  subsingleton_of_forall_eq 0 sphere4_homology_two_eq_zero

instance : Subsingleton (Homology (Sph 4) 3) :=
  subsingleton_of_forall_eq 0 sphere4_homology_three_eq_zero

/-- The leg's `[Module.Free ℤ H₁]` obligation at S⁴ (the `Ext = 0` input): `H₁ = 0` is free. -/
instance : Module.Free ℤ (Homology (Sph 4) 1) := Module.Free.of_subsingleton ℤ _

/-- The leg's `[Module.Free ℤ H₂]` obligation at S⁴ (reflexivity input): `H₂ = 0` is free. -/
instance : Module.Free ℤ (Homology (Sph 4) 2) := Module.Free.of_subsingleton ℤ _

instance : Module.Free ℤ (Homology (Sph 4) 3) := Module.Free.of_subsingleton ℤ _

/-- The leg's `[Module.Finite ℤ H₂]` obligation at S⁴: `H₂ = 0` is finite. -/
instance : Module.Finite ℤ (Homology (Sph 4) 2) := moduleFinite_of_subsingleton ℤ _

/-- **`H₄(S⁴;ℤ) is free** (≅ ℤ): transported across `topSphereIsoInt 3`. Together with finiteness
below this makes the degree-4 homology reflexive — the input for `H⁴(S⁴;ℤ) ≅ ℤ` (§2). -/
instance : Module.Free ℤ (Homology (Sph 4) 4) :=
  Module.Free.of_equiv (topSphereIsoInt 3).symm

instance : Module.Finite ℤ (Homology (Sph 4) 4) :=
  Module.Finite.equiv (topSphereIsoInt 3).symm

/-! ## §2. The S⁴ cohomology package: `H² = H³ = 0`, the rank-0 basis, `H⁴ ≅ ℤ` -/

/-- **Cohomology vanishes where homology does** (absolute integral UCT, packaged): if
`Hₘ₊₂(X;ℤ) = 0` (and the UCT instance set holds) then `Hᵐ⁺²(X;ℤ) = 0` — `Hⁿ ≅ Dual Hₙ = Dual 0 = 0`
through `ucIntEquivOfFree`. -/
theorem cohomology_subsingleton_of_homology (X : TopCat) (M : ℕ)
    [Module.Free ℤ (Homology X (M + 1))]
    [Module.Projective ℤ (boundaries X M)]
    [Module.Projective ℤ (boundaries X (M + 1))]
    [Subsingleton (Homology X (M + 2))] :
    Subsingleton (Cohomology X (M + 2)) :=
  (ucIntEquivOfFree X M).toEquiv.subsingleton

/-- **`H²(S⁴;ℤ) = 0`** — the UCT flip of `H₂(S⁴;ℤ) = 0`. The basis of `H²` (the leg's `B` datum)
is therefore EMPTY: rank 0. -/
instance : Subsingleton (Cohomology (Sph 4) 2) :=
  haveI : Module.Free ℤ (Homology (Sph 4) (0 + 1)) :=
    inferInstanceAs (Module.Free ℤ (Homology (Sph 4) 1))
  haveI : Subsingleton (Homology (Sph 4) (0 + 2)) :=
    inferInstanceAs (Subsingleton (Homology (Sph 4) 2))
  cohomology_subsingleton_of_homology (Sph 4) 0

/-- **`H³(S⁴;ℤ) = 0`** — the UCT flip of `H₃(S⁴;ℤ) = 0` (over `H₂` free). -/
instance : Subsingleton (Cohomology (Sph 4) 3) :=
  haveI : Module.Free ℤ (Homology (Sph 4) (1 + 1)) :=
    inferInstanceAs (Module.Free ℤ (Homology (Sph 4) 2))
  haveI : Subsingleton (Homology (Sph 4) (1 + 2)) :=
    inferInstanceAs (Subsingleton (Homology (Sph 4) 3))
  cohomology_subsingleton_of_homology (Sph 4) 1

/-- **The S⁴ basis datum — `intH2_basis_datum` DISCHARGED at the first witness**: the rank-0 free
basis of `H²(S⁴;ℤ) = 0`. The σ÷16 leg's `B : IntH2Basis` input is a concrete construction here,
not a disclosed hypothesis. -/
noncomputable def sphere4IntH2Basis : IntH2Basis (Sph 4) :=
  ⟨0, Module.Basis.empty _⟩

/-- **`H⁴(S⁴;ℤ) ≅ ℤ`** — the degree-4 UCT (`H⁴ ≅ Dual H₄`, over `H₃ = 0` free) composed with the
dual of the sphere tower's top iso `H₄(S⁴;ℤ) ≅ ℤ` and `Dual ℤ ℤ ≅ ℤ`. The cohomological
fundamental-class side of the S⁴ witness. -/
noncomputable def sphere4Cohomology4Iso : Cohomology (Sph 4) 4 ≃ₗ[ℤ] ℤ :=
  haveI : Module.Free ℤ (Homology (Sph 4) (2 + 1)) :=
    inferInstanceAs (Module.Free ℤ (Homology (Sph 4) 3))
  (ucIntEquivOfFree (Sph 4) 2).trans
    (((topSphereIsoInt 3).symm.dualMap).trans (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ))

/-! ## §3. The S⁴ integration check: the leg's instance set is CLOSED at the first witness -/

/-- **The σ÷16 leg's Kronecker duality at S⁴ — every hypothesis DISCHARGED.** `kronH2OfFree (Sph 4)`
type-checks with no leftover instance obligations: `H₁` free (§1), boundaries projective (§0), `H₂`
finite free (§1). This is the N5 closure certificate for the first witness — the exact instance set
of `SixteenDvdKronFree.sixteen_dvd_latticeSig_of_orientation_spin_free` is produced by computation. -/
noncomputable def kronH2Sphere4 :
    Homology (Sph 4) 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology (Sph 4) 2) :=
  kronH2OfFree (Sph 4)

/-- **σ(S⁴) = 0 through the leg's own pipeline**: the intersection matrix on the rank-0 basis is the
empty matrix, whose `latticeSig` vanishes — for EVERY fundamental-class datum. The witness value the
σ÷16 conclusion `16 ∣ σ` is trivially consistent with (`b₂(S⁴) = 0`). -/
theorem sphere4_interMatrix_latticeSig (fc : IntFundamentalClass (Sph 4)) :
    latticeSig (interMatrix fc sphere4IntH2Basis) = 0 :=
  SKEFTHawking.GMRokhlin.latticeSig_fin_zero _

/-- **The leg's `htopo` binder (E2's topological factor `2 ∣ σ/8`) DISCHARGED at S⁴**: `σ = 0`
(rank-0 basis), so `σ/8 = 0` and `2 ∣ 0`. In the exact binder shape
`sixteen_dvd_latticeSig_of_orientation_spin_free` consumes — at the S⁴ witness the leg's open
inputs reduce to the orientation datum `d` and the spin certificate `hv2` alone. -/
theorem sphere4_interMatrix_htopo (fc : IntFundamentalClass (Sph 4)) :
    (2 : ℤ) ∣ latticeSig (interMatrix fc sphere4IntH2Basis) / 8 := by
  rw [sphere4_interMatrix_latticeSig fc]
  norm_num

/-! ## §4. The S²×S² witness: frozen H-data package (no Künneth in-tree — honest freeze) -/

section SphereProdWitness

open SKEFTHawking.SpinSigmaRoute (SphereProd sphereProdFormDatum
  sphereProdFormDatum_even_unimod sphereProdFormDatum_latticeSig)

/-- `S²×S²` as a `TopCat` — the topological carrier of `SpinSigmaRoute.SphereProd`
(`sphere (0 : ℝ³) 1 × sphere (0 : ℝ³) 1`, matching `SphereProductBounding`'s convention). -/
abbrev SphereProdT : TopCat := TopCat.of SphereProd

/-- **The frozen S²×S² H-data package.** The integral (co)homology of the product is NOT computed
in-tree (no Künneth / product Mayer–Vietoris; the standard values are `H₁ = 0`, `H₂ ≅ ℤ²` with
hyperbolic intersection form — Benedetti arXiv:1907.10297 Ch. 20, the same source as
`SphereProductBounding`'s pin). Mirroring that module's datum design, the H-data is carried FROZEN:
* `free1` — `H₁(S²×S²;ℤ)` free (true value: `0`);
* `free2`/`finite2` — `H₂(S²×S²;ℤ)` finite free (true value: `ℤ²`);
* `basis2` — a rank-2 basis of `H²(S²×S²;ℤ)` (the two sphere factors' duals).
Discharge = the product computation (Künneth or a two-chart product MV), a future arc. The two
boundary projectivities need NO freeze — §0 covers every space. -/
structure SphereProdHData where
  /-- Frozen: `H₁(S²×S²;ℤ)` is free (the true value is `0`). -/
  free1 : Module.Free ℤ (Homology SphereProdT 1)
  /-- Frozen: `H₂(S²×S²;ℤ)` is free (the true value is `ℤ²`). -/
  free2 : Module.Free ℤ (Homology SphereProdT 2)
  /-- Frozen: `H₂(S²×S²;ℤ)` is finite. -/
  finite2 : Module.Finite ℤ (Homology SphereProdT 2)
  /-- Frozen: the rank-2 basis of `H²(S²×S²;ℤ)` (the two factors' Poincaré duals). -/
  basis2 : Module.Basis (Fin 2) ℤ (Cohomology SphereProdT 2)

/-- The S²×S² basis datum in the leg's `IntH2Basis` shape: rank 2 (`b₂(S²×S²) = 2`). -/
def SphereProdHData.intH2Basis (d : SphereProdHData) : IntH2Basis SphereProdT :=
  ⟨2, d.basis2⟩

/-- **The σ÷16 leg's Kronecker duality at S²×S², given the frozen package** — the instance set
closes: `H₁` free / `H₂` finite free from the package, boundaries projective from §0. The S²×S²
analogue of `kronH2Sphere4`, conditional on exactly the frozen Künneth data. -/
noncomputable def kronH2SphereProd (d : SphereProdHData) :
    Homology SphereProdT 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology SphereProdT 2) :=
  haveI := d.free1
  haveI := d.free2
  haveI := d.finite2
  kronH2OfFree SphereProdT

/-- **The Gram pin discharges the leg's `IsEvenUnimodular` hypothesis at S²×S²**: if the witness's
intersection matrix on the frozen basis equals the pinned datum `sphereProdFormDatum = Hyp`
(`II(S²×S²) = H`), then it is even unimodular — the first of the two geometric Props the σ÷16 leg
consumes, discharged from `SphereProductBounding.sphereProdFormDatum_even_unimod`. -/
theorem sphereProd_interMatrix_evenUnimodular_of_gram (d : SphereProdHData)
    (fc : IntFundamentalClass SphereProdT)
    (hgram : interMatrix fc d.intH2Basis = sphereProdFormDatum) :
    IsEvenUnimodular (interMatrix fc d.intH2Basis) := by
  rw [hgram]; exact sphereProdFormDatum_even_unimod

/-- **σ(S²×S²) = 0 under the Gram pin** — the witness's signature through the leg's own
`latticeSig ∘ interMatrix` pipeline equals the pinned datum's (`hyp_latticeSig`), consistent with
the `SpinSigmaRoute` bounding story (`[S²×S²] = ∂(S²×D³)` ⟹ σ = 0). -/
theorem sphereProd_interMatrix_latticeSig_of_gram (d : SphereProdHData)
    (fc : IntFundamentalClass SphereProdT)
    (hgram : interMatrix fc d.intH2Basis = sphereProdFormDatum) :
    latticeSig (interMatrix fc d.intH2Basis) = 0 := by
  rw [hgram]; exact sphereProdFormDatum_latticeSig

/-- **The leg's `htopo` binder (E2's topological factor) DISCHARGED at S²×S² under the Gram pin**:
`σ = 0` (hyperbolic), so `2 ∣ σ/8`. Under the pin, the σ÷16 leg's two geometric Props
(`IsEvenUnimodular`, `htopo`) BOTH hold at the second witness — the open residue is the pin's own
discharge (the Künneth computation) plus the orientation/spin data. -/
theorem sphereProd_interMatrix_htopo_of_gram (d : SphereProdHData)
    (fc : IntFundamentalClass SphereProdT)
    (hgram : interMatrix fc d.intH2Basis = sphereProdFormDatum) :
    (2 : ℤ) ∣ latticeSig (interMatrix fc d.intH2Basis) / 8 := by
  rw [sphereProd_interMatrix_latticeSig_of_gram d fc hgram]
  norm_num

end SphereProdWitness

section Sphere4Leg

/-- S⁴ as a plain type. -/
abbrev SphereFour : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1

/-- S⁴ is nonempty (the first coordinate vector). Registered so the leg's `[Nonempty M]` binder
resolves at the witness. -/
instance : Nonempty SphereFour :=
  ⟨⟨EuclideanSpace.single 0 1, by rw [mem_sphere_zero_iff_norm]; simp⟩⟩

example : CompactSpace SphereFour := inferInstance
example : T2Space SphereFour := inferInstance
noncomputable example : ChartedSpace (EuclideanSpace ℝ (Fin 4)) SphereFour := inferInstance
example : (TopCat.of SphereFour) = Sph 4 := rfl

open SKEFTHawking.IntOrientationSection
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PoincareDualityWu (wuClass2)

/-- **The σ÷16 leg INSTANTIATED at the first witness (end-to-end N4∘N5 integration check).**
`sixteen_dvd_latticeSig_of_orientation_spin_free` applied at `M = S⁴` with `B = sphere4IntH2Basis`:
every instance obligation of the kron-free leg (H₁ free, boundaries 0/1 projective, H₂ finite free)
is discharged by THIS module's computed package — no leftover instance binders. The remaining
hypotheses are exactly the still-open nodes at the witness: the orientation datum `d` (fundamental
class), the spin certificate `hv2` (N6), and E2's topological factor `htopo` (N2). By
`sphere4_interMatrix_latticeSig` the conclusion's left side is `16 ∣ 0` — S⁴ is the consistency
witness (`b₂ = 0`), not a content witness; the content witness is S²×S² (§4). -/
theorem sixteen_dvd_latticeSig_sphere4
    (d : IntOrientationData SphereFour) (h1 : ∀ x, d.orient x = 1)
    (hv2 : wuClass2 (poincareDual4Mid_of_closed (M := SphereFour)) = 0)
    (htopo : (2 : ℤ) ∣ latticeSig
      (interMatrix (intFundamentalClassOfHomology d.fundClass) sphere4IntH2Basis) / 8) :
    (16 : ℤ) ∣ latticeSig
      (interMatrix (intFundamentalClassOfHomology d.fundClass) sphere4IntH2Basis) :=
  SKEFTHawking.SixteenDvdKronFree.sixteen_dvd_latticeSig_of_orientation_spin_free d h1
    sphere4IntH2Basis hv2 htopo

end Sphere4Leg

end SKEFTHawking.SphereWitnessTowerInt
