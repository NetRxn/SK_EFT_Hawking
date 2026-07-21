import Mathlib
import SKEFTHawking.CharSurfacePDTransport
import SKEFTHawking.PinPlusKTRankZeroBounding
import SKEFTHawking.PinPlusCharPairRealizationTied

/-!
# Audit M4, carrier level — the fence and the repair, on the LIVE `pinCharSurfaceOfBundled`

`CharSurfacePDTransport` settles the transport question abstractly. This module lands it on the
actual bridge the audit named:

* §1 `pinCharSurfaceOfBundled_H1Iso` (`rfl`) — the live constructor's `H1Iso` IS the raw
  Kronecker/UCT dual, so everything the abstract module proves applies verbatim.
* §2 `gaugeBundled` — the exploit at CARRIER level: a gauge `g` of the carried cohomology basis,
  with the enhancement moved as `hpolar` forces, yields a genuine `CharPairStrBundled` with the
  SAME surface, embedding, fundamental class, `hchar` tie and Brown invariant
  (`gaugeBundled_surf`/`_emb`/`_surfClass` by `rfl`, `gaugeBundled_brown`). The two carriers are
  indistinguishable as geometry-plus-grade.
* §3 `pinCharSurfaceOfBundled_gauge_H1Iso` — yet their `PinCharSurface` views disagree: the derived
  `H1Iso` moves by the transpose-inverse while the enhancement moves by `g`. So
  `EmbeddedCircle.qVal`, `kernelL` and `TaylorKernelVanishing` read gauge-dependent values.
* §4 `pinCharSurfaceOfBundledPD` — THE REPAIR: the same constructor with the Gram-corrected
  transport. `pinCharSurfaceOfBundledPD_gauge_q_invariant` is the property §3 lacks.
* §5 `pinCharSurfaceOfBundledPD_eq_of_rank_zero` — EQUIVALENCE CERTIFICATE: at rank zero the
  repaired constructor is *equal* to the live one, so the entire live
  `RankZeroSurfaceBoundingDatum`/`toLeaves` chain is unchanged by the repair.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open scoped Manifold
open SKEFTHawking.Brown
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularKroneckerEquiv SKEFTHawking.SingularKroneckerBasisBridge
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.CharSurface
open SKEFTHawking.CharSurfacePDTransport
open SKEFTHawking.PinPlusKTRankZeroBounding

namespace SKEFTHawking.CharSurfacePDBundled

variable {t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)} [T2Space t.M]

/-! ## §1. The live bridge uses the RAW Kronecker transport -/

/-- The audited fact, on the nose: `pinCharSurfaceOfBundled` fills `H1Iso` with the raw
Kronecker/UCT dual of the carried cohomology basis. Everything `CharSurfacePDTransport` proves
about that transport therefore applies to the live bridge without transport lemmas. -/
theorem pinCharSurfaceOfBundled_H1Iso (τ : CharPairStrBundled (𝓡 4) t) :
    (pinCharSurfaceOfBundled τ).H1Iso = homologyBasisOfCohomologyBasis (N := 0) τ.basis := rfl

/-! ## §2. The gauge, at carrier level -/

/-- **The carrier-level gauge.** Replace the carried cohomology basis `e` by `g ∘ e` and the
enhancement by the move `hpolar` forces (`gaugePullback q g.symm`). Every other field is copied.
The result is a genuine `CharPairStrBundled` — the discrepancy §3 exhibits is between two HONEST
carriers of one geometry, not between an honest one and a fake. -/
noncomputable def gaugeBundled (τ : CharPairStrBundled (𝓡 4) t)
    (g : (Fin τ.n → ZMod 2) ≃ₗ[ZMod 2] (Fin τ.n → ZMod 2)) : CharPairStrBundled (𝓡 4) t :=
  { τ with
    toCharPairStr := { τ.toCharPairStr with q := gaugePullback τ.q g.symm }
    basis := τ.basis.trans g
    hpolar := hpolar_gaugePullback (X := TopCat.of τ.surf.M) (N := 0) τ.q τ.basis g
      (fun a b => kroneckerH 2 (cupH a b) τ.surfClass) τ.hpolar }

omit [T2Space t.M] in
theorem gaugeBundled_surf (τ : CharPairStrBundled (𝓡 4) t)
    (g : (Fin τ.n → ZMod 2) ≃ₗ[ZMod 2] (Fin τ.n → ZMod 2)) :
    (gaugeBundled τ g).surf = τ.surf := rfl

omit [T2Space t.M] in
theorem gaugeBundled_emb (τ : CharPairStrBundled (𝓡 4) t)
    (g : (Fin τ.n → ZMod 2) ≃ₗ[ZMod 2] (Fin τ.n → ZMod 2)) :
    (gaugeBundled τ g).emb = τ.emb := rfl

omit [T2Space t.M] in
theorem gaugeBundled_surfClass (τ : CharPairStrBundled (𝓡 4) t)
    (g : (Fin τ.n → ZMod 2) ≃ₗ[ZMod 2] (Fin τ.n → ZMod 2)) :
    (gaugeBundled τ g).surfClass = τ.surfClass := rfl

omit [T2Space t.M] in
theorem gaugeBundled_n (τ : CharPairStrBundled (𝓡 4) t)
    (g : (Fin τ.n → ZMod 2) ≃ₗ[ZMod 2] (Fin τ.n → ZMod 2)) :
    (gaugeBundled τ g).n = τ.n := rfl

omit [T2Space t.M] in
/-- **The gauge preserves the computed grade.** `abk8 = brown ∘ q` is untouched, so the gauged
carrier is not merely legitimate — it sits in the same graded class as `τ`. -/
theorem gaugeBundled_brown (τ : CharPairStrBundled (𝓡 4) t)
    (g : (Fin τ.n → ZMod 2) ≃ₗ[ZMod 2] (Fin τ.n → ZMod 2)) :
    (gaugeBundled τ g).q.brown = τ.q.brown :=
  gaugePullback_brown τ.q g.symm

/-! ## §3. THE FENCE at carrier level — the `PinCharSurface` views disagree -/

/-- **The derived `H1Iso` moves CONTRAVARIANTLY under the carrier gauge**, while the enhancement
moves covariantly (`gaugeBundled` sets `q := gaugePullback τ.q g.symm` by construction). The
composite `Q.q ∘ H1Iso` — the value `EmbeddedCircle.qVal` reports, and the value
`TaylorKernelVanishing` tests on `kernelL` — is therefore not a function of the geometry.
`CharSurfacePDTransport.not_forall_kroneckerTransport_gauge_invariant` and
`.hyperbolic2_taylor_flip` supply the kernel-checked witnesses that the mismatch is real. -/
theorem pinCharSurfaceOfBundled_gauge_H1Iso (τ : CharPairStrBundled (𝓡 4) t)
    (g : (Fin τ.n → ZMod 2) ≃ₗ[ZMod 2] (Fin τ.n → ZMod 2))
    (x : Homology (TopCat.of τ.surf.M) 1) :
    (pinCharSurfaceOfBundled (gaugeBundled τ g)).H1Iso x
      = dualGauge g ((pinCharSurfaceOfBundled τ).H1Iso x) :=
  homologyCoords_gauge (N := 0) τ.basis g x

/-! ## §4. THE REPAIR at carrier level -/

/-- **The repaired bridge**: `pinCharSurfaceOfBundled` with the Gram-corrected (Poincaré-dual)
transport. Every other field is the live constructor's, verbatim — `q`, `basis`, `emb` are still
EXACTLY the carrier's, so no new tie is introduced; only the `H₁`-side coordinate convention is
fixed to the one a Guillou–Marin/Taylor enhancement requires. -/
noncomputable def pinCharSurfaceOfBundledPD (τ : CharPairStrBundled (𝓡 4) t) :
    PinCharSurface t.M 0 :=
  { pinCharSurfaceOfBundled τ with H1Iso := homologyBasisPD (N := 0) τ.q τ.basis }

@[simp] theorem pinCharSurfaceOfBundledPD_H1Iso (τ : CharPairStrBundled (𝓡 4) t) :
    (pinCharSurfaceOfBundledPD τ).H1Iso = homologyBasisPD (N := 0) τ.q τ.basis := rfl

@[simp] theorem pinCharSurfaceOfBundledPD_Q (τ : CharPairStrBundled (𝓡 4) t) :
    (pinCharSurfaceOfBundledPD τ).Q = τ.q := rfl

/-- **THE REPAIR'S HEADLINE at carrier level**: the enhancement value read through the repaired
bridge is the SAME for a carrier and for any gauge-equivalent one — the property §3 refutes for the
live bridge. This is what makes `qVal`/`TaylorKernelVanishing` statements about the geometry. -/
theorem pinCharSurfaceOfBundledPD_gauge_q_invariant (τ : CharPairStrBundled (𝓡 4) t)
    (g : (Fin τ.n → ZMod 2) ≃ₗ[ZMod 2] (Fin τ.n → ZMod 2))
    (x : Homology (TopCat.of τ.surf.M) 1) :
    (pinCharSurfaceOfBundledPD (gaugeBundled τ g)).Q.q
        ((pinCharSurfaceOfBundledPD (gaugeBundled τ g)).H1Iso x)
      = (pinCharSurfaceOfBundledPD τ).Q.q ((pinCharSurfaceOfBundledPD τ).H1Iso x) :=
  q_homologyBasisPD_gauge_invariant (N := 0) τ.q τ.basis g x

/-! ## §5. EQUIVALENCE CERTIFICATE — nothing live regresses -/

/-- **The live rank-zero chain is untouched.** At `τ.n = 0` the repaired bridge is *equal* to the
live one, so `RankZeroSurfaceBoundingDatum`, `RankZeroSurfaceWeldAnchor.toLeaves` and everything
downstream may be restated over `pinCharSurfaceOfBundledPD` with no proof changes. The M4 defect is
strictly a nonzero-rank one. -/
theorem pinCharSurfaceOfBundledPD_eq_of_rank_zero (τ : CharPairStrBundled (𝓡 4) t)
    (hn : τ.n = 0) :
    pinCharSurfaceOfBundledPD τ = pinCharSurfaceOfBundled τ := by
  haveI : IsEmpty (Fin τ.n) := by rw [hn]; infer_instance
  have h : homologyBasisPD (N := 0) τ.q τ.basis
      = homologyBasisOfCohomologyBasis (N := 0) τ.basis :=
    LinearEquiv.ext fun _ => Subsingleton.elim (α := Fin τ.n → ZMod 2) _ _
  -- `rw [h]` fails here (the `let __src` structure-update binder hides the occurrence); the
  -- `congrArg` form rewrites the field slot directly.
  exact congrArg (fun v => { pinCharSurfaceOfBundled τ with H1Iso := v }) h

/-! ## §6. BLAST RADIUS — the seam's DERIVED bases carry the identical defect

`pinCharSurfaceOfBundled` is not the only consumer of the raw transport: the live realized carrier's
seam bases `GeoRealizationTied.derivedEσ`/`derivedEτ` are the same Kronecker dual (pulled back along
the identification homeomorphism), and they feed `transportedBInc`'s kernel `L`, on which
`TaylorLegVanishes`/`JointLagrangian` evaluate the enhancements. This section makes that claim
KERNEL-CHECKED rather than traced by reading: no field of `GeoRealizationTied` mentions `bσ`/`bτ`,
so the very same geometry is a datum for the gauged bases, and its derived seam basis moves
contravariantly exactly as §3's does. -/

section Seam

open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

variable {nσ nτ : ℕ} {Sσ Sτ : TopCat}
  {bσ : Cohomology Sσ 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)}
  {bτ : Cohomology Sτ 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)}

/-- **Re-indexing a tied realization datum along a basis gauge.** Every field of
`GeoRealizationTied` is geometry (`bdry`/`Q`/`U`/`ι`/`homσ`/`homτ`/`eQ`) or a topological
certificate; none mentions `bσ`. So the identical datum is a legitimate realization for the gauged
basis `bσ.trans g` — the σ-side analogue of `gaugeBundled`. -/
def gaugeGeoRealizationTied (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (_g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)) :
    GeoRealizationTied Sσ Sτ (bσ.trans _g) bτ :=
  { d with }

@[simp] theorem gaugeGeoRealizationTied_U (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)) :
    (gaugeGeoRealizationTied d g).U = d.U := rfl

/-- **The seam's derived σ-basis is contravariant too.** Same geometry, gauged carried basis ⟹ the
seam's `H₁(Σ_σ)` coordinates move by the transpose-inverse, while `hpolar` moves `qσ` by `g`. So
`TaylorLegVanishes qσ qτ (ker (transportedBInc …))` — the realized carrier's item-4 Taylor leg — is
gauge-dependent at nonzero rank in exactly the way §3 exhibits for the surface bridge. Any
nonzero-rank use of the realized carrier's Taylor leg needs the same Gram correction. -/
theorem gaugeGeoRealizationTied_derivedEσ (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)) (x : Homology (sub d.U) 1) :
    (gaugeGeoRealizationTied d g).derivedEσ x = dualGauge g (d.derivedEσ x) :=
  homologyCoords_gauge (N := 0) bσ g _

end Seam

end SKEFTHawking.CharSurfacePDBundled
