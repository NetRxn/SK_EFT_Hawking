import Mathlib
import SKEFTHawking.PinPlusCharPairCarrier
import SKEFTHawking.RP2IntersectionForm
import SKEFTHawking.RP4CharSurfacePushforward

/-!
# Phase 5q.H W-B/W-C — the concrete `ℝP⁴` characteristic-pair witness + W-C surjectivity

The §13 `PinPlusCharPairData.rp4CharPairBundled` is a hypothesis-parameterized bundled witness
(`embSmooth`/`embInj` open, being proven on wt2/main). Those proofs are now merged
(`RP2EquatorialInclusion.contMDiff_embRP2`, `.embRP2_injective`), so this module **concretizes** the
witness — collapsing the two hypothesis fields against the merged proofs (the bundled witness pins
`k = 0`; `contMDiff_embRP2` is `k`-generic so we specialize) — and ships:

* **§1 CONCRETE WITNESS + non-vacuity grades.** `rp4CharPair` (no hypotheses); its odd generator grade
  `q.brown = 1 ∈ ZMod 8` and its `revStr` negation `= 7 = -1`.
* **§2 THE ANCHOR-CONNECTION THEOREMS.** The abstract v4 `hchar`/`hpolar` anchor CONTENT holds at the
  witness's concrete types: (a) the `hchar` pairing form (`RP4CharSurfacePushforward.hchar_pairing`
  at the witness's surface `emb₊[ℝP²]`), and (b) the `hpolar` basis-transport — the witness's
  enhancement polar form `(stdQuadratic 1).B` on the `rp2H1EquivFun`-image of `xRP2` equals `ℝP²`'s
  mod-2 self-intersection `intersectionForm xRP2 xRP2 = 1`.
* **§3 W-C SURJECTIVITY.** `charPairBrown` is additive and hits the generator `1`, so `n`-fold sums of
  the `ℝP⁴` witness realize EVERY value of `ZMod 8`: `charPairBrown_surjective`.
* **§4 FIRST NON-DEGENERACY.** The `ℝP⁴` class is `≠ 0` in the honest group (its grade `1 ≠ 0`) — the
  first kernel-checked non-triviality statement of the rebuilt substrate. No completeness/injectivity
  Prop is stated (those are W-D/W-E, with their own vacuity gates).
* **§5 THE hchar KILL (arm-4 R1).** With the characteristic-surface tie `hchar` on
  `CharPairStrBundled`, EVERY ℝP⁴ char-pair bundle's pushed-forward surface class is nonzero
  (`rp4_bundle_surfClass_pushforward_ne_zero`: `⟨x², emb₊[Σ]⟩ = μ(x²⌣x²) = 1`), so no bundle with
  an EMPTY characteristic surface exists on ℝP⁴ (`no_empty_surface_bundle_on_rp4`) — the closure of
  the W-D gate's §6 rank-0 fake-class exhibit (`fakeRP4RankZero`, now uninhabitable).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData SKEFTHawking.RP2EquatorialInclusion
open SKEFTHawking.RP4Witness SKEFTHawking.RP4Manifold SKEFTHawking.RP2IntersectionForm
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.SingularSurfaceIntersectionForm SKEFTHawking.RP4CharSurfacePushforward
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularFundamentalClass SKEFTHawking.PoincareDualityWu
open SKEFTHawking.SingularPD4Instances SKEFTHawking.RP2PointSet SKEFTHawking.RP4PointSet
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism

namespace SKEFTHawking.RP4CharPairWitness

/-! ## §1. The concrete `ℝP⁴` witness and its non-vacuity grades -/

/-- **THE CONCRETE `ℝP⁴` CHARACTERISTIC-PAIR WITNESS** — `rp4CharPairBundled` with its two open
smoothness/injectivity hypotheses discharged against the merged `contMDiff_embRP2` (specialized to the
carrier's `k = 0`) and `embRP2_injective`. A hypothesis-free inhabitant of `CharPairStrBundled (𝓡 4)
rp4SM` carrying the rank-1 odd enhancement `stdQuadratic 1`. -/
noncomputable def rp4CharPair : CharPairStrBundled (𝓡 4) rp4SM :=
  rp4CharPairBundled (contMDiff_embRP2 (k := 0)) embRP2_injective

/-- **THE REGULARITY-GENERIC ℝP⁴ WITNESS** (`rp4CharPairK k`) — the same hypothesis-free bundled
char-pair structure, carried by the `C^k` singular manifold `RP4Manifold.rp4SM_k k` for **every**
regularity `k : WithTop ℕ∞`, in particular the smooth/analytic `k = ⊤`. Nothing new is assumed: the
carrier's smooth atlas is `RP4Manifold.isManifold_rp4` (`Cω`, hence every `k`), the surface's is
`RP2Manifold.isManifold_rp2`, and the embedding's smoothness is `contMDiff_embRP2` — proved
`k`-generic (`contMDiff_embRP2_analytic`), so the `k = 0` specialisation was a *choice*, never a
constraint. This is the witness the smooth-category (`k ≥ 1`) Pin⁺ bordism target requires
(Phase 5q.H roadmap §2 leg 2). -/
noncomputable def rp4CharPairK (k : WithTop ℕ∞) : CharPairStrBundled (𝓡 4) (rp4SM_k k) :=
  rp4CharPairBundledK k contMDiff_embRP2 embRP2_injective

/-- **The lift is conservative** — the regularity-generic witness at `k = 0` IS the historical `C⁰`
witness, definitionally. Kernel-checked, so no consumer has to take the coincidence on trust: every
`k = 0` statement below is literally the old statement, and the `k ≥ 1` ones are genuinely new. -/
theorem rp4CharPairK_zero : rp4CharPairK 0 = rp4CharPair := rfl

/-- **The witness realizes the odd generator grade** `q.brown = 1 ∈ ZMod 8` — the structure-level
non-vacuity value (`stdQuadratic 1`, the odd order-16 generator). -/
theorem rp4CharPair_q_brown : rp4CharPair.toCharPairStr.q.brown = 1 := by
  show (stdQuadratic 1).brown = 1
  rw [brown_stdQuadratic, Nat.cast_one]

/-- **The `revStr`-reversed witness realizes the negated grade** `q.brown = 7 = -1 ∈ ZMod 8` — the ABK
reflection `β(-q) = -β(q)` on the witness (`brown_neg`), confirming the enhancement carries a genuine
signed grade, not a 2-torsion shadow. -/
theorem rp4CharPairRev_q_brown :
    (charPairBundledRevStr rp4CharPair).toCharPairStr.q.brown = 7 := by
  show (neg (stdQuadratic 1)).brown = 7
  rw [brown_neg, brown_stdQuadratic, Nat.cast_one]; decide

/-! ## §2. The `hchar` / `hpolar` anchor-connection theorems (abstract anchors meet the substrate) -/

/-- **The `hchar` anchor, discharged at the witness's types.** The witness stores `emb = embRP2`
(bundled as `embRP2C`) and `surf = ℝP²`; the v4 §2 `hchar` anchor's CONTENT for this concrete surface
IS `RP4CharSurfacePushforward.hchar_pairing`: for every `a ∈ H²(ℝP⁴;ℤ/2)`, the pairing of `a` against
the pushed-forward surface class `emb₊[ℝP²]` equals `μ(a ⌣ x²)` (the characteristic-surface condition
dual to `w₁² = x²`), given the degree-1 crux. This wraps it as the witness's instance-level anchor. -/
theorem rp4CharPair_hchar_pairing (hcrux : CruxPullbackGen)
    (a : Cohomology (TopCat.of RP4) 2) :
    kroneckerH 2 a (Homology.map embRP2C 2 (surfaceFundamentalClass (M := RP2)))
      = (poincareDual4Mid_of_closed (M := RP4)).mu
          (cupH24 a (RP4CohomologyLadder.xpow 2)) :=
  hchar_pairing hcrux a

/-- **`rp2H1EquivFun xRP2 = (fun _ => 1)`** — the enhancement basis datum sends the `H¹(ℝP²;ℤ/2)`
generator `xRP2` to the standard `Fin 1` coordinate `(fun _ => 1)` (design v4 §2 ▲A-5). -/
theorem rp2H1EquivFun_xRP2 : rp2H1EquivFun xRP2 = (fun _ => 1) := by
  funext i
  fin_cases i
  rw [rp2H1EquivFun, ← rp2H1Basis_apply 0, Module.Basis.equivFun_self]
  rfl

/-- **The `hpolar` anchor, discharged as a `Fin 1` basis-transport.** The witness's enhancement polar
form `(stdQuadratic 1).B`, evaluated on the `rp2H1EquivFun`-image of the `H¹(ℝP²;ℤ/2)` generator
`xRP2`, equals `ℝP²`'s mod-2 self-intersection `intersectionForm xRP2 xRP2 = 1`. Two independently
computed rank-1 odd quantities — the algebraic `stdQuadratic 1` diagonal form and the topological
`ℝP²` intersection form — meet at value `1`, the `hpolar` tie (`q.B = Σ`'s mod-2 intersection form). -/
theorem rp4CharPair_hpolar :
    rp4CharPair.toCharPairStr.q.B (rp2H1EquivFun xRP2) (rp2H1EquivFun xRP2)
      = intersectionForm (M := RP2) xRP2 xRP2 := by
  rw [intersectionForm_xRP2_self, rp2H1EquivFun_xRP2]
  show (stdQuadratic 1).B (fun _ => 1) (fun _ => 1) = 1
  decide

/-! ## §3. W-C surjectivity of the computed mod-8 grade `charPairBrown` -/

/-- The computed grade on any class is the carried enhancement's Brown invariant (`charPairBrown`
computes by `Quot.lift`). -/
theorem charPairBrown_mk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {k : WithTop ℕ∞}
    {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
    (prov : CharPairWProviderPerOp I k) (p : StrMfd (pinPlusCharPairData prov).toTangentialData) :
    charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = p.2.q.brown :=
  rfl

/-- **The `ℝP⁴` witness class carries computed grade `1`** — at **every** regularity `k`, the smooth
`k ≥ 1` category included (the grade is read off the carried enhancement `stdQuadratic 1`, which the
`k`-generic witness carries verbatim). -/
theorem charPairBrown_rp4_eq_one {k : WithTop ℕ∞} (prov : CharPairWProviderPerOp (𝓡 4) k) :
    charPairBrown prov
        (T2DataBordismGrp.mk (pinPlusCharPairData prov) ⟨rp4SM_k k, rp4CharPairK k⟩) = 1 := by
  rw [charPairBrown_mk]
  show (stdQuadratic 1).brown = 1
  rw [brown_stdQuadratic, Nat.cast_one]

/-- **W-C: the computed mod-8 grade is SURJECTIVE.** `charPairBrown` is additive and the `ℝP⁴` witness
realizes the generator `1`; since `1` generates `ZMod 8`, its `n`-fold sums realize every value —
`n • [ℝP⁴]` maps to `n • 1 = n`. The honest faithful carrier's grade hits all of `ZMod 8`. -/
theorem charPairBrown_surjective {k : WithTop ℕ∞} (prov : CharPairWProviderPerOp (𝓡 4) k) :
    Function.Surjective (charPairBrown prov) := by
  intro y
  refine ⟨y.val • T2DataBordismGrp.mk (pinPlusCharPairData prov) ⟨rp4SM_k k, rp4CharPairK k⟩, ?_⟩
  rw [map_nsmul, charPairBrown_rp4_eq_one prov, nsmul_eq_mul, mul_one, ZMod.natCast_val,
    ZMod.cast_id]

/-! ## §4. First non-degeneracy of the rebuilt substrate -/

/-- **THE FIRST NON-TRIVIALITY OF THE HONEST CARRIER.** The `ℝP⁴` characteristic-pair class is `≠ 0`
in the certified bordism group `T2DataBordismGrp (pinPlusCharPairData prov)`: its computed grade is
`1 ≠ 0 ∈ ZMod 8`, and `charPairBrown` (a group hom) sends `0 ↦ 0`. The rebuilt substrate is NOT
collapsed — the class survives. (No completeness/injectivity Prop is asserted; those are W-D/W-E.) -/
theorem charPairBrown_rp4_ne_zero {k : WithTop ℕ∞} (prov : CharPairWProviderPerOp (𝓡 4) k) :
    T2DataBordismGrp.mk (pinPlusCharPairData prov) ⟨rp4SM_k k, rp4CharPairK k⟩ ≠ 0 := by
  intro h
  have h0 : charPairBrown prov
      (T2DataBordismGrp.mk (pinPlusCharPairData prov) ⟨rp4SM_k k, rp4CharPairK k⟩) = 0 := by
    rw [h, map_zero]
  rw [charPairBrown_rp4_eq_one prov] at h0
  exact absurd h0 (by decide)

/-! ## §5. THE hchar KILL — no empty-surface char-pair bundle exists on ℝP⁴ (arm-4 R1) -/

/-- **The pushed-forward surface class of EVERY ℝP⁴ char-pair bundle is NONZERO.** Instantiate
the bundle's `hchar` tie at `a = x²`: `⟨x², emb₊[Σ]⟩ = μ(x² ⌣ x²) = 1 ≠ 0`
(`RP4WuAssembly.mu_cupH24_xpow2_xpow2`), so `emb₊[Σ] ≠ 0`. The characteristic-surface tie makes
the ℝP⁴ cup-square topology bind every inhabitant — a fake class can no longer carry a surface
whose class dies. -/
theorem rp4_bundle_surfClass_pushforward_ne_zero {k : WithTop ℕ∞}
    (σ : CharPairStrBundled (𝓡 4) (rp4SM_k k)) :
    Homology.map (⟨σ.emb, σ.embSmooth.continuous⟩ :
        C(↑(TopCat.of σ.surf.M), ↑(TopCat.of (rp4SM_k k).M))) 2 σ.surfClass ≠ 0 := by
  intro h0
  haveI : T2Space (rp4SM_k k).M := inferInstanceAs (T2Space RP4)
  haveI : Nonempty (rp4SM_k k).M := inferInstanceAs (Nonempty RP4)
  have h := (σ.hchar (RP4CohomologyLadder.xpow 2)).trans
    SKEFTHawking.RP4WuAssembly.mu_cupH24_xpow2_xpow2
  rw [h0, map_zero] at h
  exact zero_ne_one h

/-- **No ℝP⁴ char-pair bundle has an EMPTY characteristic surface** — with `Σ = ∅` the surface
class vanishes (empty-space homology is subsingleton), so its pushforward is `0`, contradicting
`rp4_bundle_surfClass_pushforward_ne_zero`. This is the `hchar` KILL of the W-D vacuity gate's §6
rank-0 fake-class exhibit (`fakeRP4RankZero`): the exhibit is now UNINHABITABLE, so
`KTKernelCard`'s quantifier no longer ranges over geometrically impossible ℝP⁴ classes. -/
theorem no_empty_surface_bundle_on_rp4 {k : WithTop ℕ∞}
    (σ : CharPairStrBundled (𝓡 4) (rp4SM_k k))
    (h : IsEmpty σ.surf.M) : False := by
  haveI := h
  exact rp4_bundle_surfClass_pushforward_ne_zero σ
    (by rw [Subsingleton.elim σ.surfClass 0, map_zero])

end SKEFTHawking.RP4CharPairWitness
