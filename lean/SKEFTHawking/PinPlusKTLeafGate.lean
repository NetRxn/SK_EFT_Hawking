/-
# Phase 5q.H W-D GATE ROUND 10 (fresh-context VACUITY ATTACK on the W-D LEAF ROW)

Adversarial gate findings against the full W-D leaf row (`PinPlusKTSurgeryTrace`'s
`AmbientSurgeryDatum`; `PinPlusKTLemma53Wave`'s `Div32BoundingDatum` / `DualSpinForwardDatum` /
`EnriquesDatum` / `KTSpinPresentationDatum`; the assembly `kt_equiv_zmod16_of_leaves`), under the
binding round-8 spec (`PinPlusKTSectorGate`) and round-9 spec (`PinPlusKTStepGate`). Verdict:
**PASS WITH A SHARPENED LEAF ROW AND BINDING PER-LEAF SPECS** — no leaf admits a
zero-geometric-input inhabitation OFF the fenced degenerate worlds, the assembly consumes exactly
the round-8 triple, and the round-9 route-(b) fence (`hΦgeo`) genuinely holds its load; BUT the
row as shipped contains one ABSORPTION (the C-leaf contains the B-leaf: `EnriquesDatum` is
redundant in the assembly, §4), one CONCLUSION-FAKEABLE leaf (`DualSpinForwardDatum` sits at
exactly `KTNonSplit` strength — kernel-encoded locating equivalence, §3), one decorative-field
defect (`EnriquesDatum` ⟺ bare `KummerWitness.1`, §5), and a stale provider rider (the
`addClosure` residual is CLOSED; the sole remaining residual is `cylData`, §1).

## Per-leaf verdict table

* **`AmbientSurgeryDatum`** — **PASS with spec notes** (§2).
  (i) The `(x, hx0, hxq)` fields are DECORATIVE w.r.t. the assembly: no consumer reads them
  (`ktSurgeryStep_of_ambientDatum` uses only `hrank`/`b`/`hT2`/`hBor`; the `0 < n` domain fact is
  re-supplied by the supply's own hypothesis). Kernel-encoded: the x-free tether supply already
  discharges `KTSurgeryReduces` (`ktSurgeryReduces_of_tetherSupply`), and the ambient supply
  projects onto it (`tetherSupply_of_ambientDatumSupply`). The x-fields are KT-fidelity GUIDANCE
  (the §1 enhancement seam) — they make the leaf HARDER to inhabit, never easier: no vacuity hole.
  (ii) Wholesale `cylBorTethered` reuse is excluded at the kernel: the datum's tether ends differ
  in rank (`ambientSurgeryDatum_rank_ne`), and the only in-tree tether constructor is diagonal
  (σ = σ, same rank). The tether demand is at REPRESENTATIVE level (`hBor` names the structures,
  not classes), so quotient-level `[p'] = [p]` manipulation cannot reach it.
  (iii) FATTEN-FIRST POISONING (prose, binding): a single-`p` datum construction certifies
  nothing — for `p` of the shape `q ⊔ h` (`h` a rank-2 null-tethered block) a datum at `p` with
  `p' := q` records one genuine null tether, NOT the KT surgery for arbitrary `p`. The unit of
  progress is the ∀-`p` SUPPLY; per-`p` constructions are non-vacuity demonstrators only.
  (iv) The supply is STRICTLY one-way vs `KTSurgeryReduces`: KTSR is kernel-collapse-dischargeable
  (G9-1) but the supply demands genuine tethers even on the `[p] = 0` fibre — extra strength =
  harder inhabitation (sound); note a future no-go against the SUPPLY would not kill KTSR.
* **`Div32BoundingDatum`** — **PASS** (§3). The Rokhlin consumption is honest:
  `SmoothSpinManifold4.rokhlin` is the kernel-pure `16 ∣ latticeSig form` DERIVED from
  `even_unimod` + `topo` (no free σ field, no global Rokhlin hypothesis), and the K3 witness
  (`k3Spin`, `σ = −16`, `topo` by `decide` on `2 ∣ −2`) is genuine. TWO notes: (a) the structure
  is a LATTICE abstraction (`SmoothSpinManifold4` = rank/form/even_unimod/topo — no manifold), so
  the datum's geometric names (dual spin submanifold, double cover) are prose; its formal content
  is exactly "`sigM` = twice an even-unimodular-`topo` signature" (hence `32 ∣ sigM` — and every
  `32ℤ` value is classically realizable by `±E₈`-blocks, so the datum carries no more information
  than `32 ∣ sigM`). (b) As shipped it was ASSEMBLY-ORPHANED — no theorem tied it to `hfwd`; the
  tie is now kernel-encoded (`hfwd_of_boundingDatumSupply`): a per-bounding-class supply of
  bounding data IS `hfwd`. That supply form is the sharper Direction-A construction target.
* **`DualSpinForwardDatum`** — **PASS with BINDING SPEC** (§3, the round-10 tie). σ enters as a
  datum field (via `R : SpinSigmaPresentation`), but `hg` + `sig_eq` pin it nontrivial (a zero σ
  refutes `hg`). HOWEVER the datum as a whole is CONCLUSION-FAKEABLE: with Rokhlin division
  (`hdvd`) the pure-arithmetic hom `Φ := (σ/16) • k₀` (`sigmaQuotientPhi`) satisfies `hΦg` (given
  the ÷32-upper `2k₀ = 0`) and `hfwd` (given `KTNonSplit` ITSELF) — kernel-encoded
  `dualSpinForwardDatum_of_ktNonSplit`, giving the locating equivalence
  `dualSpinForwardDatum_iff_ktNonSplit`: modulo presentation infrastructure + the ÷32-upper, the
  leaf sits at EXACTLY conclusion strength. It is not vacuous (inhabiting it proves `KTNonSplit`;
  it is UNINHABITABLE in the split world — `hfwd[g]` would force `32 ∣ −16`), and the honest
  construction route (the real forgetful map's "only if") proves `hfwd` WITHOUT consuming
  `KTNonSplit`. But a "dA constructed" claim is progress ONLY under a NON-CIRCULARITY AUDIT: its
  `hfwd` proof must consume neither `KTNonSplit` nor the k₀-torsion (else it is the
  `sigmaQuotientPhi` fake, witnessed here). This is G9-4's "assume the conclusion" pattern at the
  leaf level.
* **`EnriquesDatum`** — **FAIL AS SHAPED → frozen replacement spec** (§5). The `[Ha]` fields are
  decorative: `sigK3`/`hsigK3` are a self-inhabiting constant pair (`⟨−16, rfl⟩` always), consumed
  by NO conclusion except a re-derivation of the banked `not_thirtytwo_dvd_neg_sixteen`; the
  remaining fields are literally the `EmptySigmaRepresentable` witness. Kernel-encoded:
  `enriquesDatum_iff_kummerRep` — the datum is EQUIVALENT to bare `KummerWitness.1`; the
  "Enriques" content (w₂ ≠ 0, π₁ = ℤ/2, the line bundle) has no formal footprint. REPLACEMENT
  SPEC: the B-leaf construction target is `GeometricSpinRepresentable prov k₀` (the honest
  IsEmpty-Σ form) — the real Enriques/K3 output is honestly-empty-Σ so the upgrade costs the
  construction nothing, it is STRICTLY sharper than the broad rank-0 form (G8-5/G9-5 seam), the
  broad form follows via `emptySigmaRepresentable_of_geometric`, and it supplies EXACTLY the
  C-leaf's genuine `hΦgeo` residual (§4).
* **`KTSpinPresentationDatum`** — **PASS with spec + THE ABSORPTION FINDING** (§4). The round-9
  route-(b) fence holds: `hΦgeo` is genuinely load-bearing (the `sigmaQuotientPhi` fake cannot
  cross it without `GeometricSpinRepresentable prov k₀` as input). But `hΦgeo` AT the generator
  composed with `hΦg` yields `GeometricSpinRepresentable prov k₀` outright
  (`geometricKummer_of_ktSpinPresentationDatum`) — hence `KummerWitness.1`
  (`kummerWitness1_of_ktSpinPresentationDatum`) and hence `SpinImageIsTwo` from the C-leaf ALONE
  (`spinImageIsTwo_of_ktSpinPresentationDatum`): **the C-leaf ABSORBS the B-leaf.** The full
  locating equivalence is kernel-encoded (`ktSpinPresentationDatum_iff_content`): modulo
  presentation infrastructure, the datum ⟺ `{SpinImageIsTwo ∧ GeometricSpinRepresentable k₀}`.
  The Φ-dressing is interchangeable; the construction target is exactly that pair. The round-9
  co-obligation `SectorIsGeometric` is automatic at this strength
  (`sectorIsGeometric_of_siit_of_geomKummer`) — consistent with `sectorIsGeometric_of_ktSpinPresentationDatum`.
  The two Benedetti freezes `hA`/`hB` are consumed shape-unchanged (statement-frozen Props of
  `R`, transported honestly through `spinImageCyclic_of_presentation`).
* **The assembly** — **PASS, SHARPENED** (§6). `kt_equiv_zmod16_of_leaves` consumes the leaves
  ONLY through the round-8 triple (proof inspection: exactly
  `kt_equiv_zmod16_of_sector prov hKRS (SIIT of dC,dE) (KTNS of dA)`; no side-channel). Degenerate
  coverage verified: the split world kills exactly dA; the collapsed+nonsplit world kills hKRS, dE
  AND dC (dC ⟹ `KummerWitness.1` ⟹ `k₀ = 0` under collapse, refuting `KTNonSplit`). SHARPENING:
  dE is REDUNDANT — the two-leaf assembly `kt_equiv_zmod16_of_two_leaves` `{hKRS, dC, dA}` is the
  assembly of record; dE survives only as route-documentation for constructing the B-content.

## G8-1 rider status — UPDATED (the brief's item 5, kernel-encoded §1)
`PinPlusCharPairWProviderClosed.ofCylinderEngineClosed` DISCHARGED the `addClosure` residual
(`WAdmPinned.add`, the ⊔ Lefschetz–Wu block assembly with `sumRelFundClass`). The provider's
inhabitation dependency is now the SINGLE residual
`cylData : ∀ {s} (σ : CharPairStrBundled I s), CylWAdmData s`
(kernel-encoded: `nonempty_provider_of_cylData`). The `PinPlusKTSurgeryTrace` /
`PinPlusKTLemma53Wave` headers still say "the two OPEN Track-2 residuals" — STALE by one (for the
lead; this gate does not edit attacked modules). Every per-`prov` result remains CONDITIONAL with
zero live instances until `cylData` lands; the rider otherwise applies unchanged.

## FROZEN ROUND-10 SPEC (binding on the W-D construction waves)
1. **KRS leaf**: the construction unit is the ∀-`p` tether SUPPLY (x-free minimal form,
   `ktSurgeryReduces_of_tetherSupply`); single-`p` `AmbientSurgeryDatum` constructions are
   non-vacuity demonstrators only (fatten-first poisoning); the `(x, hx0, hxq)` fields are
   enhancement-seam guidance, not load-bearing.
2. **B-leaf**: the target is `GeometricSpinRepresentable prov (ktKernelRep prov)` (IsEmpty-Σ), NOT
   `EnriquesDatum` (≡ broad `KummerWitness.1`, decorative dressing). Broad-form consumers take it
   via `emptySigmaRepresentable_of_geometric`.
3. **C-leaf**: the construction target is exactly `{SpinImageIsTwo (cyclic route), GeometricSpinRepresentable k₀}`
   (`ktSpinPresentationDatum_iff_content`); a "Φ built" claim must carry the `hΦgeo` witness
   (round-9 items 3b/4 unchanged) and note that the B-content arrives WITH it (no double-counting
   dC + dE as independent progress).
4. **A-leaf**: a `DualSpinForwardDatum` construction must pass the NON-CIRCULARITY AUDIT — its
   `hfwd` proof consumes neither `KTNonSplit` nor `k₀ + k₀ = 0` (else it is the `sigmaQuotientPhi`
   fake); the sharper honest target is the bounding-datum supply (`hfwd_of_boundingDatumSupply`).
5. **Assembly of record** = `kt_equiv_zmod16_of_two_leaves` (`{KernelReducesToSpin-supply, dC, dA}`);
   dE is retired as an assembly input.
6. **Provider rider**: every per-`prov` result is conditional on the SINGLE residual `cylData`
   (G8-1 as updated here).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTLemma53Wave
import SKEFTHawking.PinPlusCharPairWProviderClosed

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData SKEFTHawking.RP4CharPairWitness
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute
open SKEFTHawking.PinPlusKTSectorGate
open SKEFTHawking.PinPlusKTStepGate
open SKEFTHawking.PinPlusKTSurgeryTrace
open SKEFTHawking.PinPlusKTLemma53Wave
open SKEFTHawking.PinPlusCharPairWProviderTransport

namespace SKEFTHawking.PinPlusKTLeafGate

variable {k : WithTop ℕ∞}

/-! ## §1. G10-1 — the provider rider, UPDATED: the sole remaining residual is `cylData`

The round-8 rider (G8-1) named TWO residuals (`cylData` + `addClosure`).
`PinPlusCharPairWProviderClosed` closed `addClosure` (`WAdmPinned.add`); the kernel-checked
inhabitation dependency is now `cylData` alone. -/

section Provider

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **The UPDATED provider-inhabitation dependency** (G10-1, superseding the two-residual G8-1
form): `Nonempty (CharPairWProviderPerOp I k)` follows from the σ-threaded concrete-cylinder
residual `cylData` ALONE — the `addClosure` residual is discharged in-tree
(`ofCylinderEngineClosed` / `WAdmPinned.add`). Until `cylData` lands, every per-`prov` W-D
statement has zero live instances (rider otherwise unchanged). -/
theorem nonempty_provider_of_cylData
    (cylData : ∀ {s : SingularManifold.{0} PUnit.{1} k I},
      CharPairStrBundled I s → CylWAdmData s) :
    Nonempty (CharPairWProviderPerOp I k) :=
  ⟨CharPairWProviderPerOp.ofCylinderEngineClosed cylData⟩

end Provider

/-! ## §2. G10-2 — `AmbientSurgeryDatum`: the x-fields are assembly-decorative; the minimal step
leaf is the x-free tether supply; diagonal-tether reuse is rank-excluded -/

variable {prov : CharPairWProviderPerOp (𝓡 4) k}
variable {p : StrMfd (pinPlusCharPairData prov).toTangentialData}

/-- **The datum's tether ends differ in rank** (G10-2ii): `hrank` forces `p'.2.n ≠ p.2.n`, so the
diagonal tether constructor (`cylBorTethered`, the ONLY in-tree tether — same structure at both
ends, hence same rank) can never supply the datum's `hBor`. Wholesale cylinder reuse is excluded
at the kernel, not merely by inspection. -/
theorem ambientSurgeryDatum_rank_ne (d : AmbientSurgeryDatum prov p) : d.p'.2.n ≠ p.2.n := by
  have := d.hrank
  omega

/-- **The x-FREE minimal step supply already discharges `KTSurgeryReduces`** (G10-2i): a supply of
strictly-rank-dropping tethered steps — with NO isotropic-class fields and NO exact-rank-drop
demand — meets the step-Prop. Together with `tetherSupply_of_ambientDatumSupply` this pins the
`AmbientSurgeryDatum` fields `(x, hx0, hxq)` (and the exactness of `hrank`) as KT-fidelity
GUIDANCE, not load-bearing content: they make the leaf harder to inhabit, never easier. -/
theorem ktSurgeryReduces_of_tetherSupply (prov : CharPairWProviderPerOp (𝓡 4) k)
    (H : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
      0 < p.2.n →
      ∃ p' : StrMfd (pinPlusCharPairData prov).toTangentialData,
        p'.2.n < p.2.n ∧
          ∃ b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p'.1 p.1,
            T2Space b.W ∧ Nonempty (CharPairBorRealizedTethered b p'.2 p.2)) :
    KTSurgeryReduces prov := by
  intro p hbrown hpos
  obtain ⟨p', hlt, b, hT2, hBor⟩ := H p hbrown hpos
  exact surgeryStep_of_tethered prov hlt b hT2 hBor

/-- **The ambient-datum supply projects onto the x-free tether supply** (G10-2i, the other
direction of the locating pair): every consumer path of the ambient supply factors through this
projection — the assembly never reads `x`, `hx0`, `hxq`, nor the exactness of the rank drop. -/
theorem tetherSupply_of_ambientDatumSupply (prov : CharPairWProviderPerOp (𝓡 4) k)
    (H : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
      0 < p.2.n → AmbientSurgeryDatum prov p) :
    ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
      0 < p.2.n →
      ∃ p' : StrMfd (pinPlusCharPairData prov).toTangentialData,
        p'.2.n < p.2.n ∧
          ∃ b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p'.1 p.1,
            T2Space b.W ∧ Nonempty (CharPairBorRealizedTethered b p'.2 p.2) := by
  intro p hbrown hpos
  obtain d := H p hbrown hpos
  exact ⟨d.p', ambientSurgeryDatum_lt d, d.b, d.hT2, d.hBor⟩

/-! ## §3. G10-3/G10-4 — Direction A: the bounding-supply tie, and the conclusion-fakeable leaf

`Div32BoundingDatum` was assembly-orphaned (banked arithmetic with no formal tie to `hfwd`);
`hfwd_of_boundingDatumSupply` closes that seam and names the sharper Direction-A target. Then the
round-10 tie: `sigmaQuotientPhi` — the pure-arithmetic `Φ := (σ/16) • k₀` — inhabits
`DualSpinForwardDatum` from `{presentation infra, ÷32-upper, KTNonSplit}` with ZERO forgetful-map
geometry, locating the leaf at exactly conclusion strength
(`dualSpinForwardDatum_iff_ktNonSplit`). -/

section CarrierForward

variable {X : Type*} [TopologicalSpace X] {k' : WithTop ℕ∞}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {ξ : TangentialData X k' I'}

/-- **The bounding-datum supply IS `hfwd`** (G10-3, the orphan repair): if every `Φ`-bounding
class comes with a `Div32BoundingDatum` computing its signature (the honest KT anatomy: the
`w₁(W)`-dual spin `V` + the σ-doubling), then the leaf field `hfwd` follows from the banked
arithmetic (`thirtytwo_dvd_sigM` = σ-doubling + in-tree Rokhlin). This formally ties the §A.1
arithmetic to the §A.2 leaf and is the SHARPER Direction-A construction target: the open geometric
content is exactly "Pin⁺-bounding produces the dual-spin datum", nothing more. -/
theorem hfwd_of_boundingDatumSupply (prov : CharPairWProviderPerOp (𝓡 4) k)
    (R : SpinSigmaPresentation ξ)
    (Φ : DataBordismGrp ξ →+ T2DataBordismGrp (pinPlusCharPairData prov))
    (H : ∀ x, Φ x = 0 → ∃ d : Div32BoundingDatum, d.sigM = R.sig x) :
    ∀ x, Φ x = 0 → (32 : ℤ) ∣ R.sig x := by
  intro x hx
  obtain ⟨d, hd⟩ := H x hx
  exact hd ▸ d.thirtytwo_dvd_sigM

/-- **The σ-derived arithmetic hom `Φ := (σ/16) • k₀`** (G10-4, the fake's engine). Given Rokhlin
division (`hdvd`), the map `w ↦ (R.sig w / 16) • k₀` is a genuine `AddMonoidHom` — built from the
presentation's σ and the carrier's `k₀` ALONE, with zero forgetful-map geometry. It is the
round-10 analogue of G9-4's `k₀`-generated fake, now landing at the LEAF level. -/
noncomputable def sigmaQuotientPhi (prov : CharPairWProviderPerOp (𝓡 4) k)
    (R : SpinSigmaPresentation ξ) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x) :
    DataBordismGrp ξ →+ T2DataBordismGrp (pinPlusCharPairData prov) :=
  AddMonoidHom.mk' (fun w => (R.sig w / 16) • ktKernelRep prov) (by
    intro a b
    show (R.sig (a + b) / 16) • ktKernelRep prov
        = (R.sig a / 16) • ktKernelRep prov + (R.sig b / 16) • ktKernelRep prov
    obtain ⟨ca, hca⟩ := hdvd a
    obtain ⟨cb, hcb⟩ := hdvd b
    rw [map_add, hca, hcb, ← mul_add,
      Int.mul_ediv_cancel_left _ (by norm_num : (16 : ℤ) ≠ 0),
      Int.mul_ediv_cancel_left _ (by norm_num : (16 : ℤ) ≠ 0),
      Int.mul_ediv_cancel_left _ (by norm_num : (16 : ℤ) ≠ 0), add_zsmul])

@[simp] theorem sigmaQuotientPhi_apply (prov : CharPairWProviderPerOp (𝓡 4) k)
    (R : SpinSigmaPresentation ξ) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x) (w : DataBordismGrp ξ) :
    sigmaQuotientPhi prov R hdvd w = (R.sig w / 16) • ktKernelRep prov :=
  rfl

/-- **The fake `Φ` hits the generator hypothesis `hΦg`** given only the ÷32-upper (`k₀`
2-torsion): `Φ[g] = (−16/16) • k₀ = −k₀ = k₀`. -/
theorem sigmaQuotientPhi_g (prov : CharPairWProviderPerOp (𝓡 4) k)
    (R : SpinSigmaPresentation ξ) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x) {g : StrMfd ξ}
    (hg : R.sig (DataBordismGrp.mk ξ g) = -16)
    (h2 : ktKernelRep prov + ktKernelRep prov = 0) :
    sigmaQuotientPhi prov R hdvd (DataBordismGrp.mk ξ g) = ktKernelRep prov := by
  rw [sigmaQuotientPhi_apply, hg, show ((-16 : ℤ) / 16) = -1 by norm_num, neg_one_zsmul]
  exact neg_eq_of_add_eq_zero_right h2

/-- **The fake `Φ` satisfies the KT "only if" field `hfwd`** given the CONCLUSION `KTNonSplit`
itself (+ the ÷32-upper): `Φ x = (σx/16) • k₀ = 0` with `σx/16` odd would force `k₀ = 0`; even
gives `32 ∣ σx`. The `hfwd` field is therefore derivable from `KTNonSplit` — the leaf cannot pin
the genuine "bounding ⟹ ÷32" geometric content by shape. -/
theorem sigmaQuotientPhi_fwd (prov : CharPairWProviderPerOp (𝓡 4) k)
    (R : SpinSigmaPresentation ξ) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (hns : KTNonSplit prov) (h2 : ktKernelRep prov + ktKernelRep prov = 0) :
    ∀ x, sigmaQuotientPhi prov R hdvd x = 0 → (32 : ℤ) ∣ R.sig x := by
  intro x hx
  obtain ⟨c, hc⟩ := hdvd x
  rw [sigmaQuotientPhi_apply, hc,
    Int.mul_ediv_cancel_left _ (by norm_num : (16 : ℤ) ≠ 0)] at hx
  rcases Int.even_or_odd c with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨j, by rw [hc, hj]; ring⟩
  · exfalso
    apply hns
    have hck : c • ktKernelRep prov = ktKernelRep prov := by
      rw [hj, add_zsmul, one_zsmul, mul_comm, mul_zsmul,
        show (2 : ℤ) • ktKernelRep prov = 0 by rw [two_zsmul]; exact h2,
        smul_zero, zero_add]
    rw [hck] at hx
    exact hx

/-- **THE ROUND-10 TIE, constructive half** (G10-4): `DualSpinForwardDatum` is inhabitable from
`{presentation infra (R, g, hg, hdvd), the ÷32-upper h2, KTNonSplit}` with ZERO forgetful-map
geometry — the fake `Φ := (σ/16) • k₀` fills every field. A Direction-A construction wave whose
`hfwd` proof consumes `KTNonSplit` or the `k₀`-torsion has built THIS, i.e. nothing (the
non-circularity audit, frozen spec item 4). -/
theorem dualSpinForwardDatum_of_ktNonSplit (prov : CharPairWProviderPerOp (𝓡 4) k)
    (R : SpinSigmaPresentation ξ) (g : StrMfd ξ)
    (hg : R.sig (DataBordismGrp.mk ξ g) = -16) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (h2 : ktKernelRep prov + ktKernelRep prov = 0) (hns : KTNonSplit prov) :
    Nonempty (DualSpinForwardDatum prov ξ) :=
  ⟨{ R := R
     g := g
     hg := hg
     Φ := sigmaQuotientPhi prov R hdvd
     hΦg := sigmaQuotientPhi_g prov R hdvd hg h2
     hfwd := sigmaQuotientPhi_fwd prov R hdvd hns h2 }⟩

/-- **THE ROUND-10 TIE, locating equivalence** (G10-4 headline): modulo presentation
infrastructure and the ÷32-upper, the Direction-A leaf sits at EXACTLY `KTNonSplit` strength —
`Nonempty (DualSpinForwardDatum prov ξ) ↔ KTNonSplit prov`. Forward is the wave's own
`ktNonSplit_of_dualSpinForwardDatum` (sound: inhabiting the leaf genuinely proves the bit);
backward is the arithmetic fake. The leaf is a NAMED ROUTE, not a reduction: its discharge value
lies entirely in the non-circularity of the construction, which the statement shape cannot
enforce. -/
theorem dualSpinForwardDatum_iff_ktNonSplit (prov : CharPairWProviderPerOp (𝓡 4) k)
    (R : SpinSigmaPresentation ξ) (g : StrMfd ξ)
    (hg : R.sig (DataBordismGrp.mk ξ g) = -16) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (h2 : ktKernelRep prov + ktKernelRep prov = 0) :
    Nonempty (DualSpinForwardDatum prov ξ) ↔ KTNonSplit prov :=
  ⟨fun ⟨d⟩ => ktNonSplit_of_dualSpinForwardDatum d,
   fun hns => dualSpinForwardDatum_of_ktNonSplit prov R g hg hdvd h2 hns⟩

/-! ## §4. G10-5 — the C-leaf: the absorption finding and the locating equivalence -/

/-- **THE ABSORPTION, step 1** (G10-5): the C-leaf's route-(b) fence pays out at the generator —
`hΦgeo` at `[g]` rewritten along `hΦg` is `GeometricSpinRepresentable prov k₀`, the SHARP
(IsEmpty-Σ) Kummer content. The geometric-`Φ` datum cannot exist without carrying the B-direction
payload. -/
theorem geometricKummer_of_ktSpinPresentationDatum (d : KTSpinPresentationDatum prov ξ) :
    GeometricSpinRepresentable prov (ktKernelRep prov) := by
  have h := d.hΦgeo (DataBordismGrp.mk ξ d.g)
  rwa [d.hΦg] at h

/-- **THE ABSORPTION, step 2** (G10-5): the C-leaf alone yields `KummerWitness.1` (the broad
form, via `emptySigmaRepresentable_of_geometric`) — exactly what `EnriquesDatum` was shipped to
supply. The B-leaf is contained in the C-leaf. -/
theorem kummerWitness1_of_ktSpinPresentationDatum (d : KTSpinPresentationDatum prov ξ) :
    EmptySigmaRepresentable prov (ktKernelRep prov) :=
  emptySigmaRepresentable_of_geometric prov _ (geometricKummer_of_ktSpinPresentationDatum d)

/-- **THE ABSORPTION, step 3** (G10-5): `SpinImageIsTwo` from the C-leaf ALONE — the wave's
`spinImageIsTwo_of_datums (dC, dE)` over-consumes: its `dE` input is redundant (the cyclic route +
the datum's own Kummer payload suffice). -/
theorem spinImageIsTwo_of_ktSpinPresentationDatum (d : KTSpinPresentationDatum prov ξ) :
    SpinImageIsTwo prov :=
  spinImageIsTwo_of_cyclic_of_kummerRep prov
    (spinImageCyclic_of_ktSpinPresentationDatum d)
    (kummerWitness1_of_ktSpinPresentationDatum d)

/-- **The round-9 co-obligation is automatic at content strength** (G10-5, consistency): `{SIIT,
geometric-k₀}` forces `SectorIsGeometric` directly — every sector class is `0` (geometric via the
empty structure) or `k₀` (geometric by hypothesis). Confirms
`sectorIsGeometric_of_ktSpinPresentationDatum` carries no content beyond the locating pair. -/
theorem sectorIsGeometric_of_siit_of_geomKummer (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hsiit : SpinImageIsTwo prov)
    (hgeo : GeometricSpinRepresentable prov (ktKernelRep prov)) :
    SectorIsGeometric prov := by
  intro x hx
  rcases hsiit x hx with rfl | rfl
  · exact geometricSpinRepresentable_zero prov
  · exact hgeo

/-- **The C-leaf from its content pair** (G10-5, the fake direction): given presentation
infrastructure, `{SpinImageIsTwo, GeometricSpinRepresentable k₀}` inhabits
`KTSpinPresentationDatum` via the arithmetic `Φ := (σ/16) • k₀` — `hΦgeo` splits over
`zsmul_of_two_torsion` (the image is `{0, k₀}`, both geometric), `hΦrange` over SIIT. The
Φ-dressing is interchangeable: no forgetful-map geometry beyond the pair is pinned. -/
theorem ktSpinPresentationDatum_of_content (prov : CharPairWProviderPerOp (𝓡 4) k)
    (R : SpinSigmaPresentation ξ) (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd ξ) (hg : R.sig (DataBordismGrp.mk ξ g) = -16)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (hsiit : SpinImageIsTwo prov)
    (hgeo : GeometricSpinRepresentable prov (ktKernelRep prov)) :
    Nonempty (KTSpinPresentationDatum prov ξ) := by
  have h1 : EmptySigmaRepresentable prov (ktKernelRep prov) :=
    emptySigmaRepresentable_of_geometric prov _ hgeo
  have h2 : ktKernelRep prov + ktKernelRep prov = 0 :=
    kernelRep_two_torsion_of_emptySigmaRep prov h1
  have h2' : (2 : ℤ) • ktKernelRep prov = 0 := by rw [two_zsmul]; exact h2
  refine ⟨⟨R, hA, hB, g, hg, hdvd, sigmaQuotientPhi prov R hdvd,
    sigmaQuotientPhi_g prov R hdvd hg h2, ?_, ?_⟩⟩
  · intro w
    rw [sigmaQuotientPhi_apply]
    rcases zsmul_of_two_torsion (ktKernelRep prov) h2' (R.sig w / 16) with h0 | hk
    · rw [h0]; exact geometricSpinRepresentable_zero prov
    · rw [hk]; exact hgeo
  · intro y hy
    rcases hsiit y hy with rfl | rfl
    · exact ⟨0, map_zero _⟩
    · exact ⟨DataBordismGrp.mk ξ g, sigmaQuotientPhi_g prov R hdvd hg h2⟩

/-- **THE C-LEAF LOCATING EQUIVALENCE** (G10-5 headline): modulo presentation infrastructure, the
C-leaf is EXACTLY the pair `{SpinImageIsTwo, GeometricSpinRepresentable k₀}` — nothing weaker
inhabits it, nothing stronger is pinned. The construction target for the discharge wave is the
pair itself; the geometric-`Φ` structure is packaging. -/
theorem ktSpinPresentationDatum_iff_content (prov : CharPairWProviderPerOp (𝓡 4) k)
    (R : SpinSigmaPresentation ξ) (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd ξ) (hg : R.sig (DataBordismGrp.mk ξ g) = -16)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x) :
    Nonempty (KTSpinPresentationDatum prov ξ) ↔
      SpinImageIsTwo prov ∧ GeometricSpinRepresentable prov (ktKernelRep prov) :=
  ⟨fun ⟨d⟩ => ⟨spinImageIsTwo_of_ktSpinPresentationDatum d,
    geometricKummer_of_ktSpinPresentationDatum d⟩,
   fun ⟨hsiit, hgeo⟩ => ktSpinPresentationDatum_of_content prov R hA hB g hg hdvd hsiit hgeo⟩

end CarrierForward

/-! ## §5. G10-6 — the B-leaf: decorative fields; the datum IS bare `KummerWitness.1` -/

/-- **THE B-LEAF LOCATING EQUIVALENCE** (G10-6): `EnriquesDatum` is equivalent to the bare
`KummerWitness.1` — the `sigK3`/`hsigK3` pair is a self-inhabiting constant (`⟨−16, rfl⟩`) adding
zero constraint, and the remaining fields are literally the `EmptySigmaRepresentable` witness. The
"Enriques" dressing has no formal footprint; frozen spec item 2 replaces this leaf with the sharp
`GeometricSpinRepresentable prov k₀` target. -/
theorem enriquesDatum_iff_kummerRep (prov : CharPairWProviderPerOp (𝓡 4) k) :
    Nonempty (EnriquesDatum prov) ↔ EmptySigmaRepresentable prov (ktKernelRep prov) :=
  ⟨fun ⟨d⟩ => kummerWitness1_of_enriquesDatum d,
   fun ⟨p, hspin, hmk⟩ => ⟨⟨-16, rfl, p, hspin, hmk⟩⟩⟩

section Absorption

variable {X : Type*} [TopologicalSpace X] {k' : WithTop ℕ∞}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]

/-- **The absorption, closed** (G10-5 + G10-6): the C-leaf inhabits the B-leaf outright. Any
wave counting `dE` as progress independent of `dC` is double-counting. -/
theorem enriquesDatum_of_ktSpinPresentationDatum {ξ : TangentialData X k' I'}
    (d : KTSpinPresentationDatum prov ξ) : Nonempty (EnriquesDatum prov) :=
  (enriquesDatum_iff_kummerRep prov).mpr (kummerWitness1_of_ktSpinPresentationDatum d)

/-! ## §6. G10-7 — the sharpened assembly: the leaf row is `{KRS-supply, dC, dA}`; dE retired -/

/-- **THE SHARPENED ASSEMBLY — `G ≃+ ZMod 16` from TWO leaves + `KernelReducesToSpin`** (G10-7;
CONDITIONAL, discharges nothing — every hypothesis is open). The wave's four-input
`kt_equiv_zmod16_of_leaves` over-consumes: `EnriquesDatum` is redundant (the C-leaf's `hΦgeo`
carries the Kummer payload, §4). The minimal honest leaf row is `{KernelReducesToSpin-supply,
KTSpinPresentationDatum, DualSpinForwardDatum}`, consumed — as before — EXACTLY as the round-8
triple through `kt_equiv_zmod16_of_sector`. This is the assembly of record (frozen spec item 5). -/
theorem kt_equiv_zmod16_of_two_leaves {ξ : TangentialData X k' I'}
    (hKRS : KernelReducesToSpin prov)
    (dC : KTSpinPresentationDatum prov ξ) (dA : DualSpinForwardDatum prov ξ) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData prov) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_sector prov hKRS
    (spinImageIsTwo_of_ktSpinPresentationDatum dC)
    (ktNonSplit_of_dualSpinForwardDatum dA)

end Absorption

end SKEFTHawking.PinPlusKTLeafGate
