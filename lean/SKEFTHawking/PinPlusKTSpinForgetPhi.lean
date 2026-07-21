/-
# Phase 5q.H close-out (Lane C0) — THE GEOMETRIC Φ OPENER: the `Ω₄^{Spin} → Ω₄^{Pin⁺}` forgetful map

**The shared load-bearing construction for BOTH KT §5 leaves.** Builds the carrier-level forgetful
map `spinForgetPhi : DataBordismGrp (spinEmptyData prov) →+ T2DataBordismGrp (pinPlusCharPairData
prov)` — the `Ω₄^{Spin} → Ω₄^{Pin⁺}` inclusion that both `DualSpinForwardDatum` (dA) and
`KTSpinPresentationDatum` (dC) consume (the round-10 vacuity seed: before this module the `Φ`
fields had ZERO in-tree inhabitants off the split world).

**NO second-carrier program** (the W-D route decision): the spin side IS the empty-characteristic-
surface specialization of the BUILT carrier. `spinEmptyData prov` is the `TangentialData` whose
structures are the carrier's own `CharPairStrBundled` bundles SUBTYPED to `IsEmpty σ.surf.M`
(literally empty characteristic surface — the strict geometric form of G9-5), and whose bordism
witnesses are the carrier's own W-TETHERED `CharPairBorRealizedTethered` (fence
`untethered-membrane-factors-relation`: never an untethered variant) PLUS a `T2Space b.W`
certificate, so the relation descends into the Hausdorff-refined `T2DataBordismGrp` honestly. All
op witnesses are the tethered ops' degenerate/empty-membrane cases, reused VERBATIM.

**Dimension discipline**: spin side = closed 4-manifolds `M` with empty membrane (Σ = ∅)
throughout; bordisms `W` are 5-dim; the CharPair carrier's membranes `Q` are 3-dim but every
structure in this lane carries the empty characteristic surface, so the membrane content of each
tethered op witness is its degenerate case.

**THE G8-5 OVERHANG POSTURE (round-9 adjudication, BINDING)**: the sphere overhang
`SectorIsGeometric` bites exactly this route. It is CONSUMED AS A HYPOTHESIS in the dC seam
(`nonempty_ktSpinPresentationDatum_of_spinForgetPhi`), NEVER discharged. The sharp adjudication
`spinForgetPhi_range_iff_sectorIsGeometric` proves that for THIS geometric `Φ` the engine tie's
`hΦrange` is EXACTLY the recorded overhang Prop — the honest cost of the geometric route, nailed.
The `KTKernelCard` variant (`…_of_kernelCard`) wires the route that avoids the overhang (G9-4).
No NEW completeness/bounding Prop is introduced by this module.

**Fences honored**: `enriques-datum-refuted-as-shaped` — `EnriquesDatum` is neither constructed
nor consumed here; the seams target dA/dC only. `genuine-gm-carrier-eight-torsion` /
`mfd-equals-H1-dead-end` — no thin carrier is retargeted; the specialization subtypes the FULL
twice-gated bundle. The 2-torsion of image classes (`spinForgetPhi_add_self`) is enhancement-tied
through the rank-0 sector (`emptySigmaRepresentable_two_torsion`), NOT universal
`revStr`-triviality (`dataBordism_two_torsion_of_revStr_trivial` stays refuted).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTLeafGate

open scoped Manifold
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute
open SKEFTHawking.PinPlusKTStepGate
open SKEFTHawking.PinPlusKTLemma53Wave

namespace SKEFTHawking.PinPlusKTSpinForgetPhi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-! ## §1. The empty-Σ spin specialization of the built carrier

The spin-side tangential datum `spinEmptyData prov`: structures are the carrier's own bundles with
LITERALLY EMPTY characteristic surface (Σ = ∅ — the strict G9-5 geometric form, not merely rank
0), bordism witnesses are the carrier's own tethered witnesses with a Hausdorff certificate on the
bordism total space. Every op is the carrier op restricted to the empty-Σ sector: `sumStr`
preserves Σ = ∅ (`Σ₁ ⊔ Σ₂` of empties is empty), `revStr` keeps the surface verbatim, and each op
bordism's total space is T2 because its pieces are (the `T2TangentialBordism` §2 replay
instances). -/

/-- **The empty-Σ spin specialization of the built CharPair carrier** — the spin-side tangential
datum `ξ` of the KT §5 leaves. NOT a second carrier: `Mfd s` is the subtype of the built carrier's
`CharPairStrBundled I s` cut out by `IsEmpty σ.surf.M` (empty membrane, Σ = ∅), and `Bor` is the
built carrier's W-TETHERED `CharPairBorRealizedTethered` together with a `T2Space b.W` certificate
(so spin-side bordance is literally Hausdorff-refined CharPair bordance between the underlying
bundles). For `prov : CharPairWProviderPerOp (𝓡 4) k` this is the in-tree `Ω₄^{Spin}` carrier the
KT dossier's forgetful map departs from. -/
noncomputable def spinEmptyData (prov : CharPairWProviderPerOp I k) :
    TangentialData.{0, 1} PUnit k I where
  Mfd := fun s => { σ : CharPairStrBundled (k := k) I s // IsEmpty σ.surf.M }
  Bor := fun b σ τ => { _β : CharPairBorRealizedTethered b σ.val τ.val // T2Space b.W }
  emptyStr := ⟨charPairBundledEmpty, inferInstanceAs (IsEmpty PEmpty)⟩
  sumStr := fun σ τ =>
    ⟨charPairBundledSumStr σ.val τ.val, by
      haveI := σ.prop; haveI := τ.prop
      exact inferInstanceAs (IsEmpty (σ.val.surf.M ⊕ τ.val.surf.M))⟩
  cylBor := fun {s} σ =>
    ⟨cylBorTethered prov σ.val, by
      haveI := σ.val.toCharPairStr.t2
      exact inferInstanceAs (T2Space (s.M × Set.Icc (0 : ℝ) 1))⟩
  addBor := fun {s₁ t₁ s₂ t₂ b₁ b₂ σ₁ τ₁ σ₂ τ₂} β₁ β₂ =>
    ⟨addBorTethered prov β₁.val β₂.val, by
      haveI := β₁.prop; haveI := β₂.prop
      exact inferInstanceAs (T2Space (b₁.W ⊕ b₂.W))⟩
  symmBor := fun β => ⟨symmBorTethered β.val, β.prop⟩
  commBor := fun {s t} σ τ =>
    ⟨commBorTethered prov σ.val τ.val, by
      haveI := σ.val.toCharPairStr.t2; haveI := τ.val.toCharPairStr.t2
      exact inferInstanceAs (T2Space ((s.M ⊕ t.M) × Set.Icc (0 : ℝ) 1))⟩
  assocBor := fun {s t r} σ τ ρ =>
    ⟨assocBorTethered prov σ.val τ.val ρ.val, by
      haveI := σ.val.toCharPairStr.t2; haveI := τ.val.toCharPairStr.t2
      haveI := ρ.val.toCharPairStr.t2
      exact inferInstanceAs (T2Space (((s.M ⊕ t.M) ⊕ r.M) × Set.Icc (0 : ℝ) 1))⟩
  unitBor := fun {s} σ =>
    ⟨unitBorTethered prov σ.val, by
      haveI := σ.val.toCharPairStr.t2
      haveI : T2Space (emptySM (X := PUnit) (k := k) (I := I)).M := ⟨fun x => isEmptyElim x⟩
      exact inferInstanceAs
        (T2Space ((s.M ⊕ (emptySM (X := PUnit) (k := k) (I := I)).M) × Set.Icc (0 : ℝ) 1))⟩
  revStr := fun σ => ⟨charPairBundledRevStr σ.val, σ.prop⟩
  revBor := fun β => ⟨revBorTethered β.val, β.prop⟩
  negBor := fun {s} σ =>
    ⟨negBorTethered prov σ.val, by
      haveI := σ.val.toCharPairStr.t2
      exact inferInstanceAs (T2Space (s.M × Set.Icc (0 : ℝ) 1))⟩

/-! ## §2. THE GEOMETRIC Φ — the forgetful `Ω₄^{Spin} → Ω₄^{Pin⁺}` AddMonoidHom -/

/-- **THE GEOMETRIC FORGETFUL MAP** `Φ : Ω₄^{Spin} → Ω₄^{Pin⁺}` (the KT §5 shared opener) — a
spin class (empty-Σ bundle) maps to its underlying CharPair class. Well-defined on the quotients:
a spin bordism witness IS a tethered CharPair bordism witness with a Hausdorff total space (the
`Bor` subtype), i.e. exactly an `IsT2DataBordant` witness between the underlying bundles.
Additivity is definitional (`sumStr` of the specialization projects to the carrier's `sumStr`).
This is the map whose absence was the round-10 vacuity seed of `DualSpinForwardDatum` /
`KTSpinPresentationDatum`; those datums' `Φ` field is now inhabited off the split world. -/
noncomputable def spinForgetPhi (prov : CharPairWProviderPerOp I k) :
    DataBordismGrp (spinEmptyData prov) →+ T2DataBordismGrp (pinPlusCharPairData prov) where
  toFun := Quot.lift
    (fun p => T2DataBordismGrp.mk (pinPlusCharPairData prov) ⟨p.1, p.2.val⟩)
    (fun _p _q h => by
      obtain ⟨b, ⟨β⟩⟩ := h
      exact T2DataBordismGrp.mk_eq_of_bordant _ ⟨b, β.prop, ⟨β.val⟩⟩)
  map_zero' := rfl
  map_add' := by
    intro x y
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q => rfl

@[simp] theorem spinForgetPhi_mk (prov : CharPairWProviderPerOp I k)
    (p : StrMfd (spinEmptyData prov)) :
    spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) p)
      = T2DataBordismGrp.mk (pinPlusCharPairData prov) ⟨p.1, p.2.val⟩ :=
  rfl

/-! ## §3. The image is honestly geometric — `hΦgeo` for free, and the sector seams -/

variable (prov : CharPairWProviderPerOp (𝓡 4) k)

/-- **`hΦgeo` — every `Φ`-image class is honestly geometric** (the dC field, FREE from the
construction): the representative `⟨p.1, p.2.val⟩` carries `p.2`'s own `IsEmpty Σ` certificate.
This is the "route (b) geometric `Φ`" half the round-9 spec demanded — by construction, not by
hypothesis. -/
theorem spinForgetPhi_geometric (w : DataBordismGrp (spinEmptyData prov)) :
    GeometricSpinRepresentable prov (spinForgetPhi prov w) := by
  induction w using Quot.ind with | _ p =>
  exact ⟨⟨p.1, p.2.val⟩, p.2.prop, rfl⟩

/-- **`Φ` surjects onto the honestly-geometric classes** (unconditional): a geometric
representative `p` with `IsEmpty p.2.surf.M` lifts verbatim to the spin side. Together with
`spinForgetPhi_geometric`, the image of `Φ` is EXACTLY the geometric sector. -/
theorem spinForgetPhi_surj_onto_geometric (y : T2DataBordismGrp (pinPlusCharPairData prov))
    (hy : GeometricSpinRepresentable prov y) :
    ∃ w, spinForgetPhi prov w = y := by
  obtain ⟨p, hp, rfl⟩ := hy
  exact ⟨DataBordismGrp.mk (spinEmptyData prov) ⟨p.1, ⟨p.2, hp⟩⟩, rfl⟩

/-- **`hΦrange` from the recorded G8-5 overhang Prop** (`SectorIsGeometric` CONSUMED AS A
HYPOTHESIS — the round-9 gate record; NOT discharged here): if every broad-sector class is
honestly geometric, then `Φ` covers the broad sector. This is the honest cost of the geometric
route, stated exactly as the gate froze it. -/
theorem spinForgetPhi_range_of_sectorIsGeometric (hsec : SectorIsGeometric prov) :
    ∀ y, EmptySigmaRepresentable prov y → ∃ w, spinForgetPhi prov w = y :=
  fun y hy => spinForgetPhi_surj_onto_geometric prov y (hsec y hy)

/-- **THE SHARP G8-5 ADJUDICATION** — for THE geometric `Φ`, the engine tie's `hΦrange` is
EXACTLY the recorded overhang Prop: `(∀ y ∈ broad sector, y ∈ range Φ) ↔ SectorIsGeometric`.
Forward: covering the broad sector with (automatically geometric) `Φ`-images IS the
sphere-killing reduction (`sectorIsGeometric_of_phiRange_geometric`, G9-5). Backward:
`spinForgetPhi_range_of_sectorIsGeometric`. So the geometric route's residual input is the
overhang Prop and nothing else — the seam the dossier's Lemma-5.3 gap list must carry. -/
theorem spinForgetPhi_range_iff_sectorIsGeometric :
    (∀ y, EmptySigmaRepresentable prov y → ∃ w, spinForgetPhi prov w = y)
      ↔ SectorIsGeometric prov :=
  ⟨fun hr => sectorIsGeometric_of_phiRange_geometric prov (spinForgetPhi prov)
      (spinForgetPhi_geometric prov) hr,
    spinForgetPhi_range_of_sectorIsGeometric prov⟩

/-- Every `Φ`-image class lies in the BROAD spin sector (`EmptySigmaRepresentable`, the form the
in-tree sector Props consume) — geometric ⟹ broad (G9-5 proved inclusion). -/
theorem emptySigmaRepresentable_spinForgetPhi (w : DataBordismGrp (spinEmptyData prov)) :
    EmptySigmaRepresentable prov (spinForgetPhi prov w) :=
  emptySigmaRepresentable_of_geometric prov _ (spinForgetPhi_geometric prov w)

/-- **The mod-8 shadow**: `Φ`'s image lies in the kernel of the computed Brown grade
`charPairBrown` — the spin sector is Brown-invisible (`charPairBrown ∘ Φ = 0`), the carrier-level
image of "spin classes have vanishing Brown/Arf obstruction". -/
theorem charPairBrown_spinForgetPhi (w : DataBordismGrp (spinEmptyData prov)) :
    charPairBrown prov (spinForgetPhi prov w) = 0 :=
  emptySigmaRepresentable_in_kernel prov _ (emptySigmaRepresentable_spinForgetPhi prov w)

/-- **`Φ`-image 2-torsion**: `Φ w + Φ w = 0` — enhancement-tied through the rank-0 sector
(`emptySigmaRepresentable_two_torsion`; the structure-TIED grade, NOT universal
`revStr`-triviality). The ÷32-upper "2·(spin class) Pin⁺-bounds" content at the image level. -/
theorem spinForgetPhi_add_self (w : DataBordismGrp (spinEmptyData prov)) :
    spinForgetPhi prov w + spinForgetPhi prov w = 0 :=
  emptySigmaRepresentable_two_torsion prov _ (emptySigmaRepresentable_spinForgetPhi prov w)

/-! ## §4. Statement-layer wiring into the dA/dC datums

The two KT §5 leaves consume `Φ` through `DualSpinForwardDatum` (dA) and
`KTSpinPresentationDatum` (dC). With `spinForgetPhi` built, each datum reduces to its RESIDUAL
row of hypotheses — the σ-presentation content (`R`, generator, Rokhlin ÷16), the generator image
`hΦg`, and (dA) the KT "only if" `hfwd` / (dC) the G8-5 overhang or the `KTKernelCard` bound.
`EnriquesDatum` is deliberately NOT wired (fence `enriques-datum-refuted-as-shaped`). -/

/-- **dA wiring — `DualSpinForwardDatum` on the geometric `Φ`**: with `spinForgetPhi` supplying
the datum's `Φ` field, Direction A's leaf reduces to the residual row
`{R, g, hg, hΦg, hfwd}` — the σ-presentation, the K3 generator with `σ = −16`, the generator
image `Φ[g] = k₀`, and the KT "only if" `32 ∣ σ` on `Pin⁺`-bounding spin classes (each instance a
`Div32BoundingDatum`). `KTNonSplit` then follows via `ktNonSplit_of_dualSpinForwardDatum`. -/
theorem nonempty_dualSpinForwardDatum_of_spinForgetPhi
    (R : SpinSigmaPresentation (spinEmptyData prov)) (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) = ktKernelRep prov)
    (hfwd : ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ R.sig x) :
    Nonempty (DualSpinForwardDatum prov (spinEmptyData prov)) :=
  ⟨{ R := R, g := g, hg := hg, Φ := spinForgetPhi prov, hΦg := hΦg, hfwd := hfwd }⟩

/-- **dC wiring — `KTSpinPresentationDatum` on the geometric `Φ`, overhang route**: with
`spinForgetPhi` supplying `Φ`, `hΦgeo` FREE (`spinForgetPhi_geometric`), and `hΦrange` from the
G8-5 overhang Prop (`SectorIsGeometric` — CONSUMED AS A HYPOTHESIS, per the round-9 gate; a
discharge of dC on this route must co-discharge it), Direction C's leaf reduces to the residual
row `{R, hA, hB, g, hg, hdvd, hΦg, SectorIsGeometric}`. -/
theorem nonempty_ktSpinPresentationDatum_of_spinForgetPhi
    (R : SpinSigmaPresentation (spinEmptyData prov))
    (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) = ktKernelRep prov)
    (hsec : SectorIsGeometric prov) :
    Nonempty (KTSpinPresentationDatum prov (spinEmptyData prov)) :=
  ⟨{ R := R, hA := hA, hB := hB, g := g, hg := hg, hdvd := hdvd,
     Φ := spinForgetPhi prov, hΦg := hΦg,
     hΦgeo := spinForgetPhi_geometric prov,
     hΦrange := spinForgetPhi_range_of_sectorIsGeometric prov hsec }⟩

/-- **dC wiring, `KTKernelCard` route (avoids the overhang, G9-4)**: `hΦrange` is recoverable
from the kernel-cardinality bound + the generator image (`phiRange_of_KTKernelCard`), so on this
route the datum's residual row is `{R, hA, hB, g, hg, hdvd, hΦg, KTKernelCard}` — no
`SectorIsGeometric` input. (Per the G9-4 note, on THIS route the datum's `SpinImageCyclic` output
is also reachable directly from `KTKernelCard`; the datum's value here is packaging the geometric
`Φ` with `hΦgeo` retained.) -/
theorem nonempty_ktSpinPresentationDatum_of_spinForgetPhi_of_kernelCard
    (R : SpinSigmaPresentation (spinEmptyData prov))
    (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) = ktKernelRep prov)
    (hcard : KTKernelCard prov) :
    Nonempty (KTSpinPresentationDatum prov (spinEmptyData prov)) :=
  ⟨{ R := R, hA := hA, hB := hB, g := g, hg := hg, hdvd := hdvd,
     Φ := spinForgetPhi prov, hΦg := hΦg,
     hΦgeo := spinForgetPhi_geometric prov,
     hΦrange := phiRange_of_KTKernelCard prov hcard g (spinForgetPhi prov) hΦg }⟩

/-! ## §5. `hΦg` DERIVED — the generator image from `SpinImageCyclic` + `hfwd` + the ÷32 bank

The lead prep note's claim, banked: `Φ[g] = k₀` needs NO K3-to-8·ℝP⁴ bordism. `Φ[g]` lies in the
broad spin sector (free), so `SpinImageCyclic` classifies it as `m • k₀`; the 2-torsion of `k₀`
collapses `⟨k₀⟩` to `{0, k₀}` (`zsmul_of_two_torsion`); and `Φ[g] = 0` is REFUTED by the banked
÷32 arithmetic (`hfwd` + `σ(g) = −16` + `not_thirtytwo_dvd_neg_sixteen`). Hence `Φ[g] = k₀`. -/

/-- **`hΦg` derived** (the lead prep note, formalized): for THE geometric `Φ`, the generator-image
condition `Φ[g] = k₀` follows from `SpinImageCyclic` + the KT "only if" `hfwd` + `σ(g) = −16` +
the 2-torsion of `k₀` — no explicit K3-to-`8·ℝP⁴` bordism needed. `Φ[g]` is spin-sector (free), so
cyclic classification puts it in `{0, k₀}`; the `0` branch forces `32 ∣ −16`, refuted. -/
theorem spinForgetPhi_g_eq_ktKernelRep_of_cyclic
    (R : SpinSigmaPresentation (spinEmptyData prov)) (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hfwd : ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ R.sig x)
    (hcyc : SpinImageCyclic prov)
    (h2 : ktKernelRep prov + ktKernelRep prov = 0) :
    spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) = ktKernelRep prov := by
  obtain ⟨m, hm⟩ := hcyc _
    (emptySigmaRepresentable_spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g))
  have h2' : (2 : ℤ) • ktKernelRep prov = 0 := by rw [two_zsmul]; exact h2
  rcases zsmul_of_two_torsion (ktKernelRep prov) h2' m with h0 | h1
  · exfalso
    have h32 := hfwd _ (hm.trans h0)
    rw [hg] at h32
    exact not_thirtytwo_dvd_neg_sixteen h32
  · exact hm.trans h1

/-- **dA's residual row CLOSED over the derived `hΦg`**: `DualSpinForwardDatum` on the geometric
`Φ` from `{R, g, hg, hfwd, SpinImageCyclic, 2·k₀ = 0}` — the generator image is derived, not
assumed. This is Direction A's remaining gap list on the geometric-`Φ` route. -/
theorem nonempty_dualSpinForwardDatum_of_cyclic
    (R : SpinSigmaPresentation (spinEmptyData prov)) (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hfwd : ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ R.sig x)
    (hcyc : SpinImageCyclic prov)
    (h2 : ktKernelRep prov + ktKernelRep prov = 0) :
    Nonempty (DualSpinForwardDatum prov (spinEmptyData prov)) :=
  nonempty_dualSpinForwardDatum_of_spinForgetPhi prov R g hg
    (spinForgetPhi_g_eq_ktKernelRep_of_cyclic prov R g hg hfwd hcyc h2) hfwd

/-- **Direction A's conclusion from the reduced row**: `KTNonSplit` from
`{R, g, hg, hfwd, SpinImageCyclic, 2·k₀ = 0}` on the geometric `Φ` — K3 does not Pin⁺-bound,
without an assumed generator image. (The row's open members are `hfwd` — the KT "only if",
each instance a `Div32BoundingDatum` — and `SpinImageCyclic` + the 2-torsion, the ÷32-upper
inputs; everything else is banked.) -/
theorem ktNonSplit_of_spinForgetPhi_row
    (R : SpinSigmaPresentation (spinEmptyData prov)) (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hfwd : ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ R.sig x)
    (hcyc : SpinImageCyclic prov)
    (h2 : ktKernelRep prov + ktKernelRep prov = 0) :
    KTNonSplit prov :=
  (nonempty_dualSpinForwardDatum_of_cyclic prov R g hg hfwd hcyc h2).elim
    ktNonSplit_of_dualSpinForwardDatum

end SKEFTHawking.PinPlusKTSpinForgetPhi
