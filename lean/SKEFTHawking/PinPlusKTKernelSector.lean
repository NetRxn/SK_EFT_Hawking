/-
# Phase 5q.H W-D — THE W-D OPENER: the empty-Σ spin-kernel SECTOR (statement layer + decomposition)

⛔ HARD SCOPE: this module DISCHARGES NOTHING of the W-D completeness binders
`{KTKernelCard, KTKernelOrderTwo, KTNonSplit}` (`PinPlusKTExtension.lean` §2) or of the
kernel-classification Prop. It builds the **sector vocabulary** for the empty-Σ (rank-0) spin
kernel and **decomposes** the binders into the smallest named geometric sub-Props with honest
content — each of which must face its OWN vacuity gate BEFORE any consumer discharges it
(roadmap §3; premature discharge = the exact failure mode six gate rounds killed). The ONE
exception the mission authorises: cheap POSITIVE structural facts (the spin-sector 2-torsion) that
fall out of `revStr` on rank-0 enhancements — these are structural, not completeness bounds.

## Where this sits (post-flip carrier, 2026-07-15)
The live carrier is `pinPlusCharPairData prov : T2TangentialData PUnit k I` on the W-TETHERED
realized `Bor` (`CharPairBorRealizedTethered`), per-op provider `CharPairWProviderPerOp`. Gate
round 7 passed the tether (the W-tether holds; `PinPlusCharPairTetherGate.lean`) and the F7-A
σ-threading landed (the provider is honest-inhabitable). The W-D binders are GENUINELY OPEN for the
first time in the phase (`PinPlusKTVacuityGateWD.lean` §5 — the round-3/4.5 instance-level
refutations are CONVERTED; the synthetic-`bInc` replay does NOT construct against the realized
`Bor`). This module OPENS the discharge program by naming its geometric sub-Props.

## The KT §5 route (dossier `W_D_ROUTE_DOSSIER.md` §1; KT-LMS-151 §5, Thm 5.2 / Lemma 5.3, p.217)
`ker(charPairBrown) = image of Ω₄^{Spin} ≅ ℤ/2·[Kummer]`. On the carrier: a kernel class is
represented by a structured manifold whose enhancement has `brown = 0`; the EMPTY-Σ (rank-0) sector
carries the spin-image content (a Pin⁺ structure with empty characteristic surface ⟺ the
enhancement rank `n = 0` ⟺ spin-ish; the `hchar` tie makes empty-Σ bundles exist exactly on the
honest `v₂ = 0` carriers — the R1 finding). KT §5's kernel-null direction: "any element in the
kernel is Pin⁺-bordant to an orientable (Spin) manifold, so kernel = image of Ω₄^{Spin}".

## Decomposition map (Prop → content → discharge route)
* `KernelReducesToSpin`   — every `brown`-kernel class is empty-Σ-representable (KT §5 kernel-null
    direction, the DEEP completeness content). STATE only.
* `SpinImageIsTwo`        — the empty-Σ image is `{0, k₀}` (Lemma 5.3 ÷32, `Ω₄^{Spin}≅ℤ` mod
    32-classes). STATE only — an UPPER bound; vacuous ALONE (a collapsed sector satisfies it), so it
    is consumed WITH `KTNonSplit` (the non-split lower bound). Design finding, §5.
* `KummerWitness`         — `k₀` is empty-Σ-representable AND nonzero (the K3-like empty-Σ carrier
    interface, per `KTNonSplitKummerTarget`). STATE only — do NOT build K3.
* `spinSector_two_torsion` — an empty-Σ class is its own negative. BANKED (positive structural
    fact from `revStr` on rank-0: `neg q = q`), NOT a completeness bound. Stays strictly within the
    rank-0 sector — never universal `revStr`-triviality (that is the no-go
    `dataBordism_two_torsion_of_revStr_trivial`).

Standing no-go compliance (dossier §7): the ÷16/÷32 content is honestly geometric (NOT a lattice
Arf — `nogo_lattice_arf_not_sigma8`); the spin-sector 2-torsion is enhancement-tied on rank-0
ONLY, so it does NOT reproduce `dataBordism_two_torsion_of_revStr_trivial` (which forbids universal
`revStr`-triviality / a free-grade order-16 carrier). The kernel Props are stated as HYPOTHESES,
never proved here as `ker = ⊥`-style unconditional facts.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTExtension

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData SKEFTHawking.RP4CharPairWitness
open SKEFTHawking.RP4Witness
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusKTExtension

namespace SKEFTHawking.PinPlusKTKernelSector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-! ## §1. The empty-Σ sector vocabulary -/

/-- **The empty-Σ (rank-0) sector predicate on a structured manifold.** A char-pair class is in the
spin sector when its enhancement has rank `n = 0` — the algebraic shadow of an empty characteristic
surface `Σ` (dual to `w₂ + w₁²`). This is the honest, `charPairBrown`-relevant form: `charPairBrown`
reads `q.brown`, and a rank-0 form has `brown = 0` (`charPairBrown_of_spinSector`), so the whole
sector lands in `ker(charPairBrown)`. (The strictly-geometric spin form `IsEmpty σ.surf.M` FORCES
`n = 0` via the surface basis — `spinSector_of_isEmpty_surf` — but `n = 0` is the broader,
kernel-membership-relevant predicate.) -/
def IsSpinSectorStr (prov : CharPairWProviderPerOp I k)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) : Prop :=
  p.2.n = 0

/-- **A rank-0 `ZMod 4`-quadratic form is `neg`-fixed** — `neg q = q` on `Z4Quadratic (Fin 0)`.
The polar form is preserved by `neg` definitionally; on the empty index the value is forced to `0`
(`q_zero`) which is its own negative. The positive structural core of the spin-sector 2-torsion. -/
theorem z4_neg_rank_zero (q : Z4Quadratic (Fin 0)) : Z4Quadratic.neg q = q := by
  apply z4_ext
  · funext x
    rw [Subsingleton.elim x 0]
    show -(q.q 0) = q.q 0
    rw [q.q_zero, neg_zero]
  · rfl

/-- `neg`-fixedness of a rank-0 enhancement, threaded through a `n = 0` hypothesis (the shape the
sector facts consume: `p.2.n` is a projection, not a bindable variable). -/
theorem rank_zero_neg_eq : ∀ (n : ℕ), n = 0 → ∀ (q : Z4Quadratic (Fin n)),
    Z4Quadratic.neg q = q := by
  rintro n rfl q
  exact z4_neg_rank_zero q

/-- **The geometric spin form forces the algebraic sector form** — `IsEmpty σ.surf.M ⟹ σ.n = 0`.
An empty characteristic surface has vanishing `H¹` (`subsingleton_cohomology`), and the enhancement
basis `σ.basis : H¹(Σ) ≃ₗ (Fin n → ZMod 2)` then forces `Fin n → ZMod 2` subsingleton, i.e. `n = 0`.
BANKED positive structural fact: it ties the geometrically-honest spin condition (empty Σ, dual to
`w₂ + w₁² = 0`) to the `charPairBrown`-relevant rank-0 predicate. (Not a discharge: existence of a
nonzero empty-surface class is the open Kummer content; this only says the geometric form is at least
as strong as the algebraic one.) -/
theorem spinSector_of_isEmpty_surf (prov : CharPairWProviderPerOp I k)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) (h : IsEmpty p.2.surf.M) :
    IsSpinSectorStr prov p := by
  haveI := h
  haveI : Subsingleton (Fin p.2.n → ZMod 2) := p.2.basis.symm.injective.subsingleton
  by_contra hn
  obtain ⟨i⟩ : Nonempty (Fin p.2.n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  exact absurd (congrFun (Subsingleton.elim (fun _ => (0 : ZMod 2)) (fun _ => (1 : ZMod 2))) i)
    (by decide)

/-! ## §2. Kernel membership of the empty-Σ sector (the DONE direction — reuse) -/

/-- **The empty-Σ sector lands in `ker(charPairBrown)`.** A rank-0 class has computed grade
`0` — the carrier-generic "spin classes are in the kernel" fact, re-exposed in sector language
from `PinPlusKTExtension.charPairBrown_of_rank_zero`. (This is the DONE direction of the
kernel/spin-image correspondence; the CONVERSE — `KernelReducesToSpin` — is the open deep content.) -/
theorem charPairBrown_of_spinSector (prov : CharPairWProviderPerOp (𝓡 4) k)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) (h : IsSpinSectorStr prov p) :
    charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 :=
  charPairBrown_of_rank_zero prov p h

/-- **The class-level empty-Σ predicate.** A group class `x` is empty-Σ-representable when it is the
class of SOME rank-0 structured manifold. The image of `Ω₄^{Spin}` (KT §5) is exactly this subset
of the carrier — the spin sector at the level of bordism classes. -/
def EmptySigmaRepresentable (prov : CharPairWProviderPerOp I k)
    (x : T2DataBordismGrp (pinPlusCharPairData prov)) : Prop :=
  ∃ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
    IsSpinSectorStr prov p ∧ T2DataBordismGrp.mk (pinPlusCharPairData prov) p = x

/-- **Empty-Σ-representable ⟹ in the kernel** (the DONE direction at the class level). Every
empty-Σ-representable class has `charPairBrown = 0`. The honest half of `ker = image(Ω₄^{Spin})`;
the other half (`KernelReducesToSpin`) is the open completeness content. -/
theorem emptySigmaRepresentable_in_kernel (prov : CharPairWProviderPerOp (𝓡 4) k)
    (x : T2DataBordismGrp (pinPlusCharPairData prov)) (h : EmptySigmaRepresentable prov x) :
    charPairBrown prov x = 0 := by
  obtain ⟨p, hp, rfl⟩ := h
  exact charPairBrown_of_spinSector prov p hp

/-- **The zero class is empty-Σ-representable** — witnessed by the empty structure `charPairBundledEmpty`
(rank 0). Non-vacuity of `EmptySigmaRepresentable`: the sector is inhabited (by `0`). -/
theorem emptySigmaRepresentable_zero (prov : CharPairWProviderPerOp (𝓡 4) k) :
    EmptySigmaRepresentable prov 0 :=
  ⟨⟨emptySM, charPairBundledEmpty⟩, rfl, rfl⟩

/-! ## §3. The spin-sector 2-torsion — BANKED positive structural fact

An empty-Σ class is its own additive negative. Mechanism: `revStr` = enhancement negation, which is
the IDENTITY on rank-0 enhancements (`neg q = q`, §1), so `revStr` FIXES a rank-0 structure, and the
group law then gives `-x = x ⟹ x + x = 0`. This is a POSITIVE structural fact (not a completeness
bound), and it stays strictly WITHIN the rank-0 sector — it does NOT claim universal
`revStr`-triviality, so it does NOT reproduce the no-go `dataBordism_two_torsion_of_revStr_trivial`
(which forbids the WHOLE carrier being 2-torsion / a free-grade order-16 collapse; the `ℝP⁴`
generator is rank-1, `revStr`-NONtrivial `brown 1 ↦ 7`, so the carrier is honestly not 2-torsion). -/

/-- **Reversal-fixed classes are 2-torsion, T2 form.** If `revStr` fixes `p`'s structure then
`[p] + [p] = 0` (`-[p] = [p]` via `neg_mk`, then `neg_add_cancel`). The `T2DataBordismGrp`
analogue of `SphereProductBounding.mk_add_self_eq_zero_of_revStr_fixed`; per-class, never
universal. -/
theorem mk_add_self_eq_zero_of_revStr_fixed_T2 (ξ : T2TangentialData PUnit k I)
    (p : StrMfd ξ.toTangentialData) (hrev : ξ.revStr p.2 = p.2) :
    T2DataBordismGrp.mk ξ p + T2DataBordismGrp.mk ξ p = 0 := by
  have hneg : -(T2DataBordismGrp.mk ξ p) = T2DataBordismGrp.mk ξ p := by
    show T2DataBordismGrp.neg ξ (T2DataBordismGrp.mk ξ p) = T2DataBordismGrp.mk ξ p
    rw [T2DataBordismGrp.neg_mk]
    exact congrArg (fun σ => T2DataBordismGrp.mk ξ ⟨p.1, σ⟩) hrev
  calc T2DataBordismGrp.mk ξ p + T2DataBordismGrp.mk ξ p
      = -(T2DataBordismGrp.mk ξ p) + T2DataBordismGrp.mk ξ p := by rw [hneg]
    _ = 0 := neg_add_cancel _

/-- **`revStr` fixes a rank-0 bundled structure.** For `σ.n = 0`, `charPairBundledRevStr σ = σ`:
`revStr` only negates the enhancement `q ↦ neg q`, and `neg q = q` on rank-0 (`rank_zero_neg_eq`);
the surface/embedding/tie fields are copied verbatim and their types are `neg`-invariant
(`(neg q).B = q.B` definitionally, so `hpolar` transports). -/
theorem revStr_fixed_of_rank_zero {s : SingularManifold PUnit k I}
    (σ : CharPairStrBundled I s) (hn : σ.n = 0) : charPairBundledRevStr σ = σ := by
  obtain ⟨⟨t2, cert, n, q⟩, surf, sT2, emb, es, ei, sc, b, hp, hc⟩ := σ
  subst hn
  simp only [charPairBundledRevStr, charPairRevStr]
  congr 1
  congr 1
  exact z4_neg_rank_zero q

/-- **The spin sector is 2-torsion.** Every rank-0 structured manifold's class is its own negative:
`[p] + [p] = 0`. BANKED positive structural fact (§3 docstring). -/
theorem spinSector_two_torsion (prov : CharPairWProviderPerOp (𝓡 4) k)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) (h : IsSpinSectorStr prov p) :
    T2DataBordismGrp.mk (pinPlusCharPairData prov) p
      + T2DataBordismGrp.mk (pinPlusCharPairData prov) p = 0 :=
  mk_add_self_eq_zero_of_revStr_fixed_T2 (pinPlusCharPairData prov) p
    (revStr_fixed_of_rank_zero p.2 h)

/-- **Every empty-Σ-representable class is 2-torsion** (class level). BANKED. Constrains any future
Kummer witness: `κ` empty-Σ-representable ⟹ `κ + κ = 0`. -/
theorem emptySigmaRepresentable_two_torsion (prov : CharPairWProviderPerOp (𝓡 4) k)
    (x : T2DataBordismGrp (pinPlusCharPairData prov)) (h : EmptySigmaRepresentable prov x) :
    x + x = 0 := by
  obtain ⟨p, hp, rfl⟩ := h
  exact spinSector_two_torsion prov p hp

/-! ## §4. The kernel-classification decomposition Props (STATE only — NOT discharged) -/

/-- **W-D sub-Prop (b) — the kernel-null direction `KernelReducesToSpin`.** Every
`charPairBrown`-kernel class is empty-Σ-representable. KT §5 (p.217): "Any element in the kernel is
Pin⁺-bordant to an orientable (Spin) manifold, so kernel = image of `Ω₄^{Spin}`." This is the DEEP
completeness content — the geometric surgery reducing a `brown = 0` class to a spin (empty-Σ)
representative. STATED as a HYPOTHESIS; NOT discharged (it faces its own vacuity gate).

**Vacuity-attack line** (roadmap §3): a zero-geometric-input discharge would exhibit, for arbitrary
kernel `x`, a rank-0 `p` with `[p] = x`. The empty structure `charPairBundledEmpty` gives `[p] = 0`
ONLY (`emptySigmaRepresentable_zero`) — it covers `x = 0`, NOT a general nonzero kernel class. No
in-tree rank-0 witness represents a nonzero class (the Kummer carrier is UNBUILT), so the
`∀ x`-quantifier cannot be met by pointing at existing structures: producing the spin representative
IS the KT §5 surgery. The statement shape (a genuine `∃` rank-0 representative equal to `x`) blocks
the collapse. -/
def KernelReducesToSpin (prov : CharPairWProviderPerOp (𝓡 4) k) : Prop :=
  ∀ x : T2DataBordismGrp (pinPlusCharPairData prov),
    charPairBrown prov x = 0 → EmptySigmaRepresentable prov x

/-- **W-D sub-Prop — the spin image is `{0, k₀}` (`SpinImageIsTwo`).** Every empty-Σ-representable
class is `0` or the kernel representative `k₀ = 8 • [ℝP⁴]`. Lemma 5.3's ÷32 content: `Ω₄^{Spin} ≅ ℤ`
(gen [Kummer]) maps into `G` with image `ℤ/(÷32-classes) = ℤ/2`, so the spin sector image has ≤ 2
elements. STATED as a HYPOTHESIS; NOT discharged.

**Vacuity-attack line — ⚠ AMENDED BY GATE ROUND 8 (`PinPlusKTSectorGate`, the authoritative
record):** on its own this Prop is an UPPER bound, vacuously satisfiable by a COLLAPSED sector
(`spinImageIsTwo_of_sectorCollapsed`). The original claim here — that collapse falsifies
`KTNonSplit`, so `{SpinImageIsTwo, KTNonSplit}` is the safe pair — was REFUTED by the gate:
collapse does NOT force `k₀ = 0` (`k₀` need not be sector-representable), and the pair holds
jointly under collapse with trivial image (`pair_holds_under_sectorCollapsed`). What collapse
actually kills is `KummerWitness` (outright) and `KernelReducesToSpin`-given-`KTNonSplit`. The
exactly-ℤ/2 pin is `{SpinImageIsTwo, KummerWitness}` (`sector_image_eq_pair`), and the BINDING
round-8 consumption spec makes the TRIPLE `{KernelReducesToSpin, SpinImageIsTwo, KTNonSplit}`
the minimal consumption unit — every 2-subset admits a degenerate model (G8-2/G8-3). -/
def SpinImageIsTwo (prov : CharPairWProviderPerOp (𝓡 4) k) : Prop :=
  ∀ x : T2DataBordismGrp (pinPlusCharPairData prov),
    EmptySigmaRepresentable prov x → x = 0 ∨ x = ktKernelRep prov

/-- **The Kummer-witness interface (`KummerWitness`).** `k₀ = 8 • [ℝP⁴]` is empty-Σ-representable AND
nonzero — the shape a K3-like empty-Σ carrier must supply (dossier §5 option 1; per
`PinPlusKTExtension.KTNonSplitKummerTarget`). The first conjunct is the DEEP claim that `8 • [ℝP⁴]`
is Pin⁺-bordant to a spin (rank-0) manifold — NOT automatic (its natural representative is the
rank-8 `sumStr` of `ℝP⁴`'s). STATED as an interface; the K3 carrier is NOT built here.

**Vacuity-attack line**: the second conjunct is exactly `KTNonSplit` (the genuinely open bit — the
mod-8 `charPairBrown` door is blind to `{0, 8}`, dossier §5). The first conjunct cannot be
discharged by the empty structure (which represents `0`, so it would force `k₀ = 0`, contradicting
the second). A real K3/Kummer carrier is required — no zero-input witness exists. -/
def KummerWitness (prov : CharPairWProviderPerOp (𝓡 4) k) : Prop :=
  EmptySigmaRepresentable prov (ktKernelRep prov) ∧ KTNonSplit prov

/-! ## §5. The decomposition bridges — the sub-Props COMPOSE into the KT binders + assembly

These bridges are the payload of the decomposition: they show each `PinPlusKTExtension` binder is a
COMPOSITE of the smaller geometric sub-Props above, so the discharge program can target the smallest
honest pieces. NONE of these discharges a binder — they REDUCE binders to sub-Props (which stay
open). -/

/-- **`KTKernelCard` ⟸ `KernelReducesToSpin` ∧ `SpinImageIsTwo`.** The kernel-cardinality binder
decomposes into the kernel-null direction (kernel ⟹ empty-Σ) composed with the spin-image bound
(empty-Σ ⟹ `{0, k₀}`). Pure composition — NOT a discharge (both sub-Props remain open). This is the
decomposition's headline: `KTKernelCard = KernelReducesToSpin ∘ SpinImageIsTwo`. -/
theorem KTKernelCard_of_reduces_of_image (prov : CharPairWProviderPerOp (𝓡 4) k)
    (h1 : KernelReducesToSpin prov) (h2 : SpinImageIsTwo prov) : KTKernelCard prov := by
  intro x hx
  exact h2 x (h1 x hx)

/-- **`KTKernelOrderTwo` ⟸ `KernelReducesToSpin` ALONE** — the SHARP decomposition. The 2-torsion
binder needs ONLY the kernel-null direction: once a kernel class is empty-Σ-representable, its
2-torsion is FREE via the banked `emptySigmaRepresentable_two_torsion` (§3). This is strictly
stronger than `PinPlusKTExtension.kt_kernelOrderTwo_of_card` (which needs `KTKernelCard` +
`KTNonSplit`): the spin-sector 2-torsion is structural, so the non-split bit is NOT required for
`KTKernelOrderTwo`. Finding: the torsion half of `ker ≅ ℤ/2` is discharged; only the kernel-null
direction and the non-split lower bound remain open. -/
theorem KTKernelOrderTwo_of_reduces (prov : CharPairWProviderPerOp (𝓡 4) k)
    (h1 : KernelReducesToSpin prov) : KTKernelOrderTwo prov := by
  intro x hx
  exact emptySigmaRepresentable_two_torsion prov x (h1 x hx)

/-- **The full headline assembly, sector form** — `G ≃+ ZMod 16` from the sector sub-Props. Composes
`KTKernelCard_of_reduces_of_image` into `PinPlusKTExtension.kt_equiv_zmod16`: the DONE facts
(`charPairBrown` surjective, `[ℝP⁴]` grade 1) plus the three disclosed geometric sub-Props
(`KernelReducesToSpin`, `SpinImageIsTwo`, `KTNonSplit`) assemble the ℤ/16 from below (`2 · 8`).
Shows the sector decomposition is load-bearing for the ultimate target. CONDITIONAL on the open
sub-Props; nothing discharged. -/
theorem kt_equiv_zmod16_of_sector (prov : CharPairWProviderPerOp (𝓡 4) k)
    (h1 : KernelReducesToSpin prov) (h2 : SpinImageIsTwo prov) (hns : KTNonSplit prov) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData prov) ≃+ ZMod 16) :=
  kt_equiv_zmod16 prov (KTKernelCard_of_reduces_of_image prov h1 h2) hns

/-- **`KummerWitness` discharges `KTNonSplit`** — the interface consistency tie: the second conjunct
IS `KTNonSplit`. (Trivial extraction; documents that a built K3/Kummer carrier closes the non-split
bit — dossier §5 option 1.) -/
theorem KTNonSplit_of_KummerWitness (prov : CharPairWProviderPerOp (𝓡 4) k)
    (h : KummerWitness prov) : KTNonSplit prov :=
  h.2

/-- **`2 • [Kummer]` bounds — the ÷32 UPPER half is FREE once the Kummer witness is supplied.** Given
`KummerWitness` (i.e. `k₀ = 8 • [ℝP⁴]` is empty-Σ-representable), `k₀ + k₀ = 0` follows STRUCTURALLY
from the banked spin-sector 2-torsion (`emptySigmaRepresentable_two_torsion`). KT Lemma 5.3's "twice
the Kummer surface bounds a Pin⁺ manifold" is thus discharged from the sector alone — it is the
÷32-upper (`σ(2·K3) = 32`) content. What remains open is the ÷32-LOWER half ("the Kummer surface
itself does not bound", `σ(K3) = 16`), which is exactly `KTNonSplit` (`k₀ ≠ 0`). This localizes the
whole ÷32 obstruction to the single non-split bit — the dossier §5 critical node. -/
theorem kernelRep_two_torsion_of_KummerWitness (prov : CharPairWProviderPerOp (𝓡 4) k)
    (h : KummerWitness prov) : ktKernelRep prov + ktKernelRep prov = 0 :=
  emptySigmaRepresentable_two_torsion prov _ h.1

/-! ## §6. The Lemma-5.3 / ÷32 interface — the gap list for `SpinImageIsTwo`

`SpinImageIsTwo` (the spin image `= {0, k₀}`, ≅ ℤ/2) is the terminal geometric content of the
kernel classification. Its KT §5 discharge route (Lemma 5.3, p.216) is the double-cover ÷32
signature story, which further decomposes as:

* **Ω₄^{Spin} ≅ ℤ, generated by the Kummer surface** (KT input i / dossier K5). The spin image is
  cyclic; its generator is `[Kummer]`. IN-TREE: the lattice normal-form substrate
  (`HyperbolicNormalForm.exists_hyperbolic_congr`, `SpinSigmaGenerator.k3Form` with `σ = −16`).
  MISSING: `σ : Ω₄^{Spin} → ℤ` injective (Benedetti Thm 20.14, bounded-elementary) + the ONE
  handle-trade lemma (Benedetti 20.17, deep-new; dossier K5b/K5c). Carrier-side: this is what would
  let `KernelReducesToSpin`'s spin representatives be classified by a single integer.
* **Rokhlin `16 ∣ σ` for spin (the ÷32 BASE).** IN-TREE (E2): `GMRokhlinDischarge.sixteen_dvd_sig_of_gm_null`,
  `SpinCharSurfaceData.rokhlin` (`16 ∣ latticeSig`), `CharacteristicSquareModSixteen`,
  `sig_zmod16_of_charSq16`, `sixteen_dvd_sig_of_gm_metabolic`; the Arf–FK bridge assets
  (`CharSurfaceRokhlinAssembly`, `GMArfVanishing`, `AlgebraicRokhlin`, `RokhlinFromHM`). The `16 ∣ σ`
  half is essentially assembled.
* **The ÷32 Pin⁺ refinement (`32 ∣ σ ⟺ spin Pin⁺-bounds`).** MISSING: no in-tree asset. Needs the
  Enriques-surface / Habegger content (`w₂(E) ≠ 0`, `π₁ = ℤ/2`, `H²(E) = ℤ¹⁰ ⊕ ℤ/2`) refining
  Rokhlin's `16 ∣ σ` to the Pin⁺ `32 ∣ σ`. This is the one genuinely-missing signature-level piece;
  it is E2-adjacent (bounded-elementary per dossier K6, "no Rokhlin-only shortcut" — fork 07-06b).
* **The ÷32 split into upper + lower** (carrier-expressible, PARTLY banked here):
  - UPPER (`2 • k₀ = 0`, `σ(2·K3) = 32`): BANKED — `kernelRep_two_torsion_of_KummerWitness` (free
    from the sector 2-torsion once `k₀` is empty-Σ-representable).
  - LOWER (`k₀ ≠ 0`, `σ(K3) = 16 ≢ 0 mod 32`): OPEN — this IS `KTNonSplit`, the dossier §5 node.

**Net gap list** (what W-D still needs for `SpinImageIsTwo` + `KTNonSplit`):
  (1) `KernelReducesToSpin` — the KT §5 kernel-null surgery (kernel ⟹ empty-Σ representative).
  (2) the ÷32 Pin⁺ refinement (Enriques/Habegger) — the ONLY missing signature-level asset.
  (3) `Ω₄^{Spin} ≅ ℤ` finish (`σ`-injectivity + handle-trade) to pin the spin image to a single
      cyclic generator.
  (4) `KTNonSplit` / `KummerWitness` — the non-split lower bit (dossier §5, the critical node);
      structural option-1 `8 • [ℝP⁴] = [Kummer] ≠ 0`.
The Rokhlin `16 ∣ σ` base and the ÷32-UPPER (`2·Kummer bounds`) are the parts already in hand. -/

end SKEFTHawking.PinPlusKTKernelSector
