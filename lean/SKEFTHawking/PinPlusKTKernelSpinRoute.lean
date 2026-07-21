/-
# Phase 5q.H W-D WAVE-1 — the Ω₄^{Spin} / `KernelReducesToSpin` route (RE-TRIAGE opener)

⛔ HARD SCOPE (round-8 consumption spec, `PinPlusKTSectorGate` — BINDING): this module DISCHARGES
NOTHING of the TRIPLE `{KernelReducesToSpin, SpinImageIsTwo, KTNonSplit}` (nor `KummerWitness`). It
is the WAVE-1 opener for gaps **(1)** `KernelReducesToSpin` (the KT §5 kernel-null surgery) and
**(3)** the `Ω₄^{Spin} ≅ ℤ` classification interface (opener §6 gap list) — banking the ALGEBRAIC
surgery rank-reduction bricks that are genuinely reachable, plus TRANSPORT wrappers and a
STATEMENT layer that name precisely what remains geometric. Every step-Prop introduced here carries
a vacuity-attack line (round-9 will attack them). Provider-inhabitation rider (G8-1) applies to every
per-`prov` statement: `CharPairWProviderPerOp (𝓡 4) k` has ZERO in-tree inhabitants until Track-2's
`cylData`/`addClosure` residuals land, so all per-`prov` results are CONDITIONAL, not vacuous.

## What gap (1) `KernelReducesToSpin` actually is (KT-LMS-151 §5 p.217, dossier §1 K3)
"Any element in the kernel is Pin⁺-bordant to an orientable (Spin) manifold, so kernel = image of
`Ω₄^{Spin}`." On the carrier: a class with `charPairBrown = 0` is represented by a structured
manifold whose characteristic-surface enhancement `q : Z4Quadratic (Fin n)` has `q.brown = 0`; the
KT surgery kills the surface `Σ` down to `∅` (rank 0) by Pin⁺ bordism. The honest decomposition is a
COMPOSITION of two independent halves:
* **(1a) ALGEBRAIC (Witt-triviality / rank-reduction).** `q.brown = 0 ⟹ q surgery-reduces to a
  rank-0 form.` The per-step engine is IN-TREE and reused here: `BrownSurgeryReduction`'s
  `SurgeryReduction` / `exists_surgeryReduction` (an isotropic nonzero class admits a reduction) +
  `brown_surgeryReduction` (a single isotropic reduction PRESERVES `brown`) + `card_surgeryReduction`
  (rank drops by exactly 2). The metabolic terminal case is `BrownMetabolic.brown_eq_zero_of_metabolic`.
  §1 banks the missing "surgery can start" existence brick (`metabolic_isotropic_of_pos`) and the
  brown-preserving reduction packaging (`exists_brownPreserving_reduction`).
* **(1b) GEOMETRIC (tethered realization).** Each algebraic reduction is realized by a tethered Pin⁺
  bordism `CharPairBorRealizedTethered b σ_before σ_after` (the `PinPlusCharPairTetherGate` §3
  structure — its `Q`/`ιW` are the surgery-trace membrane and its boundary inclusion), so the reduced
  class EQUALS the original. §2 STATES this as the gated step-Prop `KTSurgeryRealized` (round-9 seed).

The composition `(1a) ∧ (1b) ⟹ KernelReducesToSpin` is the gated bridge — NOT discharged here.

## What gap (3) `Ω₄^{Spin} ≅ ℤ` consumes (dossier §5 K5; opener §6 first bullet)
The spin image rides `Ω₄^{Spin} ≅ ℤ` via `σ/16`; the KT route consumes it through the IN-TREE,
carrier-generic, PROVED engine `SpinSigmaRoute.SpinSigmaPresentation` — `dataBordismGrp_equiv_int`
(≅ ℤ) and `thirtytwo_dvd_sig_iff` (the ÷32 → even-multiple bridge, KT Lemma 5.3's arithmetic half).
Its DISCHARGED inputs are the lattice half (`HyperbolicNormalForm.exists_hyperbolic_congr`, used
inside `sig_injective`; `SpinSigmaGenerator.k3Form` with `latticeSig = −16`). Its OPEN inputs are the
frozen geometric statements `RealizesSphereProducts` (Benedetti 20.16/20.17 handle-trade — the ONE
Mathlib-absent step) + the ÷32 Pin⁺ refinement (Enriques/Habegger, gap (2)). §3 STATES the interface
`SpinImageInput` and banks thin transport re-exposures naming exactly this.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTKernelSector
import SKEFTHawking.BrownSurgeryReduction
import SKEFTHawking.BrownMetabolic
import SKEFTHawking.SpinSigmaRoute

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData SKEFTHawking.RP4CharPairWitness
open SKEFTHawking.RP4Witness
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector

namespace SKEFTHawking.PinPlusKTKernelSpinRoute

variable {k : WithTop ℕ∞}

/-! ## §1. Algebraic surgery rank-reduction bricks (BANKED — the reachable ALGEBRAIC half of gap 1a)

These are unconditional facts about `Z4Quadratic` forms (no `prov`, no carrier, no vacuity concern);
they supply the "surgery can start and preserves `brown`" content that iterated KT surgery rides on.
The per-step invariance (`brown_surgeryReduction`), existence (`exists_surgeryReduction`) and rank
drop (`card_surgeryReduction`) are already in `BrownSurgeryReduction`; the terminal metabolic case is
`BrownMetabolic.brown_eq_zero_of_metabolic`. Banked below: the missing existence brick that a
metabolic (Witt-trivial base) form of POSITIVE rank always has an isotropic vector to surger. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A metabolic form of positive rank has a nonzero isotropic vector** — the "surgery can start"
brick. If `Q` vanishes on a maximal isotropic `L` (`hq` + `hmax`, the `brown_eq_zero_of_metabolic`
hypotheses) and `ι` is nonempty, then `L ≠ ⊥`, so some nonzero `l ∈ L` is isotropic. Mechanism: were
`L = ⊥`, maximality `hmax` (its premise `∀ l ∈ ⊥, B v l = 0` holds vacuously via `B v 0 = 0`) would
force EVERY `v` into `⊥`, collapsing `ι → ZMod 2` to `{0}` — impossible for nonempty `ι` (the
indicator `Pi.single i 1 ≠ 0`). Combined with `exists_surgeryReduction` this is the induction-step
existence half of "metabolic ⟹ reduces to rank 0". -/
theorem metabolic_isotropic_of_pos (Q : Z4Quadratic ι)
    (L : Submodule (ZMod 2) (ι → ZMod 2))
    (hq : ∀ l ∈ L, Q.q l = 0)
    (hmax : ∀ v, (∀ l ∈ L, Q.B v l = 0) → v ∈ L)
    (hcard : 0 < Fintype.card ι) :
    ∃ x : ι → ZMod 2, x ≠ 0 ∧ Q.q x = 0 := by
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp hcard
  have hLne : ∃ l ∈ L, l ≠ 0 := by
    by_contra hL
    have hL0 : ∀ l ∈ L, l = 0 := by
      intro l hlL
      by_contra hl
      exact hL ⟨l, hlL, hl⟩
    have hall : ∀ v : ι → ZMod 2, v ∈ L := by
      intro v
      apply hmax
      intro l hlL
      rw [hL0 l hlL, Q.B_zero_right]
    have he : (Pi.single i (1 : ZMod 2)) = 0 := hL0 _ (hall _)
    have hi := congrFun he i
    rw [Pi.single_eq_same, Pi.zero_apply] at hi
    exact absurd hi (by decide)
  obtain ⟨l, hlL, hl0⟩ := hLne
  exact ⟨l, hl0, hq l hlL⟩

/-- **A metabolic form of positive rank admits a brown-preserving, rank-dropping surgery reduction.**
Composes `metabolic_isotropic_of_pos` (the isotropic class to surger) with
`BrownSurgeryReduction.exists_surgeryReduction` (the reduction exists), `brown_surgeryReduction`
(`brown` unchanged) and `card_surgeryReduction` (rank drops by exactly 2). This is the algebraic
induction STEP of "a Witt-trivial (metabolic-after-stabilization) enhancement surgers to rank 0": it
produces a strictly-smaller form with the SAME Brown invariant. The termination/iteration (that every
`brown = 0` form reaches rank 0) is the gated Witt-triviality content — carried geometrically by
`KTSurgeryReduces` (§2; round-9: proven EQUIVALENT to `KernelReducesToSpin`). BANKED positive
algebraic fact (no carrier, no `prov`, no vacuity concern). -/
theorem exists_brownPreserving_reduction (Q : Z4Quadratic ι)
    (L : Submodule (ZMod 2) (ι → ZMod 2))
    (hq : ∀ l ∈ L, Q.q l = 0)
    (hmax : ∀ v, (∀ l ∈ L, Q.B v l = 0) → v ∈ L)
    (hcard : 0 < Fintype.card ι) :
    ∃ (x : ι → ZMod 2) (S : Q.SurgeryReduction x),
      Q.brown = S.R.brown ∧ Fintype.card ι = Fintype.card S.κ + 2 := by
  obtain ⟨x, hx0, hxq⟩ := metabolic_isotropic_of_pos Q L hq hmax hcard
  obtain ⟨S⟩ := Q.exists_surgeryReduction hxq hx0
  exact ⟨x, S, Q.brown_surgeryReduction S hxq, Q.card_surgeryReduction S hxq⟩

/-! ## §2. The gap-(1) surgery-content decomposition of `KernelReducesToSpin`

`KernelReducesToSpin` (opener §4) = "every `charPairBrown`-kernel class is empty-Σ-representable" — the
KT §5 p.217 kernel-null surgery. We decompose it into the SMALLEST class-level geometric step the tree
can express — a single rank-dropping tethered surgery — and DISCHARGE the induction bridge that
composes that step into the full binder. The step itself stays GATED (round-9 seed); the bridge
reduces the `∀ x ∈ ker` quantifier to a one-step-descent Prop, exactly the "state the step-Props,
discharge only what is genuinely reachable" mandate.

⛔ This does NOT circumvent the round-8 TRIPLE: `kernelReducesToSpin_of_surgeryReduces` produces
`KernelReducesToSpin` FROM the gated `KTSurgeryReduces`, and `KernelReducesToSpin` must STILL be
consumed together with `SpinImageIsTwo` + `KTNonSplit` (G8-3: each 2-subset has a degenerate model).
The bridge only relocates the open content from an `∀`-quantified kernel statement to a single
geometric surgery step — it discharges nothing of the triple. -/

/-- **The gap-(1) smallest named step — one rank-dropping tethered surgery** (`KTSurgeryReduces`). A
`charPairBrown`-kernel class represented by a NON-spin (`0 < n`) structured manifold `p` admits a
representative `p'` of STRICTLY smaller enhancement rank with the SAME class `[p'] = [p]`. This is KT
§5's single surgery move at the class level: kill one generator of the characteristic surface `Σ` by a
Pin⁺ bordism. Geometrically (§1b algebra realized): `p'`'s enhancement is the `SurgeryReduction` of
`p.2.q`, and the class-equality `[p'] = [p]` is witnessed by a tethered bordism
`PinPlusCharPairBorTethered.CharPairBorRealizedTethered b p.2 p'.2` — the surgery-trace membrane `b.W`
with boundary inclusion `ιW` (the tether-gate §3 witness shape). STATED as a HYPOTHESIS; NOT discharged.

**Vacuity-attack line** (round-9 seed): a zero-geometric-input discharge would exhibit, for an
arbitrary non-spin brown-0 `p`, a smaller-rank `p'` with `[p'] = [p]`. The empty structure gives only
`[⟨emptySM, charPairBundledEmpty⟩] = 0` (`emptySigmaRepresentable_zero`), which is rank-0 (fails the
`0 < n` domain) and equals `0` (not a general `[p]`). No in-tree rank-reducing witness represents a
class equal to a given `[p]`: producing `p'` with `[p'] = [p]` REQUIRES an actual surgery-trace
`CharPairBorRealizedTethered` bordism (tether §3), which is the open KT surgery. The `∃ p'` with the
`mk`-equality blocks the collapse; `simp`/`aesop`/`decide` cannot supply the bordism. -/
def KTSurgeryReduces (prov : CharPairWProviderPerOp (𝓡 4) k) : Prop :=
  ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
    charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
    0 < p.2.n →
    ∃ p' : StrMfd (pinPlusCharPairData prov).toTangentialData,
      p'.2.n < p.2.n ∧
        T2DataBordismGrp.mk (pinPlusCharPairData prov) p'
          = T2DataBordismGrp.mk (pinPlusCharPairData prov) p

/-- **The tethered-bordism realizer of one surgery step** (gap-(1) step B, Lean-witnessed): a
Hausdorff bordism `b` from `p'.1` to `p.1` carrying a `(pinPlusCharPairData prov).Bor`-witness (the
realized tether `PinPlusCharPairBorTethered.CharPairBorRealizedTethered` — its `Q`/`ιW` are the
surgery-trace membrane `b.W` and its boundary inclusion) forces the class-equality `[p'] = [p]`.
Thin specialization of `T2DataBordismGrp.mk_eq_of_bordant` to the tether shape; it is the concrete
answer to "what would the surgery step's `Q`/`ιW` be" — the tether §3 witness. -/
theorem mk_eq_of_tethered (prov : CharPairWProviderPerOp (𝓡 4) k)
    {p p' : StrMfd (pinPlusCharPairData prov).toTangentialData}
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p'.1 p.1) (hT2 : T2Space b.W)
    (hBor : Nonempty ((pinPlusCharPairData prov).Bor b p'.2 p.2)) :
    T2DataBordismGrp.mk (pinPlusCharPairData prov) p'
      = T2DataBordismGrp.mk (pinPlusCharPairData prov) p :=
  T2DataBordismGrp.mk_eq_of_bordant _ ⟨b, hT2, hBor⟩

/-- **A tethered surgery step supplies the `KTSurgeryReduces` conclusion** (gap-(1) step B → step
Prop): a strictly rank-dropping `p'` tied to `p` by a tethered bordism witness meets the existential
`KTSurgeryReduces` demands at `p`. This is the exact witness shape a discharge of `KTSurgeryReduces`
must produce for each non-spin brown-0 `p`; the open content is CONSTRUCTING the `(b, tether)` pair
(the KT §5 surgery), not this packaging. -/
theorem surgeryStep_of_tethered (prov : CharPairWProviderPerOp (𝓡 4) k)
    {p p' : StrMfd (pinPlusCharPairData prov).toTangentialData} (hlt : p'.2.n < p.2.n)
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p'.1 p.1) (hT2 : T2Space b.W)
    (hBor : Nonempty ((pinPlusCharPairData prov).Bor b p'.2 p.2)) :
    ∃ q : StrMfd (pinPlusCharPairData prov).toTangentialData,
      q.2.n < p.2.n ∧
        T2DataBordismGrp.mk (pinPlusCharPairData prov) q
          = T2DataBordismGrp.mk (pinPlusCharPairData prov) p :=
  ⟨p', hlt, mk_eq_of_tethered prov b hT2 hBor⟩

/-- **The induction engine** — strong induction on enhancement rank. Given the one-step surgery
`KTSurgeryReduces`, every brown-kernel class represented by a rank-`n` manifold is
empty-Σ-representable: at rank 0 it IS spin-sector; at rank `> 0`, one surgery step gives a
strictly-smaller representative of the SAME (still brown-0) class, and the induction hypothesis
finishes. This is the honest reduction of the KT §5 kernel-null direction to its single geometric
move. -/
theorem emptySigmaRep_of_surgeryReduces (prov : CharPairWProviderPerOp (𝓡 4) k)
    (h : KTSurgeryReduces prov) : ∀ (n : ℕ)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData), p.2.n = n →
    charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
    EmptySigmaRepresentable prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro p hpn hbrown
    rcases Nat.eq_zero_or_pos p.2.n with hz | hpos
    · exact ⟨p, hz, rfl⟩
    · obtain ⟨p', hlt, heq⟩ := h p hbrown hpos
      have hb' : charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p') = 0 := by
        rw [heq]; exact hbrown
      have hlt' : p'.2.n < n := hpn ▸ hlt
      have hres := IH p'.2.n hlt' p' rfl hb'
      rwa [heq] at hres

/-- **The gap-(1) bridge — `KTSurgeryReduces ⟹ KernelReducesToSpin`** (CONDITIONAL, discharges
nothing of the triple). Reduces the deep `∀ x ∈ ker` kernel-null direction to the single gated
geometric surgery step. Pure composition of `emptySigmaRep_of_surgeryReduces` (the rank induction)
with `Quot.ind` (every class is a `mk`). This is the load-bearing decomposition headline for gap (1):
the KT §5 surgery content is exactly `KTSurgeryReduces`, and NOTHING more. -/
theorem kernelReducesToSpin_of_surgeryReduces (prov : CharPairWProviderPerOp (𝓡 4) k)
    (h : KTSurgeryReduces prov) : KernelReducesToSpin prov := by
  intro x hx
  induction x using Quot.ind with
  | _ p => exact emptySigmaRep_of_surgeryReduces prov h p.2.n p rfl hx

/-! ## §3. The gap-(3) `Ω₄^{Spin} ≅ ℤ` interface — pinning the spin image to one cyclic generator

Gap (3) (opener §6 first bullet): the empty-Σ (spin) image rides `Ω₄^{Spin} ≅ ℤ` via `σ/16`. The KT
route consumes this through the IN-TREE PROVED engine `SpinSigmaRoute.SpinSigmaPresentation`:
`dataBordismGrp_equiv_int` (the spin carrier ≅ ℤ, modulo the two frozen geometric statements) and
`thirtytwo_dvd_sig_iff` (KT Lemma 5.3's arithmetic half: `32 ∣ σ ⟺ EVEN multiple of the generator`).
Its DISCHARGED lattice inputs are `HyperbolicNormalForm.exists_hyperbolic_congr` (`σ=0 ⟹ n·H`, used
inside `sig_injective`) and `SpinSigmaGenerator.k3Form` (`latticeSig = −16`, the σ = −16 generator).
Its OPEN inputs are `SpinSigmaPresentation.RealizesSphereProducts` (Benedetti 20.16/20.17
handle-trade — the ONE Mathlib-absent step), the ÷32 Pin⁺ refinement (Enriques/Habegger, gap (2)),
AND the spin-specialization map `Φ : DataBordismGrp ξ → G` onto the empty-Σ image (dossier §3: the
empty-Σ specialization of the CharPair carrier — the `Ω₄^{Spin} → Ω₄^{Pin⁺}` inclusion at the class
level).

On the CARRIER's group `G`, the net content the ℤ-classification delivers is `SpinImageCyclic`: the
empty-Σ image is contained in the cyclic subgroup generated by the kernel representative
`k₀ = ktKernelRep prov` (the `σ/16` image of the K3 generator). We STATE it, bank the honest bridge to
`SpinImageIsTwo` (routing through Lemma 5.3 — exactly the G8-4-mandated route, NOT a collapse-smell),
and give the engine tie `spinImageCyclic_of_presentation` (how the `SpinSigmaPresentation` engine
discharges it, exposing the one open geometric input `Φ`). -/

/-- An integer multiple of a 2-torsion element is `0` or the element itself (parity of `m`). The
algebraic core of "a cyclic subgroup generated by a 2-torsion element has ≤ 2 elements". -/
theorem zsmul_of_two_torsion {A : Type*} [AddCommGroup A] (x : A) (hx : (2 : ℤ) • x = 0) (m : ℤ) :
    m • x = 0 ∨ m • x = x := by
  rcases Int.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact Or.inl (by rw [hj, ← two_mul, mul_comm, mul_zsmul, hx, smul_zero])
  · exact Or.inr (by rw [hj, add_zsmul, one_zsmul, mul_comm, mul_zsmul, hx, smul_zero, zero_add])

/-- **The gap-(3) interface Prop `SpinImageCyclic`** — the empty-Σ image is contained in the cyclic
subgroup generated by `k₀ = ktKernelRep prov`. This is the net content the `Ω₄^{Spin} ≅ ℤ`
classification delivers on `G`: every spin (empty-Σ) class is an integer multiple of the `σ/16` image
of the K3 generator (`k₀`). STATED as a HYPOTHESIS; NOT discharged (its discharge is
`spinImageCyclic_of_presentation` from the engine + the open map `Φ`).

**Vacuity-attack line** (round-9 seed): a zero-geometric-input discharge would present every empty-Σ
class as an integer multiple of `k₀`. The empty structure gives only `0 = 0 • k₀`
(`emptySigmaRepresentable_zero`, the `m = 0` case) — it does NOT cover a general empty-Σ class. No
in-tree witness classifies arbitrary empty-Σ classes as `⟨k₀⟩`-multiples: that IS the
`Ω₄^{Spin} ≅ ℤ` cyclic structure transported through the (unbuilt) spin-specialization `Φ`
(`SpinSigmaPresentation.generates`). Because the route runs through the cyclic ÷32 (Lemma 5.3)
structure, it is the honest SIIT route (G8-4), not the `∀ sector x, x = 0` collapse (which would
refute `KummerWitness`). -/
def SpinImageCyclic (prov : CharPairWProviderPerOp (𝓡 4) k) : Prop :=
  ∀ y : T2DataBordismGrp (pinPlusCharPairData prov),
    EmptySigmaRepresentable prov y → ∃ m : ℤ, y = m • ktKernelRep prov

/-- **The gap-(3) bridge — `SpinImageCyclic` + `k₀`-representability ⟹ `SpinImageIsTwo`**
(CONDITIONAL; discharges nothing of the triple). Routes `SpinImageIsTwo` through the Lemma-5.3 cyclic
classification (the G8-4-mandated honest route): the ℤ-classification (`SpinImageCyclic`) puts every
empty-Σ class at `m • k₀`, and `k₀`'s empty-Σ-representability (`KummerWitness.1`, the ÷32-upper
input) makes `k₀` 2-torsion (banked `emptySigmaRepresentable_two_torsion`), collapsing `⟨k₀⟩` to
`{0, k₀}` via `zsmul_of_two_torsion`. Both hypotheses are OPEN; per the round-8 spec `SpinImageIsTwo`
is still consumed with `KernelReducesToSpin` + `KTNonSplit`. -/
theorem spinImageIsTwo_of_cyclic_of_kummerRep (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hcyc : SpinImageCyclic prov)
    (hk : EmptySigmaRepresentable prov (ktKernelRep prov)) : SpinImageIsTwo prov := by
  intro y hy
  obtain ⟨m, rfl⟩ := hcyc y hy
  have h2 : (2 : ℤ) • ktKernelRep prov = 0 := by
    rw [two_zsmul]; exact emptySigmaRepresentable_two_torsion prov _ hk
  exact zsmul_of_two_torsion (ktKernelRep prov) h2 m

section EngineTie
open SKEFTHawking.SpinSigmaRoute SKEFTHawking.TangentialDataBordism

variable {X : Type*} [TopologicalSpace X] {k' : WithTop ℕ∞}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]

/-- **The gap-(3) engine tie — how `SpinSigmaPresentation` discharges `SpinImageCyclic`**
(CONDITIONAL; discharges nothing of the triple). Given the IN-TREE PROVED `Ω₄^{Spin} ≅ ℤ` engine on a
spin carrier `ξ` (a `SpinSigmaPresentation` with the two geometric freezes `hA`/`hB`, Rokhlin `hdvd`,
and a `σ = −16` generator `g` — the K3 datum, `SpinSigmaGenerator.k3Form`), PLUS the spin-specialization
map `Φ : DataBordismGrp ξ → G` sending the generator to `k₀` (`hΦg`) with image the empty-Σ classes
(`hΦrange`), `SpinImageCyclic` follows: an empty-Σ class `y = Φ w`, and `SpinSigmaPresentation.generates`
writes `w = n • [g]`, so `y = n • Φ[g] = n • k₀`. This EXPOSES the exact open input gap (3) needs
beyond the in-tree engine: the map `Φ` (the `Ω₄^{Spin} → Ω₄^{Pin⁺}` inclusion realized on the CharPair
carrier — dossier §3's empty-Σ specialization), plus the freezes `hA` (handle-trade) + Rokhlin. It is
NOT a discharge: `Φ` with these properties is unbuilt (no in-tree spin-specialization witness). -/
theorem spinImageCyclic_of_presentation (prov : CharPairWProviderPerOp (𝓡 4) k)
    {ξ : TangentialData X k' I'} (R : SpinSigmaPresentation ξ)
    (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd ξ) (hg : R.sig (DataBordismGrp.mk ξ g) = -16) (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (Φ : DataBordismGrp ξ →+ T2DataBordismGrp (pinPlusCharPairData prov))
    (hΦg : Φ (DataBordismGrp.mk ξ g) = ktKernelRep prov)
    (hΦrange : ∀ y, EmptySigmaRepresentable prov y → ∃ w, Φ w = y) :
    SpinImageCyclic prov := by
  intro y hy
  obtain ⟨w, rfl⟩ := hΦrange y hy
  obtain ⟨n, rfl⟩ := R.generates hA hB g hg hdvd w
  exact ⟨n, by rw [map_zsmul, hΦg]⟩

end EngineTie

end SKEFTHawking.PinPlusKTKernelSpinRoute
