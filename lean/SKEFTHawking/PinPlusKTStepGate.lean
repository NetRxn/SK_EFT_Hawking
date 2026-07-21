/-
# Phase 5q.H W-D GATE ROUND 9 (fresh-context VACUITY ATTACK on the wave-1 step-Props + the G8-5 seam)

Adversarial gate findings against W-D wave 1 (`PinPlusKTKernelSpinRoute`: the gated step-Props
`KTSurgeryReduces` / `SpinImageCyclic`, the proven bridges, the banked algebra and transport
wrappers) and the round-8 seed G8-5 (the `σ.n = 0` vs `IsEmpty Σ` sector-form seam). Verdict:
**PASS WITH FROZEN SPEC** — no step-Prop admits a zero-geometric-input discharge outside the
already-fenced G8 degenerate worlds, the bridges consume exactly what they claim (settled by
EQUIVALENCE, G9-1), and the surgery-trace construction wave MAY proceed against the current
statement shapes subject to the spec at the bottom of this header.

## G9-1 — `KTSurgeryReduces` IS `KernelReducesToSpin` (equivalence; the bridge is SHARP and the
step-Prop inherits every round-8 degenerate model VERBATIM; kernel-encoded, §1).

Wave 1 proved `kernelReducesToSpin_of_surgeryReduces` (strong induction on rank). The CONVERSE is
one line (§1, `surgeryReduces_of_kernelReducesToSpin`): a kernel class's rank-0 representative
(supplied by `KernelReducesToSpin`) is itself the strictly-rank-dropping `p'` demanded at any
`0 < n` representative. Hence `ktSurgeryReduces_iff_kernelReducesToSpin`: the decomposition
RELOCATES the open content (from a `∀ x ∈ ker` binder to a single geometric surgery step) but does
NOT weaken it — the step-Prop sits at EXACTLY `KernelReducesToSpin` strength. Consequences:
* the induction bridge consumes exactly `KTSurgeryReduces` — sharpness settled by the equivalence
  (nothing weaker could produce KRTS, nothing stronger is consumed);
* every G8 degenerate model transfers verbatim (kernel-encoded): the G8-3 kernel-collapse
  DISCHARGES the step-Prop at zero geometric cost (`ktSurgeryReduces_of_kernelTrivial` — in the
  split world every brown-0 class is `0`, and the EMPTY structure is the smaller representative),
  and the G8-2 sector-collapse + `KTNonSplit` REFUTES it
  (`not_ktSurgeryReduces_of_sectorCollapsed_of_nonsplit`);
* therefore the round-8 consumption spec applies to `KTSurgeryReduces` UNCHANGED: a discharge
  wave must name which degenerate model its construction excludes, and the result is consumed
  only inside the triple `{KernelReducesToSpin, SpinImageIsTwo, KTNonSplit}`.

## G9-2 — ZERO-GEOMETRIC-INPUT ATTACK ON `KTSurgeryReduces`: BLOCKED (mechanisms named).

The brief's three exploit shapes were run against the tree; each is blocked by a verified
structural fact (no failing code shipped; mechanisms recorded):
* **Reflexive/cylinder bordism with a reindexed structure** — blocked: the only in-tree tether
  constructor is `PinPlusCharPairBorTethered.cylBorTethered prov σ :
  CharPairBorRealizedTethered (reflCylinder s) σ σ` — it relates a structure to ITSELF (same `σ`
  both ends, rank identical), and reindexing cannot change rank (`σ.n` is pinned by the basis
  equiv `H¹(Σ;ℤ/2) ≃ₗ (Fin n → ZMod 2)`: two structures on the same surface have the same `n`).
* **Sum-with-something rank laundering** — blocked: `sumStr`/`charPairBundledSumStr` ADD ranks
  (`orthSum` + reindex to `Fin (m + n)`), and `revStr` preserves rank; no in-tree operation on
  representatives lowers `n`. A `[p ⊔ q] = [p]` trick (null `q`) RAISES the visible rank.
* **Arbitrary-manifold escape** — the statement does allow `p'` on a different underlying
  manifold, and that is CORRECT (KT §5 surgery changes the manifold); the fence is the
  class-equality conjunct `[p'] = [p]`: rank is not a class invariant, so a smaller-rank `p'`
  smuggles nothing — the induction consumes only `[p'] = [p]` (brown transports) + `n' < n`
  (termination). Producing `[p'] = [p]` across ranks requires an actual `Bor` witness chain; the
  only in-tree witnesses are the reflexive cylinders and the op-coherence bordisms (rank-matched).
The `0 < n` domain + strict-drop conjunct also block the empty-structure fake: `[∅-structure] = 0`
covers only the `[p] = 0` fibre, which is exactly the G8-3 kernel-collapse world (G9-1, fenced).

## G9-3 — `SpinImageCyclic` IS THE ≤-CYCLIC FACE OF `SpinImageIsTwo` (NOT new content; both G8
collapse models discharge it; recoverable from `KTKernelCard`; kernel-encoded, §2).

`spinImageCyclic_of_spinImageIsTwo`: SIIT ⟹ SpinImageCyclic OUTRIGHT (`m ∈ {0, 1}`); wave-1's
`spinImageIsTwo_of_cyclic_of_kummerRep` recovers SIIT from it + `KummerWitness.1`. So the DELTA
between the two Props is exactly the 2-torsion collapse of `⟨k₀⟩` — supplied by the banked
`emptySigmaRepresentable_two_torsion` under `KummerWitness.1` — and `SpinImageCyclic` is the
WEAKER statement. Degenerate models (kernel-encoded): sector-collapse discharges it (`m = 0`
everywhere, `spinImageCyclic_of_sectorCollapsed`); kernel-collapse discharges it through the NEW
composition brick `sectorCollapsed_of_kernelTrivial` (the G8-3 world collapses the sector too);
and it is recoverable from the kernel bound (`spinImageCyclic_of_KTKernelCard`, the G8-4 pattern
one Prop down). The composed-bridge pair `{SpinImageCyclic, KummerWitness.1}` is fenced at the
triple level: under sector-collapse the pair forces `k₀ = 0`
(`not_KTNonSplit_of_kummerRep_of_sectorCollapsed`), so + `KTNonSplit` excludes both collapse
worlds — the round-8 spec item 3 (route declaration) applies to `SpinImageCyclic` discharge waves
UNCHANGED.

## G9-4 — THE Φ ENGINE TIE (`spinImageCyclic_of_presentation`): `hΦg` IS CHEAP, `hΦrange` IS THE
WHOLE LOAD; THE ZERO-Φ EXPLOIT EXISTS AND LANDS EXACTLY IN THE FENCED WORLDS (kernel-encoded, §3).

Nothing in the tie's statement pins `Φ` to the geometric `Ω₄^{Spin} → Ω₄^{Pin⁺}` inclusion — and
nothing needs to, because the hypotheses self-locate any fake:
* **zero map**: `zeroPhi_apply_g_iff_not_KTNonSplit` — a zero-`Φ` discharge of `hΦg` is EXACTLY
  the split world's `k₀ = 0` (refutes `KTNonSplit`); `zeroPhi_range_iff_sectorCollapsed` — a
  zero-`Φ` discharge of `hΦrange` is EXACTLY `SectorCollapsed`. Both are excluded by the triple.
* **`k₀`-generated fake** (`Φ := (e : DataBordismGrp ξ ≃+ ℤ) ↦ · • k₀`, buildable once the engine
  equiv lands): makes `hΦg` FREE — but its `hΦrange` becomes literally the conclusion
  `SpinImageCyclic` (sector ⊆ `⟨k₀⟩`). The tie cannot leak: a fake `Φ` reduces it to "assume the
  conclusion". A discharge wave claiming "`Φ` built, only `hΦrange` left" has built NOTHING.
* **the honest bound**: `phiRange_of_KTKernelCard` — `hΦrange` is recoverable from
  `KTKernelCard` + `hΦg`, so the interface's genuinely open input is `KTKernelCard`-grade (or the
  G8-5 overhang on the geometric route, G9-5). `hΦrange` is NOT a leaf input.

## G9-5 — THE G8-5 SEAM ADJUDICATED: the broad (`n = 0`) sector is HONEST for every route consumed
in-tree; the characteristic-sphere overhang is REAL, now FROZEN as `SectorIsGeometric` (§4).

Adjudication (the round-9 seed's either/or): the kernel-encoded reduction "rank-0 ⟹ the class
equals an honestly-empty-Σ class" is NOT provable in-tree (killing a nonempty trivial-`H¹` sphere
is one more genuine surgery — no tether exists), so the overhang is NAMED instead:
* `GeometricSpinRepresentable` (§4) — the honestly-geometric class predicate (`∃` representative
  with `IsEmpty Σ`), with the PROVED inclusion `emptySigmaRepresentable_of_geometric`
  (geometric ⟹ broad, via `spinSector_of_isEmpty_surf`) and non-vacuity
  `geometricSpinRepresentable_zero` (the empty structure). The converse inclusion is the overhang
  Prop `SectorIsGeometric` — GATED, not discharged; collapse-satisfiable
  (`sectorIsGeometric_of_sectorCollapsed`), so it is an interface, not a fence.
* WHY the in-tree routes are honest: every consumer (the assembly `kt_equiv_zmod16_of_sector`,
  both wave-1 bridges, the G8-4 recoveries) consumes the BROAD forms on BOTH sides — coherent and
  kernel-checked since round 8; and the broad upper bounds are RECOVERABLE from `KTKernelCard`
  (G8-4, G9-3), whose intended discharge (kernel = `{0, k₀}`) is blind to the seam.
* WHERE the overhang bites — the Lemma-5.3/Φ route ONLY: `sectorIsGeometric_of_phiRange_geometric`
  (§4) — an honest GEOMETRIC-ranged `Φ` (every `Φ w` empty-Σ-representable in the geometric
  sense) satisfying `hΦrange` FORCES `SectorIsGeometric`. I.e. the geometric-`Φ` discharge of
  `hΦrange` cannot avoid also discharging the sphere-overhang reduction. FROZEN SPEC below.

## G9-6 — FRESH-EYES AUDIT OF THE WAVE-1 BANKED BRICKS (prose findings).

* `metabolic_isotropic_of_pos` / `exists_brownPreserving_reduction`: honest unconditional algebra;
  hypotheses jointly satisfiable (hyperbolic plane, classically); consumption sharp. ⚠ NOTE the
  metabolic package `(L, hq, hmax)` is NOT supplied by `brown = 0` in-tree — the Witt-triviality
  gap is real and correctly gated. ⚠ DOCSTRING-INTEGRITY DEFECT (for the lead; the gate does not
  edit attacked modules): `exists_brownPreserving_reduction`'s docstring forward-references
  `EnhancementReducesToSpin` — NO such declaration exists in-tree (the shipped step-Prop is
  `KTSurgeryReduces`). Stale pointer from a pre-ship draft; fix the docstring.
* `mk_eq_of_tethered` / `surgeryStep_of_tethered`: thin packaging over
  `T2DataBordismGrp.mk_eq_of_bordant`; direction (`p' → p` bordism ⟹ `[p'] = [p]`) matches the
  underlying engine; `Nonempty (Bor …)` with `Bor := CharPairBorRealizedTethered` demands the
  genuine membrane structure (`Q`/`ιW`/pin data) — only reflexive-cylinder witnesses exist
  in-tree, so no cross-rank instantiation is currently possible (G9-2).
* `zsmul_of_two_torsion`: sound minimal algebra (parity split), load-bearing for the `⟨k₀⟩`
  collapse; not a tautology.
* `emptySigmaRep_of_surgeryReduces` terminal case: honest w.r.t. the BROAD predicate by
  definition; the broad-vs-geometric seam is G9-5's overhang, not a defect of the induction.

## FROZEN ROUND-9 SPEC (binding on the KTSurgeryReduces discharge wave and the Φ wave):
1. `KTSurgeryReduces` is consumed and audited AS `KernelReducesToSpin` (G9-1 equivalence): the
   round-8 triple discipline applies verbatim; the discharge wave's headline must name the
   excluded degenerate model (its construction must fail in the G8-3 split world's vacuous-fibre
   sense — i.e. produce a GENUINE tether, not the empty-structure fake, off the `[p] = 0` fibre).
2. A `SpinImageCyclic` discharge is subject to round-8 spec item 3 (route declaration) unchanged;
   it is NOT independent progress (G9-3: SIIT already implies it).
3. An `hΦrange` discharge must declare its route: (a) `KTKernelCard`-first (then
   `phiRange_of_KTKernelCard` makes `Φ` redundant for `SpinImageCyclic` — check the wave is not
   circular), or (b) geometric `Φ` — which MUST co-discharge `SectorIsGeometric` (G9-5); the
   dossier's Lemma-5.3 gap list must add `SectorIsGeometric` as a named input on route (b).
4. `hΦg` alone is never progress (G9-4: cheap/fake-able).
5. Provider-inhabitation rider (G8-1) on every per-`prov` result, unchanged.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTKernelSpinRoute
import SKEFTHawking.PinPlusKTSectorGate

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
open SKEFTHawking.PinPlusKTSectorGate
open SKEFTHawking.PinPlusKTKernelSpinRoute

namespace SKEFTHawking.PinPlusKTStepGate

variable {k : WithTop ℕ∞}

/-! ## §1. G9-1 — the step-Prop is EQUIVALENT to the binder; every G8 model transfers -/

/-- **The converse bridge** (G9-1): `KernelReducesToSpin ⟹ KTSurgeryReduces`. The rank-0
representative `p'` that KRTS supplies for the kernel class `[p]` is itself the strictly
rank-dropping representative the step-Prop demands at any `0 < p.2.n` representative
(`p'.2.n = 0 < p.2.n`). One line — which is the finding: the wave-1 decomposition RELOCATES the
open content, it does not weaken it. -/
theorem surgeryReduces_of_kernelReducesToSpin (prov : CharPairWProviderPerOp (𝓡 4) k)
    (h : KernelReducesToSpin prov) : KTSurgeryReduces prov := by
  intro p hbrown hpos
  obtain ⟨p', hp', heq⟩ := h _ hbrown
  exact ⟨p', by rw [show p'.2.n = 0 from hp']; exact hpos, heq⟩

/-- **G9-1 headline — the equivalence.** `KTSurgeryReduces ⟺ KernelReducesToSpin`. Settles the
bridge-sharpness question (attack line (b)) maximally: the induction bridge consumes exactly the
step-Prop, and the step-Prop is exactly the binder. All round-8 vacuity structure (degenerate
models, consumption discipline) transfers verbatim between the two shapes. -/
theorem ktSurgeryReduces_iff_kernelReducesToSpin (prov : CharPairWProviderPerOp (𝓡 4) k) :
    KTSurgeryReduces prov ↔ KernelReducesToSpin prov :=
  ⟨kernelReducesToSpin_of_surgeryReduces prov, surgeryReduces_of_kernelReducesToSpin prov⟩

/-- **The G8-3 kernel-collapse discharges `KTSurgeryReduces`** at zero geometric cost (G9-1 model
transfer): in the split world every brown-0 class is `0`, so the empty structure is a valid
strictly-smaller representative for every `0 < n` kernel representative. A surgery-trace
construction that only ever lands on the `[p] = 0` fibre has discharged NOTHING beyond this
degenerate model — the wave must produce tethers off that fibre. -/
theorem ktSurgeryReduces_of_kernelTrivial (prov : CharPairWProviderPerOp (𝓡 4) k)
    (ht : KernelTrivial prov) : KTSurgeryReduces prov :=
  surgeryReduces_of_kernelReducesToSpin prov (kernelReducesToSpin_of_kernelTrivial prov ht)

/-- **The G8-2 sector-collapse + `KTNonSplit` REFUTES `KTSurgeryReduces`** (G9-1 model transfer):
in the collapsed-sector nonsplit world `k₀` is a `0 < n`-represented kernel class admitting NO
rank-lowering chain (it would terminate at a rank-0 representative the collapse forbids). The
step-Prop is fenced on BOTH sides — satisfiable in the split world, refutable in the
collapsed+nonsplit world — hence genuinely open, sitting at exactly KRTS strength. -/
theorem not_ktSurgeryReduces_of_sectorCollapsed_of_nonsplit (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hc : SectorCollapsed prov) (hns : KTNonSplit prov) : ¬ KTSurgeryReduces prov :=
  fun h => not_kernelReducesToSpin_of_sectorCollapsed_of_nonsplit prov hc hns
    (kernelReducesToSpin_of_surgeryReduces prov h)

/-! ## §2. G9-3 — `SpinImageCyclic` located: the ≤-cyclic face of `SpinImageIsTwo` -/

/-- **`SpinImageIsTwo` implies `SpinImageCyclic` outright** (G9-3): `y = 0 = 0 • k₀` or
`y = k₀ = 1 • k₀`. The new wave-1 Prop is the WEAKER of the two — its only delta from SIIT is the
2-torsion collapse of `⟨k₀⟩` (recovered by wave-1's `spinImageIsTwo_of_cyclic_of_kummerRep` from
`KummerWitness.1`). A `SpinImageCyclic` discharge is therefore never independent progress past
SIIT. -/
theorem spinImageCyclic_of_spinImageIsTwo (prov : CharPairWProviderPerOp (𝓡 4) k)
    (h2 : SpinImageIsTwo prov) : SpinImageCyclic prov := by
  intro y hy
  rcases h2 y hy with rfl | rfl
  · exact ⟨0, (zero_smul ℤ _).symm⟩
  · exact ⟨1, (one_smul ℤ _).symm⟩

/-- **Sector-collapse discharges `SpinImageCyclic`** (G9-3 degenerate model, `m = 0` everywhere):
the G8-2 world satisfies the wave-1 Prop at zero geometric cost. -/
theorem spinImageCyclic_of_sectorCollapsed (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hc : SectorCollapsed prov) : SpinImageCyclic prov :=
  spinImageCyclic_of_spinImageIsTwo prov (spinImageIsTwo_of_sectorCollapsed prov hc)

/-- **Kernel-collapse collapses the sector** (G9-3 composition brick): the sector sits inside the
kernel, so the G8-3 world is a sub-world of the G8-2 world. (Round 8 proved the two SIIT
discharges independently; this is the honest containment.) -/
theorem sectorCollapsed_of_kernelTrivial (prov : CharPairWProviderPerOp (𝓡 4) k)
    (ht : KernelTrivial prov) : SectorCollapsed prov :=
  fun x hx => ht x (emptySigmaRepresentable_in_kernel prov x hx)

/-- **Kernel-collapse discharges `SpinImageCyclic`** (G9-3): via the containment. Both G8
degenerate models satisfy the wave-1 Prop; its consumption is subject to the round-8 route
discipline unchanged. -/
theorem spinImageCyclic_of_kernelTrivial (prov : CharPairWProviderPerOp (𝓡 4) k)
    (ht : KernelTrivial prov) : SpinImageCyclic prov :=
  spinImageCyclic_of_sectorCollapsed prov (sectorCollapsed_of_kernelTrivial prov ht)

/-- **`SpinImageCyclic` is recoverable from `KTKernelCard`** (G9-3, the G8-4 pattern one Prop
down): the kernel bound already classifies the sector into `{0, k₀} ⊆ ⟨k₀⟩`. Discharge waves
should target `KTKernelCard`/`KernelReducesToSpin`; `SpinImageCyclic` is a recoverable face. -/
theorem spinImageCyclic_of_KTKernelCard (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hcard : KTKernelCard prov) : SpinImageCyclic prov :=
  spinImageCyclic_of_spinImageIsTwo prov (spinImageIsTwo_of_KTKernelCard prov hcard)

/-- **The composed-bridge pair `{SpinImageCyclic, KummerWitness.1}` is triple-fenced** (G9-3):
under sector-collapse, `k₀`'s representability hands the collapse `k₀ = 0`, refuting
`KTNonSplit` — so consuming the pair TOGETHER WITH `KTNonSplit` (the round-8 triple) excludes
both collapse worlds. The wave-1 bridge `spinImageIsTwo_of_cyclic_of_kummerRep` stays honest
exactly when its output SIIT is consumed inside the triple. -/
theorem not_KTNonSplit_of_kummerRep_of_sectorCollapsed (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hc : SectorCollapsed prov)
    (hk : EmptySigmaRepresentable prov (ktKernelRep prov)) : ¬ KTNonSplit prov :=
  fun hns => hns (hc _ hk)

/-! ## §3. G9-4 — the Φ interface: `hΦg` cheap, `hΦrange` the whole load, zero-Φ self-locating -/

section PhiInterface

variable {X : Type*} [TopologicalSpace X] {k' : WithTop ℕ∞}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {ξ : TangentialData X k' I'}

/-- **A zero-map discharge of `hΦg` is exactly the split world** (G9-4): `0 = k₀` is the negation
of `KTNonSplit`. The engine tie's generator hypothesis cannot be faked by the zero map without
landing in the world the triple already excludes. -/
theorem zeroPhi_apply_g_iff_not_KTNonSplit (prov : CharPairWProviderPerOp (𝓡 4) k)
    (g : StrMfd ξ) :
    ((0 : DataBordismGrp ξ →+ T2DataBordismGrp (pinPlusCharPairData prov))
        (DataBordismGrp.mk ξ g) = ktKernelRep prov) ↔ ¬ KTNonSplit prov := by
  simp [KTNonSplit, eq_comm]

/-- **A zero-map discharge of `hΦrange` is exactly `SectorCollapsed`** (G9-4): surjectivity of
the zero map onto the sector says every sector class is `0`. The engine tie's range hypothesis
cannot be faked by the zero map without asserting the G8-2 collapse outright. -/
theorem zeroPhi_range_iff_sectorCollapsed (prov : CharPairWProviderPerOp (𝓡 4) k) :
    (∀ y, EmptySigmaRepresentable prov y →
        ∃ w : DataBordismGrp ξ,
          (0 : DataBordismGrp ξ →+ T2DataBordismGrp (pinPlusCharPairData prov)) w = y)
      ↔ SectorCollapsed prov := by
  constructor
  · intro h y hy
    obtain ⟨w, hw⟩ := h y hy
    simpa using hw.symm
  · intro hc y hy
    exact ⟨0, by simpa using (hc y hy).symm⟩

/-- **`hΦrange` is recoverable from `KTKernelCard` + `hΦg`** (G9-4): the kernel bound classifies
the sector into `{0, k₀}`, and `{0, k₀} ⊆ range Φ` needs only `map_zero` and the generator
hypothesis. So the Φ interface's genuinely open input is `KTKernelCard`-grade (or the G8-5
overhang on the geometric route, G9-5) — `hΦrange` is NOT a leaf input, and a wave that builds
`Φ` + `hΦg` and then obtains `hΦrange` from `KTKernelCard` has made `Φ` redundant for
`SpinImageCyclic` (`spinImageCyclic_of_KTKernelCard` is direct). -/
theorem phiRange_of_KTKernelCard (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hcard : KTKernelCard prov) (g : StrMfd ξ)
    (Φ : DataBordismGrp ξ →+ T2DataBordismGrp (pinPlusCharPairData prov))
    (hΦg : Φ (DataBordismGrp.mk ξ g) = ktKernelRep prov) :
    ∀ y, EmptySigmaRepresentable prov y → ∃ w, Φ w = y := by
  intro y hy
  rcases hcard y (emptySigmaRepresentable_in_kernel prov y hy) with rfl | rfl
  · exact ⟨0, map_zero Φ⟩
  · exact ⟨DataBordismGrp.mk ξ g, hΦg⟩

end PhiInterface

/-! ## §4. G9-5 — the G8-5 seam frozen: the geometric predicate and the sphere overhang -/

/-- **The honestly-geometric spin-class predicate** (G9-5): `x` has a representative whose
characteristic surface is literally EMPTY (`IsEmpty Σ`) — the class-level image of the geometric
spin condition (`w₂ + w₁²`-dual surface removable), STRICTLY stronger in form than the broad
`EmptySigmaRepresentable` (`n = 0`, H¹-triviality). The `Ω₄^{Spin}` image the KT dossier speaks
of is THIS predicate; the broad form is what the in-tree sector Props consume. -/
def GeometricSpinRepresentable (prov : CharPairWProviderPerOp (𝓡 4) k)
    (x : T2DataBordismGrp (pinPlusCharPairData prov)) : Prop :=
  ∃ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
    IsEmpty p.2.surf.M ∧ T2DataBordismGrp.mk (pinPlusCharPairData prov) p = x

/-- **Geometric ⟹ broad** (G9-5, the PROVED inclusion): an empty surface forces rank 0
(`spinSector_of_isEmpty_surf`). The converse is the OPEN sphere-overhang (`SectorIsGeometric`). -/
theorem emptySigmaRepresentable_of_geometric (prov : CharPairWProviderPerOp (𝓡 4) k)
    (x : T2DataBordismGrp (pinPlusCharPairData prov)) (h : GeometricSpinRepresentable prov x) :
    EmptySigmaRepresentable prov x := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p, spinSector_of_isEmpty_surf prov p hp, rfl⟩

/-- Non-vacuity of the geometric predicate: `0` is geometrically spin-representable (the empty
structure's surface is `emptySM`, whose carrier is `PEmpty`). -/
theorem geometricSpinRepresentable_zero (prov : CharPairWProviderPerOp (𝓡 4) k) :
    GeometricSpinRepresentable prov 0 :=
  ⟨⟨emptySM, charPairBundledEmpty⟩, inferInstanceAs (IsEmpty PEmpty), rfl⟩

/-- **THE G8-5 OVERHANG, FROZEN** (G9-5): every broad-sector class is honestly-geometric — the
"one more surgery killing the characteristic sphere" reduction (a rank-0-nonempty-Σ representative
is bordant to a genuinely-empty-Σ one). GATED: not provable in-tree (no tether kills a nonempty
trivial-`H¹` surface), and NOT required by any in-tree consumer — it bites ONLY the geometric-`Φ`
route to `hΦrange` (`sectorIsGeometric_of_phiRange_geometric`). A `SpinImageIsTwo`/`SpinImageCyclic`
discharge via geometric `Φ` must co-discharge this Prop; the `KTKernelCard` route avoids it.

**Vacuity-attack line** (round-10 seed): collapse-satisfiable (`sectorIsGeometric_of_sectorCollapsed`
— `0` is geometric), so this is an INTERFACE, not a fence; its honest discharge demands, for each
nonzero broad-sector class, an actual sphere-killing bordism — no in-tree witness exists (the only
geometric representative in-tree is the empty structure, covering the `0` fibre only). -/
def SectorIsGeometric (prov : CharPairWProviderPerOp (𝓡 4) k) : Prop :=
  ∀ x : T2DataBordismGrp (pinPlusCharPairData prov),
    EmptySigmaRepresentable prov x → GeometricSpinRepresentable prov x

/-- **Sector-collapse discharges the overhang Prop** (G9-5): every sector class is `0`, and `0`
is geometric. The overhang is therefore an interface (collapse-satisfiable), not a fence — its
consumption inherits the triple discipline like everything else in the sector layer. -/
theorem sectorIsGeometric_of_sectorCollapsed (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hc : SectorCollapsed prov) : SectorIsGeometric prov := by
  intro x hx
  rw [hc x hx]
  exact geometricSpinRepresentable_zero prov

section PhiSeam

variable {X : Type*} [TopologicalSpace X] {k' : WithTop ℕ∞}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {ξ : TangentialData X k' I'}

/-- **WHERE THE OVERHANG BITES** (G9-5, the seam adjudication headline): an honest GEOMETRIC `Φ`
(every image class geometrically spin-representable — the real `Ω₄^{Spin} → Ω₄^{Pin⁺}` inclusion)
satisfying the engine tie's `hΦrange` FORCES the overhang Prop `SectorIsGeometric`. So the
geometric route to `hΦrange` cannot dodge the characteristic-sphere overhang: covering the BROAD
sector with geometric classes IS the sphere-killing reduction. The dossier's Lemma-5.3 gap list
must carry `SectorIsGeometric` as a named input on this route (frozen spec item 3b). -/
theorem sectorIsGeometric_of_phiRange_geometric (prov : CharPairWProviderPerOp (𝓡 4) k)
    (Φ : DataBordismGrp ξ →+ T2DataBordismGrp (pinPlusCharPairData prov))
    (hgeo : ∀ w, GeometricSpinRepresentable prov (Φ w))
    (hΦrange : ∀ y, EmptySigmaRepresentable prov y → ∃ w, Φ w = y) :
    SectorIsGeometric prov := by
  intro x hx
  obtain ⟨w, rfl⟩ := hΦrange x hx
  exact hgeo w

end PhiSeam

end SKEFTHawking.PinPlusKTStepGate
