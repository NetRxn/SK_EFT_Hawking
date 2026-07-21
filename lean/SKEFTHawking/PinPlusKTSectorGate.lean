/-
# Phase 5q.H W-D GATE ROUND 8 (fresh-context VACUITY ATTACK on the sector Props)

Adversarial gate findings against the W-D opener `PinPlusKTKernelSector` (the empty-Σ spin-kernel
sector: `KernelReducesToSpin` / `SpinImageIsTwo` / `KummerWitness` + bridges + banked 2-torsion),
over the tethered carrier (`pinPlusCharPairData prov`, `Bor := CharPairBorRealizedTethered`) and the
σ-threaded per-op provider (F7-A landed). Verdict: **PASS WITH BINDING CONSUMPTION SPEC** — no
sector Prop admits a zero-geometric-input discharge in-tree, every bridge consumes exactly what it
claims, and the 2-torsion fence is kernel-verified unbreachable (§6); BUT the opener's PRE-FLAGGED
pair-gating discipline (`{SpinImageIsTwo, KTNonSplit}` "pins the image to EXACTLY ℤ/2") is
REFUTED at the kernel level (§2) and is replaced by the frozen round-8 consumption spec below.

## G8-1 — PROVIDER INHABITATION (the F6/F7-A pattern one level up): CONDITIONAL, NOT VACUOUS,
ZERO IN-TREE INSTANCES. LOUD CAVEAT ON EVERY W-D RESULT.

`CharPairWProviderPerOp (𝓡 4) k` has **no unconditional in-tree inhabitant** (grep-verified: the
only constructor is `CharPairWProviderPerOp.ofCylinderEngine`, which consumes the two OPEN Track-2
residuals). Unlike round 7's F7-A (where the bare-`s` provider was mathematically UNINHABITABLE and
`∀ prov`-statements were classically vacuous), the σ-threaded form is honest-inhabitable — so the
W-D layer is **CONDITIONAL, not vacuous**: nothing here is vacuously true, but every per-`prov`
theorem (the three sector Props, all bridges, AND the banked positive facts
`spinSector_two_torsion` / `emptySigmaRepresentable_two_torsion`) currently has ZERO live
instances. The precise inhabitation dependency is kernel-encoded (§1,
`nonempty_provider_of_residuals`): `Nonempty (CharPairWProviderPerOp I k)` ⟸
  (a) `cylData : ∀ {s} (σ : CharPairStrBundled I s), CylWAdmData s` — the σ-threaded concrete-
      cylinder Lefschetz–Wu residual (Track-2 seam: `CylinderWAdmPinned.toCylWAdmData` + the
      `ofClosedPD*` engine family, each still consuming per-`M` closed-PD tower inputs), and
  (b) `addClosure` — the ⊔-block-diagonal admissibility. **CLOSED (arm 4):** `SumRelFundClass`
      is concretely inhabited (`sumRelFundClass`, PoincareLefschetzRelFundClassSumGen) and
      `WAdmPinned.add` (PinPlusCharPairWProviderClosed) consumes it directly — residual (b)
      is discharged unconditionally; only residual (a)'s per-`M` leaves remain.
DISCIPLINE: a W-D discharge wave's headline MUST carry the "conditional on provider inhabitation
(Track-2 residuals (a)+(b))" rider until an in-tree `prov` lands. A "discharged" sector Prop with
no `prov` instance is a theorem about a possibly-empty parameter space — real, but not yet about
Pin⁺ bordism.

## G8-2 — THE PRE-FLAGGED PAIR FINDING: VERIFIED IN KIND, WRONG IN MECHANISM; PAIR-GATING IS
INSUFFICIENT (kernel-encoded, §2).

The opener (§4, `SpinImageIsTwo` docstring) pre-flagged: a collapsed sector (every empty-Σ class
`= 0`) discharges `SpinImageIsTwo` trivially, and claimed "that same collapse makes `k₀ = 0`,
i.e. FALSIFIES `KTNonSplit` — hence the pair `{SpinImageIsTwo, KTNonSplit}` must be gated
TOGETHER; the pair pins the image to EXACTLY ℤ/2." The first half is CONFIRMED
(`spinImageIsTwo_of_sectorCollapsed`). The second half is FALSE:
* sector-collapse does NOT force `k₀ = 0` — `k₀` need not be empty-Σ-representable at all absent
  `KummerWitness`/`KernelReducesToSpin`; what collapse falsifies is `KummerWitness`
  (`not_kummerWitness_of_sectorCollapsed`), NOT `KTNonSplit`.
* consequently the PAIR `{SpinImageIsTwo, KTNonSplit}` is JOINTLY satisfied under sector-collapse
  (`pair_holds_under_sectorCollapsed`) with the sector image `= {0}` — trivial, NOT ℤ/2
  (`sector_image_eq_singleton_of_sectorCollapsed`). Pair-gating excludes nothing.
* what the collapse actually kills, GIVEN `KTNonSplit`, is `KernelReducesToSpin`
  (`not_kernelReducesToSpin_of_sectorCollapsed_of_nonsplit`) — `k₀` is a kernel class with no
  rank-0 representative in the collapsed world.
* the CORRECTED exactly-ℤ/2 pin is `{SpinImageIsTwo, KummerWitness}`:
  `sector_image_eq_pair` + `sector_image_ncard_two` (the image is the 2-element set `{0, k₀}`).

## G8-3 — THE SYMMETRIC KERNEL-COLLAPSE (the quantifier trick the brief asked for, §3):
`KernelReducesToSpin` has its OWN collapse-discharge. A trivial kernel (`∀ x ∈ ker, x = 0`)
discharges BOTH `KernelReducesToSpin` AND `SpinImageIsTwo` at zero geometric cost
(`kernelReducesToSpin_of_kernelTrivial`, `spinImageIsTwo_of_kernelTrivial`) — this is exactly the
SPLIT-extension world (`G ≅ ℤ/8`, `k₀ = 0`), and the ONLY Prop excluding it is `KTNonSplit`
(`not_KTNonSplit_of_kernelTrivial`). Net (G8-2 + G8-3): **each 2-subset of the triple
`{KernelReducesToSpin, SpinImageIsTwo, KTNonSplit}` admits a degenerate collapse model**
(sector-collapse satisfies `{SIIT, KTNS}`; kernel-collapse satisfies `{KRTS, SIIT}`; `{KRTS,
KTNS}` bounds no cardinality). The MINIMAL honest consumption unit is the TRIPLE — exactly the
hypothesis row of `kt_equiv_zmod16_of_sector` — or `{SpinImageIsTwo, KummerWitness}` +
`KernelReducesToSpin` (since `KummerWitness = k₀-representability ∧ KTNonSplit` is the one
self-fenced Prop: BOTH collapses refute it).

## G8-4 — `SpinImageIsTwo` IS NOT INDEPENDENT CONTENT on the algebraic sector predicate (§4):
since the sector lands inside the kernel (`emptySigmaRepresentable_in_kernel`, DONE direction),
`KTKernelCard → SpinImageIsTwo` outright (`spinImageIsTwo_of_KTKernelCard`), and
`KTKernelCard + k₀-representability → KernelReducesToSpin`
(`kernelReducesToSpin_of_card_of_kummerRep`). So the decomposition `{KRTS, SIIT} ⟺ KTKernelCard`
is an equivalence **modulo `KummerWitness.1`**, and the genuinely NEW geometric content of the
sector decomposition is exactly `{KernelReducesToSpin, KummerWitness.1}` — `SpinImageIsTwo` is
the recoverable face. Discharge waves should target KRTS/KummerWitness first; an SIIT-first
discharge that does not route through Lemma 5.3 is a collapse-smell (check it against G8-2).

## G8-5 — THE SECTOR-FORM SEAM (`σ.n = 0` vs `IsEmpty σ.surf.M`, §5): the algebraic predicate is
provably keyed to H¹-TRIVIALITY, not surface emptiness (`rank_zero_of_subsingleton_H1`: any
bundle whose surface has subsingleton `H¹(Σ;ℤ/2)` is rank-0 — the basis equiv forces it). A
NONEMPTY surface with trivial `H¹` (classically: `Σ = S²`, e.g. a characteristic sphere
representing `PD(w₁²) ≠ 0`) would be `IsSpinSectorStr` while geometrically NON-spin — the
converse of `spinSector_of_isEmpty_surf` is NOT provable and (classically) FALSE. No such
in-tree witness exists (none constructible without a sphere `H¹` computation), so this is a
DEFERRED TIE, not a live exploit: all banked facts (brown = 0, 2-torsion) are SOUND on the broad
predicate (kernel-checked), and the assembly is insensitive (broad-SIIT is *stronger*, and the
{KRTS, SIIT} pair composes to the same `KTKernelCard` either way). ROUND-9 SEED: an
`SpinImageIsTwo` discharge via KT Lemma 5.3 covers genuinely-spin (`Σ = ∅`) representatives
only; the `n = 0`-nonempty-Σ overhang (characteristic spheres) must be covered either by routing
through `KTKernelCard` (G8-4) or by a sphere-reduction lemma — the dossier's Lemma-5.3 gap list
(§6 of the opener) does not yet name this overhang.

## G8-6 — THE 2-TORSION FENCE: KERNEL-VERIFIED UNBREACHABLE (§6). The brief's attack — leak
`spinSector_two_torsion` + in-tree ops (rank-0 sums, unit laws) into carrier-wide 2-torsion,
reproducing the no-go `dataBordism_two_torsion_of_revStr_trivial` — is not merely unproven but
PROVABLY IMPOSSIBLE on this carrier: `ktRP4Class_not_two_torsion` (`[ℝP⁴] + [ℝP⁴] ≠ 0`, since
`charPairBrown` maps it to `2 ≠ 0` in `ZMod 8`) gives `no_carrierWide_two_torsion`
(`¬ ∀ x, x + x = 0`). Any purported carrier-wide collapse — by whatever mechanism — now
contradicts a kernel theorem. The rank-0 restriction genuinely avoids the no-go's collapse
mechanism: `revStr_fixed_of_rank_zero` requires `σ.n = 0` and `[ℝP⁴]`'s structure is rank-1, so
the fence's gate is typed, and the leak is refuted semantically, not just syntactically.

## G8-7 — BRIDGE-SHARPNESS AUDIT (§7): `KTKernelOrderTwo_of_reduces` consumes exactly
`{KernelReducesToSpin}` + the banked structural 2-torsion (verified by proof inspection — no
hidden `KTNonSplit`/`KTKernelCard`); `kt_equiv_zmod16_of_sector` consumes exactly the triple.
ONE over-consumption found (minor): `kernelRep_two_torsion_of_KummerWitness` takes the full
`KummerWitness` but uses only its FIRST conjunct — the sharp form is
`kernelRep_two_torsion_of_emptySigmaRep` (§7 below). Consumers needing only the ÷32-upper bound
should take the representability conjunct alone, not the whole witness.

## Zero-geometric-input discharge probes (live `lean_multi_attempt`, recorded — no failing code):
* `KernelReducesToSpin prov`: `intro x hx; exact ⟨⟨emptySM, charPairBundledEmpty⟩, rfl, ?⟩` dies —
  the final goal `mk … = x` is exactly `0 = x`, unavailable for arbitrary kernel `x`;
  `simp [KernelReducesToSpin]`, `aesop`, `tauto`, `decide` all fail (`decide`: free carrier).
* `SpinImageIsTwo prov`: `intro x h; left` reduces to the open collapse `x = 0`;
  `rcases h with ⟨p, hp, rfl⟩; left` needs `[p] = 0` for ARBITRARY rank-0 `p` — not available
  (only the empty structure's class computes to `0`); `right` needs `x = k₀` — likewise open.
* `KummerWitness prov`: `exact ⟨emptySigmaRepresentable_zero prov, ?⟩` type-mismatches unless
  `k₀ = 0` — which is the NEGATION of the second conjunct; no other rank-0 witness exists in-tree
  (the Kummer carrier is unbuilt). The Prop self-fences (G8-3).

## FROZEN ROUND-8 CONSUMPTION SPEC (binding on the W-D discharge waves):
1. Consumption unit = the TRIPLE `{KernelReducesToSpin, SpinImageIsTwo, KTNonSplit}` (or
   equivalently `{KRTS, SIIT, KummerWitness}`); NEVER a proper subset, and NEVER the opener's
   pair `{SIIT, KTNonSplit}` (refuted, G8-2). A wave discharging ONE Prop must name which
   degenerate model (G8-2/G8-3) its route excludes.
2. Every W-D result ships with the provider-inhabitation rider (G8-1) until Track-2's
   `cylData`/`addClosure` residuals land an in-tree `prov`.
3. An `SpinImageIsTwo` discharge must state its route: via Lemma 5.3 + the `n = 0`-nonempty-Σ
   overhang (G8-5), or via `KTKernelCard` (G8-4). A collapse-shaped route (`∀ sector x, x = 0`)
   is a program-death signal, not a discharge — it refutes `KummerWitness`.
4. The ÷32-upper consumers take `EmptySigmaRepresentable prov (ktKernelRep prov)` (the sharp
   hypothesis, §7), not the full `KummerWitness`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTKernelSector
import SKEFTHawking.PinPlusCharPairWProviderTransport

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
open SKEFTHawking.PinPlusCharPairWProviderTransport
open SKEFTHawking.SingularCohomologyMod2

namespace SKEFTHawking.PinPlusKTSectorGate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-! ## §1. G8-1 — the provider-inhabitation dependency, kernel-encoded

The σ-threaded provider has NO unconditional in-tree inhabitant; its inhabitation reduces EXACTLY
to the two Track-2 residuals. This theorem is the loud, kernel-checked form of the dependency —
the one-level-up F6/F7-A status: CONDITIONAL (not vacuous), zero live instances. -/

/-- **The provider-inhabitation dependency** (G8-1). `Nonempty (CharPairWProviderPerOp I k)`
follows from the two open Track-2 residuals — the σ-threaded concrete-cylinder Lefschetz–Wu
bundle and the ⊔-closure — and from NOTHING LESS in-tree (the only constructor is
`ofCylinderEngine`). Until these land, every per-`prov` W-D statement has zero live instances. -/
theorem nonempty_provider_of_residuals
    (cylData : ∀ {s : SingularManifold.{0} PUnit.{1} k I},
      CharPairStrBundled I s → CylWAdmData s)
    (addClosure : ∀ {s₁ t₁ s₂ t₂ : SingularManifold.{0} PUnit.{1} k I}
      {b₁ : Bordism (I.prod (𝓡∂ 1)) s₁ t₁} {b₂ : Bordism (I.prod (𝓡∂ 1)) s₂ t₂},
      WAdmPinned b₁ → WAdmPinned b₂ → WAdmPinned (b₁.add b₂)) :
    Nonempty (CharPairWProviderPerOp I k) :=
  ⟨CharPairWProviderPerOp.ofCylinderEngine cylData addClosure⟩

/-! ## §2. G8-2 — the sector-collapse demonstrators: the pre-flagged pair discipline is REFUTED

`SectorCollapsed prov` = the degenerate world where the only empty-Σ-representable class is `0`
(no Kummer witness ever lands). The opener pre-flagged that this discharges `SpinImageIsTwo`
alone; here we kernel-verify the flag AND refute the claimed fence: the PAIR
`{SpinImageIsTwo, KTNonSplit}` survives the collapse (so pair-gating excludes nothing); what the
collapse kills is `KummerWitness` outright and — given `KTNonSplit` — `KernelReducesToSpin`. -/

/-- The sector-collapse hypothesis: the only empty-Σ-representable class is `0` (the world where
no nonzero rank-0 representative exists — e.g. no Kummer-flavoured carrier ever lands). NOT
provable in-tree (it is itself open geometric content); used purely as the degenerate-model
hypothesis for the vacuity demonstrators. -/
def SectorCollapsed (prov : CharPairWProviderPerOp (𝓡 4) k) : Prop :=
  ∀ x : T2DataBordismGrp (pinPlusCharPairData prov), EmptySigmaRepresentable prov x → x = 0

/-- **The pre-flagged finding, kernel-verified** (G8-2a): sector-collapse discharges
`SpinImageIsTwo` at zero geometric cost (left disjunct everywhere). -/
theorem spinImageIsTwo_of_sectorCollapsed (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hc : SectorCollapsed prov) : SpinImageIsTwo prov :=
  fun x hx => Or.inl (hc x hx)

/-- **The opener's pair-gating claim is REFUTED** (G8-2b): under sector-collapse the pair
`{SpinImageIsTwo, KTNonSplit}` HOLDS JOINTLY — the collapse does NOT falsify `KTNonSplit`
(`k₀` need not be empty-Σ-representable), so gating the pair together excludes the collapse
model NOT AT ALL. The pair does not pin the image to ℤ/2 (see
`sector_image_eq_singleton_of_sectorCollapsed`: the image is trivial in this world). -/
theorem pair_holds_under_sectorCollapsed (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hc : SectorCollapsed prov) (hns : KTNonSplit prov) :
    SpinImageIsTwo prov ∧ KTNonSplit prov :=
  ⟨spinImageIsTwo_of_sectorCollapsed prov hc, hns⟩

/-- Under sector-collapse the empty-Σ image is the SINGLETON `{0}` — not `{0, k₀}`, not ℤ/2
(G8-2b, the "exactly ℤ/2" half of the opener's pair claim fails in the collapse world). -/
theorem sector_image_eq_singleton_of_sectorCollapsed (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hc : SectorCollapsed prov) :
    {x : T2DataBordismGrp (pinPlusCharPairData prov) | EmptySigmaRepresentable prov x} = {0} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ⟨hc x, fun h => h ▸ emptySigmaRepresentable_zero prov⟩

/-- **What sector-collapse ACTUALLY falsifies, part 1** (G8-2c): `KummerWitness` — its
representability conjunct hands the collapse `k₀ = 0`, contradicting its non-split conjunct.
(`KummerWitness` is the one self-fenced sector Prop.) -/
theorem not_kummerWitness_of_sectorCollapsed (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hc : SectorCollapsed prov) : ¬ KummerWitness prov :=
  fun hk => hk.2 (hc _ hk.1)

/-- **What sector-collapse ACTUALLY falsifies, part 2** (G8-2d): GIVEN `KTNonSplit`, the collapse
kills `KernelReducesToSpin` — `k₀` is a genuine kernel class (`charPairBrown_ktKernelRep`) that
the collapsed sector cannot represent. This is the honest triple-level fence: the collapse model
satisfies `{SIIT, KTNS}` but never all three. -/
theorem not_kernelReducesToSpin_of_sectorCollapsed_of_nonsplit
    (prov : CharPairWProviderPerOp (𝓡 4) k) (hc : SectorCollapsed prov) (hns : KTNonSplit prov) :
    ¬ KernelReducesToSpin prov :=
  fun hred => hns (hc _ (hred _ (charPairBrown_ktKernelRep prov)))

/-- **The CORRECTED exactly-ℤ/2 pin** (G8-2e): the pair that genuinely pins the empty-Σ image to
the two-element set `{0, k₀}` is `{SpinImageIsTwo, KummerWitness}` — SIIT gives `⊆`, the banked
zero-representability gives `0 ∈`, and the Kummer witness gives `k₀ ∈`. (Compare the refuted
`{SIIT, KTNonSplit}`, which is collapse-satisfiable with trivial image.) -/
theorem sector_image_eq_pair (prov : CharPairWProviderPerOp (𝓡 4) k)
    (h2 : SpinImageIsTwo prov) (hk : KummerWitness prov) :
    {x : T2DataBordismGrp (pinPlusCharPairData prov) | EmptySigmaRepresentable prov x}
      = {0, ktKernelRep prov} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨h2 x, ?_⟩
  rintro (rfl | rfl)
  · exact emptySigmaRepresentable_zero prov
  · exact hk.1

/-- The corrected pin, cardinality form (G8-2e): under `{SpinImageIsTwo, KummerWitness}` the
empty-Σ image has EXACTLY two elements — the honest "spin image ≅ ℤ/2" count. -/
theorem sector_image_ncard_two (prov : CharPairWProviderPerOp (𝓡 4) k)
    (h2 : SpinImageIsTwo prov) (hk : KummerWitness prov) :
    {x : T2DataBordismGrp (pinPlusCharPairData prov) | EmptySigmaRepresentable prov x}.ncard
      = 2 := by
  rw [sector_image_eq_pair prov h2 hk]
  exact Set.ncard_pair (Ne.symm hk.2)

/-! ## §3. G8-3 — the kernel-collapse demonstrators: `KernelReducesToSpin`'s own quantifier trick

The symmetric degenerate model: a TRIVIAL kernel (the split-extension world `G ≅ ℤ/8`,
`k₀ = 0`). It discharges BOTH `KernelReducesToSpin` and `SpinImageIsTwo` at zero geometric cost;
only `KTNonSplit` excludes it. Hence no 2-subset of the triple is collapse-proof: the TRIPLE is
the minimal honest consumption unit. -/

/-- The kernel-collapse hypothesis: the `charPairBrown` kernel is trivial (the split world).
NOT provable in-tree; the degenerate-model hypothesis for the G8-3 demonstrators. -/
def KernelTrivial (prov : CharPairWProviderPerOp (𝓡 4) k) : Prop :=
  ∀ x : T2DataBordismGrp (pinPlusCharPairData prov), charPairBrown prov x = 0 → x = 0

/-- **`KernelReducesToSpin` is kernel-collapse-dischargeable** (G8-3a): if the kernel is trivial,
every kernel class is `0`, and `0` is empty-Σ-representable (the empty structure). The
zero-geometric-input discharge of KRTS exists exactly in the split world. -/
theorem kernelReducesToSpin_of_kernelTrivial (prov : CharPairWProviderPerOp (𝓡 4) k)
    (ht : KernelTrivial prov) : KernelReducesToSpin prov := by
  intro x hx
  rw [ht x hx]
  exact emptySigmaRepresentable_zero prov

/-- **`SpinImageIsTwo` is ALSO kernel-collapse-dischargeable** (G8-3b): the sector sits inside the
kernel (`emptySigmaRepresentable_in_kernel`), so kernel-triviality collapses the sector too. -/
theorem spinImageIsTwo_of_kernelTrivial (prov : CharPairWProviderPerOp (𝓡 4) k)
    (ht : KernelTrivial prov) : SpinImageIsTwo prov :=
  fun x hx => Or.inl (ht x (emptySigmaRepresentable_in_kernel prov x hx))

/-- **Only `KTNonSplit` excludes the kernel-collapse** (G8-3c): kernel-triviality forces `k₀ = 0`
(`k₀` is a kernel class), i.e. the split extension. The pair `{KRTS, SIIT}` — the full
`KTKernelCard`-strength content — is satisfiable in the split world; the triple is minimal. -/
theorem not_KTNonSplit_of_kernelTrivial (prov : CharPairWProviderPerOp (𝓡 4) k)
    (ht : KernelTrivial prov) : ¬ KTNonSplit prov :=
  fun hns => hns (ht _ (charPairBrown_ktKernelRep prov))

/-! ## §4. G8-4 — `SpinImageIsTwo` is the recoverable face of `KTKernelCard`

On the algebraic sector predicate the decomposition `{KRTS, SIIT} → KTKernelCard` is an
equivalence modulo the Kummer representability bit: `KTKernelCard` recovers `SIIT` outright
(sector ⊆ kernel) and recovers `KRTS` given `KummerWitness.1`. The genuinely NEW geometric
content of the sector decomposition is `{KernelReducesToSpin, KummerWitness.1}`. -/

/-- **`KTKernelCard → SpinImageIsTwo`** (G8-4a): the sector lands in the kernel, so the kernel's
`{0, k₀}` cover restricts to the sector. `SpinImageIsTwo` is NOT independent content — it is the
sector face of the binder it helps discharge. -/
theorem spinImageIsTwo_of_KTKernelCard (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hcard : KTKernelCard prov) : SpinImageIsTwo prov :=
  fun x hx => hcard x (emptySigmaRepresentable_in_kernel prov x hx)

/-- **`KTKernelCard + k₀-representability → KernelReducesToSpin`** (G8-4b): a kernel class is `0`
(empty-representable) or `k₀` (representable by hypothesis). Together with G8-4a: the
decomposition adds over `KTKernelCard` exactly the Kummer representability content. -/
theorem kernelReducesToSpin_of_card_of_kummerRep (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hcard : KTKernelCard prov) (hrep : EmptySigmaRepresentable prov (ktKernelRep prov)) :
    KernelReducesToSpin prov := by
  intro x hx
  rcases hcard x hx with h0 | hk0
  · rw [h0]; exact emptySigmaRepresentable_zero prov
  · rw [hk0]; exact hrep

/-! ## §5. G8-5 — the sector-form seam: the algebraic predicate keys on H¹-triviality

`spinSector_of_isEmpty_surf` ties the geometric spin form to the algebraic `n = 0`; its converse
is absent BY NECESSITY. Kernel-encoding of the seam: rank-0 is forced by SUBSINGLETON `H¹(Σ)`
alone — surface emptiness is not what the basis equiv reads. A nonempty `Σ` with trivial `H¹`
(classically `S²`, e.g. a characteristic sphere dual to `w₁² ≠ 0`) would be `IsSpinSectorStr`
while geometrically non-spin. No in-tree witness exists (deferred tie, round-9 seed — see the
header G8-5 for the Lemma-5.3 overhang this creates). -/

/-- **The sector predicate is an H¹-triviality predicate** (G8-5): any bundled structure whose
characteristic surface has subsingleton `H¹(Σ;ℤ/2)` is rank-0 — emptiness of `Σ` is NOT what
`n = 0` reads. (`spinSector_of_isEmpty_surf` factors through this via `subsingleton_cohomology`;
the classical `Σ = S²` case shows the two predicates genuinely differ.) -/
theorem rank_zero_of_subsingleton_H1 {s : SingularManifold.{0} PUnit.{1} k I}
    (σ : CharPairStrBundled I s)
    (h : Subsingleton (Cohomology (TopCat.of σ.surf.M) 1)) : σ.n = 0 := by
  haveI := h
  haveI : Subsingleton (Fin σ.n → ZMod 2) := σ.basis.symm.injective.subsingleton
  by_contra hn
  obtain ⟨i⟩ : Nonempty (Fin σ.n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  exact absurd (congrFun (Subsingleton.elim (fun _ => (0 : ZMod 2)) (fun _ => (1 : ZMod 2))) i)
    (by decide)

/-- The seam surfaced at the sector predicate (G8-5): `IsSpinSectorStr` follows from H¹-triviality
of the carried surface — the class-level `emptySigmaRepresentable` therefore admits (classically)
geometrically-non-spin representatives with nonempty spherical characteristic surface. -/
theorem isSpinSectorStr_of_subsingleton_H1 (prov : CharPairWProviderPerOp (𝓡 4) k)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData)
    (h : Subsingleton (Cohomology (TopCat.of p.2.surf.M) 1)) : IsSpinSectorStr prov p :=
  rank_zero_of_subsingleton_H1 p.2 h

/-! ## §6. G8-6 — the 2-torsion fence, kernel-verified unbreachable

The attack: leak `spinSector_two_torsion` through in-tree ops into carrier-wide 2-torsion (the
no-go `dataBordism_two_torsion_of_revStr_trivial`'s collapse). Refutation: the carrier PROVABLY
contains a non-2-torsion class — `[ℝP⁴] + [ℝP⁴]` has `charPairBrown = 2 ≠ 0` in `ZMod 8`. Any
leak, by any mechanism, now contradicts a kernel theorem. -/

/-- **`[ℝP⁴]` is NOT 2-torsion** (G8-6a): `charPairBrown ([ℝP⁴] + [ℝP⁴]) = 1 + 1 = 2 ≠ 0` in
`ZMod 8`. The sector 2-torsion provably CANNOT extend to the whole carrier. -/
theorem ktRP4Class_not_two_torsion (prov : CharPairWProviderPerOp (𝓡 4) k) :
    ktRP4Class prov + ktRP4Class prov ≠ 0 := by
  intro h
  have h8 : charPairBrown prov (ktRP4Class prov + ktRP4Class prov) = 0 := by rw [h, map_zero]
  rw [map_add, charPairBrown_ktRP4Class] at h8
  exact absurd h8 (by decide)

/-- **The fence, absolute form** (G8-6b): the carrier is NOT globally 2-torsion — no combination
of the banked sector 2-torsion with in-tree ops (rank-0 sums, unit laws, anything) can produce
the no-go's carrier-wide collapse, because its conclusion is kernel-refuted here. -/
theorem no_carrierWide_two_torsion (prov : CharPairWProviderPerOp (𝓡 4) k) :
    ¬ ∀ x : T2DataBordismGrp (pinPlusCharPairData prov), x + x = 0 :=
  fun h => ktRP4Class_not_two_torsion prov (h _)

/-! ## §7. G8-7 — bridge-sharpness: the ÷32-upper bridge over-consumes (minor)

`kernelRep_two_torsion_of_KummerWitness` takes the full `KummerWitness` but uses only the
representability conjunct. The sharp form: -/

/-- **The sharp ÷32-upper bridge** (G8-7): `k₀ + k₀ = 0` needs ONLY `k₀`'s
empty-Σ-representability — NOT the non-split conjunct. Consumers of the ÷32-upper bound should
take this hypothesis (`KummerWitness.1`), keeping the open non-split bit out of their row. -/
theorem kernelRep_two_torsion_of_emptySigmaRep (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hrep : EmptySigmaRepresentable prov (ktKernelRep prov)) :
    ktKernelRep prov + ktKernelRep prov = 0 :=
  emptySigmaRepresentable_two_torsion prov _ hrep

end SKEFTHawking.PinPlusKTSectorGate
