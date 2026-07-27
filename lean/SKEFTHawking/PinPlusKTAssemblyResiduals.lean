/-
# Phase 5q.H — THE ASSEMBLY WIRING (block #193): the end-to-end conditional `kt_equiv_zmod16`

This module lands the ONE theorem that makes the phase's ENTIRE remaining geometric obligation
visible as a single conditional: `kt_equiv_zmod16_of_residuals`, whose CONCLUSION is the final
target shape (`Ω₄^{Pin⁺} ≃+ ZMod 16` on the faithful tethered carrier — the same conclusion type as
`PinPlusKTLeafGate.kt_equiv_zmod16_of_two_leaves`) and whose HYPOTHESIS LIST is exactly the CURRENT
residual atoms — the deepest already-gated reductions of each of the three leaves {KRS, dC, dA}.

The gate round 12 (`PinPlusResidualGate`) verified the assembly seams of
`kt_equiv_zmod16_of_two_leaves`: it consumes `{hKRS, dC, dA}` with no ungated seam. This module
composes the deepest suppliers of those three inputs into a single statement, over a CONCRETE
provider `residualProv` produced UNCONDITIONALLY by `nonempty_charPairWProviderPerOp` (the provider
is discharged, never hypothesized — round-7 gate `PASSED` the carrier; the provider inhabits with no
open residual).

## The three leaves, deepest current form (provenance per hypothesis in the theorem docstring)
* **KRS leaf** ← `kernelReducesToSpin_of_residualRow` (module `PinPlusTraceCapstoneResidualRow`,
  gate round 12 §4/§5): the ∀-`p` `KRSResidualRow` supply. Kept as the ∀-`p` row (round-12 spec 3),
  never weakened to a per-instance.
* **dC leaf** ← `nonempty_ktSpinPresentationDatum_of_row_of_collapse` (module
  `PinPlusKTSectorGeometricReduce`, round-9 freeze / gate round 12 §3): the collapse atom
  `RankZeroCollapsesToEmptySurf` = the per-structure bounding datum, plus the presentation row's
  freezes and the derived generator image.
* **dA leaf** ← the HONEST hfwd route `PinPlusTraceLeafGate.spinForgetPhi_hfwd_of_ker_sub_doubles`
  on the geometric `Φ = spinForgetPhi` (module `PinPlusKTKerPhiDoubles` /
  `PinPlusKTSpinPresentationRow`): the kernel characterization `KerPhiSubDoubles` (= `ker Φ ⊆
  doubles`), NOT `hfwd`/`KTNonSplit`-strength directly (round-11 fork
  `geometric-phi-does-not-close-hfwd-fakeability`). The dA datum is built through the genuine
  `spinForgetPhi` whose ambient is the tethered witness — NOT the free-`amb` `DualSpinConstruction`
  (round-12 fork `dual-spin-opened-construction-conclusion-fakeable`, spec 1).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`. Pure statement-level wiring — every discharge lemma exists.
-/
import Mathlib
import SKEFTHawking.PinPlusKTLeafGate
import SKEFTHawking.PinPlusKTSpinPresentationRow
import SKEFTHawking.PinPlusKTKerPhiDoubles
import SKEFTHawking.PinPlusKTSectorGeometricReduce
import SKEFTHawking.PinPlusTraceLeafGate
import SKEFTHawking.PinPlusTraceCapstoneResidualRow
import SKEFTHawking.PinPlusCylComponentClsIdentDisc

open scoped Manifold
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute
open SKEFTHawking.PinPlusKTLemma53Wave
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusKTKerPhiDoubles
open SKEFTHawking.PinPlusTraceLeafGate
open SKEFTHawking.PinPlusTraceCapstoneResidualRow
open SKEFTHawking.PinPlusKTSectorGeometricReduce
open SKEFTHawking.PinPlusKTLeafGate

namespace SKEFTHawking.PinPlusKTAssemblyResiduals

/-- **THE CANONICAL char-pair `W`-provider** — the UNCONDITIONAL provider, produced by
`nonempty_charPairWProviderPerOp` (round-7 gate `PASSED` the carrier; the provider inhabits with no
open residual). Fixing this concrete provider is how the assembly INSTANTIATES the provider rather
than hypothesizing it: the phase's remaining obligation is the residual atoms below, NOT the
provider. -/
noncomputable def residualProvK (k : WithTop ℕ∞) : CharPairWProviderPerOp (𝓡 4) k :=
  (SKEFTHawking.PinPlusCylComponentClsIdentDisc.nonempty_charPairWProviderPerOp
    (I := 𝓡 4) (k := k)).some

/-- **The `C⁰` specialisation of the canonical provider** — the historical name, unchanged in type.
`nonempty_charPairWProviderPerOp` was always `k`-generic (its binder is `{k : WithTop ℕ∞}`), so the
old `(k := 0)` instantiation was a *choice*, never a constraint; `residualProv = residualProvK 0`
definitionally. -/
noncomputable def residualProv : CharPairWProviderPerOp (𝓡 4) 0 := residualProvK 0

/-! ## §R. THE REGULARITY-GENERIC CORE — the assembly at ANY smoothness exponent `k`

The Phase 5q.H roadmap §2 leg 2 is a **hard constraint**: the carrier must live in the SMOOTH
category (`k ≥ 1`), because at `k = 0` Mathlib's `IsManifold I 0 M` binder is *free* (it proves
`contDiffGroupoid 0 I = continuousGroupoid H` and registers an unconditional instance for every
charted space — see `PinPlusRegularityFence`), so a `k = 0` carrier is the class of compact
boundaryless charted **topological** 4-manifolds, whose Pin⁺ bordism is `≅ ℤ/2 ⊕ ℤ/8`
(Kirby–Siebenmann; E₈), not `ℤ/16`.

There is **no generic `C⁰ → C¹` transport** — `PinPlusRegularitySeparation.no_generic_zero_to_one_
transport` refutes it — so the lift cannot be a transport theorem. It has to be a **re-declaration
at `k ≥ 1`**, and that is exactly what this section does: the whole assembly chain below
`kt_equiv_zmod16_of_two_leaves` turned out to be regularity-generic already (the provider
`nonempty_charPairWProviderPerOp`, the ℝP⁴ witness — `RP4Manifold.isManifold_rp4` is `Cω` and
`RP2EquatorialInclusion.contMDiff_embRP2` is `k`-generic — the grade, the sector/step/leaf gates, the
spin-forget `Φ`, the presentation row, the ker-Φ and collapse leaves). Only the KRS lane's
*constructed supplier* is `C⁰`-only (see the note on `kt_equiv_zmod16_of_residuals` below).

`kt_equiv_zmod16_of_residuals_ofKRS` is therefore the honest core: the same proof, over an arbitrary
regularity exponent, taking the KRS leaf in its regularity-neutral form `KernelReducesToSpin`. The
`k = 0` theorem of record becomes a corollary of it, unchanged in statement. -/

/-- **THE REGULARITY-GENERIC END-TO-END CONDITIONAL** — `Ω₄^{Pin⁺} ≃+ ZMod 16` on the faithful
tethered char-pair carrier at **any** smoothness exponent `k : WithTop ℕ∞`, in particular the smooth
`k = ⊤` the literature-grade Kirby–Taylor theorem is about.

Hypotheses are the residual atoms in their regularity-neutral form. Two leaves differ from the `k = 0`
theorem of record, both in the *weakening* direction:

* the KRS leaf is taken as `KernelReducesToSpin prov` — the Prop itself ("every Brown-kernel class is
  empty-Σ representable"), meaningful at every `k`. That is *weaker* than the `k = 0` `KRSResidualRow`
  supply (the row implies it via `kernelReducesToSpin_of_residualRow`);
* the pair `{hcyc : SpinImageCyclic, h2 : k₀ + k₀ = 0}` is replaced by the single generator-image atom
  `hΦg : Φ[g] = k₀` — the row is **seven** binders here against eight in `…_ofKRS`. This is the
  `k`-generic analogue of the `k = 0` `PinPlusKTBinderDischarge.kt_equiv_zmod16_of_residuals_phig`:
  both consumers of the pair need only `hΦg` (the dC leaf takes it directly; the dA leaf via
  `nonempty_dualSpinForwardDatum_of_spinForgetPhi`), and `{hcyc, h2}` entered the assembly ONLY as a
  way to derive it. That the direction is genuinely `{hcyc, h2} ⟹ hΦg` and not a lateral trade is
  kernel-checked immediately below, where `…_ofKRS` is re-derived as a corollary of this theorem.

Circularity audit (unchanged from the `k = 0` binder discharge): `hΦg` is UPSTREAM of `KTNonSplit`
(the dA datum built on it *yields* `KTNonSplit` via `ktNonSplit_of_dualSpinForwardDatum`) and asserts
nothing about `k₀ ≠ 0` or the ÷32 conclusion, so taking it as an atom consumes neither — the fence
`geometric-phi-does-not-close-hfwd-fakeability` is respected. -/
theorem kt_equiv_zmod16_of_residuals_ofKRS_phig {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hKRS : KernelReducesToSpin prov)
    (row : SpinPresentationRow prov)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf prov)
    (hker : KerPhiSubDoubles prov)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) row.g)
        = ktKernelRep prov) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData prov) ≃+ ZMod 16) := by
  -- dA's honest `hfwd` (KT Lemma 5.3 "only if"): FREE on doubles from Rokhlin, given `ker Φ ⊆ doubles`.
  have hfwd : ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ row.R.sig x :=
    spinForgetPhi_hfwd_of_ker_sub_doubles prov row.R row.hdvd hker
  -- dC leaf: the presentation row + the concrete collapse atom yield `KTSpinPresentationDatum`.
  obtain ⟨dC⟩ := nonempty_ktSpinPresentationDatum_of_row_of_collapse row hA hB hΦg hcol
  -- dA leaf: `hΦg` + the honest `hfwd` alone yield `DualSpinForwardDatum` — `{hcyc, h2}` entered the
  -- assembly ONLY through deriving `hΦg`, so at this grain they are gone from both leaves.
  obtain ⟨dA⟩ :=
    nonempty_dualSpinForwardDatum_of_spinForgetPhi prov row.R row.g row.hg hΦg hfwd
  -- the gate-certified assembly of record fires with the three real leaf inputs.
  exact kt_equiv_zmod16_of_two_leaves hKRS dC dA

/-- **The `{hcyc, h2}` form as a COROLLARY of the `hΦg` form** — statement unchanged from the theorem
of record; the proof now *factors through* `…_ofKRS_phig`, which makes the "`hΦg` is the weaker
hypothesis" claim a kernel fact rather than a docstring assertion: the derivation
`spinForgetPhi_g_eq_ktKernelRep_of_cyclic` is exactly the arrow `{hcyc, h2} ⟹ hΦg` (given the row and
`hker`), and it is called here. -/
theorem kt_equiv_zmod16_of_residuals_ofKRS {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hKRS : KernelReducesToSpin prov)
    (row : SpinPresentationRow prov)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf prov)
    (hker : KerPhiSubDoubles prov)
    (hcyc : SpinImageCyclic prov)
    (h2 : ktKernelRep prov + ktKernelRep prov = 0) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData prov) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_ofKRS_phig prov hKRS row hA hB hcol hker
    (spinForgetPhi_g_eq_ktKernelRep_of_cyclic prov row.R row.g row.hg
      (spinForgetPhi_hfwd_of_ker_sub_doubles prov row.R row.hdvd hker) hcyc h2)

/-- **THE REGULARITY-GENERIC CONDITIONAL, geometric-row form.** The KRS leaf is taken one level
deeper, at the `AmbientSurgeryDatum` row — the *ambient KT §5 surgery* atom (an isotropic class, its
surgered representative with rank dropped by 2, and a genuine tethered surgery-trace bordism between
them). This row is regularity-generic by construction: `AmbientSurgeryDatum prov p` demands a
`Bordism ((𝓡 4).prod (𝓡∂ 1)) p'.1 p.1`, whose `IsManifold … k` and `ContMDiff … k` fields carry the
regularity honestly. At `k = 0` those two fields are free and the datum is supplied in-tree by the
constructed handle-attachment capstone; at `k ≥ 1` they are the genuine smooth surgery trace, which
is the honest open geometric content of the smooth lift. -/
theorem kt_equiv_zmod16_of_residuals_ofAmbientRow {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k)
    (H : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
        charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
        0 < p.2.n → SKEFTHawking.PinPlusKTSurgeryTrace.AmbientSurgeryDatum prov p)
    (row : SpinPresentationRow prov)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf prov)
    (hker : KerPhiSubDoubles prov)
    (hcyc : SpinImageCyclic prov)
    (h2 : ktKernelRep prov + ktKernelRep prov = 0) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData prov) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_ofKRS prov
    (SKEFTHawking.PinPlusKTSurgeryTrace.kernelReducesToSpin_of_ambientDatumSupply H)
    row hA hB hcol hker hcyc h2

/-- **THE SMOOTH-CATEGORY HEADLINE** (`k = ⊤`) — the `C^∞`/`Cω` instantiation of the assembly on the
canonical provider `residualProvK ⊤`. This is the statement roadmap §2 leg 2 demands and the `k = 0`
theorem of record does **not** deliver: the carrier here is the class of compact boundaryless
`ChartedSpace (EuclideanSpace ℝ (Fin 4))` spaces whose `IsManifold (𝓡 4) ⊤` binder is a genuine
`C^∞`-atlas obligation, not the free `k = 0` one. Since `C¹ ⟹` a unique compatible smooth structure
(Whitney), `k = ⊤` is the flagship instantiation of the whole `k ≥ 1` family. -/
theorem kt_equiv_zmod16_of_residuals_smooth
    (H : ∀ p : StrMfd (pinPlusCharPairData (residualProvK ⊤)).toTangentialData,
        charPairBrown (residualProvK ⊤)
            (T2DataBordismGrp.mk (pinPlusCharPairData (residualProvK ⊤)) p) = 0 →
        0 < p.2.n → SKEFTHawking.PinPlusKTSurgeryTrace.AmbientSurgeryDatum (residualProvK ⊤) p)
    (row : SpinPresentationRow (residualProvK ⊤))
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf (residualProvK ⊤))
    (hker : KerPhiSubDoubles (residualProvK ⊤))
    (hcyc : SpinImageCyclic (residualProvK ⊤))
    (h2 : ktKernelRep (residualProvK ⊤) + ktKernelRep (residualProvK ⊤) = 0) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData (residualProvK ⊤)) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_ofAmbientRow (residualProvK ⊤) H row hA hB hcol hker hcyc h2

/-! ### §R.1 — the smooth carrier is NOT vacuous (unconditional). -/

/-- **THE SMOOTH CARRIER IS NON-DEGENERATE — UNCONDITIONALLY.** At `k = ⊤` the computed mod-8 grade
`charPairBrown` is already **surjective** onto `ZMod 8`, realized by the honestly-smooth (indeed
real-analytic) `ℝP⁴` witness `RP4CharPairWitness.rp4CharPairK ⊤`: `RP4Manifold.isManifold_rp4` is
`Cω`, `RP2Manifold.isManifold_rp2` is `Cω`, and `RP2EquatorialInclusion.contMDiff_embRP2` gives the
`ℝP² ↪ ℝP⁴` characteristic-surface embedding at every regularity. So the smooth-category
instantiation above is not an empty shell: its carrier carries at least the 8 grade classes, with a
genuine smooth generator. No hypothesis. -/
theorem charPairBrown_surjective_smooth :
    Function.Surjective (charPairBrown (residualProvK ⊤)) :=
  SKEFTHawking.RP4CharPairWitness.charPairBrown_surjective (residualProvK ⊤)

/-- **The smooth `ℝP⁴` class is nonzero in the smooth-category carrier** — unconditional
non-triviality of the `k = ⊤` group (grade `1 ≠ 0 ∈ ZMod 8`). -/
theorem rp4_ne_zero_smooth :
    T2DataBordismGrp.mk (pinPlusCharPairData (residualProvK ⊤))
        ⟨SKEFTHawking.RP4Manifold.rp4SM_k ⊤, SKEFTHawking.RP4CharPairWitness.rp4CharPairK ⊤⟩ ≠ 0 :=
  SKEFTHawking.RP4CharPairWitness.charPairBrown_rp4_ne_zero (residualProvK ⊤)

/-- **THE END-TO-END CONDITIONAL** — `Ω₄^{Pin⁺} ≃+ ZMod 16` on the faithful tethered carrier from the
CURRENT residual atoms. This is the single authoritative statement of everything that remains open in
Phase 5q.H: discharge these hypotheses and the Kirby–Taylor `Ω₄^{Pin⁺} ≅ ℤ/16` lands unconditionally.
Same conclusion type as `kt_equiv_zmod16_of_two_leaves`; the provider is instantiated, not assumed.

Residual atoms (deepest already-gated reduction of each leaf):
* `H` — **[KRS leaf | gate round 12 §4/§5 · `PinPlusTraceCapstoneResidualRow`]** the ∀-`p`
  `KRSResidualRow` supply (one residual row per non-spin Brown-0 representative of positive
  enhancement rank). Discharges `KernelReducesToSpin` via `kernelReducesToSpin_of_residualRow`;
  kept as the ∀-`p` row (round-12 spec 3), never a per-instance.
* `row` — **[presentation infra | `PinPlusKTSpinPresentationRow`]** the `Ω₄^{Spin} ≅ ℤ`
  σ-presentation row (`R`, Rokhlin `hdvd`, the K3 generator `g` with `b₂ = 22` / `hk3`).
* `hA`, `hB` — **[Freeze-A/B | `PinPlusKTSpinPresentationRow`]** the `n·H` handle-trade realization
  and the `S²×S²` bound on `row.R`.
* `hcol` — **[dC leaf | round-9 freeze / gate round 12 §3 · `PinPlusKTSectorGeometricReduce`]** the
  concrete collapse atom `RankZeroCollapsesToEmptySurf` (every rank-0 structure is one-step tethered
  bordant to an empty-Σ structure — the per-structure bounding datum), the honest dC overhang.
* `hker` — **[dA leaf | round-11 fork `geometric-phi-does-not-close-hfwd-fakeability` ·
  `PinPlusKTKerPhiDoubles`]** the kernel characterization `KerPhiSubDoubles` (`ker Φ ⊆ doubles`),
  the gate-blessed hfwd target — taken INSTEAD of `hfwd`/`KTNonSplit`-strength (which the fork
  showed are interderivable given the row).
* `hcyc` — **[dA leaf | `PinPlusKTKernelSpinRoute`]** `SpinImageCyclic` (the spin image is cyclic),
  the ÷32-upper input the derived generator image `hΦg` consumes.
* `h2` — **[dA leaf | KT Lemma 5.3 ÷32-upper]** `2·k₀ = 0` (the kernel representative is 2-torsion).

The dA datum is built through the genuine geometric `Φ = spinForgetPhi` (ambient = the tethered
witness), NOT the free-`amb` `DualSpinConstruction` (round-12 fork
`dual-spin-opened-construction-conclusion-fakeable`, spec 1). -/
theorem kt_equiv_zmod16_of_residuals
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf residualProv)
    (hker : KerPhiSubDoubles residualProv)
    (hcyc : SpinImageCyclic residualProv)
    (h2 : ktKernelRep residualProv + ktKernelRep residualProv = 0) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  -- KRS leaf: the ∀-`p` residual row supply discharges the deep KT §5 kernel-null binder;
  -- everything after it is the regularity-generic core (§R).
  kt_equiv_zmod16_of_residuals_ofKRS residualProv (kernelReducesToSpin_of_residualRow H)
    row hA hB hcol hker hcyc h2

/-! ## W-E — the Rokhlin-16 corollary (pure wiring from the equivalence). -/

/-- **W-E — THE ROKHLIN-16 COROLLARY** (`rokhlin_sixteen_of_residuals`): from the SAME residual row
that discharges the assembly, the faithful Pin⁺ bordism carrier has EXACTLY 16 elements —
`Nat.card Ω₄^{Pin⁺} = 16`. This is the project's recorded Rokhlin-16 target form (the order-16
statement, paralleling `PinPlusKTExtension.kt_card_eq_16`): the ABK/Brown grade takes 16 values,
so the signature of a closed spin representative is well-defined mod 16 — Rokhlin's theorem in Pin⁺
bordism form. PURE statement-level wiring from `kt_equiv_zmod16_of_residuals` (transport of
`Nat.card (ZMod 16) = 16` back across the additive equivalence); it introduces NO new residual atom.
The `= 16` (not `≤ 16`) is the non-vacuous form: it forces `Finite` on the carrier. -/
theorem rokhlin_sixteen_of_residuals
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf residualProv)
    (hker : KerPhiSubDoubles residualProv)
    (hcyc : SpinImageCyclic residualProv)
    (h2 : ktKernelRep residualProv + ktKernelRep residualProv = 0) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 := by
  obtain ⟨e⟩ := kt_equiv_zmod16_of_residuals H row hA hB hcol hker hcyc h2
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-- **W-E — THE ROKHLIN-16 COROLLARY IN THE SMOOTH CATEGORY** (`k = ⊤`). Same pure wiring as
`rokhlin_sixteen_of_residuals`, on the smooth-category carrier: the faithful Pin⁺ char-pair bordism
group of compact boundaryless `C^∞` 4-manifolds has EXACTLY 16 elements. This — not the `k = 0`
form — is the shape the literature's `Ω₄^{Pin⁺} ≅ ℤ/16` asserts (roadmap §2 leg 2). -/
theorem rokhlin_sixteen_of_residuals_smooth
    (H : ∀ p : StrMfd (pinPlusCharPairData (residualProvK ⊤)).toTangentialData,
        charPairBrown (residualProvK ⊤)
            (T2DataBordismGrp.mk (pinPlusCharPairData (residualProvK ⊤)) p) = 0 →
        0 < p.2.n → SKEFTHawking.PinPlusKTSurgeryTrace.AmbientSurgeryDatum (residualProvK ⊤) p)
    (row : SpinPresentationRow (residualProvK ⊤))
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf (residualProvK ⊤))
    (hker : KerPhiSubDoubles (residualProvK ⊤))
    (hcyc : SpinImageCyclic (residualProvK ⊤))
    (h2 : ktKernelRep (residualProvK ⊤) + ktKernelRep (residualProvK ⊤) = 0) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData (residualProvK ⊤))) = 16 := by
  obtain ⟨e⟩ := kt_equiv_zmod16_of_residuals_smooth H row hA hB hcol hker hcyc h2
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

end SKEFTHawking.PinPlusKTAssemblyResiduals
