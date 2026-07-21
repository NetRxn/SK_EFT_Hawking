/-
# Phase 5q.H close-out GATE ROUND 11 (fresh-context VACUITY ATTACK on the trace-leaf / geometric-Φ
# / hfwd / provider frontier)

Adversarial gate findings against everything new since round 10: the trace leaf rows
(`TraceWAdmLeaves` / `TraceMembraneLeaves` / `TraceRelFundLeaves` / `SurgeredEndDatum`), the
geometric Φ (`spinEmptyData` / `spinForgetPhi`), the `hfwd` field shape, the post-round-10 provider
shapes (`DisconnectedCylCoreND` / `CylinderWuResidual` / the FlankReduce twins / the Wu-leaf
desuspension atoms `CylV2Desuspend`/`CylV1Desuspend`), and the c56388ab addClosure docstring fix.

Verdict: **CONDITIONAL PASS with one ROUND-11 TIE and binding supply specs.**

## Per-item verdict table

* **Item 1 — the trace leaf rows** — **PASS** (certification, §4 record). (i) The KRS-consumer path
  `ambientSurgeryDatum_of_traceLeaves` produces a literal `AmbientSurgeryDatum`, so the round-10
  forcings apply BY TYPE to its output: `ambientSurgeryDatum_rank_ne` (no diagonal-cylinder reuse),
  `ambientSurgeryDatum_pos_rank` (off the rank-0 spin fibre — `hx0` at rank 0 is uninhabitable, so
  the empty/degenerate world is INERT for Consumer 1). (ii) The leaf-row pair CANNOT launder a
  Brown-violating bordance: `traceLeaves_brown_eq` forces `brown(q_σ) = brown(q_τ)` through the
  membrane kernel — kernel-recorded here as the row-level exclusion
  `isEmpty_traceMembraneLeaves_of_brown_ne` (§4). Consumer 2 (`dataBordant_of_traceLeaves`) is
  therefore Brown-graded: no degenerate row identifies classes across Brown grades. (iii)
  `TraceMembraneLeaves` has ZERO in-tree inhabitants off the empty world (its `real` field is the
  twice-gated `GeoRealizationTied`; the only in-tree tether is the diagonal cylinder, excluded for
  Consumer 1 by `hrank`); the empty world satisfies it but both consumers are inert there. (iv)
  `TraceRelFundLeaves`: the `gen` freedom is NIL over `ℤ/2` (a 1-dimensional `ℤ/2`-module has a
  UNIQUE iso to `ℤ/2`), so the datum's only content is {T1 certificate, class existence} as claimed;
  a no-interior carrier degenerately satisfies `hasClass` only at the price of `nondeg14/23` forcing
  the cohomology trivial — and a NONEMPTY `(𝓡 4).prod (𝓡∂ 1)`-charted carrier always has interior
  points (every nonempty open of the half-space model contains `t > 0` points), so that world is
  empty-only, hence inert. (v) `SurgeredEndDatum.bdry` is a definite Prop against the FIXED
  constructed atlas (the `letI` chain pins `carrierChartedSpace`); the adversary has no chart
  freedom, and an empty-target degenerate (`eM'` off `t.M = ∅`) must still PROVE
  `∂W = range ktSourceEnd` for that fixed atlas — no shape hole. RIDER (fatten-first, round-10 spec
  1, unchanged): per-`p` leaf-row constructions are non-vacuity demonstrators; the KRS unit remains
  the ∀-`p` supply.

* **Item 2 — the geometric Φ** — **PASS with the §3 collapse-blocker**. `spinEmptyData` cannot be
  degenerately consumed: any collapse (Subsingleton) of `DataBordismGrp (spinEmptyData prov)` makes
  the σ-presentation row UNINHABITABLE (`nontrivial_spinBordism_of_sig_row`: `hg` forces the group
  nontrivial), so degeneracy BLOCKS the dA/dC wiring rather than feeding it. The `Bor` subtype
  (tethered witness + `T2Space b.W`) only ever ADDS witnesses-side demands — no over-quotienting
  channel exists in the definition (the quotient is by exactly the subtype witnesses). The image of
  `Φ` is pinned to the geometric sector unconditionally
  (`spinForgetPhi_geometric` + `spinForgetPhi_surj_onto_geometric`), independent of source fineness.
  CIRCULARITY AUDIT (the round-10 owed item): `spinForgetPhi_g_eq_ktKernelRep_of_cyclic` and
  `ktNonSplit_of_spinForgetPhi_row` consume `{hg, hfwd, hcyc, h2}` — `KTNonSplit` is NOT a
  hypothesis of either (statement-shape certificate). BUT the load has moved into `hfwd` — see the
  ROUND-11 TIE below: the audit passes formally and bites materially on the `hfwd` supply.

* **Item 3 — hfwd's shape** — **THE ROUND-11 TIE (§1) + two degenerate models REFUTED (§2)**.
  (i) THE TIE: for the FIXED geometric `Φ = spinForgetPhi`, in the presence of the full
  presentation row `{hA, hB, hg, hdvd, hΦg, h2}`, the bare-∀ `hfwd` sits at EXACTLY `KTNonSplit`
  strength — `spinForgetPhi_hfwd_iff_ktNonSplit`. Backward is the fake: `R.generates` writes every
  spin class as `n • [g]`, so `Φ x = n • k₀`, and `KTNonSplit` + the ÷32-upper force `n` even,
  giving `32 ∣ σ(x)` with ZERO forgetful-map geometry (`spinForgetPhi_hfwd_of_ktNonSplit`). Fixing
  `Φ` to the geometric map does NOT close round 10's conclusion-fakeability: the presentation row
  itself collapses the geometric `Φ` to the arithmetic formula. Consequently the geometric-Φ dA
  leaf is inhabitable from the conclusion + presentation infra
  (`nonempty_dualSpinForwardDatum_geometric_of_ktNonSplit`) — a "dA discharged on the geometric Φ"
  claim is progress ONLY under the non-circularity audit (its `hfwd` proof consumes neither
  `KTNonSplit` nor the `k₀`-torsion-parity argument). (ii) The bare ∀ is nonetheless an ACCEPTABLE
  consumption shape — both flagged vacuity models are kernel-refuted: `Φ`-injectivity is
  UNREACHABLE (`spinForgetPhi_not_injective` — `2[g] ≠ 0` yet `Φ(2[g]) = 0`), and a σ trivialized
  on `ker Φ` is UNREACHABLE (`sig_not_vanishing_on_ker` — `σ(2[g]) = −32 ≠ 0` on a forced kernel
  element). `hfwd` makes at least one honest demand per presentation row. (iii) The honest supply
  spec: on the FORCED kernel (the doubles) `hfwd` is FREE from Rokhlin; its whole open content is
  the kernel characterization `ker Φ ⊆ doubles`, from which `hfwd` follows by banked arithmetic
  consuming NO `k₀` facts (`spinForgetPhi_hfwd_of_ker_sub_doubles`) — the sharpest audit-friendly
  construction target. The per-instance `Div32BoundingDatum` supply remains equally honest but is
  itself shape-fakeable (round 10 §3: the datum ⟺ `32 ∣ sigM`), so NO statement shape enforces
  non-circularity; the audit is proof-inspection, permanently.

* **Item 4 — the provider shapes** — **PASS** (certification). (i) The case split of
  `nonempty_provider_of_wuLeaf_and_disconnectedCoreND` is TOTAL (empty / nonempty-connected /
  nonempty-disconnected) and the σ-threading is `∀`-strong: `ofCylinderEngine` consumes `cylData`
  at exactly `{cyl, doubling, mapCyl}` (all at the σ-carrying source `s`) plus the DISCHARGED
  `addClosure` — the quantification is what the ops need, by type. (ii) `CylinderWuResidual` and
  the desuspension atoms are NEVER vacuous at consumption: their ∀-nd legs are applied to the
  terminal engine's own internal non-degeneracy terms (the elaborated `hRes _ _` of
  `cylinderWAdmPinned_of_wuResidual` certifies those terms exist for every closed connected `M`).
  (iii) `DisconnectedCylCoreND.D` is a genuine detection-carrying `RelFundClassDatum` (over `ℤ/2`
  the `gen` family has no gauge), and `nd14/nd23/hwu` are stated against ITS `μ` — no free-field
  laundering. (iv) The FlankReduce twins thread `PuncturedTopVanish` as a hypothesis and never
  claim it for disconnected `M` (where it is the registry-fenced FALSE leaf); the clopen-split
  D-route's folded `RestrictsToRelGenOn` demands detection against the CANONICAL `cylGen` on each
  piece — an empty piece merely reduces to the global demand, no shortcut.

* **Item 5 — the c56388ab docstring fix** — **VERIFIED**. Full elaborated signatures:
  `sumRelFundClass : {A B : TopCat} → {S₁ S₂} → SumRelFundClass A B S₁ S₂` (NO hypotheses — its own
  docstring's `[T1Space]` remark is stale in the SAFE direction) and
  `WAdmPinned.add : WAdmPinned b₁ → WAdmPinned b₂ → WAdmPinned (b₁.add b₂)` (unconditional;
  kernel-pure `{propext, Classical.choice, Quot.sound}`), so
  `ofCylinderEngineClosed : cylData → CharPairWProviderPerOp I k` discharges `addClosure`
  unconditionally. The gate-rider text of c56388ab is CORRECT.

* **Item 6 — the Wu-leaf desuspension atoms** (`PinPlusCylDataDischargeWuLeaf`, read from main) —
  **PASS**. (a) NOT self-discharging: `CylV2Desuspend`/`CylV1Desuspend` have NO free fields — both
  sides of each equation are canonical (the pinned `cylinderP14/23` over the canonical
  `cylinderDatum`, against `M`'s own `pd4Mid/pd4Lo`); the only quantifiers are the Prop-nd legs,
  inhabited at consumption by the engine's internal terms (same as (ii) above), so no vacuous-∀
  world is consumable. The PINNING IS REAL and kernel-recorded: `cylinderP14/23 :=
  LefschetzWuDatum.ofRelFund14/23 (cylinderDatum hcls) …` with `sqOp := relSq1/relSq2`,
  `cup := relCupH14/23`, `μ := (cylinderDatum hcls).mu` — certified by `cylinderP14_pinned` /
  `cylinderP23_pinned` (kernel-pure), and consumed DEFINITIONALLY by
  `CylV2Desuspend_of_pairing`'s `exact h b` (which type-checks only because `pairing`/
  `wuFunctional` unfold to exactly the pinned `relCupH23`/`relSq2`/`μ` forms — the F3 `zeroSq`
  exploit cannot reach these data). A pairing-trivial or rank-collapsed world is not choosable:
  `W = cylW M` is determined by `M`, and an `H²(M) = 0` instance satisfies the atom HONESTLY
  (`w₂ ∈ H² = 0`). (b) The σ.cert wiring is SOUND and does no hidden completeness work:
  `PinPlusCertK I s = ∀ [T2][Nonempty], wuW2 (pd4Mid s.M) (pd4Lo s.M) = 0` is a PER-OBJECT
  `w₂(M) = 0` certificate (a bundle field closed under empty/sum/rev), and the worker's correction
  is mathematically right — given the two desuspension identities the α-collapse ring-iso carries
  `wuW2(cyl)` to the base `wuW2(M)`, so the residual holds IFF `w₂(M) = 0`; consuming `σ.cert` is
  exactly the pin⁺ condition the carrier already carries, not a new ∀-completeness Prop.
  (c) BINDING SUPPLY SPEC: see item 5 of the frozen spec below.

## FROZEN ROUND-11 SPEC (binding on the inhabitation/consumption wave)
1. **hfwd (dA on the geometric Φ)**: conclusion-strength modulo the presentation row
   (`spinForgetPhi_hfwd_iff_ktNonSplit`). A discharge claim must pass the NON-CIRCULARITY AUDIT by
   proof inspection: its proof consumes neither `KTNonSplit` nor the parity-of-`n` argument through
   `k₀`-torsion. The audit-friendly target is the kernel characterization
   `∀ x, Φ x = 0 → ∃ w, x = w + w` (`ker Φ ⊆ doubles` — a pure spin-side statement), from which
   `hfwd` follows via `spinForgetPhi_hfwd_of_ker_sub_doubles` consuming no `k₀` facts.
2. **The bare-∀ shape of `hfwd` is acceptable for CONSUMPTION** (both vacuity models are
   kernel-refuted, §2); it is NOT acceptable as a construction-progress claim without item 1's
   audit.
3. **spinEmptyData**: any inhabitation wave must land `(R, g, hg)` BEFORE claiming dA/dC progress —
   a collapsed spin carrier blocks the row (`nontrivial_spinBordism_of_sig_row`); conversely no
   consumer fires from a collapsed carrier, so "the spin side might be tiny" is never a soundness
   risk, only a liveness one.
4. **Trace leaf rows**: the KRS unit stays the ∀-`p` supply (round-10 spec 1); per-`p`
   `ambientSurgeryDatum_of_traceLeaves` instances are demonstrators. A `TraceMembraneLeaves`
   construction must respect the Brown fence (it is IsEmpty across Brown grades, §4) — any claimed
   inhabitant with `brown(q_σ) ≠ brown(q_τ)` is a contradiction, not progress.
5. **Wu-leaf atoms**: supply `CylV2Desuspend`/`CylV1Desuspend` through the PAIRING form
   (`CylV2Desuspend_of_pairing`/`CylV1Desuspend_of_pairing`) — the suspension-Fubini identities
   against the CANONICAL `cylinderDatum.mu` — quantified per-`M` over the full instance row
   `[T2][CompactSpace][Nonempty][PreconnectedSpace][T1 (cylW M)]` (the provider row consumes them
   at EVERY connected closed carrier, not one `M`). The nd legs stay Prop-quantified — never
   fields. `σ.cert` is the only admissible `w₂(M) = 0` source (no per-`M` re-derivation).
6. **Provider rider (G10-1 updated)**: with `addClosure` closed (item 5) and the Wu leaf reduced
   (item 6), the provider-inhabitation dependency row is
   `{CylV2Desuspend, CylV1Desuspend, DisconnectedCylCoreND}` (via
   `nonempty_provider_of_desuspendLeaves_and_disconnectedCoreND`); every per-`prov` W-D statement
   still has zero live instances until all three land.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSpinForgetPhi
import SKEFTHawking.PinPlusTraceMembranePresented

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
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusTraceMembranePresented

namespace SKEFTHawking.PinPlusTraceLeafGate

variable {k : WithTop ℕ∞}

variable (prov : CharPairWProviderPerOp (𝓡 4) k)

/-! ## §1. G11-1 — THE ROUND-11 TIE: `hfwd` on the GEOMETRIC `Φ` is conclusion-strength modulo the
presentation row.

Round 10 located `DualSpinForwardDatum` at exactly `KTNonSplit` strength via the arithmetic fake
`Φ := (σ/16) • k₀` — a fake possible because the datum's `Φ` is a FREE field. The imminent
consumption wave fixes `Φ := spinForgetPhi` (the geometric map), and the dispatch question was
whether that closes the hole. IT DOES NOT: the presentation row itself (`R.generates`) collapses
the geometric `Φ` to the arithmetic formula `Φ x = n • k₀` with `n` read off `σ`, and `KTNonSplit`
+ the ÷32-upper force the parity that yields `32 ∣ σ(x)` — zero forgetful-map geometry. -/

/-- **THE ROUND-11 FAKE** (G11-1, the backward direction): for the FIXED geometric
`Φ = spinForgetPhi`, the KT "only if" field `hfwd` is derivable from the presentation row
`{hA, hB, hg, hdvd, hΦg, h2}` plus the CONCLUSION `KTNonSplit` — with zero forgetful-map geometry.
`R.generates` writes `x = n • [g]`, so `Φ x = n • k₀`; `Φ x = 0` with `n` odd would force `k₀ = 0`
(refuting `KTNonSplit`), and `n` even gives `σ(x) = −16n ∈ 32ℤ`. Round 10's conclusion-fakeability
survives the geometric-`Φ` fix; the non-circularity audit (frozen spec item 1) is permanent. -/
theorem spinForgetPhi_hfwd_of_ktNonSplit
    (R : SpinSigmaPresentation (spinEmptyData prov))
    (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) = ktKernelRep prov)
    (h2 : ktKernelRep prov + ktKernelRep prov = 0)
    (hns : KTNonSplit prov) :
    ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ R.sig x := by
  intro x hx
  obtain ⟨n, hn⟩ := R.generates hA hB g hg hdvd x
  have hΦx : n • ktKernelRep prov = 0 := by
    rw [← hΦg, ← map_zsmul, ← hn]
    exact hx
  rcases Int.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨-j, by rw [hn, map_zsmul, hg, smul_eq_mul, hj]; ring⟩
  · exfalso
    apply hns
    have hodd : n • ktKernelRep prov = ktKernelRep prov := by
      rw [hj, add_zsmul, one_zsmul, mul_comm, mul_zsmul,
        show (2 : ℤ) • ktKernelRep prov = 0 by rw [two_zsmul]; exact h2,
        smul_zero, zero_add]
    rw [← hodd]
    exact hΦx

/-- **THE ROUND-11 TIE, locating equivalence** (G11-1 headline): modulo the presentation row
`{hA, hB, hg, hdvd, hΦg, h2}`, the bare-∀ `hfwd` on the GEOMETRIC `Φ` sits at EXACTLY `KTNonSplit`
strength. Forward is sound (`hfwd` at `[g]` refutes the split world via `32 ∤ −16`); backward is
the round-11 fake. The leaf's discharge value lies entirely in the non-circularity of the
construction, which the statement shape cannot enforce — now proven AT the geometric `Φ`, not
merely at a free `Φ` field. -/
theorem spinForgetPhi_hfwd_iff_ktNonSplit
    (R : SpinSigmaPresentation (spinEmptyData prov))
    (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) = ktKernelRep prov)
    (h2 : ktKernelRep prov + ktKernelRep prov = 0) :
    (∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ R.sig x) ↔ KTNonSplit prov := by
  constructor
  · intro hfwd h0
    have hΦ0 : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) = 0 := by
      rw [hΦg]; exact h0
    have h32 := hfwd _ hΦ0
    rw [hg] at h32
    exact not_thirtytwo_dvd_neg_sixteen h32
  · exact spinForgetPhi_hfwd_of_ktNonSplit prov R hA hB g hg hdvd hΦg h2

/-- **The geometric-Φ dA leaf is inhabitable from the conclusion** (G11-1 corollary, the round-11
analogue of round 10's `dualSpinForwardDatum_of_ktNonSplit` — now on the GENUINE geometric `Φ`):
`{presentation row, hΦg, h2, KTNonSplit}` inhabit `DualSpinForwardDatum prov (spinEmptyData prov)`
with `Φ := spinForgetPhi` and zero new geometry. A "dA constructed on the geometric Φ" claim is
progress only under the frozen non-circularity audit. -/
theorem nonempty_dualSpinForwardDatum_geometric_of_ktNonSplit
    (R : SpinSigmaPresentation (spinEmptyData prov))
    (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) = ktKernelRep prov)
    (h2 : ktKernelRep prov + ktKernelRep prov = 0)
    (hns : KTNonSplit prov) :
    Nonempty (DualSpinForwardDatum prov (spinEmptyData prov)) :=
  nonempty_dualSpinForwardDatum_of_spinForgetPhi prov R g hg hΦg
    (spinForgetPhi_hfwd_of_ktNonSplit prov R hA hB g hg hdvd hΦg h2 hns)

/-! ## §2. G11-2 — the two flagged `hfwd` vacuity models are UNREACHABLE, and the honest reduction.

The dispatch flagged "`Φ` injective on the relevant sector makes `hfwd` vacuous — is that
reachable?" and (implicitly) the trivialized-σ model. Both are kernel-refuted by the FORCED kernel
elements: the 2-torsion of the geometric image (`spinForgetPhi_add_self`) puts every DOUBLE in
`ker Φ`, and the σ-row keeps `σ` nonzero there. On the forced kernel `hfwd` is FREE from Rokhlin;
its whole open content is the kernel characterization `ker Φ ⊆ doubles`. -/

/-- **Every double is a forced kernel element of the geometric `Φ`** (G11-2 engine): the image
2-torsion (`spinForgetPhi_add_self`, enhancement-tied through the rank-0 sector) kills `Φ(w + w)`
for EVERY spin class `w` — `ker (spinForgetPhi)` contains all doubles unconditionally. -/
theorem spinForgetPhi_double_mem_ker (w : DataBordismGrp (spinEmptyData prov)) :
    spinForgetPhi prov (w + w) = 0 := by
  rw [map_add]
  exact spinForgetPhi_add_self prov w

/-- The σ-value of the forced kernel element `2[g]` is `−32 ≠ 0`. -/
theorem sig_double_g (R : SpinSigmaPresentation (spinEmptyData prov))
    (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16) :
    R.sig (DataBordismGrp.mk (spinEmptyData prov) g + DataBordismGrp.mk (spinEmptyData prov) g)
      = -32 := by
  rw [map_add, hg]
  norm_num

/-- **The `Φ`-injectivity vacuity model is UNREACHABLE** (G11-2a): given any σ-row `(R, g, hg)`,
the geometric `Φ` is NOT injective — `Φ(2[g]) = 0 = Φ(0)` while `σ(2[g]) = −32` forces
`2[g] ≠ 0`. The flagged degenerate world in which `hfwd` is vacuous (`ker Φ = 0`) cannot coexist
with the presentation row the datum itself carries. -/
theorem spinForgetPhi_not_injective (R : SpinSigmaPresentation (spinEmptyData prov))
    (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16) :
    ¬ Function.Injective ⇑(spinForgetPhi prov) := by
  intro hinj
  have h0 : DataBordismGrp.mk (spinEmptyData prov) g + DataBordismGrp.mk (spinEmptyData prov) g
      = 0 :=
    hinj (by rw [map_zero]; exact spinForgetPhi_double_mem_ker prov _)
  have hs := sig_double_g prov R g hg
  rw [h0, map_zero] at hs
  norm_num at hs

/-- **The trivialized-σ vacuity model is UNREACHABLE** (G11-2b): no σ-row has `σ` vanishing on
`ker (spinForgetPhi)` — the forced kernel element `2[g]` carries `σ = −32 ≠ 0`. Together with
G11-2a: `hfwd`'s `∀` makes at least one honest, nontrivial demand per presentation row; the bare-∀
shape is not vacuously dischargeable. -/
theorem sig_not_vanishing_on_ker (R : SpinSigmaPresentation (spinEmptyData prov))
    (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16) :
    ¬ (∀ x, spinForgetPhi prov x = 0 → R.sig x = 0) := by
  intro hvan
  have h0 := hvan _ (spinForgetPhi_double_mem_ker prov (DataBordismGrp.mk (spinEmptyData prov) g))
  rw [sig_double_g prov R g hg] at h0
  norm_num at h0

/-- **The honest `hfwd` reduction** (G11-2c, the frozen supply target): on doubles `hfwd` is FREE
from Rokhlin (`σ(w + w) = 2σ(w) ∈ 32ℤ` from `16 ∣ σ(w)`), so the whole open content of `hfwd` is
the kernel characterization `ker Φ ⊆ doubles`. This derivation consumes NO `k₀` facts — no
`KTNonSplit`, no `k₀`-torsion — so a discharge routed through it passes the non-circularity audit
by construction. The audit obligation moves to the `hker` supply (a pure spin-side statement). -/
theorem spinForgetPhi_hfwd_of_ker_sub_doubles
    (R : SpinSigmaPresentation (spinEmptyData prov))
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (hker : ∀ x, spinForgetPhi prov x = 0 → ∃ w, x = w + w) :
    ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ R.sig x := by
  intro x hx
  obtain ⟨w, rfl⟩ := hker x hx
  obtain ⟨c, hc⟩ := hdvd w
  exact ⟨c, by rw [map_add, hc]; ring⟩

/-! ## §3. G11-3 — `spinEmptyData` collapse BLOCKS the σ-row (degeneracy is inert, never feeding).

The dispatch asked whether a degenerate `DataBordismGrp (spinEmptyData prov)` (empty `Mfd` type,
over-quotiented `Bor`) can make the dA/dC wiring consumable with a collapsed source. It cannot:
every consumer row carries `hg : σ[g] = −16`, and a collapsed (Subsingleton) group forces
`σ ≡ σ(0) = 0` on it. Degeneracy of the spin carrier is a LIVENESS risk (nothing lands), never a
soundness risk (nothing fires). -/

/-- **The σ-row forces the spin carrier nontrivial** (G11-3): `hg : σ[g] = −16` refutes
`[g] = 0`, so `DataBordismGrp (spinEmptyData prov)` is nontrivial in every world where the dA/dC
residual rows are inhabited. A collapsed `spinEmptyData` blocks consumption rather than enabling
it. -/
theorem nontrivial_spinBordism_of_sig_row (R : SpinSigmaPresentation (spinEmptyData prov))
    (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16) :
    Nontrivial (DataBordismGrp (spinEmptyData prov)) := by
  refine ⟨DataBordismGrp.mk (spinEmptyData prov) g, 0, fun h => ?_⟩
  have h0 := congrArg R.sig h
  rw [hg, map_zero] at h0
  norm_num at h0

/-! ## §4. G11-4 — the trace leaf rows preserve the anti-collapse Brown fence (item 1 record).

The KRS-supply consumers fire only through a literal `AmbientSurgeryDatum` (rank forcing
`ambientSurgeryDatum_rank_ne` + off-spin-fibre `ambientSurgeryDatum_pos_rank` apply BY TYPE), and
the two-leaf-row path carries the membrane kernel's Brown forcing (`traceLeaves_brown_eq`).
Kernel record: across Brown grades the membrane leaf row is EMPTY given any W-admissibility row —
no degenerate instantiation can launder a Brown-violating bordance through
`dataBordant_of_traceLeaves`. -/

section TraceRows

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
variable {s t : SingularManifold.{0} PUnit.{1} k I}

/-- **The Brown fence at the leaf-row level** (G11-4): if `brown(q_σ) ≠ brown(q_τ)` then the
membrane-presentation leaf row is uninhabitable alongside any W-admissibility leaf row on the same
bordism — the anti-collapse engine (`traceLeaves_brown_eq`, Taylor-leg + joint-Lagrangian membrane
kernel) reaches through the trace rows. Consumer 2 (`dataBordant_of_traceLeaves`) is therefore
Brown-graded: no degenerate row identifies classes across Brown grades. -/
theorem isEmpty_traceMembraneLeaves_of_brown_ne {b : Bordism (I.prod (𝓡∂ 1)) s t}
    {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (hne : σ.q.brown ≠ τ.q.brown) (wl : TraceWAdmLeaves b) :
    IsEmpty (TraceMembraneLeaves b σ τ) :=
  ⟨fun ml => hne (traceLeaves_brown_eq wl ml)⟩

end TraceRows

end SKEFTHawking.PinPlusTraceLeafGate
