/-
# Phase 5q.H close-out GATE ROUND 13 (fresh-context attack on the post-round-12 shape frontier)

Adversarial gate findings against the post-#196/#198/#199 frontier: the collar-bridge Prop
(`ClosedSeamAttachedCollarBridge`, #198 item d), the rank-0 collapse datum (`RankZeroCollapseDatum`,
#199), the Novikov "genuine-tower" carrier (`NovikovGeometricPairLESData`, #196 §4 — the fork-20
perimeter), the controlled-rep supplier (`CapstoneSeamTransferResidualCtrl`, #198 item c), and the
assembly-row chain (#193 → #197 → #199 → #195). Inherits and re-affirms ALL round-11/round-12
binding specs (see `PinPlusResidualGate` header).

Verdict: **CONDITIONAL PASS across the board, with THREE new kernel-encoded ties (§1, §2, §4) and
one PASS certificate (§3); no consumption seam requires a FIX before the assembly fires.**

## Per-item verdict table

* **Item 1 — `ClosedSeamAttachedCollarBridge` (#198 item d)** — **CONDITIONAL PASS with the
  round-13 support tie (§2).** The bridge Prop is kernel-LOCATED as a pure SUPPORT statement:
  `bridge S a ↔ a ∈ subspaceChains S ⊔ subspaceChains (sphere ∖ S)`
  (`closedSeamAttachedCollarBridge_iff_mem_sup`) — no class content, no detection, nothing pinning
  `cSeam`. Zero-collar inhabitation is exhibited (`closedSeamAttachedCollarBridge_of_freeSphere`:
  any free-sphere-supported `a` inhabits with `cSeam := 0`; `closedSeamAttachedCollarBridge_zero`).
  BUT the consumption site is guarded — NOT by the bridge's shape, by the SHARED-`cSeam` tie of
  `CapstoneSeamTransferSeam`, now kernel-precise: a `cSeam = 0` inhabitant forces the fundamental
  top face entirely OFF the attaching region (`capstoneSeamTransferSeam_topFace_unattached_of_
  cSeam_zero`) and `∂cHa` entirely into the free sphere (`…_boundary_freeSphere_of_cSeam_zero`).
  So a fake bridge cannot launder INTO the full seam structure at a genuine attachment. Spec 2
  below binds discharges.

* **Item 2 — `RankZeroCollapseDatum` + `rankZeroCollapsesToEmptySurf_of_datumSupply` (#199)** —
  **CONDITIONAL PASS with the locating iffs (§4).** Per-field audit: `hemp` is the collapse's
  defining demand; `hBor` is exactly the `IsT2DataBordant` packaging; `target_spinSector` is
  DERIVED from `hemp` (good — not a fakeable separate conjunct). The datum is the SKOLEMIZED
  per-object conclusion — `Nonempty (RankZeroCollapseDatum prov p) ↔` the collapse body at `p`
  (`nonempty_rankZeroCollapseDatum_iff`), and the ∀-supply is EXACTLY the collapse atom
  (`rankZeroCollapsesToEmptySurf_iff_datumSupply`). So #199's reduction is an honest RENAMING
  (naming + per-field inspectability, zero statement strength) — same standard as the round-9/10
  `AmbientSurgeryDatum` gating, whose forcing theorems (`pos_rank`, `rank_ne`) have their analogue
  here in `target_spinSector`. The #199 header's own "NOT a discharge" framing is CORRECT. The
  round-12 spec-4 debt ("the collapse atom owes the bounding datum") is ANSWERED BY NAMING, not by
  discharge — the genuine membrane is still owed, and the audit is data inspection (spec 3).

* **Item 3 — `NovikovGeometricPairLESData` + `ofGeometricPairLESData` (#196, the fork-20
  perimeter)** — **CONDITIONAL PASS with THE ROUND-13 TIE (§1, headline).** The carrier's field
  row does NOT force genuine tower data: the substrate rebuilds the carrier
  (`novikovGeometricPairLESDataOfRealPairLES` — `pairing := ½·pairing`, `hadjDot` DERIVED from
  `hadj` via the polarization factor), so carrier and substrate are inhabitation-equivalent
  (`nonempty_novikovGeometricPairLESData_iff_realPairLES`), and at a boundary block pair the
  carrier sits at EXACTLY σ-agreement strength: `Nonempty (Data (blockDiag A (−B))) ↔ σ(A) = σ(B)`
  (`nonempty_novikovGeometricPairLESData_iff_sig_eq`; diagonal exhibit `…_diag`; soundness half
  `isEmpty_…_of_sig_ne` — the carrier still genuinely FORCES σ-agreement). Composing the round-12
  Witt step with `ofLagrangian` and the reverse map populates every field — `hexact`, `hnondeg`,
  `hadjDot` included — from a bare Lagrangian, ZERO bordism geometry. `hadjDot` did not close the
  fork-20 perimeter; it moved it. Consumption of #201 (in flight) binds to spec 1 below.

* **Item 4 — `CapstoneSeamTransferResidualCtrl` + `.toHasClass` (#198 item c)** — **PASS (§3).**
  Field-by-field: `z`/`hz`/`hdetAB` identical shapes; `seam` over `Sdᵘ diskDetectChain`; the
  `hdetHa` supply for `toHasClass` is the PROVEN transported detection
  (`diskDetectChain_iterate_hdet`), not a weakened hypothesis. The `μ = 0` fibre is definitionally
  interchangeable with the banked residual in BOTH directions (`ctrlZeroOfResidual` /
  `residualOfCtrlZero`), and both `toHasClass` outputs share one type — a genuine variant
  constructor, no weakened field, no new residual.

* **Item 5 — the assembly-row chain** — **PASS (by proof inspection; trace recorded here).**
  `kt_equiv_zmod16_of_residuals` consumes {`H`→`hKRS` via `kernelReducesToSpin_of_residualRow`;
  `row.hdvd`+`hker`→`hfwd` via `spinForgetPhi_hfwd_of_ker_sub_doubles`; `hfwd`+`hcyc`+`h2`→`hΦg`
  via `spinForgetPhi_g_eq_ktKernelRep_of_cyclic` (consumes the banked `zsmul_of_two_torsion` +
  `not_thirtytwo_dvd_neg_sixteen`; NO `KTNonSplit`, NO ÷32 conclusion); dC ←
  `nonempty_ktSpinPresentationDatum_of_row_of_collapse` (SectorIsGeometric derived from `hcol` in
  place); dA ← `nonempty_dualSpinForwardDatum_of_row` (Φ := the genuine `spinForgetPhi`, ambient
  pinned — NOT the free-`amb` `DualSpinConstruction`, fork-19 respected); closes via the
  round-12-certified `kt_equiv_zmod16_of_two_leaves`}. `_phig` (#197) replaces `{hcyc, h2}` by
  `hΦg` — verified UPSTREAM: `ktKernelRep := 8 • [ℝP⁴]` is pure definition, `hΦg` is an equation
  between two constructions carrying no `k₀ ≠ 0` bit; `h2_of_generatorImage` routes through
  `spinForgetPhi_add_self` = the structure-TIED `emptySigmaRepresentable_two_torsion`
  (rank-0-sector `revStr`-fixity), NOT universal `revStr`-triviality — the no-go
  `dataBordism_two_torsion_of_revStr_trivial` is NOT reproduced. `_collapseDatum` (#199) consumes
  exactly `_phig` + `rankZeroCollapsesToEmptySurf_of_datumSupply`. `_terminal_atoms`/`_k3_element`
  (#195) consume exactly `spinPresentationRow_of_atoms`/`realizesSphereProducts_of_cobordism_and_
  base`/the banked `K3RealizingElement.presentationRow`. No ungated Prop enters at any seam; the
  round-12 item-8 pattern holds through all four variants.

* **Item 6 — `exact_seam_split_of_attachedBridge`'s hypothesis** — **PASS, load-bearing
  kernel-PROVED (§2).** The wiring's conclusion IS the bridge at `w`
  (`exact_seam_split_conclusion_iff_bridge`, definitional) — so the theorem is precisely "the
  bridge is closed under adding free-sphere chains". The hypothesis is NOT decorative: an instance
  of `hsplit`+`hvOut` with the conclusion FALSE is exhibited
  (`exact_seam_split_hypothesis_load_bearing`, via the constant-simplex non-membership crux
  `single_constSimplex_notMem_subspaceChains` at the disk center).

## FROZEN ROUND-13 SPEC (binding on the discharge/consumption waves; adds to rounds 11–12)
1. **Novikov tower lane (the fork-20 perimeter)**: a `NovikovGeometricPairLESData` population is
   fork-compliant progress ONLY if `rest2`/`delta`/`pairing` are the ⊗ℝ base-changes of the
   genuine integral tower maps (`pullbackCochainInt`-restriction / `deltaRelHInt` /
   `relKroneckerHInt`) of an ACTUAL relative cycle `Z` on an actual bordism carrier — checked by
   DATA INSPECTION; the field row (`hadjDot` included) sits at σ-agreement strength
   (`nonempty_novikovGeometricPairLESData_iff_sig_eq`) and can never enforce it. A population
   whose `H3rel` is a quotient of the boundary coordinate space (the `ofLagrangian` shape) is
   ZERO progress by construction.
2. **Collar-bridge lane**: a discharge of `ClosedSeamAttachedCollarBridge` must exhibit `cSeam`
   by DATA (the collar retraction's actual chain on `↥S`); the Prop is pure support
   (`closedSeamAttachedCollarBridge_iff_mem_sup`) and zero-collar inhabitants exist
   (`…_of_freeSphere`). CONSUMPTION must keep the single shared `cSeam` field of
   `CapstoneSeamTransferSeam` — never restructure into independent cylinder-side and disk-side
   bridges (the shared-`cSeam` tie is the ONLY shape-level anti-laundering guard:
   `capstoneSeamTransferSeam_topFace_unattached_of_cSeam_zero`).
3. **dC collapse lane**: the ∀-datum supply IS the collapse atom
   (`rankZeroCollapsesToEmptySurf_iff_datumSupply`); a datum-supply discharge is audited by DATA
   inspection of `b` (the genuine membrane-kill trace, `emptySourceRealizationTied`-realized) —
   the round-9 freeze / round-12 spec 4 obligation transfers verbatim to the datum.
4. **Assembly lane**: consume the chain only through the four audited variants (`_of_residuals` /
   `_phig` / `_collapseDatum` / `_terminal_atoms`+`_k3_element`); `hΦg` stays a bare-equation atom
   (upstream of `KTNonSplit`) and `h2` must only ever be derived via the structure-TIED
   `emptySigmaRepresentable_two_torsion`, never a universal `revStr`-triviality argument.

## Registry-worthy fork candidate (for the lead; encode-on-settle)
* `novikov-geometric-tower-carrier-conclusion-fakeable` — false_statement: "the
  `NovikovGeometricPairLESData` field row (`hexact`+`hnondeg`+`hadjDot`+`hbdnd`) is a
  stronger-than-conclusion carrier whose inhabitation certifies genuine bounding-`W` tower
  progress" — backings: `novikovGeometricPairLESDataOfRealPairLES`,
  `nonempty_novikovGeometricPairLESData_iff_realPairLES`,
  `nonempty_novikovGeometricPairLESData_iff_sig_eq`, `nonempty_novikovGeometricPairLESData_diag`.
  (Extends fork 20 from the substrate to the #196 carrier — the exact perimeter #201 consumes.)

No fork proposal for the bridge or the collapse datum: their fakeability is at the SHAPE level
(support-only / conclusion-strength) and their consumption sites carry the guard; specs 2–3
suffice. The Ctrl variant and the assembly chain are clean passes.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`, `lean_verify`-confirmed per declaration);
no `sorry`, no new project axiom, no `native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusResidualGate
import SKEFTHawking.PinPlusKTNovikovTowerInstantiate
import SKEFTHawking.PinPlusTraceSeamResidualNarrow
import SKEFTHawking.PinPlusKTCollapseDischarge

open scoped Manifold
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTSpinSigmaNovikovRealSubstrate
open SKEFTHawking.PinPlusKTNovikovTowerInstantiate
open SKEFTHawking.SingularRelativeRealBaseChange
open SKEFTHawking.PinPlusResidualGate
open SKEFTHawking.PinPlusKTSectorGeometricReduce
open SKEFTHawking.PinPlusKTCollapseDischarge

namespace SKEFTHawking.PinPlusRoundThirteenGate

variable {k : WithTop ℕ∞}

/-! ## §1. G13-1 — the Novikov "genuine-tower" carrier is conclusion-fakeable: the field row of
`NovikovGeometricPairLESData` sits at EXACTLY substrate (= σ-agreement = `hbord`) strength. -/

/-- **THE ROUND-13 REVERSE MAP** — the substrate rebuilds the "genuine-tower" carrier: from any
`NovikovRealPairLES Bd` (in particular a SYNTHETIC one — `ofLagrangian`'s quotient fabrication) and
the symmetry of `Bd`, all nine fields of `NovikovGeometricPairLESData Bd` are inhabited with ZERO
new geometry: the same `H2W`/`H3rel`/`rest2`/`delta`, `pairing := ½·pairing` (un-absorbing the
polarization factor), and `hadjDot` DERIVED from the substrate's `hadj` via
`polarBilin_toQuadraticMap'_isSymm`. Composed with `ofLagrangian`, the carrier is populated from a
bare half-dimensional isotropic subspace — no bordism `W`, no pair-LES tower. -/
noncomputable def novikovGeometricPairLESDataOfRealPairLES {n : ℕ}
    {Bd : Matrix (Fin n) (Fin n) ℤ} (hsymm : Bd.IsSymm) (N : NovikovRealPairLES Bd) :
    NovikovGeometricPairLESData Bd where
  H2W := N.H2W
  H3rel := N.H3rel
  rest2 := N.rest2
  delta := N.delta
  pairing := (2⁻¹ : ℝ) • N.pairing
  hexact := N.hexact
  hnondeg := fun x hx => N.hnondeg x fun a => by
    have h := hx a
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  hbdnd := N.hbdnd
  hsymm := hsymm
  hadjDot := fun a v => by
    have h := N.hadj a v
    rw [polarBilin_toQuadraticMap'_isSymm _ (hsymm.map _)] at h
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, ← h]
    ring

/-- **The carrier and the substrate are inhabitation-EQUIVALENT** (for symmetric `Bd`): forward is
the banked honest reduction `ofGeometricPairLESData`; backward is the round-13 reverse map. The
carrier's field row therefore adds ZERO statement strength over `NovikovRealPairLES`. -/
theorem nonempty_novikovGeometricPairLESData_iff_realPairLES {n : ℕ}
    {Bd : Matrix (Fin n) (Fin n) ℤ} (hsymm : Bd.IsSymm) :
    Nonempty (NovikovGeometricPairLESData Bd) ↔ Nonempty (NovikovRealPairLES Bd) :=
  ⟨fun ⟨D⟩ => ⟨NovikovRealPairLES.ofGeometricPairLESData D⟩,
   fun ⟨N⟩ => ⟨novikovGeometricPairLESDataOfRealPairLES hsymm N⟩⟩

/-- **THE ROUND-13 σ-TIE (headline)** — at a boundary block pair the "genuine-tower" carrier is
inhabited EXACTLY when the signatures agree: `Nonempty (NovikovGeometricPairLESData
(blockDiag A (−B))) ↔ σ(A) = σ(B)`. Forward is the banked `latticeSig_eq` consumer (#196 §5);
backward is the round-12 Witt step (`exists_lagrangian_of_latticeSig_eq_zero`) feeding the synthetic
`ofLagrangian` substrate through the round-13 reverse map — ZERO bordism geometry. Consequence: the
`hadjDot`/`hexact`/`hnondeg` field row does NOT force genuine tower data; a "carrier populated"
claim is fork-20-compliant progress ONLY if `rest2`/`delta`/`pairing` are the ⊗ℝ base-changes of an
actual bounding `W`'s pair-LES maps, checked by DATA INSPECTION — the statement shape can never
enforce it (round-13 spec 1). -/
theorem nonempty_novikovGeometricPairLESData_iff_sig_eq {r s : ℕ}
    (A : Matrix (Fin r) (Fin r) ℤ) (B : Matrix (Fin s) (Fin s) ℤ)
    (hA : IsEvenUnimodular A) (hB : IsEvenUnimodular B) :
    Nonempty (NovikovGeometricPairLESData (blockDiag A (-B)))
      ↔ latticeSig A = latticeSig B := by
  constructor
  · rintro ⟨D⟩
    exact NovikovGeometricPairLESData.latticeSig_eq A B hA hB D
  · intro hsig
    have hnegB := isEvenUnimodular_neg _ hB
    have hbd_eu := isEvenUnimodular_blockDiag A (-B) hA hnegB
    have hsymmZ : (blockDiag A (-B)).IsSymm := hbd_eu.1
    have hsig0 : latticeSig (blockDiag A (-B)) = 0 := by
      rw [latticeSig_blockDiag A (-B) hA hnegB, latticeSig_neg]
      omega
    obtain ⟨L, hdim, hiso⟩ :=
      exists_lagrangian_of_latticeSig_eq_zero _ hbd_eu.radical_eq_bot hsig0
    exact ⟨novikovGeometricPairLESDataOfRealPairLES hsymmZ
      (NovikovRealPairLES.ofLagrangian _ hbd_eu.radical_eq_bot L hdim hiso)⟩

/-- **The soundness half survives** (the PASS component of the verdict): the carrier still FORCES
σ-agreement — it is empty across σ-grades, so no degenerate population can launder a σ-jump. The
carrier is a genuine constraint; it is just not MORE than the σ-agreement conclusion. -/
theorem isEmpty_novikovGeometricPairLESData_of_sig_ne {r s : ℕ}
    (A : Matrix (Fin r) (Fin r) ℤ) (B : Matrix (Fin s) (Fin s) ℤ)
    (hA : IsEvenUnimodular A) (hB : IsEvenUnimodular B)
    (hne : latticeSig A ≠ latticeSig B) :
    IsEmpty (NovikovGeometricPairLESData (blockDiag A (-B))) :=
  ⟨fun D => hne (NovikovGeometricPairLESData.latticeSig_eq A B hA hB D)⟩

/-- **The diagonal degenerate model reaches the carrier** — at any matrix-equal pair the
"genuine-tower" carrier is inhabited with zero geometry (the round-12 diagonal exhibit, lifted
through the reverse map). The sharpest per-pair form of the fake. -/
theorem nonempty_novikovGeometricPairLESData_diag {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (heu : IsEvenUnimodular A) :
    Nonempty (NovikovGeometricPairLESData (blockDiag A (-A))) :=
  (nonempty_novikovGeometricPairLESData_iff_sig_eq A A heu heu).mpr rfl

/-! ## §2. G13-2 — the collar bridge is a PURE SUPPORT Prop: located as a submodule-sum
membership; zero-collar inhabitation exhibits; and the hypothesis of the conditional wiring is
kernel-provably load-bearing. -/

section CollarBridge

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.SingularExcision
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.PinPlusTraceCapstoneSeamSplit
open SKEFTHawking.PinPlusTraceSeamResidualNarrow
open SKEFTHawking.DiskChartGeneric (D5)
open Opposite

/-- **The generic support-sum locating lemma** — "pushforward-from-`↥S` plus a `T`-supported
remainder" is EXACTLY membership in the submodule sum `subspaceChains S ⊔ subspaceChains T`. The
shape of `ClosedSeamAttachedCollarBridge` (and of `exact_seam_split_of_attachedBridge`'s conclusion)
is a pure SUPPORT statement — no class content, no detection, nothing pinning `cSeam`. -/
theorem exists_mapChain_add_iff_mem_sup {X : TopCat} (S T : Set ↑X) (n : ℕ)
    (a : SingularChain X n) :
    (∃ (cS : SingularChain (sub S) n) (corr : SingularChain X n),
        a = mapChain (ambIncl S) n cS + corr ∧ corr ∈ subspaceChains T n)
      ↔ a ∈ subspaceChains S n ⊔ subspaceChains T n := by
  constructor
  · rintro ⟨cS, corr, rfl, hcorr⟩
    exact Submodule.add_mem_sup
      ((mem_subspaceChains_iff_exists_mapChain_ambIncl S n _).mpr ⟨cS, rfl⟩) hcorr
  · intro h
    obtain ⟨y, hy, z, hz, hsum⟩ := Submodule.mem_sup.mp h
    obtain ⟨cS, hcS⟩ := (mem_subspaceChains_iff_exists_mapChain_ambIncl S n y).mp hy
    exact ⟨cS, z, by rw [hcS, hsum], hz⟩

/-- **THE BRIDGE, LOCATED** (G13-2a): `ClosedSeamAttachedCollarBridge S a` is EXACTLY the
submodule-sum membership `a ∈ subspaceChains S ⊔ subspaceChains (sphere ∖ S)`. The Prop carries
support information ONLY — nothing in its shape demands the collar retraction, a nonzero `cSeam`,
or any class/detection content. Its anti-fake guard therefore lives entirely at the CONSUMPTION
site (the shared-`cSeam` tie of `CapstoneSeamTransferSeam`, §3). -/
theorem closedSeamAttachedCollarBridge_iff_mem_sup (S : Set D5)
    (a : SingularChain (TopCat.of D5) (3 + 1)) :
    ClosedSeamAttachedCollarBridge S a ↔
      a ∈ subspaceChains (X := TopCat.of D5) S (3 + 1)
          ⊔ subspaceChains (X := TopCat.of D5)
              ({v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S) (3 + 1) := by
  unfold ClosedSeamAttachedCollarBridge
  exact exists_mapChain_add_iff_mem_sup S _ (3 + 1) a

/-- **The zero-collar degenerate inhabitation** (G13-2b): any free-sphere-supported chain inhabits
the bridge with `cSeam := 0` — zero collar geometry, zero seam content. The bridge Prop per se
cannot certify collar-retraction progress. -/
theorem closedSeamAttachedCollarBridge_of_freeSphere {S : Set D5}
    {a : SingularChain (TopCat.of D5) (3 + 1)}
    (ha : a ∈ subspaceChains (X := TopCat.of D5)
        ({v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S) (3 + 1)) :
    ClosedSeamAttachedCollarBridge S a :=
  ⟨0, a, by rw [map_zero, zero_add], ha⟩

/-- The bridge is inhabited at the zero chain, for every `S` — the degenerate floor. -/
theorem closedSeamAttachedCollarBridge_zero (S : Set D5) :
    ClosedSeamAttachedCollarBridge S 0 :=
  closedSeamAttachedCollarBridge_of_freeSphere (Submodule.zero_mem _)

/-- **The constant-simplex non-membership crux** — a constant simplex at a point OUTSIDE `A` is not
an `A`-supported chain. The engine of the load-bearing exhibit: evaluate the realization (the
`toSSetObjEquiv` naturality of `simplexIncl`) at any point of the (nonempty) standard simplex. -/
theorem single_constSimplex_notMem_subspaceChains {X : TopCat} {A : Set ↑X} {x : ↑X}
    (hx : x ∉ A) (n : ℕ) :
    Finsupp.single (constSimplex x n) (1 : ZMod 2) ∉ subspaceChains A n := by
  rintro ⟨d, hd⟩
  have hrange : constSimplex x n ∈ Set.range (simplexIncl A n) := by
    by_contra hr
    have h0 : chainIncl A n d (constSimplex x n) = 0 := by
      rw [chainIncl, Finsupp.lmapDomain_apply]
      exact Finsupp.mapDomain_notin_range d _ hr
    rw [hd, Finsupp.single_eq_same] at h0
    exact one_ne_zero h0
  obtain ⟨τ, hτ⟩ := hrange
  have heval := congrArg (X.toSSetObjEquiv (op (SimplexCategory.mk n))) hτ
  rw [toSSetObjEquiv_simplexIncl,
    show X.toSSetObjEquiv (op (SimplexCategory.mk n)) (constSimplex x n)
      = ContinuousMap.const _ x from Equiv.apply_symm_apply _ _] at heval
  obtain ⟨pt⟩ : Nonempty ↑(stdSimplex ℝ (Fin (n + 1))) := inferInstance
  have hval := ContinuousMap.congr_fun heval pt
  rw [ContinuousMap.comp_apply, ContinuousMap.const_apply] at hval
  exact hx (hval ▸ ((sub A).toSSetObjEquiv (op (SimplexCategory.mk n)) τ pt).2)

/-- The center of the disk `D⁵`. -/
noncomputable def diskCenter : D5 :=
  ⟨0, Metric.mem_closedBall_self (by norm_num)⟩

theorem diskCenter_notMem_sphere :
    diskCenter ∉ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} := by
  simp [diskCenter]

/-- **The bridge is NOT universally inhabited** (G13-2c): at `S = ∅` the bridge demands full
sphere-support, and the interior constant simplex at the disk center refutes it. -/
theorem not_closedSeamAttachedCollarBridge_center :
    ¬ ClosedSeamAttachedCollarBridge ∅
        (Finsupp.single (constSimplex diskCenter (3 + 1)) (1 : ZMod 2)) := by
  intro h
  rw [closedSeamAttachedCollarBridge_iff_mem_sup] at h
  have hle : subspaceChains (X := TopCat.of D5) (∅ : Set D5) (3 + 1)
        ⊔ subspaceChains (X := TopCat.of D5)
            ({v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} \ ∅) (3 + 1)
      ≤ subspaceChains (X := TopCat.of D5)
          {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1) :=
    sup_le (subspaceChains_mono (Set.empty_subset _) (3 + 1))
      (subspaceChains_mono Set.diff_subset (3 + 1))
  exact single_constSimplex_notMem_subspaceChains diskCenter_notMem_sphere (3 + 1) (hle h)

/-- **The conditional wiring's conclusion IS the bridge at `w`** — definitionally. The theorem
`exact_seam_split_of_attachedBridge` is thus, in locating form, "the bridge Prop is closed under
adding free-sphere chains": `bridge(a) → bridge(a + vOut)`. Honest wiring; nothing extra. -/
theorem exact_seam_split_conclusion_iff_bridge (S : Set D5)
    (w : SingularChain (TopCat.of D5) (3 + 1)) :
    (∃ (cSeam : SingularChain (sub (X := TopCat.of D5) S) (3 + 1))
        (vOut' : SingularChain (TopCat.of D5) (3 + 1)),
      w = mapChain (ambIncl (X := TopCat.of D5) S) (3 + 1) cSeam + vOut'
        ∧ vOut' ∈ subspaceChains (X := TopCat.of D5)
            ({v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S) (3 + 1))
      ↔ ClosedSeamAttachedCollarBridge S w :=
  Iff.rfl

/-- **THE HYPOTHESIS IS LOAD-BEARING** (item 6, kernel-encoded): there is an instance of
`exact_seam_split_of_attachedBridge`'s OTHER hypotheses (`hsplit` + `hvOut`) at which its conclusion
(= the bridge at `w`, by `exact_seam_split_conclusion_iff_bridge`) FAILS — so the conclusion is NOT
derivable from the split (b) alone, and the collar-bridge hypothesis is genuinely consumed, never
decorative. (Witness: `S = ∅`, `w = a =` the interior constant simplex, `vOut = 0`.) -/
theorem exact_seam_split_hypothesis_load_bearing :
    ∃ (S : Set D5) (w a vOut : SingularChain (TopCat.of D5) (3 + 1)),
      w = a + vOut
      ∧ vOut ∈ subspaceChains (X := TopCat.of D5)
          ({v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S) (3 + 1)
      ∧ ¬ ClosedSeamAttachedCollarBridge S w := by
  refine ⟨∅, Finsupp.single (constSimplex diskCenter (3 + 1)) (1 : ZMod 2),
    Finsupp.single (constSimplex diskCenter (3 + 1)) (1 : ZMod 2), 0, ?_,
    Submodule.zero_mem _, not_closedSeamAttachedCollarBridge_center⟩
  exact (add_zero _).symm

end CollarBridge

/-! ## §3. G13-2d/G13-4 — the consumption-site guard (the shared-`cSeam` tie, kernel-precise) and
the controlled-rep supplier interchange at the `μ = 0` fibre. -/

section SeamStructure

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCoverGlue
open SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk
open SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
open SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply
open SKEFTHawking.PinPlusTraceSeamResidualNarrow
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.PinPlusTraceDiskCorePair

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE SHARED-`cSeam` TIE, kernel-precise (cylinder side)**: a `CapstoneSeamTransferSeam`
inhabitant with the DEGENERATE seam `cSeam = 0` forces the fundamental top face `z@⊤` to be
supported entirely OFF the attaching region (`M × {⊤} ∖ range φ`). A zero-collar fake laundered
through the bridge into `hsplitHa` cannot inhabit the full seam structure unless the fundamental
class's top face avoids the attachment altogether — the anti-laundering demand the bridge Prop
itself lacks lives HERE, in the single `cSeam` field shared by `hsplit` and `hsplitHa`. -/
theorem capstoneSeamTransferSeam_topFace_unattached_of_cSeam_zero
    {z : cycles (TopCat.of s.M) (2 + 2)}
    {cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)}
    (R : CapstoneSeamTransferSeam s S hS φ hφ hφinj z cHa) (h0 : R.cSeam = 0) :
    mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (z : SingularChain (TopCat.of s.M) (3 + 1))
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1) := by
  have h := R.hsplit
  rw [h0, map_zero, zero_add] at h
  rw [h]
  exact R.hwOut

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE SHARED-`cSeam` TIE, kernel-precise (disk side)**: with `cSeam = 0` the disk boundary
`∂cHa` is forced entirely into the free sphere `S⁴ ∖ S` — the attached region receives NOTHING.
Together with the cylinder side: a zero-seam inhabitant of the structure carries no seam transfer
at all, and both split equations collapse to pure support statements. -/
theorem capstoneSeamTransferSeam_boundary_freeSphere_of_cSeam_zero
    {z : cycles (TopCat.of s.M) (2 + 2)}
    {cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)}
    (R : CapstoneSeamTransferSeam s S hS φ hφ hφinj z cHa) (h0 : R.cSeam = 0) :
    chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
          ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S) (3 + 1) := by
  have h := R.hsplitHa
  rw [h0, map_zero, zero_add] at h
  rw [h]
  exact R.hvOut

variable (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-- **The controlled-rep supplier recovers the banked residual at `μ = 0`** (item 4): a
`CapstoneSeamTransferResidual` transports DEFINITIONALLY to `CapstoneSeamTransferResidualCtrl _ 0`
(`Sd⁰ = id`). No field is weakened, strengthened, or dropped. -/
def ctrlZeroOfResidual
    (R : CapstoneSeamTransferResidual s t S hS φ hφ hφinj cd hseam d) :
    CapstoneSeamTransferResidualCtrl s t S hS φ hφ hφinj cd hseam d 0 where
  z := R.z
  hz := R.hz
  seam := R.seam
  hdetAB := R.hdetAB

/-- **…and conversely** — the `μ = 0` fibre of the controlled-rep supplier IS the banked residual.
With `ctrlZeroOfResidual`, the two variants are definitionally interchangeable at `μ = 0` and their
`toHasClass` outputs share one type, so the controlled-rep row is a genuine variant constructor —
a PASS certificate for the item-4 audit. -/
def residualOfCtrlZero
    (R : CapstoneSeamTransferResidualCtrl s t S hS φ hφ hφinj cd hseam d 0) :
    CapstoneSeamTransferResidual s t S hS φ hφ hφinj cd hseam d where
  z := R.z
  hz := R.hz
  seam := R.seam
  hdetAB := R.hdetAB

end

end SeamStructure

/-! ## §4. G13-3 — the rank-0 collapse datum sits at EXACTLY per-object conclusion strength. -/

section CollapseDatum

variable {prov : CharPairWProviderPerOp (𝓡 4) k}

/-- **The collapse datum is the Skolemized per-object conclusion** — `Nonempty (RankZeroCollapseDatum
prov p)` is EQUIVALENT to the collapse Prop's body at `p`. Forward: project the datum's fields.
Backward: repackage the `IsT2DataBordant` witness. The datum's field row (`hemp`/`b`/`hT2`/`hBor`)
adds NAMING and per-field inspectability, but ZERO statement strength: nothing in the shape pins `b`
to the genuine membrane-kill trace. (`target_spinSector` is DERIVED from `hemp`, not an independent
anti-laundering conjunct.) A datum-supply discharge is therefore audited by DATA INSPECTION — the
round-9 freeze / round-12 spec 4 obligation transfers verbatim to the datum (round-13 spec 3). -/
theorem nonempty_rankZeroCollapseDatum_iff
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) :
    Nonempty (RankZeroCollapseDatum prov p) ↔
      ∃ p' : StrMfd (pinPlusCharPairData prov).toTangentialData,
        IsEmpty p'.2.surf.M ∧ IsT2DataBordant (pinPlusCharPairData prov) p p' := by
  constructor
  · rintro ⟨d⟩
    exact ⟨d.p', d.hemp, d.isT2DataBordant⟩
  · rintro ⟨p', hemp, b, hT2, hBor⟩
    exact ⟨⟨p', hemp, b, hT2, hBor⟩⟩

/-- **The ∀-datum supply is EXACTLY the collapse atom** — `RankZeroCollapsesToEmptySurf prov ↔
(∀ rank-0 p, Nonempty (RankZeroCollapseDatum prov p))`. The #199 reduction
(`rankZeroCollapsesToEmptySurf_of_datumSupply`) is therefore an honest RENAMING of the dC overhang,
not a strengthening or weakening — the locating theorem the consumption spec hangs on. -/
theorem rankZeroCollapsesToEmptySurf_iff_datumSupply :
    RankZeroCollapsesToEmptySurf prov ↔
      ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
        IsSpinSectorStr prov p → Nonempty (RankZeroCollapseDatum prov p) := by
  constructor
  · intro h p hp
    exact (nonempty_rankZeroCollapseDatum_iff p).mpr (h p hp)
  · intro H p hp
    exact (nonempty_rankZeroCollapseDatum_iff p).mp (H p hp)

end CollapseDatum

end SKEFTHawking.PinPlusRoundThirteenGate
