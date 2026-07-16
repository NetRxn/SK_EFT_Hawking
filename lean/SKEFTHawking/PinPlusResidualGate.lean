/-
# Phase 5q.H close-out GATE ROUND 12 (fresh-context attack on the CONSOLIDATED residual frontier)

Adversarial gate findings against the post-#186 frontier: the six completeness-adjacent flags
(`NovikovHalfDimAtom`/`NovikovCoIsoAtom`, `RankZeroCollapsesToEmptySurf`, the dual-spin `hcob`,
`SpinSigmaAtoms`' Pi-fields + `CanonicalSpinSigmaAtoms.fc_sum`/`B_sum`), the Type-valued rows
(`KRSResidualRow`, `CapstoneSeamTransfer`, `TauMembraneWeldDatum`, `NovikovRealPairLES`), and the
assembly seams of `kt_equiv_zmod16_of_two_leaves`.

Verdict: **CONDITIONAL PASS with THE ROUND-12 TIE (kernel-encoded, §1) + a KERNEL-LOCATED
degenerate model on the σ-descent lane (§2, with the Witt ceiling FLAGGED) and binding specs.**

## Per-item verdict table

* **Item 1 — `NovikovHalfDimAtom`/`NovikovCoIsoAtom` (the ∀-Prop pair)** — **CONDITIONAL PASS.**
  (i) The soundness attack is REPELLED and now kernel-encoded pointwise: an Opener substrate on a
  boundary block pair FORCES σ-agreement (`novikovBoundaryRestriction_sig_eq`), and the substrate
  is EMPTY across σ-grades (`isEmpty_novikovBoundaryRestriction_of_sig_ne`) — the merge-note's
  "inhabitable only when σ agrees" is TRUE (the RealSubstrate grade already had
  `latticeSig_eq_of_realPairLES`; this adds the Opener grade). (ii) No round-trip of the
  equivalence quartet is a disguised tautology — each is an honest lateral equivalence and the
  substrate makes falsifiable demands (i). (iii) BUT the degenerate-model attack LANDS at
  matrix-equal pairs: `nonempty_novikovBoundaryRestriction_diag` /
  `nonempty_novikovRealPairLES_diag` — zero-geometry inhabitation from the diagonal Lagrangian
  through the synthetic `ofLagrangian` quotient (H³(W,∂W) impersonated by `(Fin n → ℝ) ⧸ L`). The
  atoms' entire open content therefore sits on bordant pairs with genuinely DIFFERENT disclosed
  forms. (iv) ⚠ FLAGGED CEILING (not yet kernel-encoded): classically — real Witt decomposition, a
  nondegenerate signature-zero real form has a Lagrangian — σ-agreement alone inhabits the
  substrate at EVERY pair, i.e. the whole four-formulation atom family sits at EXACTLY `hbord`
  strength. Mathlib has the full inertia API for the missing brick
  (`QuadraticForm.equivalent_weightedSumSquares` + `sigPos_of_equiv_weightedSumSquares` +
  `sigPos_add_sigNeg_add_radical`); kernel-encoding it upgrades (iv) to a locating iff and is the
  recommended follow-up. Until then, spec 2 below binds.

* **Item 2 — `RankZeroCollapsesToEmptySurf`** — **PASS** (§3). The target-laundering channel
  ("empty-surfaced `p'` with hidden positive-rank enhancement fakes dC's overhang") is CLOSED at
  the kernel: `rankZeroCollapse_target_in_sector` — the `basis` linear equiv forces any empty-surf
  target into the genuine rank-0 sector (banked G8-5 `rank_zero_of_subsingleton_H1` +
  `subsingleton_cohomology`). The G8-5 caveat is UNCHANGED and orthogonal (the sector Prop reads
  H¹-triviality, not emptiness — the nonempty-S² world is the honest round-9 overhang, not an
  exploit). The one-step-bordance strengthening over `SectorIsGeometric` survives re-inspection
  (`mk_eq_of_bordant` consumes it soundly; no `EqvGen` shortcut).

* **Item 3 — `hcob` / the opened dual-spin construction** — **THE ROUND-12 TIE** (§1, headline).
  `hcob` IS conclusion-fakeable, at the kernel: on an unpinned ambient the OPENED construction —
  all seven fields, `hcob` included — is inhabitable from bare `32 ∣ σ`
  (`nonempty_dualSpinConstruction_iff_thirtytwo_dvd`), and the whole per-kernel-element supply
  `KTSharpnessSupplyConstr` sits at EXACTLY `hfwd` strength modulo the row + Freeze atoms
  (`nonempty_ktSharpnessSupplyConstr_iff_hfwd`). Mechanism: `amb` is a FREE `TopCat` field and the
  lattice fields are σ-onto (`spinOfSigMul16` realizes every multiple of 16 from `K3`/`rev K3`
  block sums), so arithmetic impersonates geometry. Opening `DualSpinFromW` one level deeper added
  ZERO statement-shape strength; the round-10/11 non-circularity audit EXTENDS to data inspection
  (spec 1) — permanently.

* **Item 4 — `SpinSigmaAtoms`' Π-fields + `CanonicalSpinSigmaAtoms.fc_sum`/`B_sum`** — **PASS**
  (adjudicated, no new exhibit needed). The bundle carries its own anti-collapse pins: `s2s2_rank`/
  `s2s2_hyp` force a genuine rank-2 hyperbolic slot (no globally-degenerate bundle exists), and
  per-slot `pd` forces unimodularity (no zero-functional `fc` at positive rank). `fc_sum`/`B_sum`
  are coherence equations between the bundle's OWN slots — a "fake sums" bundle must still satisfy
  them at every pair including the pinned `s2s2` slot, and the block atom is then DERIVED through
  #164's real cohomological work, never vacuously. Locally-degenerate bundles are liveness-blocked
  by the row (`hrank = 22`/`hk3`/derived `hg = −16`), the same inert-degeneracy pattern as G11-3.
  Consumption guidance stands: inhabitation claims must exhibit the WHOLE bundle.

* **Item 5 — `KRSResidualRow`** — **PASS** (§4). The round-10 forcings SURVIVE the consolidation
  and are re-recorded at the row: `krsResidualRow_rank_ne` (no diagonal-cylinder reuse),
  `krsResidualRow_two_le_rank` + `isEmpty_krsResidualRow_of_rank_lt_two` (the spin fibre and the
  rank-1 step are type-void). Brown fence at the row = `KRSResidualRow.brown_eq` (#186, verified).
  `hsNe`/`hsConn` are genuinely load-bearing (typed into `residualHasClass`'s instance row — not
  droppable). The ∀-fields are object-local exactly as the #186 §5 inventory claims (`hdetAB` over
  the builder's carrier points; `hYAB` over ℕ; `glueσ`/`glueτ` over the builder's membrane;
  `hwf14`/`hwf23` functional equations at the DERIVED hasClass). `nondeg14`/`nondeg14flip` are NOT
  a redundant pair (the dimension equality needs both; only post-`dimeq` are they interderivable).
  No degenerate instantiation fires `kernelReducesToSpin_of_residualRow`: the unit is the ∀-`p`
  supply and per-`p` rows demand genuine chain detection (`hz`/`T`/`hdetAB`).

* **Item 6 — `CapstoneSeamTransfer` + controlled representatives** — **PASS** (adjudicated). The
  datum's fields are splits/supports plus ONE literal seam-face equation on the builder's own
  chains; degenerate splits (`wOut := 0` etc.) are type-correct but carry no detection — the
  detection content lives in `hdetAB` + the BANKED disk triple (`diskDetectChain_hc`/`_hdet`),
  both typed at the derived `hasClass`, and the row keeps them as separate fields. The #178
  division of labor (transfer = the φ-geometric seam; detection = `hdetAB`) survives the
  consolidation intact; the `.choose` verdict is unchanged (named chains, no opacity).

* **Item 7 — `TauMembraneWeldDatum`** — **PASS, terminal-only** (adjudicated). Sufficiency for
  "Σ bounds" is carried by the typed consumption (`ofTauMembraneWeldDatum` under
  `[IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)]`) + the PROVEN `brown_zero` anti-vacuity bridge (the
  datum FORCES the Arf-Brown obstruction to vanish — exactly the obstruction-theoretic content of
  the bounding claim); `hq`/`hlagK` are ∀-Props over the datum's OWN bounding kernel
  (object-local). The residual row respects #186 finding 2: the nine general-step membrane atoms
  are kept verbatim (verified in `KRSResidualRow` §2) — no terminal-datum absorption leak.

* **Item 8 — the assembly seams** — **PASS** (trace verified). `kt_equiv_zmod16_of_two_leaves`
  consumes `{hKRS, dC, dA}` exactly as the round-8 triple (no side-channel). hKRS ← the ∀-`p`
  `KRSResidualRow` supply (Type-valued rows, forcings §4). dC ← row + (`RankZeroCollapsesToEmptySurf`
  | `KTKernelCard`), both consumed as EXPLICIT hypotheses (§3 closes the collapse target's
  laundering). dA ← row + `hfwd` + `hcyc` + `h2`, with the `hfwd` supply lane now kernel-LOCATED
  (§1). No seam consumes an ungated Prop or a vacuous instantiation silently. ROUND-11 SPECS
  RE-VERIFIED post-consolidation: (1) the hfwd non-circularity audit — EXTENDED by G12-1 to data
  inspection at the opened supply; (2) bare-∀ consumption acceptable — unchanged; (3) the
  spinEmptyData liveness posture — unchanged; (4) the KRS unit stays the ∀-`p` supply — now in the
  sharper `KRSResidualRow` form, same unit, Brown fence banked at the row; (5) the Wu-leaf
  pairing-form supply spec — untouched by the consolidation; (6) the provider rider — unchanged
  (zero live `prov` instances until `cylData`).

## FROZEN ROUND-12 SPEC (binding on the inhabitation/consumption waves)
1. **dA lane (the opened supply)**: a `KTSharpnessSupplyConstr`/`KTSharpnessSupplyGeo` claim is
   construction progress ONLY if `amb x hx` is the tethered witness's `TopCat.of b.W` and
   `Vspace`/`ιV`/`edge` are the genuine `w₁(W)`-dual data — checked by DATA INSPECTION; the
   statement shape is conclusion-strength (G12-1) and can never enforce this.
2. **σ lane (the Novikov atoms)**: a discharge claim for ANY of the four formulations must exhibit
   the ℝ-images of a genuine bounding `W`'s restriction/pair-LES tower; a route producing per-pair
   Lagrangians from σ-agreement by linear algebra (the diagonal grade is kernel-encoded here; the
   general Witt grade is classical) is ZERO progress. Follow-up brick: kernel-encode the Witt step
   (σ = 0 + nondegenerate ⟹ Lagrangian, over ℝ) to upgrade the flag to a locating iff.
3. **KRS lane**: the consumption unit stays the ∀-`p` `KRSResidualRow` supply; per-`p` instances
   are non-vacuity demonstrators; rank-<2 instances are void by type.
4. **dC lane**: the collapse atom's target needs NO extra sector certificate (forced, §3); a
   discharge must still supply the genuine terminal-KRS bounding datum (round-9 freeze unchanged).

## Registry-worthy fork candidates (for the lead; encode-on-settle)
* `dual-spin-opened-construction-conclusion-fakeable` — false_statement: "the opened
  `DualSpinConstruction` row (equivalently `KTSharpnessSupplyConstr`) is a stronger-than-conclusion
  supply shape whose inhabitation certifies geometric dA progress" — backings:
  `nonempty_dualSpinConstruction_iff_thirtytwo_dvd`, `nonempty_ktSharpnessSupplyConstr_iff_hfwd`,
  `spinOfSigMul16_sig`.
* `novikov-substrate-synthetic-inhabitation` — false_statement: "inhabiting
  `NovikovBoundaryRestriction`/`NovikovRealPairLES` at a boundary block pair certifies
  bordism-geometric content" — backings (diagonal grade): `nonempty_novikovBoundaryRestriction_diag`,
  `nonempty_novikovRealPairLES_diag`; Witt grade flagged, follow-up brick named in spec 2.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTDualSpinConstruction
import SKEFTHawking.PinPlusKTSpinSigmaNovikovRealSubstrate
import SKEFTHawking.PinPlusKTSectorGeometricReduce
import SKEFTHawking.PinPlusKTSectorGate
import SKEFTHawking.PinPlusTraceCapstoneResidualRow

open scoped Manifold
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusKTLemma53Wave
open SKEFTHawking.PinPlusKTDualSpinConstruction
open SKEFTHawking.PinPlusKTSpinSigmaAtom
open SKEFTHawking.PinPlusKTSpinSigmaNovikovOpener
open SKEFTHawking.PinPlusKTSpinSigmaNovikovHalfDim
open SKEFTHawking.PinPlusKTSpinSigmaNovikovRealSubstrate
open SKEFTHawking.PinPlusKTSectorGate
open SKEFTHawking.PinPlusKTSectorGeometricReduce
open SKEFTHawking.PinPlusCharPairSurfaceTie
open SKEFTHawking.PinPlusTraceCapstoneResidualRow

namespace SKEFTHawking.PinPlusResidualGate

/-! ## §1. G12-1 — THE ROUND-12 DUAL-SPIN TIE: the OPENED construction (`hcob` included) is
conclusion-fakeable; `KTSharpnessSupplyConstr` sits at exactly `hfwd` strength modulo the row.

The #180/#186 dual-spin row exposes `hcob : sigM = edge.sig` as a named atom. The fake below shows
the OPENING did not close round-11's conclusion-fakeability: because `DualSpinConstruction`'s
`Vspace`/`edge` fields are FREE lattice data and the supply's `amb` field is a FREE `TopCat`, the
entire opened construction — `hcob` and all — is derivable from the arithmetic conclusion
`32 | sigM` with ZERO geometry. The realization engine is a σ-onto family of `SmoothSpinManifold4`s
(`spinOfSigMul16`: every multiple of 16 is realized by block-sums of `K3` and its reversal). -/

/-- **The empty spin lattice** — rank 0, `σ = 0`. The base of the σ-realization engine. -/
noncomputable def spinZero : SmoothSpinManifold4 where
  rank := 0
  form := 1
  even_unimod := ⟨Matrix.transpose_one, Or.inl Matrix.det_one, fun i => i.elim0⟩
  topo := by rw [GMRokhlin.latticeSig_fin_zero]; norm_num

@[simp] theorem spinZero_sig : spinZero.sig = 0 :=
  GMRokhlin.latticeSig_fin_zero _

/-- **Block sum of spin lattices** — `σ` adds; even-unimodularity and the Rokhlin topological
factor are closed under `blockDiag`. -/
noncomputable def spinBlockSum (A B : SmoothSpinManifold4) :
    SmoothSpinManifold4 where
  rank := A.rank + B.rank
  form := blockDiag A.form B.form
  even_unimod := isEvenUnimodular_blockDiag _ _ A.even_unimod B.even_unimod
  topo := by
    rw [latticeSig_blockDiag _ _ A.even_unimod B.even_unimod]
    obtain ⟨a, ha⟩ := A.rokhlin
    obtain ⟨b, hb⟩ := B.rokhlin
    rw [show latticeSig A.form = A.sig from rfl, show latticeSig B.form = B.sig from rfl, ha, hb,
      show (16 * a + 16 * b : ℤ) = 8 * (2 * (a + b)) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num : (8 : ℤ) ≠ 0)]
    exact ⟨a + b, by ring⟩

@[simp] theorem spinBlockSum_sig (A B : SmoothSpinManifold4) :
    (spinBlockSum A B).sig = A.sig + B.sig := by
  show latticeSig (blockDiag A.form B.form) = _
  rw [latticeSig_blockDiag _ _ A.even_unimod B.even_unimod]
  rfl

/-- **Orientation reversal of a spin lattice** — `σ` negates; even-unimodularity and the Rokhlin
factor are closed under negation. -/
noncomputable def spinRev (A : SmoothSpinManifold4) : SmoothSpinManifold4 where
  rank := A.rank
  form := -A.form
  even_unimod := isEvenUnimodular_neg _ A.even_unimod
  topo := by
    rw [latticeSig_neg]
    obtain ⟨a, ha⟩ := A.rokhlin
    rw [show latticeSig A.form = A.sig from rfl, ha,
      show (-(16 * a) : ℤ) = 8 * (2 * (-a)) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num : (8 : ℤ) ≠ 0)]
    exact ⟨-a, by ring⟩

@[simp] theorem spinRev_sig (A : SmoothSpinManifold4) : (spinRev A).sig = -A.sig :=
  latticeSig_neg _

/-- `n`-fold block power of a spin lattice: `σ = n·σ(V)`. -/
noncomputable def spinRep : ℕ → SmoothSpinManifold4 → SmoothSpinManifold4
  | 0, _ => spinZero
  | n + 1, V => spinBlockSum V (spinRep n V)

@[simp] theorem spinRep_sig (n : ℕ) (V : SmoothSpinManifold4) :
    (spinRep n V).sig = n * V.sig := by
  induction n with
  | zero => rw [show spinRep 0 V = spinZero from rfl, spinZero_sig]; ring
  | succ n ih =>
      rw [show spinRep (n + 1) V = spinBlockSum V (spinRep n V) from rfl,
        spinBlockSum_sig, ih]
      push_cast
      ring

/-- **THE σ-ONTO REALIZATION ENGINE** — every multiple of 16 is the signature of a genuine
`SmoothSpinManifold4` (block-sums of `K3` and its reversal). This is the arithmetic freedom the
round-12 fake exploits: the `Vspin`/`edge` fields of the opened dual-spin construction can be
STOCKED to any 16-divisible target, so nothing in the lattice data pins them to the geometry. -/
noncomputable def spinOfSigMul16 : ℤ → SmoothSpinManifold4
  | .ofNat n => spinRep n (spinRev k3Spin)
  | .negSucc n => spinRep (n + 1) k3Spin

@[simp] theorem spinOfSigMul16_sig (m : ℤ) : (spinOfSigMul16 m).sig = 16 * m := by
  cases m with
  | ofNat n =>
      rw [show spinOfSigMul16 (.ofNat n) = spinRep n (spinRev k3Spin) from rfl, spinRep_sig,
        spinRev_sig, k3Spin_sig, Int.ofNat_eq_natCast]
      push_cast
      ring
  | negSucc n =>
      rw [show spinOfSigMul16 (.negSucc n) = spinRep (n + 1) k3Spin from rfl, spinRep_sig,
        k3Spin_sig, Int.negSucc_eq]
      push_cast
      ring

/-- **THE ROUND-12 FAKE (per-object form)**: the OPENED dual-spin construction — `Vspace`, `ιV`,
`hclosed`, `Vspin`, `edge`, `hcover`, AND `hcob` — is inhabitable from the bare arithmetic
conclusion `32 ∣ sigM`, on a trivial ambient, with zero geometry: `Vspin := spinOfSigMul16 (σ/32)`,
`edge := edgeDoubleSpin Vspin`. In particular the `hcob` field ("cobordism invariance
`σ(M) = σ(∂E(V))`") is satisfied by CHOOSING `edge` to match — it constrains nothing unless `edge`
is independently pinned to the geometric `∂E(V)`. -/
noncomputable def dualSpinConstructionOfEq {sigM c : ℤ} (hc : sigM = 32 * c) :
    DualSpinConstruction PUnit sigM where
  Vspace := PUnit
  ιV := ContinuousMap.id _
  hclosed := Topology.IsClosedEmbedding.id
  Vspin := spinOfSigMul16 c
  edge := edgeDoubleSpin (spinOfSigMul16 c)
  hcover := by rw [edgeDoubleSpin_sig]
  hcob := by rw [edgeDoubleSpin_sig, spinOfSigMul16_sig, hc]; ring

/-- The fake, packaged from the bare divisibility. -/
noncomputable def dualSpinConstructionOfThirtytwoDvd {sigM : ℤ} (h : (32 : ℤ) ∣ sigM) :
    DualSpinConstruction PUnit sigM :=
  dualSpinConstructionOfEq h.choose_spec

/-- **THE ROUND-12 TIE, per-object locating equivalence**: on an unpinned ambient the opened
dual-spin construction sits at EXACTLY `32 ∣ σ` strength — forward is the banked Rokhlin arithmetic
(`DualSpinConstruction.thirtytwo_dvd`), backward is the fake. The construction's discharge value is
therefore entirely in the PINNING of `amb`/`Vspace`/`edge` to the tethered witness's genuine
geometry, which the statement shape cannot enforce. -/
theorem nonempty_dualSpinConstruction_iff_thirtytwo_dvd (sigM : ℤ) :
    Nonempty (DualSpinConstruction PUnit sigM) ↔ (32 : ℤ) ∣ sigM :=
  ⟨fun ⟨d⟩ => d.thirtytwo_dvd, fun h => ⟨dualSpinConstructionOfThirtytwoDvd h⟩⟩

variable {prov : CharPairWProviderPerOp (𝓡 4) 0}

/-- **THE ROUND-12 FAKE (supply form)**: the whole `KTSharpnessSupplyConstr` — the per-kernel-element
family of opened constructions — is inhabitable from the bare `hfwd` conclusion, because `amb` is a
FREE `TopCat` field: take `amb := PUnit` everywhere and stock the lattice fields from
`spinOfSigMul16`. Zero forgetful-map or bordism geometry consumed. -/
noncomputable def ktSharpnessSupplyConstrOfHfwd (R : SpinSigmaPresentation (spinEmptyData prov))
    (hfwd : ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ R.sig x) :
    KTSharpnessSupplyConstr R where
  amb := fun _ _ => TopCat.of PUnit
  constr := fun x hx => dualSpinConstructionOfThirtytwoDvd (hfwd x hx)

/-- **THE ROUND-12 TIE (headline)**: modulo the presentation row and the terminal Freeze atoms
`{hCob, hBase, hBnd}`, the opened sharpness supply is EQUIVALENT to the `hfwd` conclusion —
`Nonempty (KTSharpnessSupplyConstr row.R) ↔ (∀ x ∈ ker Φ, 32 ∣ σ x)`. Forward is
`hfwd_of_row_of_supplyConstr` (the honest banked chain through `KerPhiSubDoubles`); backward is the
round-12 fake. Consequence: OPENING `DualSpinFromW` into `{V, Vspin, edge, hcover, hcob}` did NOT
create a statement shape enforcing geometric progress — a "supply constructed" claim is progress
ONLY under the round-10/11 non-circularity audit EXTENDED to data inspection: `amb x hx` must be the
tethered witness's `TopCat.of b.W` and `edge` the genuine `∂E(V)`, checked by inspection,
permanently. -/
theorem nonempty_ktSharpnessSupplyConstr_iff_hfwd (row : SpinPresentationRow prov)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hBnd : row.R.SphereProductBounds) :
    Nonempty (KTSharpnessSupplyConstr row.R) ↔
      ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ row.R.sig x :=
  ⟨fun ⟨S⟩ => hfwd_of_row_of_supplyConstr row hCob hBase hBnd S,
   fun h => ⟨ktSharpnessSupplyConstrOfHfwd row.R h⟩⟩

/-! ## §2. G12-2 — the Novikov σ-descent lane: pointwise soundness KERNEL-ENCODED; the diagonal
degenerate model KERNEL-ENCODED (zero-geometry inhabitation at matrix-equal pairs); the full
σ-agreement fake FLAGGED (Witt step — see the record).

The dispatch asked (i) whether the equivalence quartet hides a disguised tautology, and (ii) to
attack the substrate's "inhabitable only when σ agrees" soundness claim. Answers: (ii) the
soundness claim is TRUE and now pointwise kernel-encoded (`novikovBoundaryRestriction_sig_eq`,
`isEmpty_novikovBoundaryRestriction_of_sig_ne`) — the substrate genuinely constrains; (i) no
round-trip is a tautology, BUT the lane has a σ-strength CEILING: at any pair whose disclosed
intersection matrices are EQUAL the substrate is inhabitable with zero bordism geometry
(`nonempty_novikovBoundaryRestriction_diag` — the diagonal Lagrangian), and classically (Witt) the
same holds whenever the σs merely AGREE, so the whole four-formulation atom family sits at exactly
`hbord` strength. The Witt step is not yet kernel-encoded (flagged in the record as the follow-up
brick); the diagonal grade suffices to bind the consumption spec below. -/

/-- **Pointwise σ-soundness of the opener substrate** — a `NovikovBoundaryRestriction` on the
boundary block form FORCES the signatures to agree. The substrate cannot be inhabited for
σ-disagreeing even-unimodular blocks: its `lagrangian` output makes the (nondegenerate) block form
metabolic, hence `σ = 0`, hence `σ(A) = σ(B)`. This is the "inhabitable only when σ agrees"
merge-note claim, kernel-encoded at the Opener grade (the RealSubstrate grade already had
`latticeSig_eq_of_realPairLES`). -/
theorem novikovBoundaryRestriction_sig_eq {r s : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (B : Matrix (Fin s) (Fin s) ℤ) (hA : IsEvenUnimodular A) (hB : IsEvenUnimodular B)
    (d : NovikovBoundaryRestriction (blockDiag A (-B))) :
    latticeSig A = latticeSig B := by
  obtain ⟨L, hdim, hiso⟩ := d.lagrangian
  have hnegB := isEvenUnimodular_neg _ hB
  have hbd_eu := isEvenUnimodular_blockDiag A (-B) hA hnegB
  have hzero := latticeSig_eq_zero_of_lagrangian hdim (blockDiag A (-B)) hbd_eu.radical_eq_bot L
    rfl hiso
  have hadd := latticeSig_blockDiag A (-B) hA hnegB
  rw [latticeSig_neg] at hadd
  omega

/-- **The substrate is EMPTY across σ-grades** — the anti-vacuity certificate the dispatch demanded:
no degenerate instantiation of `NovikovBoundaryRestriction` can launder a σ-jump. -/
theorem isEmpty_novikovBoundaryRestriction_of_sig_ne {r s : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (B : Matrix (Fin s) (Fin s) ℤ) (hA : IsEvenUnimodular A) (hB : IsEvenUnimodular B)
    (hne : latticeSig A ≠ latticeSig B) :
    IsEmpty (NovikovBoundaryRestriction (blockDiag A (-B))) :=
  ⟨fun d => hne (novikovBoundaryRestriction_sig_eq A B hA hB d)⟩

/-- The fold `Fin (r + r) → Fin r` collapsing the two blocks (both summands to the identity). -/
def foldMap (r : ℕ) : Fin (r + r) → Fin r := fun i => Sum.elim id id (finSumFinEquiv.symm i)

theorem foldMap_surjective (r : ℕ) : Function.Surjective (foldMap r) := fun a =>
  ⟨finSumFinEquiv (Sum.inl a), by simp [foldMap]⟩

/-- The diagonal embedding `ℝ^r → ℝ^(r+r)`, `x ↦ (x, x)` (precomposition with the fold). -/
noncomputable def diagEmbed (r : ℕ) : (Fin r → ℝ) →ₗ[ℝ] (Fin (r + r) → ℝ) :=
  LinearMap.funLeft ℝ ℝ (foldMap r)

theorem diagEmbed_injective (r : ℕ) : Function.Injective (diagEmbed r) :=
  LinearMap.funLeft_injective_of_surjective ℝ ℝ _ (foldMap_surjective r)

/-- The diagonal vector, unfolded through the block equivalence: `diagEmbed r v ∘ finSumFinEquiv`
is `Sum.elim v v`. -/
theorem diagEmbed_comp_equiv (r : ℕ) (v : Fin r → ℝ) :
    (diagEmbed r v) ∘ finSumFinEquiv = Sum.elim v v := by
  funext a
  show v (Sum.elim id id (finSumFinEquiv.symm (finSumFinEquiv a))) = Sum.elim v v a
  rw [Equiv.symm_apply_apply]
  cases a <;> rfl

/-- **The diagonal is isotropic in `blockDiag A (−A)`** — `Q(v, v) = Q_A(v) − Q_A(v) = 0`. -/
theorem diag_isotropic {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → ℝ) :
    ((blockDiag A (-A)).map (Int.cast : ℤ → ℝ)).toQuadraticMap' (diagEmbed r v) = 0 := by
  simp only [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']
  have hmat : (blockDiag A (-A)).map (Int.cast : ℤ → ℝ)
      = (Matrix.fromBlocks (A.map (Int.cast : ℤ → ℝ)) 0 0
          (-(A.map (Int.cast : ℤ → ℝ)))).submatrix ⇑finSumFinEquiv.symm ⇑finSumFinEquiv.symm := by
    rw [blockDiag_def, Matrix.reindex_apply]
    ext i j
    rcases hs : finSumFinEquiv.symm i with a | a <;> rcases ht : finSumFinEquiv.symm j with b | b <;>
      simp [Matrix.submatrix_apply, Matrix.map_apply, hs, ht]
  rw [hmat, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, diagEmbed_comp_equiv r v,
    Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, add_zero, zero_add,
    Matrix.neg_mulVec]
  rw [dotProduct_comp_equiv_symm, diagEmbed_comp_equiv r v, sumElim_dotProduct_sumElim,
    dotProduct_neg]
  ring

/-- **The diagonal Lagrangian of `blockDiag A (−A)`** — a half-dimensional isotropic subspace,
constructed by pure linear algebra (no bordism, no manifold). This is the `NovikovLagrangianAtom`
BODY at any matrix-equal pair, inhabited for free. -/
theorem exists_lagrangian_blockDiag_neg_self {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) :
    ∃ L : Submodule ℝ (Fin (r + r) → ℝ),
      r + r = 2 * Module.finrank ℝ L ∧
      ∀ x ∈ L, ((blockDiag A (-A)).map (Int.cast : ℤ → ℝ)).toQuadraticMap' x = 0 := by
  refine ⟨LinearMap.range (diagEmbed r), ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (diagEmbed_injective r)]
    simp [two_mul]
  · rintro x ⟨v, rfl⟩
    exact diag_isotropic A v

/-- **THE DIAGONAL DEGENERATE MODEL** — the real pair-LES substrate (and through
`toBoundaryRestriction` the Opener substrate) is inhabitable at any matrix-equal boundary pair with
ZERO bordism geometry: the synthetic quotient stands in for `H³(W,∂W)` and the diagonal Lagrangian
for the restriction image. Consequence: a claimed "discharge" of any of the four σ-descent atom
formulations that only ever produces substrates at σ-matching pairs by linear algebra is ZERO
progress — the honest content is the pair-LES data of a GENUINE bounding `W`, checkable only by
inspection (spec item 2 of the record). -/
theorem nonempty_novikovRealPairLES_diag {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (heu : IsEvenUnimodular A) :
    Nonempty (NovikovRealPairLES (blockDiag A (-A))) := by
  obtain ⟨L, hdim, hiso⟩ := exists_lagrangian_blockDiag_neg_self A
  have hbd_eu := isEvenUnimodular_blockDiag A (-A) heu (isEvenUnimodular_neg _ heu)
  exact ⟨NovikovRealPairLES.ofLagrangian _ hbd_eu.radical_eq_bot L hdim hiso⟩

/-- The diagonal model reaches the Opener substrate too (via `toBoundaryRestriction`). -/
theorem nonempty_novikovBoundaryRestriction_diag {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (heu : IsEvenUnimodular A) :
    Nonempty (NovikovBoundaryRestriction (blockDiag A (-A))) :=
  ⟨(nonempty_novikovRealPairLES_diag A heu).some.toBoundaryRestriction⟩

/-! ## §3. G12-3 — the collapse atom's target is FORCED into the genuine spin sector: no
degenerate `p'` (empty surface, hidden positive rank) can fake dC's overhang.

The laundering worry: `RankZeroCollapsesToEmptySurf` demands only `IsEmpty p'.2.surf.M` — could a
builder supply an empty-surfaced `p'` carrying a hidden positive-rank enhancement (a free-floating
`q` untied to any surface), smuggling non-sector data into `GeometricSpinRepresentable`? NO: the
`CharPairStrBundled.basis` field is a linear EQUIV `H¹(Σ;ℤ/2) ≃ (Fin n → ℤ/2)`, so an empty surface
(subsingleton `H¹`, banked `subsingleton_cohomology`) forces `n = 0` (banked round-8
`rank_zero_of_subsingleton_H1`). The atom's target therefore lands in the honest rank-0 sector. -/

/-- **The collapse target is in the spin sector** (G12-3): any `p'` produced by
`RankZeroCollapsesToEmptySurf` satisfies `IsSpinSectorStr` — empty surface forces rank 0 through
the basis equiv. The "degenerate `W`/`p'` fakes dC's overhang" channel is closed at the kernel. -/
theorem rankZeroCollapse_target_in_sector (hcol : RankZeroCollapsesToEmptySurf prov)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) (hp : IsSpinSectorStr prov p) :
    ∃ p' : StrMfd (pinPlusCharPairData prov).toTangentialData,
      IsSpinSectorStr prov p' ∧ IsEmpty p'.2.surf.M ∧
        IsT2DataBordant (pinPlusCharPairData prov) p p' := by
  obtain ⟨p', hemp, hbord⟩ := hcol p hp
  haveI := hemp
  exact ⟨p', isSpinSectorStr_of_subsingleton_H1 prov p' inferInstance, hemp, hbord⟩

/-! ## §4. G12-4 — the KRS residual row: the round-10 forcings SURVIVE the consolidation.

`KRSResidualRow.toSupplyMV` re-derives `CapstoneAmbientSupplyWeldedMV`, so the round-10 forcings
apply BY TYPE downstream; the two theorems below re-record them at the consolidated row itself, so
no future re-wiring can shed them silently. Note the row is STRICTLY rank-≥2: a rank-0 or rank-1
`p` admits NO row at all (`hrank : p'.2.n + 2 = p.2.n`), so the spin fibre and the last odd step
are type-level excluded — consistent with the consumption guard `0 < p.2.n` in
`kernelReducesToSpin_of_residualRow` (which the ∀-supply `H` receives as a hypothesis). -/

/-- **No diagonal-cylinder reuse at the consolidated row** (the round-10
`ambientSurgeryDatum_rank_ne` forcing, re-recorded on `KRSResidualRow`): the surgered
representative's rank strictly differs. -/
theorem krsResidualRow_rank_ne {p : StrMfd (pinPlusCharPairData prov).toTangentialData}
    (R : KRSResidualRow prov p) : R.p'.2.n ≠ p.2.n := by
  have := R.hrank
  omega

/-- **The consolidated row is off the spin fibre by TWO** — `2 ≤ p.2.n` is forced by `hrank`. -/
theorem krsResidualRow_two_le_rank {p : StrMfd (pinPlusCharPairData prov).toTangentialData}
    (R : KRSResidualRow prov p) : 2 ≤ p.2.n := by
  have := R.hrank
  omega

/-- **The row is UNINHABITABLE at rank < 2** — the degenerate/spin-fibre world is inert for the
KRS supply at the type level (the round-10 `ambientSurgeryDatum_pos_rank` forcing, strengthened to
the consolidation's exact-drop form). -/
theorem isEmpty_krsResidualRow_of_rank_lt_two
    {p : StrMfd (pinPlusCharPairData prov).toTangentialData} (h : p.2.n < 2) :
    IsEmpty (KRSResidualRow prov p) :=
  ⟨fun R => absurd R.hrank (by omega)⟩

end SKEFTHawking.PinPlusResidualGate
