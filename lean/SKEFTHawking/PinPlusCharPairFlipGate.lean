/-
# Phase 5q.H W-A GATE ROUND 6 (fresh-context adversarial vacuity attack on the FLIPPED carrier)

Adversarial gate findings against the FLIPPED carrier (`pinPlusCharPairData` with
`Bor := CharPairBorRealized`, THE FLIP 2026-07-15). Verdict: **FAIL (structural)** — one
unconditional kernel-encoded finding (F4), one conditional kernel-encoded finding (F5), and two
kernel-encoded PASS-evidence records (A1, A2) showing which attacks the flip DOES block and by
exactly which field.

**F4 — THE MEMBRANE IS COMPLETELY UNTETHERED TO THE BORDISM (`Q ⊄ W`; bordism-blindness).**
The §5 conversion banner of `PinPlusKTVacuityGateWD` claims a realized witness "needs an actual
compact-T2 membrane `Q ⊆ (ℝP⁴)⁴ × I`". That claim is FALSE at the type level:
`CharPairBorRealized.real : GeoRealizationTied (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis
τ.basis` mentions NEITHER `b` nor `b.W` — `Q` is an arbitrary compact-T2 `TopCat` (not a manifold,
not a subspace of anything). Kernel-encoded here as:

* `CharPairBorRealized.transport` — a realized witness on ANY bordism `b` transports verbatim to
  ANY other bordism `b'` between the same ends (given the pinned provider and `T2Space b'.W`):
  every non-provider field of the witness is `b`-independent.
* `isT2DataBordant_pinPlusCharPair_factors` — **the structured relation FACTORS**:
  `IsT2DataBordant (pinPlusCharPairData prov) p q ↔ (∃ b, T2Space b.W) ∧ HasEndsRealization`.
  The right-hand side contains NO Wu/w₂ content and NO interaction between the bordism and the
  tangential data: given the provider, the `hwu` "filter" filters NOTHING (every bordism receives
  its admissibility from `prov` uniformly), and the whole tangential refinement reduces to an
  ends-only condition about abstract compact-T2 spaces.

**F5 — THE F1-FAMILY IS CLOSED ONLY AT THE IN-TREE HORIZON, NOT MATHEMATICALLY (conditional
`8 • [ℝP⁴] = 0`).** Because of F4, the round-4.5 exploit does not need a membrane in
`(ℝP⁴)⁴ × I`; it needs ONE abstract compact-T2 pair: a space `Q` with a closed embedding of the
8-fold `ℝP²` end surface whose `H₁`-kernel is the e₈ graph. Kernel-encoded here as the reduction
`ktNonSplit_false_of_realization : UnreversedDoublingRealization → ∀ prov, ¬ KTNonSplit prov`
(with `unreversedDoublingRealization_of_e8` discharging ALL the algebra from the retained §3/§4.5
engines — the sole remaining hypothesis is the topological realization `E8MembraneRealization`).
Mathematically that hypothesis is TRUE: take `Q` = the 8 `ℝP²`'s joined by a tree of arcs (H₁
unchanged) with four 2-cells attached along loops representing the graph-of-`(J+I)` classes —
a compact Hausdorff CW pair whose `H₁`-kernel is exactly the e₈ graph. The tree cannot currently
EXPRESS this `Q` (no CW/Mayer–Vietoris machinery for adjunction spaces), which is why the replay
does not construct in-tree — but that is a statement about the tree's homology toolbox, NOT about
geometry. On the flipped carrier the W-D binder `KTNonSplit` is therefore mathematically FALSE
(pending only homology machinery), and `KTKernelCard ∧ KTNonSplit` unsatisfiable. **The W-D
binder-discharge work must NOT open on this carrier shape.**

**A1 — PASS-evidence: the identity membrane (F1 replay) is blocked by `hlag`, and ONLY by
`hlag`.** `GeoRealizationTied` itself is synthesizable from nothing for EVERY end pair
(`idRealizationTied`: `Q = ∂Q = Σ_σ ⊔ Σ_τ`, `ι = id`) — the structure alone is a shape. Its
computed kernel is `⊥` (`idRealizationTied_transportedBInc_ker`), and `⊥` is never jointly
Lagrangian in positive rank (`not_jointLagrangian_bot`). So the filtering power of the flipped
`Bor` lives ENTIRELY in `htaylor`/`hlag` over the computed kernel — the topology certificates
filter nothing by themselves.

**A2 — PASS-evidence: the in-tree doubling realization cannot host the un-reversed double.** The
type-correct in-tree realization for the `(σ₈, ∅)` doubling ends is `doublingRealizationTied`,
whose computed kernel is the anti-diagonal `ker (negBorBInc 4)`; on it the UN-reversed 8-fold odd
joint form does not vanish (`unreversed_double_diag_not_taylorLeg` — the `2·q ≠ 0` two-torsion
trap doing its designed job). Together with the homeo-graph shape of every other in-tree engine
(`cylRealizationTied` = diagonal, `mapCylRealizationTied` = graph of a homeomorphism-induced
transport, sum realizations = block sums of these) and component-permutation rigidity of
self-maps of disjoint `ℝP²`'s (each component maps into ONE component, so induced `H₁` matrices
have ≤ 1 nonzero entry per column — `J + I` has three), NO in-tree engine realizes the e₈ kernel:
the F1/F2/F3 replays are genuinely blocked at the in-tree horizon.

**FROZEN MINIMAL STRENGTHENING SPEC (round 6):**
1. **The W-tether**: `CharPairBorRealized` must tie the membrane INTO the bordism — a map
   `ιW : C(↑real.Q, b.W)` (honest form: a closed embedding) with commuting conditions gluing
   `real.ι`, the boundary identifications `homσ/homτ`, the ends' `σ.emb/τ.emb`, and `b`'s boundary
   structure. Only then does the e₈ exploit demand an e₈-kernel membrane inside `(ℝP⁴)⁴ × I`
   specifically — the genuinely geometric content the §5 banner already (wrongly) claims.
2. **Manifold discipline on `Q`** (secondary, after 1): abstract compact-T2 admits CW pathologies;
   `Q` should carry charted/dimension certificates like every other carrier object.
3. **Provider quantification**: `CharPairWProviderPinned.wadm : ∀ b, WAdmPinned b` quantifies over
   ALL bordisms — including `w₂(W) ≠ 0` ones (e.g. any `M⁴ × I` with `w₂(M) ≠ 0`) on which a
   PINNED datum with `hwu` is mathematically impossible, and non-T2 ones where Lefschetz-duality
   data may not exist. The pinned provider is therefore likely UNINHABITABLE, making every
   `∀ prov`-statement (discharges AND refutations alike) vacuous. Restrict the quantification to
   the op-bordism family actually consumed (cylinders/mapCylinders/sums/doublings), or supply
   per-op admissibility data. (Not kernel-encoded this round — needs a `w₂ ≠ 0` manifold in-tree;
   recorded as the spec's item 3.)

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTVacuityGateWD

open scoped Manifold
open CategoryTheory Opposite Topology
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.BordismTheory
open SKEFTHawking.TangentialDataBordism
open SKEFTHawking.T2TangentialBordism
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularDisjointUnion SKEFTHawking.SingularDisjointUnionHn
open SKEFTHawking.SingularCohomologyDisjointSum
open SKEFTHawking.SingularKroneckerBasisBridge
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairSurfaceTie
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusCharPairBorRealized
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTVacuityGateWD
open SKEFTHawking.RP4Witness SKEFTHawking.RP4CharPairWitness

namespace SKEFTHawking.PinPlusCharPairFlipGate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-! ## §0. THE FROZEN UNTETHERED INSTANCE (the round-6 exhibit, preserved AT THE RE-FLIP)

At the round-7 re-flip (2026-07-15) the LIVE carrier `pinPlusCharPairData` moved onto the
W-TETHERED `CharPairBorRealizedTethered` with the per-op provider — precisely to kill the F4/F5
findings below. This module's findings are statements about the UNTETHERED shape; to preserve
them as the permanent kernel-checked record (the registry fork
`untethered-membrane-factors-relation` backs onto them), the untethered instance and the KT
Props it consumed are FROZEN here verbatim (`…Untethered` / `…U` names). They are historical
exhibits — nothing downstream consumes them. -/

/-- The round-6 exhibit: the untethered realized instance, verbatim as flipped 2026-07-15. -/
noncomputable def pinPlusCharPairDataUntethered (prov : CharPairWProviderPinned I k) :
    T2TangentialData.{0, 1} PUnit k I where
  Mfd := charPairBundledMfd (k := k) (I := I)
  Bor := fun b σ τ => CharPairBorRealized b σ τ
  emptyStr := charPairBundledEmpty
  sumStr := fun σ τ => charPairBundledSumStr σ τ
  cylBor := fun σ => SKEFTHawking.PinPlusCharPairBorRealized.cylBorRealized prov σ
  addBor := fun β₁ β₂ =>
    SKEFTHawking.PinPlusCharPairAddRealization.addBorRealized prov β₁ β₂
  symmBor := fun β => SKEFTHawking.PinPlusCharPairBorRealized.symmBorRealized β
  commBor := fun σ τ =>
    SKEFTHawking.PinPlusCharPairBorRealizedOps.commBorRealized prov σ τ
  assocBor := fun σ τ ρ =>
    SKEFTHawking.PinPlusCharPairBorRealizedOps.assocBorRealized prov σ τ ρ
  unitBor := fun σ => SKEFTHawking.PinPlusCharPairBorRealizedOps.unitBorRealized prov σ
  revStr := fun σ => charPairBundledRevStr σ
  revBor := fun β => SKEFTHawking.PinPlusCharPairBorRealized.revBorRealized β
  negBor := fun σ => SKEFTHawking.PinPlusCharPairBorRealized.negBorRealized prov σ
  t2Str := fun m => m.toCharPairStr.t2

/-- The frozen mod-8 grade on the untethered exhibit (verbatim `charPairBrown`). -/
noncomputable def charPairBrownU (prov : CharPairWProviderPinned I k) :
    T2DataBordismGrp (pinPlusCharPairDataUntethered prov) →+ ZMod 8 where
  toFun := Quot.lift (fun p => p.2.q.brown)
    (fun _p _q h => by
      obtain ⟨_, _, ⟨str⟩⟩ := h
      exact CharPairBorRealized.brown_eq str)
  map_zero' := by show (stdQuadratic 0).brown = 0; rw [brown_stdQuadratic, Nat.cast_zero]
  map_add' := by
    intro x y
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q =>
    show ((Z4Quadratic.orthSum p.2.q q.2.q).reindex finSumFinEquiv).brown
        = p.2.q.brown + q.2.q.brown
    rw [reindex_brown, brown_orthSum]

/-- The frozen `[ℝP⁴]` class on the untethered exhibit. -/
noncomputable def ktRP4ClassU (prov : CharPairWProviderPinned (𝓡 4) 0) :
    T2DataBordismGrp (pinPlusCharPairDataUntethered prov) :=
  T2DataBordismGrp.mk (pinPlusCharPairDataUntethered prov) ⟨rp4SM, rp4CharPair⟩

/-- The frozen kernel representative `8 • [ℝP⁴]`. -/
noncomputable def ktKernelRepU (prov : CharPairWProviderPinned (𝓡 4) 0) :
    T2DataBordismGrp (pinPlusCharPairDataUntethered prov) :=
  (8 : ℕ) • ktRP4ClassU prov

/-- The frozen non-split Prop. -/
def KTNonSplitU (prov : CharPairWProviderPinned (𝓡 4) 0) : Prop :=
  ktKernelRepU prov ≠ 0

/-- The frozen kernel-card Prop. -/
def KTKernelCardU (prov : CharPairWProviderPinned (𝓡 4) 0) : Prop :=
  ∀ x : T2DataBordismGrp (pinPlusCharPairDataUntethered prov),
    charPairBrownU prov x = 0 → x = 0 ∨ x = ktKernelRepU prov

/-! ## §1. F4 — the membrane is untethered to the bordism (kernel-encoded) -/

/-- **F4 (transport): a realized witness is BORDISM-BLIND.** Every field of
`CharPairBorRealized b σ τ` other than the provider-supplied item-1 block is independent of `b`:
`real`/`htaylor`/`hlag` mention only the ends, and `P14/P23/hwu/pin14/pin23` are drawn from the
provider **for every bordism uniformly**. So a witness on `b` transports verbatim to ANY other
bordism `b'` between the same ends, given only `T2Space b'.W`. The membrane `Q` never sees `W`. -/
noncomputable def CharPairBorRealized.transport (prov : CharPairWProviderPinned I k)
    {s t : SingularManifold.{0} PUnit.{1} k I}
    {b b' : Bordism (I.prod (𝓡∂ 1)) s t}
    {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (β : CharPairBorRealized b σ τ) (hT2' : T2Space b'.W) :
    CharPairBorRealized b' σ τ :=
  mkCharPairBorRealized prov b' hT2' β.real β.htaylor β.hlag

/-- **The ends-only content of a realized bordism witness** — a derived-basis realization datum at
the two ends' carried surfaces/bases whose computed kernel is Taylor-vanishing and jointly
Lagrangian. NOTE: no bordism appears. This Prop is what `Bor` actually certifies beyond the
provider-supplied admissibility. -/
def HasEndsRealization {s t : SingularManifold.{0} PUnit.{1} k I}
    (σ : CharPairStrBundled I s) (τ : CharPairStrBundled I t) : Prop :=
  ∃ real : GeoRealizationTied (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis,
    TaylorLegVanishes σ.q τ.q ((real.toMembrane σ.q τ.q).L)
      ∧ JointLagrangian σ.q τ.q ((real.toMembrane σ.q τ.q).L)

/-- **F4 (factorization): the flipped structured relation FACTORS through the unstructured one.**
`IsT2DataBordant (pinPlusCharPairDataUntethered prov) p q` holds iff (i) SOME Hausdorff bordism exists
between the underlying manifolds — with NO structure on it whatsoever — and (ii) the ends satisfy
the bordism-free condition `HasEndsRealization`. The right-hand side contains no `w₂`/Wu content
(given `prov`, the `hwu` filter is definitionally trivial) and no interaction between the
tangential data and the bordism topology: the "Pin⁺ characteristic-pair bordism" relation is
unstructured-T2-bordism ∧ ends-algebra-with-abstract-topology. -/
theorem isT2DataBordant_pinPlusCharPair_factors (prov : CharPairWProviderPinned I k)
    {s t : SingularManifold.{0} PUnit.{1} k I}
    (σ : CharPairStrBundled I s) (τ : CharPairStrBundled I t) :
    IsT2DataBordant (pinPlusCharPairDataUntethered prov) ⟨s, σ⟩ ⟨t, τ⟩
      ↔ (∃ b : Bordism.{0} (I.prod (𝓡∂ 1)) s t, T2Space b.W) ∧ HasEndsRealization σ τ := by
  constructor
  · rintro ⟨b, hT2, ⟨β⟩⟩
    exact ⟨⟨b, hT2⟩, ⟨β.real, β.htaylor, β.hlag⟩⟩
  · rintro ⟨⟨b, hT2⟩, ⟨real, ht, hl⟩⟩
    exact ⟨b, hT2, ⟨mkCharPairBorRealized prov b hT2 real ht hl⟩⟩

/-! ## §2. A1 — the identity membrane: `GeoRealizationTied` is synthesizable from nothing;
the block is `hlag`, and only `hlag` -/

section IdMembrane

variable {nσ nτ : ℕ} (Sσ Sτ : TopCat)
  [T2Space (Sσ : Type)] [CompactSpace (Sσ : Type)]
  [T2Space (Sτ : Type)] [CompactSpace (Sτ : Type)]
  (bσ : Cohomology Sσ 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
  (bτ : Cohomology Sτ 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2))

/-- **A1 (the identity membrane).** For EVERY end pair, the boundary itself is its own membrane:
`Q := ∂Q := Σ_σ ⊔ Σ_τ`, `ι := id`. Every per-object certificate is real (sums of compact-T2 are
compact-T2; `id` is a closed embedding), the bases are derived — so `GeoRealizationTied` is
inhabited with ZERO geometric input beyond the ends. The structure alone filters nothing; all the
filtering lives downstream in `htaylor`/`hlag` (see `idRealizationTied_transportedBInc_ker` +
`not_jointLagrangian_bot`). -/
noncomputable def idRealizationTied : GeoRealizationTied Sσ Sτ bσ bτ where
  bdry := TopCat.of ((Sσ : Type) ⊕ (Sτ : Type))
  Q := TopCat.of ((Sσ : Type) ⊕ (Sτ : Type))
  U := Set.range Sum.inl
  hU := ⟨isClosed_range_inl, isOpen_range_inl⟩
  bdryT2 := inferInstanceAs (T2Space ((Sσ : Type) ⊕ (Sτ : Type)))
  bdryCompact := inferInstanceAs (CompactSpace ((Sσ : Type) ⊕ (Sτ : Type)))
  QT2 := inferInstanceAs (T2Space ((Sσ : Type) ⊕ (Sτ : Type)))
  QCompact := inferInstanceAs (CompactSpace ((Sσ : Type) ⊕ (Sτ : Type)))
  ι := ContinuousMap.id _
  hιce := IsClosedEmbedding.id
  homσ := IsClosedEmbedding.inl.isEmbedding.toHomeomorph.symm
  homτ := (Homeomorph.setCongr Set.compl_range_inl).trans
    IsClosedEmbedding.inr.isEmbedding.toHomeomorph.symm
  mid := nσ + nτ
  eQ := homologyBasisOfCohomologyBasis (sumBasis bσ bτ)

/-- The identity membrane's computed kernel is `⊥` — `H₁(id)` is injective. -/
theorem idRealizationTied_transportedBInc_ker :
    LinearMap.ker (transportedBInc (idRealizationTied Sσ Sτ bσ bτ).toData) = ⊥ := by
  rw [transportedBInc_ker]
  have hι : (idRealizationTied Sσ Sτ bσ bτ).toData.ι = ContinuousMap.id _ := rfl
  rw [hι]
  erw [Homology.map_id, LinearMap.ker_id, Submodule.map_bot]

/-- **The block: `⊥` is never jointly Lagrangian in positive rank.** Coisotropy of `⊥` demands
the whole boundary space vanish; any index refutes it. This — not any topology certificate — is
what stops the identity membrane from inhabiting `CharPairBorRealized` between rank-positive
ends. -/
theorem not_jointLagrangian_bot {nσ nτ : ℕ} (qσ : Z4Quadratic (Fin nσ))
    (qτ : Z4Quadratic (Fin nτ)) (j : Fin nσ ⊕ Fin nτ) :
    ¬ JointLagrangian qσ qτ (⊥ : Submodule (ZMod 2) ((Fin nσ ⊕ Fin nτ) → ZMod 2))  := by
  intro h
  have hmem : (fun _ => 1 : (Fin nσ ⊕ Fin nτ) → ZMod 2) ∈
      (⊥ : Submodule (ZMod 2) ((Fin nσ ⊕ Fin nτ) → ZMod 2)) := by
    refine h _ (fun l hl => ?_)
    rw [(Submodule.mem_bot (ZMod 2)).mp hl, (jointEnhancement qσ qτ).B_symm]
    exact (jointEnhancement qσ qτ).B_zero_left _
  exact one_ne_zero (congrFun ((Submodule.mem_bot (ZMod 2)).mp hmem) j)

end IdMembrane

/-! ## §3. A2 — the in-tree doubling realization cannot host the un-reversed double -/

/-- **A2: the anti-diagonal kernel refuses the un-reversed 8-fold odd joint form.** The only
in-tree realization with the `(σ₈, ∅)` doubling end types is `doublingRealizationTied`, whose
computed kernel is `ker (negBorBInc 4)` (the reindexed anti-diagonal). On the doubled-single
witness `l = e₀⊕e₀` the UN-reversed joint enhancement evaluates to `q(e₀) + q(e₀) = 2 ≠ 0` in
`ZMod 4` — the two-torsion trap (`plain_joint_forces_two_torsion_on_diagonal`) doing exactly its
designed job. So the in-tree replay of the round-4.5 exploit dies at `htaylor`. -/
theorem unreversed_double_diag_not_taylorLeg :
    ¬ TaylorLegVanishes (charPairBundledSumStr sig4 sig4).q
        (charPairBundledEmpty (I := 𝓡 4) (k := 0)).q
        (LinearMap.ker (negBorBInc 4)) := by
  intro h
  have hl : (Sum.elim (fun i : Fin (4 + 4) => if i.val = 0 ∨ i.val = 4 then 1 else 0)
      (fun _ : Fin 0 => 0) : Fin (4 + 4) ⊕ Fin 0 → ZMod 2) ∈ LinearMap.ker (negBorBInc 4) := by
    rw [LinearMap.mem_ker]
    decide
  have hq := h _ hl
  revert hq
  decide

/-! ## §4. F5 — the conditional refutation: `KTNonSplitU` is one abstract compact-T2 pair away
from FALSE (all algebra discharged in-tree; no `W`, no manifold, no bordism content remains) -/

/-- The concrete empty end at `I = 𝓡 4`, `k = 0` (universe-pinned). -/
noncomputable abbrev emptyEnd :
    CharPairStrBundled (𝓡 4) (emptySM : SingularManifold.{0} PUnit.{1} 0 (𝓡 4)) :=
  charPairBundledEmpty

/-- **The residual hypothesis, in full**: a derived-basis realization for the `(σ₈, ∅)` doubling
ends whose computed kernel is Taylor-vanishing + jointly Lagrangian for the UN-reversed 8-fold odd
form. By F4 this mentions NO bordism and NO ambient `W` — it is a statement about one abstract
compact-T2 pair. -/
def UnreversedDoublingRealization : Prop :=
  HasEndsRealization (charPairBundledSumStr sig4 sig4) emptyEnd

/-- **The e₈-kernel form of the residual hypothesis**: a realization whose computed kernel is
EXACTLY the reindexed e₈ graph (the round-4.5 exploit kernel). Mathematically satisfiable: the
8 `ℝP²`'s joined by a tree of arcs with four 2-cells attached along graph-of-`(J+I)` classes is a
compact Hausdorff CW pair with precisely this `H₁`-kernel — only the tree's missing CW/MV homology
machinery blocks its in-tree construction. -/
def E8MembraneRealization : Prop :=
  ∃ real : GeoRealizationTied
      (TopCat.of (charPairBundledSumStr sig4 sig4).surf.M)
      (TopCat.of emptyEnd.surf.M)
      (charPairBundledSumStr sig4 sig4).basis
      emptyEnd.basis,
    LinearMap.ker (transportedBInc real.toData)
      = blockSub ((graphSub phiLin).comap (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv))
          (⊤ : Submodule (ZMod 2) (Fin 0 → ZMod 2))

/-- **The algebra is fully discharged in-tree**: an e₈-kernel realization satisfies the residual
hypothesis — Taylor-vanishing and Lagrangian-ness of the e₈ graph for the un-reversed 8-fold odd
form are the retained §3/§4.5 engines (`L44_metabolic` + `IsMetabolic.reindex/orthSum`) verbatim.
Nothing but the topological realization itself remains. -/
theorem unreversedDoublingRealization_of_e8 (h : E8MembraneRealization) :
    UnreversedDoublingRealization := by
  obtain ⟨real, hker⟩ := h
  have hSe : IsMetabolic (Z4Quadratic.neg (stdQuadratic 0))
      (⊤ : Submodule (ZMod 2) (Fin 0 → ZMod 2)) :=
    ⟨fun l _ => by rw [Subsingleton.elim l 0]; exact (Z4Quadratic.neg (stdQuadratic 0)).q_zero,
     fun _ _ => Submodule.mem_top⟩
  have hSs : IsMetabolic (charPairSumStr sig4.toCharPairStr sig4.toCharPairStr).q
      ((graphSub phiLin).comap (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv)) :=
    L44_metabolic.reindex finSumFinEquiv
  have hmeta := hSs.orthSum hSe
  refine ⟨real, ?_, ?_⟩
  · show TaylorLegVanishes _ _ (LinearMap.ker (transportedBInc real.toData))
    rw [hker]
    exact hmeta.1
  · show JointLagrangian _ _ (LinearMap.ker (transportedBInc real.toData))
    rw [hker]
    exact hmeta.2

/-- **The round-4.5 killer witness, REBUILT on the flipped carrier** — conditional on the residual
hypothesis only. Item-1 admissibility comes from the provider (as for every op witness); `T2` of
the doubling cylinder is real; the membrane and its Taylor/Lagrangian data are the hypothesis. -/
theorem doubleKillerBorRealized_nonempty (prov : CharPairWProviderPinned (𝓡 4) 0)
    (h : UnreversedDoublingRealization) :
    Nonempty (CharPairBorRealized (doublingBordism s4M)
      (charPairBundledSumStr sig4 sig4) emptyEnd) := by
  obtain ⟨real, ht, hl⟩ := h
  have hT2W : T2Space (doublingBordism s4M).W := by
    haveI : T2Space rp4SM.M := rp4CharPair.toCharPairStr.t2
    exact inferInstanceAs
      (T2Space (((rp4SM.M ⊕ rp4SM.M) ⊕ (rp4SM.M ⊕ rp4SM.M)) × Set.Icc (0 : ℝ) 1))
  exact ⟨mkCharPairBorRealized prov (doublingBordism s4M) hT2W real ht hl⟩

/-- **`k₀ = 8 • [ℝP⁴] = 0` on the FLIPPED carrier, for every pinned provider — conditional on the
residual hypothesis.** The pre-flip §5 refutation replayed verbatim, with `doubleKillerBorTied`
replaced by the conditional realized witness. -/
theorem ktKernelRep_eq_zero_of_realization (h : UnreversedDoublingRealization)
    (prov : CharPairWProviderPinned (𝓡 4) 0) : ktKernelRepU prov = 0 := by
  have hT2W : T2Space (doublingBordism s4M).W := by
    haveI : T2Space rp4SM.M := rp4CharPair.toCharPairStr.t2
    exact inferInstanceAs
      (T2Space (((rp4SM.M ⊕ rp4SM.M) ⊕ (rp4SM.M ⊕ rp4SM.M)) × Set.Icc (0 : ℝ) 1))
  have key : T2DataBordismGrp.mk (pinPlusCharPairDataUntethered prov)
        ⟨s4M.sum s4M, charPairBundledSumStr sig4 sig4⟩
      = (0 : T2DataBordismGrp (pinPlusCharPairDataUntethered prov)) :=
    T2DataBordismGrp.mk_eq_of_bordant _
      ⟨doublingBordism s4M, hT2W, doubleKillerBorRealized_nonempty prov h⟩
  show (8 : ℕ) • ktRP4ClassU prov = 0
  have h84 : (8 : ℕ) • ktRP4ClassU prov
      = (4 : ℕ) • ktRP4ClassU prov + (4 : ℕ) • ktRP4ClassU prov := by
    rw [← add_nsmul]
  have h42 : (4 : ℕ) • ktRP4ClassU prov
      = (2 : ℕ) • ktRP4ClassU prov + (2 : ℕ) • ktRP4ClassU prov := by
    rw [← add_nsmul]
  have h2 : (2 : ℕ) • ktRP4ClassU prov = ktRP4ClassU prov + ktRP4ClassU prov :=
    two_nsmul _
  rw [h84, h42, h2]
  exact key

/-- **`KTNonSplitU` is refuted for every pinned provider, conditional on the residual hypothesis.**
Since the hypothesis is mathematically true (CW realization of the e₈ kernel), the W-D non-split
bit is mathematically FALSE on the flipped carrier — the binder must not open here. -/
theorem ktNonSplit_false_of_realization (h : UnreversedDoublingRealization)
    (prov : CharPairWProviderPinned (𝓡 4) 0) : ¬ KTNonSplitU prov :=
  fun hns => hns (ktKernelRep_eq_zero_of_realization h prov)

/-- The W-D binder pair is jointly unsatisfiable, conditional on the residual hypothesis. -/
theorem kt_binders_unsatisfiable_of_realization (h : UnreversedDoublingRealization)
    (prov : CharPairWProviderPinned (𝓡 4) 0) :
    ¬ (KTKernelCardU prov ∧ KTNonSplitU prov) :=
  fun hc => ktNonSplit_false_of_realization h prov hc.2

/-- `addOrderOf [ℝP⁴] ∣ 8` on the flipped carrier, conditional on the residual hypothesis —
the carrier's cyclic part is (at most) ℤ/8, not ℤ/16. -/
theorem ktRP4Class_addOrderOf_dvd_eight_of_realization (h : UnreversedDoublingRealization)
    (prov : CharPairWProviderPinned (𝓡 4) 0) :
    addOrderOf (ktRP4ClassU prov) ∣ 8 :=
  addOrderOf_dvd_of_nsmul_eq_zero (ktKernelRep_eq_zero_of_realization h prov)

/-- **The composed headline**: an e₈-kernel realization — one abstract compact-T2 pair, no `W`,
no manifold, no bordism — refutes the W-D non-split bit for every pinned provider. -/
theorem ktNonSplit_false_of_e8 (h : E8MembraneRealization)
    (prov : CharPairWProviderPinned (𝓡 4) 0) : ¬ KTNonSplitU prov :=
  ktNonSplit_false_of_realization (unreversedDoublingRealization_of_e8 h) prov

end SKEFTHawking.PinPlusCharPairFlipGate
