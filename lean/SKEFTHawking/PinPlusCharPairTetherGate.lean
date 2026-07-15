/-
# Phase 5q.H W-A GATE ROUND 7 (fresh-context adversarial vacuity attack on the TETHERED carrier)

Adversarial gate findings against the RE-FLIPPED carrier (`pinPlusCharPairData` with
`Bor := CharPairBorRealizedTethered`, per-op provider `CharPairWProviderPerOp`, THE RE-FLIP
2026-07-15). Verdict: **CONDITIONAL PASS — the W-TETHER ITSELF HOLDS** (every round-6 F4/F5-class
attack on the tether is blocked, with kernel-encoded evidence below), **but ONE structural finding
survives from round 6's spec item 3 (F7-A, provider-inhabitability class, prose+spec like F6):
the per-op provider still quantifies over BARE manifolds, so it is mathematically uninhabitable
and every `∀ prov`-statement (the live W-D binders included) is vacuous until the quantifier is
narrowed to the cert-carrying family.**

## F7-A — THE PER-OP PROVIDER QUANTIFIES OVER BARE `s`, NOT CERT-CARRYING ENDS (F6 RECURS ONE
LEVEL DOWN; prose-class finding + frozen spec, kernel-encodable only with absent machinery).

`CharPairWProviderPerOp.cyl : ∀ {s : SingularManifold.{0} PUnit.{1} k I}, WAdmPinned
(reflCylinder s)` (and `doubling`, `mapCyl` likewise) quantifies over EVERY closed 4-manifold `s`
in the universe — no characteristic-pair certificate is consumed (`providerCylUnfiltered` /
`providerMapCylUnfiltered` below kernel-record the unfiltered instantiation). But a PINNED
`WAdmPinned (reflCylinder s)` forces the HONEST `w₂(W) = 0` on `W = s.M × I`
(`LefschetzWuPinned*` pin `μ`/`cup`/`sqOp` to the substrate; `MuPinned`'s `RelFundClassDatum.cls`
is forced by its `restricts` field — on a connected `W`, `H₅(W,∂W;ℤ/2) ≅ ℤ/2` leaves no freedom —
so `hwu : wuW2 P14 P23 = 0` is the genuine Wu-form `w₂(W) = v₂ + v₁² = 0`). Since
`w₂(s.M × I) = w₂(s.M)`, ANY closed 4-manifold with `w₂ ≠ 0` (`ℂP²`, `ℝP² × ℝP²`, …) makes its
`cyl` instance empty — hence `CharPairWProviderPerOp (𝓡 4) 0` is mathematically UNINHABITABLE.
The in-tree proof of emptiness needs a `w₂ ≠ 0` closed 4-manifold with its Wu tower (absent
machinery — exactly round 6's F6 epistemic state, which is why this is a prose+spec finding, per
the round-6 precedent).

Impact: the live W-D binder layer (`PinPlusKTExtension.KTKernelCard/KTNonSplit`, the `kt_*`
assembly) and every carrier theorem are `∀ prov`-quantified over an empty type — discharges AND
refutations alike would be vacuous. The W-D binder work must NOT open on this provider shape.

**FROZEN MINIMAL SPEC (round 7).** Narrow the three op fields to the family ACTUALLY CONSUMED —
op bordisms over CERT-CARRYING ends. Every use site already has the bundle in scope
(`cylBorTethered prov σ`, `negBorTethered prov σ`, `unitBor/commBor/assocBorTethered prov σ τ ρ`),
so thread it:

  * `cyl : ∀ {s} (σ : CharPairStrBundled I s), WAdmPinned (reflCylinder s)`
  * `doubling : ∀ {s} (σ : CharPairStrBundled I s), WAdmPinned (doublingBordism s)`
  * `mapCyl : ∀ {s t} (σ : CharPairStrBundled I s) (τ : CharPairStrBundled I t)
      (φ : Diffeomorph I I s.M t.M k) (hf : t.f ∘ φ = s.f), WAdmPinned (mapCylinder φ hf)`
  * `addClosure` unchanged (it already consumes the two witnesses' own pins).

  (The minimal honest filter is the carried `w₂ = 0` certificate `σ.cert : PinPlusCertK I s`;
  passing the full bundle is acceptable and matches the use sites.) The narrowed family is
  honest-inhabitable — `w₂(s.M) = 0 ⟹ w₂(s.M × I) = 0` — and its discharge seam is exactly
  Track 2's `CylinderWAdmPinned` engines (whose `hwu` residual is a per-`M` computation, honest
  for cert-carrying `M`; see `PinPlusCharPairBorTethered` §6). This terminates the recursion:
  the quantifier finally matches the honest mathematical family.

## The tether attacks — ALL BLOCKED (kernel-encoded evidence in §1–§3)

* **A-R7-1 (glue coverage / interior components — the round-7 brief's primary attack): BLOCKED,
  kernel-encoded.** The conjecture "extra closed components change H₁(Q) hence the kernel" is
  FALSE: `ker_transportedBInc_addClosedPiece` (§1) proves that extending ANY realization's
  membrane by ANY closed piece `C` (compact T2, any `H₁`) leaves the computed Taylor-leg kernel
  `ker (transportedBInc ·.toData)` UNCHANGED. Mechanism: `H₁(∂Q) → H₁(Q ⊔ C)` factors through the
  boundary-carrying component, and `H₁(inl)` is injective by the degree-1 ⊔-additivity
  (`splitHnEquiv`). Since `htaylor`/`hlag` consume ONLY the kernel, interior-component freedom
  admits NO new witnesses — the e₈-grade kernel cannot be steered by decorating a membrane with
  closed junk inside `W̊`, in `(ℝP⁴)⁴ × I` or anywhere else.

* **A-R7-2 (`b.e` degeneracy): BLOCKED by `Bordism`'s own fields + the witness's `hWT2`.**
  `he_inj : Function.Injective e` and `he_boundary : Set.range e = J.boundary W` leave no
  degenerate-`e` freedom; `s.M ⊕ t.M` is compact (`SingularManifold.compactSpace`) and the
  witness certifies `T2Space b.W`, so `e` is automatically a closed embedding onto `∂W`. The
  glue therefore anchors the membrane's boundary to the genuine boundary:
  `tethered_boundary_lands_on_boundary` (§2) kernel-encodes `ιW (ι x) ∈ ∂W` for EVERY boundary
  point of the membrane.

* **A-R7-3 (`chartQ` decorative?): BLOCKED — `ChartedSpace` has real content here.** Mathlib's
  `ChartedSpace H M` fields (`chartAt : M → OpenPartialHomeomorph M H`, `mem_chart_source`)
  force every point of `Q` to have an OPEN neighborhood homeomorphic to an OPEN subset of
  `ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)` (an `OpenPartialHomeomorph` has
  open source AND open target with continuity both ways — no vacuous global pseudo-chart
  exists). So `Q` is locally a topological 3-manifold-with-boundary: the round-6 CW pathologies
  (wedge points, 2-cell attachments, wrong-dimension strata) are excluded by invariance of
  domain. Notably the TETHER ALONE would NOT have blocked the round-6 identity-membrane replay
  (`ιW := b.e ∘ (σ.emb ⊔ τ.emb) ∘ (homσ ⊔ homτ)` is a genuine closed embedding of `Q = ∂Q` —
  compact into T2 — satisfying both glues BY CONSTRUCTION); it is `chartQ` that kills it
  (`Q = Σσ ⊔ Στ` is 2-dimensional — no open subset of a 3-dim half-space model is homeomorphic
  to an open subset of a surface), with `hlag`'s `not_jointLagrangian_bot` as the second,
  independent block in positive rank. Residuals honestly noted: no smooth-compatibility
  (`IsManifold`) is demanded (the module's recorded round-6 JUDGMENT), and `ι(∂Q)` is not tied
  to `Q`'s chart-boundary — both are freedom WITHIN honest membranes, not vacuity (the kernel
  is computed from the honest `H₁` regardless).

* **A-R7-4 (`homσ`/`homτ` freedom post-tether — does the glue bite?): BITES, kernel-encoded.**
  `glueSigma_pins_homSigma`/`glueTau_pins_homTau` (§2): given the geometry `(Q, ι, ιW)`, the glue
  determines
  the boundary identifications POINTWISE — any candidate value matching the glue equation IS
  `homσ x` (via `b.he_inj` + `Sum.inl_injective` + `σ.embInj`). The round-5 F2 gauge freedom is
  dead at the identification level too.

* **A-R7-5 (transport / factorization replay): BLOCKED at the type level** — `ιW : C(↑real.Q,
  b.W)` makes every witness `b`-specific; `mkCharPairBorRealizedTethered` REQUIRES the tether,
  which `HasEndsRealization` does not supply (the tethered module's §7 record). The round-7
  RESIDUAL is kernel-encoded here as `ktKernelRep_eq_zero_of_tethered_double` +
  `ktNonSplit_requires_no_tethered_double` (§3): to kill `8 • [ℝP⁴]` an exploit must now supply
  an actual bordism `b` (with `T2Space b.W` and pinned `w₂(W) = 0` admissibility) TOGETHER WITH a
  charted 3-dim membrane closed-embedded in THAT `b.W`, glued through `b.e`, whose computed
  `H₁`-kernel is the e₈ graph. Unlike round 6's residual (ONE abstract compact-T2 pair,
  mathematically TRUE via CW), this is genuinely open Kirby–Taylor geometry — the tether
  converted the exploit's residual into the honest completeness question. (For the in-tree
  `doublingBordism s4M` specifically it is DEAD: `W = s4M.M × I` has 4 components, each membrane
  component lands in one `W`-component, so tethered kernels are block-diagonal across the four
  `(ℝP⁴, ℝP⁴)`-column pairs — the e₈ graph `graph(J+I)` is not. Recorded as analysis; the ∃-`b`
  form above is what the binder discharge must exclude.)

* **A-R7-6 (empty-Σ sector): FILTERED honestly.** A rank-0 witness reduces to `T2Space b.W` +
  `WAdmPinned b` (empty boundary, trivial kernel, vacuous glue/Taylor/Lagrangian) — but (i) the
  ends that ADMIT rank-0 bundles are `hchar`-filtered (a nonzero characteristic pairing forces
  `Σ ≠ ∅`: `RP4CharPairWitness.no_empty_surface_bundle_on_rp4`), and (ii) the relating bordisms
  are `hwu`-filtered by the honest PINNED `w₂(W) = 0` — which for 5-manifolds is exactly Pin⁺
  existence. So the rank-0 sector is spin-sector bordism under honest Pin⁺-admissible bordisms —
  the intended KT §5 kernel content (`charPairBrown_of_rank_zero`), not a collapse channel.
  (Both filters presuppose F7-A's fix — with an empty provider type the question is moot.)

* **A-R7-7 (`eQ`/`mid` interior freedom): HARMLESS, mechanism verified.** `eQ` enters the
  witness ONLY through `ker (transportedBInc toData)` (gauge-invariance:
  `PinPlusCharPairGeoRealizationGate.ker_transportedBInc_gaugeQ`, cross-reference verified
  live); `mid` is pinned to `dim H₁(Q)` by `eQ`'s mere existence; no downstream consumer reads
  `mem.mid`/`mem.bInc` except through `L` (audited: `brown_eq`, `toTied`, the op regroupings).

* **A-R7-8 (frozen-exhibit hygiene): CLEAN.** `pinPlusCharPairDataUntethered`, `charPairBrownU`,
  `ktRP4ClassU`, `ktKernelRepU`, `KTNonSplitU`, `KTKernelCardU` are consumed by NO module outside
  `PinPlusCharPairFlipGate` (grep-audited); the registry fork
  `untethered-membrane-factors-relation`'s three backing theorems exist by exactly the names the
  registry lists and still state what it says they state (checked against
  `src/core/constants.py:3582`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTExtension
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
open SKEFTHawking.SingularCohomologyPairRestrict
open SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularDisjointUnion SKEFTHawking.SingularDisjointUnionHn
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.SingularCohomologyDisjointSum
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairSurfaceTie
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusCharPairAddRealization
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTVacuityGateWD
open SKEFTHawking.RP4Witness SKEFTHawking.RP4CharPairWitness

namespace SKEFTHawking.PinPlusCharPairTetherGate

/-! ## §1. A-R7-1 — interior closed components CANNOT steer the computed kernel.

The round-7 brief's primary attack conjectured that a membrane `Q ⊔ C` (an honest membrane plus a
closed component `C ⊆ W̊`) "changes `H₁(Q)` hence the kernel", re-admitting e₈-grade kernels. We
kernel-encode the refutation: the extension leaves `ker (transportedBInc ·.toData)` unchanged, for
EVERY realization and EVERY closed piece. Since `htaylor`/`hlag` consume only this kernel, the
interior-component freedom is (htaylor, hlag)-invisible. -/

variable {nσ nτ : ℕ} {Sσ Sτ : TopCat}
  {bσ : Cohomology Sσ 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)}
  {bτ : Cohomology Sτ 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)}

/-- **The attack constructor** — extend a derived-basis realization's membrane by an arbitrary
closed piece `C` (compact T2, arbitrary `H₁` basis): `Q ↦ Q ⊔ C`, `ι ↦ inlMap ∘ ι`, boundary data
and identifications UNCHANGED. This is exactly the "membrane ⊔ closed component inside `W̊`"
shape of the round-7 brief's attack 1. -/
noncomputable def addClosedPiece (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (C : TopCat) [T2Space (↑C : Type)] [CompactSpace (↑C : Type)] {mc : ℕ}
    (eC : Homology C 1 ≃ₗ[ZMod 2] (Fin mc → ZMod 2)) :
    GeoRealizationTied Sσ Sτ bσ bτ where
  bdry := d.bdry
  Q := sumSpace d.Q C
  U := d.U
  hU := d.hU
  bdryT2 := d.bdryT2
  bdryCompact := d.bdryCompact
  QT2 := by
    haveI := d.QT2
    exact inferInstanceAs (T2Space (↑d.Q ⊕ ↑C))
  QCompact := by
    haveI := d.QCompact
    exact inferInstanceAs (CompactSpace (↑d.Q ⊕ ↑C))
  ι := (inlMap d.Q C).comp d.ι
  hιce := by
    haveI := d.bdryCompact
    haveI := d.QT2
    haveI : T2Space (↑d.Q ⊕ ↑C) := inferInstance
    exact (continuous_inl.comp d.ι.continuous).isClosedEmbedding
      (Sum.inl_injective.comp d.hιce.injective)
  homσ := d.homσ
  homτ := d.homτ
  mid := d.mid + mc
  eQ := disjointSumHnEquiv.symm.trans
    ((d.eQ.prodCongr eC).trans
      ((LinearEquiv.sumArrowLequivProdArrow (Fin d.mid) (Fin mc) (ZMod 2) (ZMod 2)).symm.trans
        (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) finSumFinEquiv.symm)))

/-- `H₁(inl) : H₁(Q) → H₁(Q ⊔ C)` is INJECTIVE — through the degree-1 ⊔-additivity
`disjointSumHnEquiv`, `inl₊ w` corresponds to `(w, 0)`, a split injection. -/
theorem homology_map_inlMap_injective (Q C : TopCat) :
    Function.Injective ⇑(Homology.map (inlMap Q C) 1) := by
  have hcoord : ∀ w : Homology Q 1,
      (disjointSumHnEquiv (Q₁ := Q) (Q₂ := C)).symm (Homology.map (inlMap Q C) 1 w)
        = (w, 0) := by
    intro w
    rw [LinearEquiv.symm_apply_eq, disjointSumHnEquiv_apply, map_zero, add_zero]
  intro a b hab
  have h2 : ((a, 0) : Homology Q 1 × Homology C 1) = (b, 0) := by
    rw [← hcoord a, ← hcoord b, hab]
  exact congrArg Prod.fst h2

/-- **A-R7-1, THE KERNEL-ENCODED REFUTATION of the steering conjecture**: extending a membrane by
ANY closed piece leaves the computed Taylor-leg kernel UNCHANGED. `H₁(∂Q) → H₁(Q ⊔ C)` factors
through the boundary-carrying component, and `H₁(inl)` is injective — so the kernel a tethered
witness's `htaylor`/`hlag` consume is blind to interior components. No decoration of a membrane
with closed junk (in `(ℝP⁴)⁴ × I` or anywhere) can steer the kernel toward the e₈ graph. -/
theorem ker_transportedBInc_addClosedPiece (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (C : TopCat) [T2Space (↑C : Type)] [CompactSpace (↑C : Type)] {mc : ℕ}
    (eC : Homology C 1 ≃ₗ[ZMod 2] (Fin mc → ZMod 2)) :
    LinearMap.ker (transportedBInc (addClosedPiece d C eC).toData)
      = LinearMap.ker (transportedBInc d.toData) := by
  have hker : LinearMap.ker (Homology.map (addClosedPiece d C eC).toData.ι 1)
      = LinearMap.ker (Homology.map d.toData.ι 1) := by
    show LinearMap.ker (Homology.map (X := d.bdry) (Y := sumSpace d.Q C)
        ((inlMap d.Q C).comp d.toData.ι) 1)
      = LinearMap.ker (Homology.map (X := d.bdry) (Y := d.Q) d.toData.ι 1)
    rw [Homology.map_comp, LinearMap.ker_comp,
      LinearMap.ker_eq_bot.mpr (homology_map_inlMap_injective d.Q C), Submodule.comap_bot]
  rw [transportedBInc_ker, transportedBInc_ker, hker]
  rfl

/-! ## §2. A-R7-2 / A-R7-4 — the tether's glue genuinely bites.

Two kernel-encoded records: (i) the membrane's ENTIRE boundary lands on the bordism's honest
boundary `∂W = range b.e` (the glue + `he_boundary` anchor — no interior-of-`W` escape for
`ι(∂Q)`, answering the round-7 brief's `b.e`-degeneracy attack); (ii) the glue DETERMINES the
boundary identifications `homσ`/`homτ` pointwise given the geometry — the identification carries
zero residual gauge freedom (the round-5 F2 freedom is dead at this level too). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
variable {s t : SingularManifold.{0} PUnit.{1} k I}
variable {b : Bordism (I.prod (𝓡∂ 1)) s t}
variable {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}

/-- **A-R7-2: the tethered membrane's boundary lands on `∂W`.** For every point of `∂Q`, the
tether image `ιW (ι x)` lies in the bordism's honest boundary `(I.prod (𝓡∂ 1)).boundary b.W` —
the glue routes it through `b.e`, whose range IS the boundary (`he_boundary`). The membrane is
anchored to the bordism's boundary structure, not to an arbitrary subset of `W`. -/
theorem tethered_boundary_lands_on_boundary (β : CharPairBorRealizedTethered b σ τ)
    (x : ↑β.real.bdry) :
    β.ιW (β.real.ι x) ∈ (I.prod (𝓡∂ 1)).boundary b.W := by
  by_cases hx : x ∈ β.real.U
  · have hglue := β.glueσ ⟨x, hx⟩
    have hincl : β.real.ι (subInclCM β.real.U ⟨x, hx⟩) = β.real.ι x := rfl
    rw [hincl] at hglue
    rw [hglue, ← b.he_boundary]
    exact Set.mem_range_self _
  · have hglue := β.glueτ ⟨x, hx⟩
    have hincl : β.real.ι (subInclCM β.real.Uᶜ ⟨x, hx⟩) = β.real.ι x := rfl
    rw [hincl] at hglue
    rw [hglue, ← b.he_boundary]
    exact Set.mem_range_self _

/-- **A-R7-4 (σ): the glue PINS `homσ` pointwise.** Any candidate end-point `y` whose `b.e`-image
matches the tether image of a σ-boundary point IS `homσ x`: the identification is determined by
`(ι, ιW, b.e, σ.emb)` — via `b.he_inj`, `Sum.inl_injective`, and `σ.embInj`. No residual gauge
freedom survives in the boundary identification once the tether is fixed. -/
theorem glueSigma_pins_homSigma (β : CharPairBorRealizedTethered b σ τ)
    (x : ↑(sub β.real.U)) (y : σ.surf.M)
    (hy : β.ιW (β.real.ι (subInclCM β.real.U x)) = b.e (Sum.inl (σ.emb y))) :
    β.real.homσ x = y :=
  σ.embInj (Sum.inl_injective (b.he_inj ((β.glueσ x).symm.trans hy)))

/-- **A-R7-4 (τ): the glue PINS `homτ` pointwise** (mirror). -/
theorem glueTau_pins_homTau (β : CharPairBorRealizedTethered b σ τ)
    (x : ↑(sub β.real.Uᶜ)) (y : τ.surf.M)
    (hy : β.ιW (β.real.ι (subInclCM β.real.Uᶜ x)) = b.e (Sum.inr (τ.emb y))) :
    β.real.homτ x = y :=
  τ.embInj (Sum.inr_injective (b.he_inj ((β.glueτ x).symm.trans hy)))

/-! ## §3. A-R7-5 — THE ROUND-7 RESIDUAL, kernel-encoded on the TETHERED carrier.

Round 6's F5 reduced the W-D-killing exploit to ONE abstract compact-T2 pair (mathematically TRUE
via CW). On the tethered carrier the same reduction now REQUIRES a bordism + tether: the two
theorems below record precisely (i) what an exploit must supply (`ktKernelRep_eq_zero_of_…`), and
(ii) the contrapositive geometric content the W-D binder discharge must establish
(`ktNonSplit_requires_…`): NO pinned-admissible Hausdorff bordism `b` from the 8-fold `ℝP⁴` ends
to `∅` carries a charted, closed-embedded, glued membrane whose computed kernel is Taylor-
vanishing + jointly Lagrangian for the UN-reversed 8-fold odd form. That is genuinely open
Kirby–Taylor geometry — not a CW bookkeeping gap. -/

/-- **The round-7 residual (i)**: a tethered exploit witness on ANY Hausdorff bordism from the
un-reversed 8-fold `ℝP⁴` ends to `∅` kills `8 • [ℝP⁴]` on the tethered carrier. This is the
round-6 arithmetic replayed against `pinPlusCharPairData` — the exploit's remaining obligation is
the (bordism + tether + e₈-kernel membrane) triple itself. -/
theorem ktKernelRep_eq_zero_of_tethered_double (prov : CharPairWProviderPerOp (𝓡 4) 0)
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) (s4M.sum s4M) (emptySM : SingularManifold.{0} PUnit.{1} 0 (𝓡 4)))
    (hT2 : T2Space b.W)
    (hβ : Nonempty (CharPairBorRealizedTethered b
      (charPairBundledSumStr sig4 sig4) charPairBundledEmpty)) :
    ktKernelRep prov = 0 := by
  have key : T2DataBordismGrp.mk (pinPlusCharPairData prov)
        ⟨s4M.sum s4M, charPairBundledSumStr sig4 sig4⟩
      = (0 : T2DataBordismGrp (pinPlusCharPairData prov)) :=
    T2DataBordismGrp.mk_eq_of_bordant _ ⟨b, hT2, hβ⟩
  show (8 : ℕ) • ktRP4Class prov = 0
  have h84 : (8 : ℕ) • ktRP4Class prov
      = (4 : ℕ) • ktRP4Class prov + (4 : ℕ) • ktRP4Class prov := by
    rw [← add_nsmul]
  have h42 : (4 : ℕ) • ktRP4Class prov
      = (2 : ℕ) • ktRP4Class prov + (2 : ℕ) • ktRP4Class prov := by
    rw [← add_nsmul]
  have h2 : (2 : ℕ) • ktRP4Class prov = ktRP4Class prov + ktRP4Class prov :=
    two_nsmul _
  rw [h84, h42, h2]
  exact key

/-- **The round-7 residual (ii), contrapositive form** — the PRECISE geometric obligation of the
W-D non-split discharge: `KTNonSplit prov` holds ONLY IF no Hausdorff bordism from the un-reversed
8-fold `ℝP⁴` ends to `∅` carries a tethered witness. The binder discharge must exclude exactly
this family of (bordism, membrane) pairs — the honest KT §5 content, now with the membrane forced
inside the bordism. -/
theorem ktNonSplit_requires_no_tethered_double (prov : CharPairWProviderPerOp (𝓡 4) 0)
    (hns : KTNonSplit prov)
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) (s4M.sum s4M) (emptySM : SingularManifold.{0} PUnit.{1} 0 (𝓡 4)))
    (hT2 : T2Space b.W) :
    IsEmpty (CharPairBorRealizedTethered b
      (charPairBundledSumStr sig4 sig4) charPairBundledEmpty) := by
  by_contra h
  rw [not_isEmpty_iff] at h
  exact hns (ktKernelRep_eq_zero_of_tethered_double prov b hT2 h)

/-! ## §4. F7-A — the provider-width demonstrators (the kernel-checked record that NO certificate
is consumed by the per-op quantifiers; the finding itself is prose+spec in the header, per the
round-6 F6 precedent — the in-tree emptiness proof needs a `w₂ ≠ 0` 4-manifold's Wu tower). -/

/-- **F7-A demonstrator (cyl)**: the per-op provider hands PINNED cylinder admissibility for EVERY
closed 4-manifold `s` — instantiating at `s` consumes NO characteristic-pair certificate. For any
`s` with `w₂(s.M) ≠ 0` (e.g. `ℂP²`), the target type is mathematically empty (the pins force the
honest `w₂(s.M × I) = 0`), so the provider type itself is uninhabitable. -/
def providerCylUnfiltered (prov : CharPairWProviderPerOp I k)
    (s : SingularManifold.{0} PUnit.{1} k I) : WAdmPinned (reflCylinder s) :=
  prov.cyl

/-- **F7-A demonstrator (mapCyl)**: likewise for EVERY diffeomorphism's mapping cylinder — the
quantifier ranges over all closed 4-manifold pairs, cert-free. -/
def providerMapCylUnfiltered (prov : CharPairWProviderPerOp I k)
    {s t : SingularManifold.{0} PUnit.{1} k I} (φ : Diffeomorph I I s.M t.M k)
    (hf : t.f ∘ φ = s.f) : WAdmPinned (mapCylinder φ hf) :=
  prov.mapCyl φ hf

/-- **F7-A demonstrator (doubling)**: likewise for the doubling bordism over EVERY closed
4-manifold. -/
def providerDoublingUnfiltered (prov : CharPairWProviderPerOp I k)
    (s : SingularManifold.{0} PUnit.{1} k I) : WAdmPinned (doublingBordism s) :=
  prov.doubling

end SKEFTHawking.PinPlusCharPairTetherGate
