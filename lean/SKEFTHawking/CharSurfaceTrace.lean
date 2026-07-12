/-
# Phase 5q.H (N2 · pin⁻-on-low-dimensional-manifolds vocabulary) — the framed circle's
`Ω₁^{Spin} ≅ ℤ/2` bit, the surgery-trace datum, and Taylor Lemma 1.2's FULL ⟺ (now stateable)

Round 1's E2 layer (`CharSurfaceCircle`) froze only the DESCENT direction of Taylor `0802.0111`
Lemma 1.2, because the CONVERSE ("extends over the trace ⟹ q(S¹) = 0") was honestly un-stateable:
"extends" needs (i) the trace-of-surgery 3-manifold `(F×I) ∪_{S¹×D¹} (D²×D¹)` as an object and
(ii) a Pin⁻-structure-on-3-manifolds vocabulary — equivalently (DAG item A5,
`Lit-Search/Phase-5qH/ABK_injectivity_routes_lemma_DAG_20260703.md`) the `Ω₁^{Spin} ≅ ℤ/2`
framed-circle bounding invariant — and every enhancement-level surrogate for "extends" is either
false or a tautology. This module supplies that vocabulary at the DATA level, in the same
enhancement-first idiom as `CharSurfaceBounding`/`CharSurfaceCircle`:

* `FramedCircle` — a framed embedded-circle datum: the embedded circle, the trivial-normal-bundle
  shadow (`S¹•S¹ = 0`, as data), and its `Ω₁^{Spin} ≅ ℤ/2` class `spinClass` as INDEPENDENT data
  (`0` = the induced spin structure bounds, `1` = the Lie/non-bounding framing). The enhancement
  alone cannot express this bit — carrying it as data is what makes the ⟺'s LHS stateable.
* `FramedCircle.SpinClassDetectsQ` — **statement freeze** of the circle-level `q` definition via
  induced framings (Taylor's Lemma 1.2 proof paragraph; GM-normalizations report §1):
  `embed2 spinClass = q(S¹)`, i.e. `Ω₁^{Spin} ≅ ℤ/2` detects `q(S¹) ∈ {0,2} ⊂ ℤ/4`. All the
  {0,2}-detection arithmetic is DERIVED now (`spinClass` is the `toZ2`-reduction of `q`;
  `spinClass = 0 ↔ q = 0`; evenness of `q` on framed circles), plus the KT-LMS torsor action at
  the framed-circle datum level (`shiftEnh`: detection-transported, 2-torsion on values).
* `TraceData` — the trace-of-surgery 3-manifold as DATA, not a construction: a compact
  3-manifold-with-boundary in the same collar encoding as `BordismGroup.Bordism` /
  `PinCharSurface.Bounding` (one smooth injection of `F ⊔ F'` onto `∂V`), together with the
  class-level surgery tie (the far end's `H₁` IS the pair complement of the surgery pair).
* `TraceData.PinExtendsOverTrace` — the pin⁻-extension-over-the-trace Prop (the ⟺'s LHS): the
  framed circle's `Ω₁^{Spin}` class bounds AND the far-end enhancement is the descended one.
* `PinCharSurface.TaylorSurgeryTrace` — **statement freeze, Taylor `0802.0111` Lemma 1.2, the
  FULL ⟺**, with exact debt accounting proved around it: the converse direction is DERIVED from
  the detection freeze (`qVal_eq_zero_of_spinClass_eq_zero`), the full ⟺ is EQUIVALENT to its
  descent half (`taylorSurgeryTrace_iff_taylorTraceDescends`), and it SUBSUMES the round-1 freeze
  (`taylorSurgeryDescends_of_taylorSurgeryTrace` — no double-counted geometric debt).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.CharSurfaceCircle
import SKEFTHawking.GMArfVanishing

namespace SKEFTHawking.CharSurface

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.SingularHomologyMod2 (Homology)
open scoped Manifold

/-! ## The {0,2}-detection arithmetic (pure `ZMod 4`, derived NOW) -/

/-- `embed2 b = 0` exactly when the bit vanishes (`embed2` is injective with `embed2 0 = 0`). -/
lemma embed2_eq_zero_iff (b : ZMod 2) : embed2 b = 0 ↔ b = 0 := by revert b; decide

/-- A `ZMod 4` value is in the image of `embed2` exactly when it lies in `{0, 2}` — the
arithmetic core of "`Ω₁^{Spin} ≅ ℤ/2` detects `q(S¹) ∈ {0,2} ⊂ ℤ/4`" (DAG item A5). -/
lemma exists_embed2_eq_iff (a : ZMod 4) : (∃ b : ZMod 2, embed2 b = a) ↔ a = 0 ∨ a = 2 := by
  revert a; decide

/-- Halving inverts `embed2` on its image: `embed2 b = a ⟹ b = a.val / 2` — the arithmetic shape
of the `Z4Quadratic.toZ2` reduction (`GMArfVanishing`). -/
lemma embed2_halved {b : ZMod 2} {a : ZMod 4} (h : embed2 b = a) :
    b = ((a.val / 2 : ℕ) : ZMod 2) := by subst h; revert b; decide

/-! ## The framed circle and its `Ω₁^{Spin} ≅ ℤ/2` class as data -/

variable {X : Type} [TopologicalSpace X] {k : WithTop ℕ∞}

/-- **A framed embedded-circle datum** in an enhanced characteristic surface `C` (the subject of
Taylor `0802.0111` Lemma 1.2: *"Let S¹ ⊂ F be an embedded circle with trivial normal bundle"*):
the embedded circle, the mod-2 shadow of the trivial normal bundle (`S¹•S¹ = 0`, carried as data
in the E1-checklist idiom), and the `Ω₁^{Spin} ≅ ℤ/2` class of the spin structure the framing
induces on the circle, carried as **independent data** — Taylor's proof paragraph (via the
GM-normalizations report §1, verbatim): *"A tubular neighborhood of the circle is now oriented
and so a Pin⁻-structure on F restricts to a Spin-structure on this neighborhood. The framing on
the normal bundle induces a stable framing of S¹ and q(S¹) ∈ MSpin₁ ≅ ℤ/2ℤ."* The enhancement
alone cannot express this bounding/non-bounding bit; its tie to the in-tree `q`-values is the
separate statement freeze `SpinClassDetectsQ`. -/
structure FramedCircle (C : PinCharSurface X k) extends EmbeddedCircle C where
  /-- The `Ω₁^{Spin} ≅ ℤ/2` class of the induced spin structure on the framed circle, as
  independent data: `0` = bounds, `1` = the Lie (non-bounding) framing. -/
  spinClass : ZMod 2
  /-- The trivial-normal-bundle shadow, as data: the circle class is `B`-isotropic
  (`S¹•S¹ ∈ ℤ/2` is the normal Euler number mod 2, which a framing kills). -/
  trivNormal : toEmbeddedCircle.selfPair = 0

namespace FramedCircle

variable {C : PinCharSurface X k}

/-- The framed circle's class in the enhancement's space (through the parent datum). -/
noncomputable abbrev cls (γ : FramedCircle C) : C.ι → ZMod 2 := γ.toEmbeddedCircle.cls

/-- The framed circle's enhancement value `q(S¹) ∈ ℤ/4` (through the parent datum). -/
noncomputable abbrev qVal (γ : FramedCircle C) : ZMod 4 := γ.toEmbeddedCircle.qVal

/-- **Statement freeze — the circle-level `q` definition via induced framings** (Taylor
`0802.0111` Lemma 1.2's proof paragraph, quoted on `FramedCircle`; DAG item A5: *"the induced
spin structure on the framed circle bounds (Ω₁^{Spin} ≅ ℤ/2 detects q(S¹) ∈ {0,2} ⊂ ℤ/4)"*; the
general `ℤ/4`-valued circle-wise definition is KT-LMS "just before Definition 3.5"): the framed
circle's `Ω₁^{Spin}` class computes the enhancement value, `embed2 spinClass = q(S¹)`.
Falsifiable: it forces `q(S¹) ∈ {0,2}` (`qVal_eq_zero_or_two_of_detects`) — a datum whose
underlying circle has the `ℝP²`-generator value `q = ±1` satisfies it for NEITHER spin bit — and
it pins `spinClass` to the `toZ2` reduction of `q` (`spinClass_eq_toZ2_of_detects`), so a
Lie-framed (`spinClass = 1`) circle with `q = 0` violates it. -/
def SpinClassDetectsQ (γ : FramedCircle C) : Prop := embed2 γ.spinClass = γ.qVal

/-- Detection forces the framed circle's enhancement value into `{0, 2} ⊂ ℤ/4` — the A5
evenness (a framed circle is never an `ℝP²`-generator circle). -/
theorem qVal_eq_zero_or_two_of_detects {γ : FramedCircle C} (h : γ.SpinClassDetectsQ) :
    γ.qVal = 0 ∨ γ.qVal = 2 :=
  (exists_embed2_eq_iff γ.qVal).mp ⟨γ.spinClass, h⟩

/-- Under detection, the `Ω₁^{Spin}` class is exactly the `toZ2` halving reduction of the
enhancement value (`GMArfVanishing.toZ2`, the Arf datum reduction) evaluated at the circle
class. -/
theorem spinClass_eq_toZ2_of_detects {γ : FramedCircle C} (h : γ.SpinClassDetectsQ) :
    γ.spinClass = C.Q.toZ2 γ.cls :=
  embed2_halved h

/-- Under detection, **the spin structure bounds iff the circle is isotropic**:
`spinClass = 0 ↔ q(S¹) = 0` — the arithmetic half of Taylor Lemma 1.2's ⟺. -/
theorem spinClass_eq_zero_iff_of_detects {γ : FramedCircle C} (h : γ.SpinClassDetectsQ) :
    γ.spinClass = 0 ↔ γ.qVal = 0 := by
  rw [← h]; exact (embed2_eq_zero_iff _).symm

/-- Under detection, an isotropic framed circle has bounding induced spin structure — the
direction of `spinClass_eq_zero_iff_of_detects` the ⟺-freeze's converse consumes. -/
theorem qVal_eq_zero_of_spinClass_eq_zero {γ : FramedCircle C} (h : γ.SpinClassDetectsQ)
    (h0 : γ.spinClass = 0) : γ.qVal = 0 := by
  rw [← h, h0]; decide

/-! ### The KT-LMS torsor action at the framed-circle datum level -/

/-- **Changing the Pin⁻ structure under the framed circle** (KT-LMS Lemma 3.7 / DG Thm 3.12
torsor, at datum level): on the shifted surface `C.shiftEnh w` the same embedded circle carries
the spin bit `spinClass + B(w, cls)` — the `H¹(F;ℤ/2)`-torsor acts on the induced spin structure
of the framed circle through the Poincaré-dual pairing, exactly compensating the enhancement
shift `q ↦ q + embed2 (B w ·)` (`detects_shiftEnh_iff`). -/
noncomputable def shiftEnh (γ : FramedCircle C) (w : C.ι → ZMod 2) :
    FramedCircle (C.shiftEnh w) where
  toEmbeddedCircle := ⟨γ.f, γ.inj, γ.fund⟩
  spinClass := γ.spinClass + C.Q.B w γ.cls
  trivNormal := γ.trivNormal

@[simp] lemma shiftEnh_spinClass (γ : FramedCircle C) (w : C.ι → ZMod 2) :
    (γ.shiftEnh w).spinClass = γ.spinClass + C.Q.B w γ.cls := rfl

@[simp] lemma shiftEnh_cls (γ : FramedCircle C) (w : C.ι → ZMod 2) :
    (γ.shiftEnh w).cls = γ.cls := rfl

/-- **Detection is torsor-equivariant**: the shifted framed circle detects the shifted
enhancement iff the original detects the original — KT-LMS Lemma 3.7's compatibility at the
circle level, DERIVED (the `2·B(w, cls)` enhancement shift is matched by the `B(w, cls)` spin-bit
shift). -/
theorem detects_shiftEnh_iff (γ : FramedCircle C) (w : C.ι → ZMod 2) :
    (γ.shiftEnh w).SpinClassDetectsQ ↔ γ.SpinClassDetectsQ := by
  show embed2 (γ.spinClass + C.Q.B w γ.cls) = (C.Q.shift w).q γ.cls ↔ _
  rw [embed2_add, shift_q]
  exact ⟨fun h => add_right_cancel h, fun h => by rw [SpinClassDetectsQ] at h; rw [h]; rfl⟩

/-- The torsor action on the spin bit is an involution (value level; the surface-level involution
is `PinCharSurface.shiftEnh_shiftEnh`). -/
theorem shiftEnh_shiftEnh_spinClass (γ : FramedCircle C) (w : C.ι → ZMod 2) :
    ((γ.shiftEnh w).shiftEnh w).spinClass = γ.spinClass := by
  show γ.spinClass + C.Q.B w γ.cls + C.Q.B w γ.cls = γ.spinClass
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

end FramedCircle

/-! ## The surgery-trace datum: `(F×I) ∪_{S¹×D¹} (D²×D¹)` in the collar encoding -/

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H']

/-- **A surgery-trace datum** for the framed circle `γ` — the trace of the surgery, DAG item A5
(*"glue D²×D¹ to S¹×D¹"*, i.e. `(F×I) ∪_{S¹×D¹} (D²×D¹)`), as DATA, not a construction: a
compact `C^k` 3-manifold-with-boundary `V` (model `J`, one dimension up) whose boundary is
identified with `F ⊔ F'` by one smooth injection (the same collar encoding as
`BordismGroup.Bordism` and `PinCharSurface.Bounding`), where the far end `F'` carries the
CLASS-LEVEL surgery tie: its `H₁` is the pair complement of the surgery pair `(cls, z)`. The
class-level tie is pin-free smooth topology (the surgered surface's homology); the enhancement
descent is deliberately NOT a field — it is exactly what `PinExtendsOverTrace` asserts, so that
a trace datum exists for BOTH spin bits while the extension Prop separates them. -/
structure TraceData (J : ModelWithCorners ℝ E' H') (C : PinCharSurface X k)
    (γ : FramedCircle C) where
  /-- The far-end surface of the trace: the surgered enhanced surface (its enhancement is free
  data here; `PinExtendsOverTrace` is what ties it to the descended Pin⁻ shadow). -/
  C' : PinCharSurface X k
  /-- The transverse partner of the circle class. -/
  z : C.ι → ZMod 2
  /-- Transversality: `B(cls, z) = 1`. -/
  pairing : C.Q.B γ.cls z = 1
  /-- The class-level surgery tie: the far end's enhancement space IS the pair complement. -/
  e : (C'.ι → ZMod 2) ≃ₗ[ZMod 2] ↥(C.Q.pairComplement γ.cls z)
  /-- The trace 3-manifold-with-boundary. -/
  V : Type
  [topV : TopologicalSpace V]
  [chartV : ChartedSpace H' V]
  [mfdV : IsManifold J k V]
  [compactV : CompactSpace V]
  /-- The two boundary identifications, collar-encoded: a smooth injection of `F ⊔ F'`
  onto `∂V`. -/
  bdry : C.F.M ⊕ C'.F.M → V
  bdry_smooth : ContMDiff (𝓡 2) J k bdry
  bdry_inj : Function.Injective bdry
  bdry_boundary : Set.range bdry = J.boundary V

namespace TraceData

variable {J : ModelWithCorners ℝ E' H'} {C : PinCharSurface X k} {γ : FramedCircle C}

instance (T : TraceData J C γ) : TopologicalSpace T.V := T.topV
instance (T : TraceData J C γ) : ChartedSpace H' T.V := T.chartV
instance (T : TraceData J C γ) : IsManifold J k T.V := T.mfdV
instance (T : TraceData J C γ) : CompactSpace T.V := T.compactV

/-- **The Pin⁻ structure extends over the trace** — the LHS of Taylor `0802.0111` Lemma 1.2's ⟺
(verbatim: *"One can do surgery on this embedding and extend the Pin⁻-structure to the trace of
the surgery if and only if q(S¹) = 0"*), stated through the A5 vocabulary: the extension
criterion is that the induced spin structure on the framed circle bounds (*"extension over the
trace ⇔ the induced spin structure on the framed circle bounds"* — the `Ω₁^{Spin} ≅ ℤ/2` bit
carried by the datum vanishes), and the extension's restriction to the far boundary is the
DESCENDED enhancement (values agree through the class-level tie). Falsifiable in both conjuncts:
a Lie-framed circle (`spinClass = 1`) admits no extension over any trace, and a far end whose
enhancement is not the descent (e.g. a torsor translate of it) is not the trace restriction of
any extension. -/
def PinExtendsOverTrace (T : TraceData J C γ) : Prop :=
  γ.spinClass = 0 ∧ ∀ u, T.C'.Q.q u = C.Q.q (T.e u)

/-- An extending trace yields the round-1 surgered-surface datum (the descent's witness shape,
`CharSurfaceCircle.SurgeredSurface`) — the vocabulary bridge the reconciliation theorems ride. -/
def toSurgeredSurface (T : TraceData J C γ) (h : T.PinExtendsOverTrace) :
    SurgeredSurface C γ.toEmbeddedCircle where
  C' := T.C'
  z := T.z
  pairing := T.pairing
  e := T.e
  agree := h.2

omit [FiniteDimensional ℝ E'] in
/-- **An extension over the trace leaves the Brown invariant unchanged, with isotropy DERIVED**:
`β(F) = β(F')` for any extending trace of a detection-coherent framed circle — the trace-level
form of the surgery induction step, with `q(S¹) = 0` obtained from the extension itself
(`qVal_eq_zero_of_spinClass_eq_zero`) rather than hypothesized. -/
theorem brown_eq_of_pinExtends (T : TraceData J C γ) (hdet : γ.SpinClassDetectsQ)
    (hext : T.PinExtendsOverTrace) : C.Q.brown = T.C'.Q.brown :=
  brown_surgeredSurface (T.toSurgeredSurface hext)
    (γ.qVal_eq_zero_of_spinClass_eq_zero hdet hext.1)

end TraceData

/-! ## Taylor Lemma 1.2, the FULL ⟺ — stateable, frozen, reconciled -/

/-- **Statement freeze — Taylor `0802.0111` Lemma 1.2, the FULL ⟺** (DAG item A5, verbatim:
*"Let S¹ ⊂ F be an embedded circle with trivial normal bundle… One can do surgery on this
embedding and extend the Pin⁻-structure to the trace of the surgery if and only if
q(S¹) = 0"*): for every detection-coherent framed circle with homologically nontrivial class,
an extending trace exists iff `q(S¹) = 0`. What round 1 could not state, the new data carry:
`spinClass` names the `Ω₁^{Spin} ≅ ℤ/2` bit the enhancement cannot express (so the LHS is a
genuine condition, not the always-true existence of an abstract reduction datum), and
`TraceData` demands the actual compact trace 3-manifold with both boundary identifications (so
the ⟸ direction carries the geometric construction `(F×I) ∪ (D²×D¹)`, strictly more than the
round-1 `TaylorSurgeryDescends`). Hypotheses: detection-coherence is required (an incoherent
datum with `spinClass = 1`, `q = 0` falsifies the raw ⟸), and `cls ≠ 0` matches the pair-
complement shape of the class-level tie (the homologically trivial case has no transverse
partner; same exclusion as the round-1 freeze). Debt accounting is exact and PROVED: the ⟹
direction is carried entirely by the detection freeze (`qVal_eq_zero_of_spinClass_eq_zero`), so
this ⟺ is equivalent to its descent half (`taylorSurgeryTrace_iff_taylorTraceDescends`), and it
subsumes the round-1 descent freeze (`taylorSurgeryDescends_of_taylorSurgeryTrace`). -/
def PinCharSurface.TaylorSurgeryTrace (C : PinCharSurface X k)
    (J : ModelWithCorners ℝ E' H') : Prop :=
  ∀ γ : FramedCircle C, γ.SpinClassDetectsQ → γ.cls ≠ 0 →
    ((∃ T : TraceData J C γ, T.PinExtendsOverTrace) ↔ γ.qVal = 0)

/-- **The descent half of the ⟺, at trace level**: every detection-coherent, isotropic,
homologically nontrivial framed circle admits an extending trace — the surgery is performed and
the Pin⁻ structure descends over the genuine trace 3-manifold. This is the ⟺-freeze's ONLY
genuinely geometric content (`taylorSurgeryTrace_iff_taylorTraceDescends`), and it strictly
refines the round-1 `TaylorSurgeryDescends` by producing the trace `(F×I) ∪ (D²×D¹)` alongside
the surgered surface. -/
def PinCharSurface.TaylorTraceDescends (C : PinCharSurface X k)
    (J : ModelWithCorners ℝ E' H') : Prop :=
  ∀ γ : FramedCircle C, γ.SpinClassDetectsQ → γ.cls ≠ 0 → γ.qVal = 0 →
    ∃ T : TraceData J C γ, T.PinExtendsOverTrace

omit [FiniteDimensional ℝ E'] in
/-- **Exact debt accounting for the full ⟺** (PROVED): the Lemma 1.2 ⟺-freeze is EQUIVALENT to
its descent half. The converse direction ("extends ⟹ q = 0") costs nothing beyond the
detection freeze already carried by each coherent framed circle — mirroring Taylor's own proof,
where the converse IS the circle-level `q` definition read through `Ω₁^{Spin} ≅ ℤ/2`. -/
theorem PinCharSurface.taylorSurgeryTrace_iff_taylorTraceDescends (C : PinCharSurface X k)
    (J : ModelWithCorners ℝ E' H') : C.TaylorSurgeryTrace J ↔ C.TaylorTraceDescends J := by
  constructor
  · exact fun h γ hdet hne hq => (h γ hdet hne).mpr hq
  · intro h γ hdet hne
    exact ⟨fun ⟨_, hext⟩ => γ.qVal_eq_zero_of_spinClass_eq_zero hdet hext.1, h γ hdet hne⟩

omit [FiniteDimensional ℝ E'] in
/-- **The full ⟺ subsumes the round-1 descent freeze** (PROVED — no double-counted debt): a
surface satisfying `TaylorSurgeryTrace` satisfies `TaylorSurgeryDescends`. From an isotropic
embedded circle, equip the canonical bounding framing (`spinClass = 0`, detection-coherent since
`q = 0`; the trivial-normal-bundle shadow is forced by isotropy), extract the extending trace,
and forget the 3-manifold. -/
theorem PinCharSurface.taylorSurgeryDescends_of_taylorSurgeryTrace {C : PinCharSurface X k}
    {J : ModelWithCorners ℝ E' H'} (h : C.TaylorSurgeryTrace J) : C.TaylorSurgeryDescends := by
  intro γ hq hne
  let γ' : FramedCircle C := ⟨γ, 0, C.Q.B_self_eq_zero_of_q_eq_zero hq⟩
  have hdet : γ'.SpinClassDetectsQ := by
    show embed2 (0 : ZMod 2) = C.Q.q γ.cls
    rw [hq]; decide
  obtain ⟨T, hext⟩ := (h γ' hdet hne).mpr hq
  exact ⟨T.toSurgeredSurface hext⟩

end SKEFTHawking.CharSurface
