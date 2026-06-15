/-
# Phase 5q.F W5 — the geometric Smith map's real line bundle `L_a` and its section zero locus

The genuine geometric Smith homomorphism (Tachikawa–Yonekura arXiv:1805.02772 §3.2, eqs 3.6–3.8)
sends a `spin[k]`-manifold `M` with a mod-2 class `a ∈ H¹(M; ℤ/2)` to the **Poincaré-dual
submanifold** `N = PD(a)`, defined as the zero locus of a generic section, transverse to the zero
section, of the **associated real line bundle** `L_a` — the rank-1 real vector bundle with structure
group `ℤ/2 ⊂ ℝˣ` (acting on the fibre `ℝ` by `±1`) determined by the class `a`. The tangent bundle
then splits `TM|_N ≅ TN ⊕ L_a|_N`, giving the Stiefel–Whitney inheritance
`w₁(N) = a`, `w₂(N) = w₂(M) − a²` (whence `w₂(N) = 0` under the Spin-ℤ₄ constraint —
`SymTFT/SmithMechanism.lean`).

This module ships the **load-bearing geometric core** of that construction on top of Mathlib's
genuine vector-bundle machinery (`Bundle.VectorBundleCore`) and the project's regular-value theorem
(`SmithRegularValueGeneral.levelSetIsManifold`):

## What is built (all kernel-pure: only {propext, Classical.choice, Quot.sound})

**1. The real line bundle `L_a` from `±1` cocycle data (`SignCocycle` → `VectorBundleCore`).** A
`SignCocycle` packages the honest combinatorial input of a real line bundle: an open cover
`baseSet : ι → Set B`, an index map `indexAt`, and a **`±1`-valued multiplicative cocycle**
`sign : ι → ι → B → ℝ` (`sign² = 1`, `sign i i = 1`, continuous, with the cocycle composition
`sign j k · sign i j = sign i k`). The associated `coordChange i j b := sign i j b • id_ℝ` satisfies
the three `VectorBundleCore` laws, so `lineBundleCore` is a genuine `VectorBundleCore ℝ B ℝ ι`, and
Mathlib's automatic `VectorBundleCore.vectorBundle` instance makes `lineBundleCore.Fiber` a real
`VectorBundle ℝ ℝ` of rank 1 — the genuine `L_a`. Every coordinate change is multiplication by `±1`,
i.e. the structure group is exactly `ℤ/2 ⊂ ℝˣ` (`coordChange_eq_sign_smul`, `sign_isUnit`).

**2. The section zero locus is a codim-1 submanifold (reusing the regular-value theorem).** A section
of `L_a` is read in a local trivialization as a real-valued **coordinate function** `B → ℝ`; the
zero locus of the section coincides with the zero locus of that coordinate function (the `±1`
coordinate changes are nonzero, so they preserve the zero set — `coordFun_zero_iff`,
`zeroLocus_coordFun_indep`). When the base is the model space `E` and the coordinate function is a
`C^∞` submersion (the transversality-to-the-zero-section hypothesis), the regular-value theorem
`SmithRegularValueGeneral.levelSetIsManifold` makes the zero locus a genuine `C^∞` codimension-1
manifold, with the inclusion `N ↪ E` a smooth embedding — `sectionZeroLocus_isManifold`,
`sectionZeroLocus_contMDiff_subtypeVal`. This is `N = PD(a)`.

**3. The Stiefel–Whitney inheritance `w₂(N) = 0` (bridge to `SmithMechanism`).** The Whitney split
`TM|_N = TN ⊕ L_a|_N` with `w₁(L_a|_N) = a|_N` gives `w₂(N) = w₂(M)|_N + a² ` which, under the
Spin-ℤ₄ constraint `w₂(M)|_N = a²`, vanishes — re-exported here through
`SymTFT.smith_w2_vanishes`/`smith_RP4_isPinPlus_via_mechanism` so that the present line-bundle
construction and the SW mechanism are tied (`sectionZeroLocus_w2_vanishes`,
`PD_RP4_isPinPlus`).

## Honest scope boundary

The input is the **`±1` cocycle / `VectorBundleCore` data**, not a classifying map out of a *singular*
cohomology class `a ∈ H¹(B; ℤ/2)`: realising the cocycle from a singular `H¹` class (a classifying
map `B → Bℤ/2 = ℝP^∞`) is the part Mathlib lacks (no singular cohomology classifying-space theory)
and is the declared boundary, exactly as `StiefelWhitney.lean` carries the cohomology side as a
predicate substrate. The line bundle itself, its rank-1 `VectorBundle ℝ ℝ` structure, the
section-zero-locus = coordinate-zero-locus identity, and the regular-value codim-1 manifold structure
are all built genuinely here. The `w₁(N) = a` / `w₂(N) = w₂(M) − a²` inheritance is the same tracked
mod-2 characteristic-class content as `SmithMechanism.lean`; its arithmetic core (`b² + b² = 0`) is
genuine and re-exported.

Kernel-pure; no axioms beyond Mathlib's core {propext, Classical.choice, Quot.sound}.

## References
  - Tachikawa–Yonekura, arXiv:1805.02772 §3.2 eqs 3.6–3.8 — the geometric Smith homomorphism / `PD(a)`.
  - Hason–Komargodski–Thorngren, arXiv:1910.14039 Thm 4.1 — spectra-free Smith iso.
  - Lawson–Michelsohn, *Spin Geometry* II.1.7 — Pin⁺ exists iff `w₂ = 0`.
  - `SKEFTHawking.SmithRegularValueGeneral` — the regular-value theorem (zero locus of a submersion).
  - `SKEFTHawking.SymTFT.SmithMechanism` — the `w₂(N) = 0` Stiefel–Whitney mechanism.
-/
import Mathlib
import SKEFTHawking.SmithRegularValueGeneral
import SKEFTHawking.SymTFT.SmithMechanism

namespace SKEFTHawking.SmithLineBundle

open scoped Topology Manifold
open Bundle

noncomputable section

/-! ## §1. The `±1` sign cocycle — the honest combinatorial input of a real line bundle -/

/-- **The `±1` cocycle data of a real line bundle.** This is the honest input boundary for the
associated bundle `L_a` of the geometric Smith construction: an open cover `baseSet` of the base `B`,
an index map `indexAt`, and a **multiplicative `ℤ/2`-valued cocycle** `sign : ι → ι → B → ℝ`
(`sign i j b ∈ {±1}`, encoded as `sign i j b ^ 2 = 1`) satisfying `sign i i = 1` on `baseSet i`, the
cocycle composition `sign j k b · sign i j b = sign i k b`, and continuity on overlaps. The structure
group is `ℤ/2 ⊂ ℝˣ`. From a class `a ∈ H¹(B; ℤ/2)` (a double cover) one obtains such data; realising
that step from *singular* `H¹` is the Mathlib-absent classifying-map content (see module docstring). -/
structure SignCocycle (B : Type*) [TopologicalSpace B] (ι : Type*) where
  /-- The open cover of the base on which the bundle is trivialised. -/
  baseSet : ι → Set B
  /-- Each `baseSet` is open. -/
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  /-- A choice of trivialising index for each base point. -/
  indexAt : B → ι
  /-- Each point lies in its chosen trivialising set. -/
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  /-- The `±1` transition function between charts `i` and `j`. -/
  sign : ι → ι → B → ℝ
  /-- The transition functions take values in `{±1}` (structure group `ℤ/2 ⊂ ℝˣ`). -/
  sign_sq : ∀ i j b, sign i j b ^ 2 = 1
  /-- The diagonal transition is the identity sign `+1` on its chart. -/
  sign_self : ∀ i, ∀ b ∈ baseSet i, sign i i b = 1
  /-- The transition functions are continuous on chart overlaps. -/
  continuousOn_sign : ∀ i j, ContinuousOn (sign i j) (baseSet i ∩ baseSet j)
  /-- The multiplicative cocycle composition `sign j k · sign i j = sign i k`. -/
  sign_comp : ∀ i j k, ∀ b ∈ baseSet i ∩ baseSet j ∩ baseSet k,
    sign j k b * sign i j b = sign i k b

namespace SignCocycle

variable {B : Type*} [TopologicalSpace B] {ι : Type*} (c : SignCocycle B ι)

/-- A sign value is `±1`, hence a unit of `ℝ` (the structure group is `ℤ/2 ⊂ ℝˣ`). -/
theorem sign_isUnit (i j : ι) (b : B) : IsUnit (c.sign i j b) :=
  ⟨⟨c.sign i j b, c.sign i j b, by rw [← sq]; exact c.sign_sq i j b,
    by rw [← sq]; exact c.sign_sq i j b⟩, rfl⟩

/-- A sign value is never zero (it is `±1`). This is what makes the `±1` coordinate change preserve
the zero set of a section. -/
theorem sign_ne_zero (i j : ι) (b : B) : c.sign i j b ≠ 0 := by
  intro h
  have h2 := c.sign_sq i j b
  rw [h] at h2
  norm_num at h2

/-! ## §2. The associated real line bundle `L_a` as a genuine `VectorBundleCore` -/

/-- The coordinate change of the line bundle: scaling the fibre `ℝ` by the `±1` sign,
`coordChange i j b = sign i j b • id_ℝ : ℝ →L[ℝ] ℝ`. -/
def coordChange (i j : ι) (b : B) : ℝ →L[ℝ] ℝ := c.sign i j b • ContinuousLinearMap.id ℝ ℝ

@[simp] theorem coordChange_apply (i j : ι) (b : B) (v : ℝ) :
    c.coordChange i j b v = c.sign i j b * v := by
  simp only [coordChange, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul]

/-- **The real line bundle `L_a`, as a `VectorBundleCore ℝ B ℝ ι`.** Rank-1 (`F = ℝ`), real
(`R = ℝ`), with every coordinate change `sign i j b • id` a multiplication by `±1` — i.e. structure
group `ℤ/2 ⊂ ℝˣ`. The three `VectorBundleCore` laws are exactly the diagonal-identity, continuity,
and multiplicative-cocycle properties of the `SignCocycle`. -/
def lineBundleCore : VectorBundleCore ℝ B ℝ ι where
  baseSet := c.baseSet
  isOpen_baseSet := c.isOpen_baseSet
  indexAt := c.indexAt
  mem_baseSet_at := c.mem_baseSet_at
  coordChange := c.coordChange
  coordChange_self := by
    intro i b hb v
    rw [coordChange_apply, c.sign_self i b hb, one_mul]
  continuousOn_coordChange := by
    intro i j
    -- `b ↦ sign i j b • id` is continuous on the overlap, since `sign i j` is and `· • id` is.
    have hsmul : Continuous (fun s : ℝ => s • (ContinuousLinearMap.id ℝ ℝ)) :=
      continuous_id.smul continuous_const
    exact hsmul.comp_continuousOn (c.continuousOn_sign i j)
  coordChange_comp := by
    intro i j k b hb v
    simp only [coordChange_apply]
    rw [← mul_assoc, c.sign_comp i j k b hb]

@[simp] theorem lineBundleCore_coordChange (i j : ι) (b : B) :
    (c.lineBundleCore).coordChange i j b = c.coordChange i j b := rfl

@[simp] theorem lineBundleCore_baseSet (i : ι) :
    (c.lineBundleCore).baseSet i = c.baseSet i := rfl

@[simp] theorem lineBundleCore_indexAt (b : B) :
    (c.lineBundleCore).indexAt b = c.indexAt b := rfl

/-- The fibre of the associated line bundle `L_a` over a base point. By the automatic
`VectorBundleCore.vectorBundle` instance this is a rank-1 real `VectorBundle ℝ ℝ`. -/
abbrev Fiber (b : B) : Type _ := (c.lineBundleCore).Fiber b

/-- The total space of the associated line bundle `L_a = Bundle.TotalSpace ℝ (c.Fiber)`. -/
abbrev TotalSpace : Type _ := (c.lineBundleCore).TotalSpace

/-- **`L_a` is a genuine rank-1 real vector bundle.** Mathlib's `VectorBundleCore.vectorBundle`
instance applies to `lineBundleCore`, giving `VectorBundle ℝ ℝ (c.Fiber)` — the honest associated
bundle of the Smith construction, whose `±1` structure group is `ℤ/2 ⊂ ℝˣ`. -/
example : VectorBundle ℝ ℝ (c.Fiber) := inferInstance

/-- Every coordinate change of `L_a` is multiplication by the `±1` sign — the `ℤ/2 ⊂ ℝˣ`
structure-group statement made explicit on the bundle. -/
theorem coordChange_eq_sign_smul (i j : ι) (b : B) :
    (c.lineBundleCore).coordChange i j b = c.sign i j b • ContinuousLinearMap.id ℝ ℝ := rfl

/-- Each coordinate change of `L_a` is a linear isomorphism of the fibre (it is a nonzero scaling),
confirming the structure group sits in `ℝˣ`. -/
theorem coordChange_isUnit_apply (i j : ι) (b : B) {v : ℝ} (hv : v ≠ 0) :
    (c.lineBundleCore).coordChange i j b v ≠ 0 := by
  rw [lineBundleCore_coordChange, coordChange_apply]
  exact mul_ne_zero (c.sign_ne_zero i j b) hv

/-! ## §3. Sections of `L_a`, their coordinate functions, and the (trivialization-independent)
zero locus -/

/-- A **section** of the line bundle `L_a`: a base-point-preserving map into the total space,
`σ : B → c.TotalSpace` with `(σ b).proj = b`. (The zero section is the canonical example.) -/
def IsSection (σ : B → c.TotalSpace) : Prop := ∀ b, (σ b).proj = b

/-- The **fibre-coordinate function** of a section, read in the *canonical* trivialization at each
base point: `sectionCoord σ b = (σ b).snd ∈ ℝ`. (By `VectorBundleCore.localTrivAt_apply` this is
exactly the second component `(localTrivAt b (σ b)).2`.) The section `σ` vanishes at `b` — i.e. its
value is the zero of the fibre — iff `sectionCoord σ b = 0`. This `ℝ`-valued function is the local
model on which the regular-value theorem operates. -/
def sectionCoord (σ : B → c.TotalSpace) : B → ℝ := fun b => (σ b).snd

@[simp] theorem sectionCoord_eq_localTrivAt (σ : B → c.TotalSpace) (b : B) :
    c.sectionCoord σ b = ((c.lineBundleCore).localTrivAt (σ b).proj (σ b)).2 := by
  rw [sectionCoord, (c.lineBundleCore).localTrivAt_apply (σ b)]

/-- The **section zero locus** `s⁻¹(0)` of `L_a`: the set of base points where the section is the
zero of the fibre, equivalently the zero locus of its canonical coordinate function. This is the set
underlying the Poincaré-dual submanifold `N = PD(a)`. -/
def sectionZeroLocus (σ : B → c.TotalSpace) : Set B :=
  SKEFTHawking.SmithRegularValue.zeroLocus (c.sectionCoord σ)

@[simp] theorem mem_sectionZeroLocus (σ : B → c.TotalSpace) (b : B) :
    b ∈ c.sectionZeroLocus σ ↔ (σ b).snd = 0 := Iff.rfl

/-- **The section's zero locus is trivialization-independent.** In *any* local trivialization
`localTriv i` over a chart point `b ∈ baseSet i`, the fibre coordinate `(localTriv i (σ b)).2`
vanishes iff the canonical coordinate `sectionCoord σ b` does — because the `±1` coordinate change is
nonzero, hence injective on the fibre. So `sectionZeroLocus` is well-defined: it does not depend on
the choice of trivialising chart. -/
theorem coordFun_zero_iff (σ : B → c.TotalSpace) (hσ : c.IsSection σ) (i : ι) {b : B}
    (_hb : b ∈ c.baseSet i) :
    ((c.lineBundleCore).localTriv i (σ b)).2 = 0 ↔ b ∈ c.sectionZeroLocus σ := by
  rw [mem_sectionZeroLocus, VectorBundleCore.localTriv_apply, hσ b, lineBundleCore_coordChange,
    coordChange_apply]
  simp only
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd h1 (c.sign_ne_zero _ i b)
    · exact h2
  · intro h
    rw [h]; exact mul_zero _

/-- Restated: the section zero locus equals, in any chart, the zero locus of the chart fibre
coordinate. Concretely `b ∈ s⁻¹(0)` iff the trivialised coordinate `(localTriv i (σ b)).2 = 0`
(for `b` in that chart). -/
theorem zeroLocus_coordFun_indep (σ : B → c.TotalSpace) (hσ : c.IsSection σ) (i j : ι) {b : B}
    (hi : b ∈ c.baseSet i) (hj : b ∈ c.baseSet j) :
    (((c.lineBundleCore).localTriv i (σ b)).2 = 0) ↔
      (((c.lineBundleCore).localTriv j (σ b)).2 = 0) := by
  rw [c.coordFun_zero_iff σ hσ i hi, c.coordFun_zero_iff σ hσ j hj]

end SignCocycle

/-! ## §4. The Poincaré-dual submanifold `N = PD(a)` — the section zero locus is a codim-1 manifold

When the base is the model normed space `E` and the section's coordinate function `sectionCoord σ`
is a `C^∞` **submersion** (transverse to the zero section: at every zero `x`, `fderiv (sectionCoord σ)
x ≠ 0`), the regular-value theorem `SmithRegularValueGeneral.levelSetIsManifold` makes the section
zero locus `s⁻¹(0)` a genuine `C^∞` codimension-1 manifold modelled on `EuclideanSpace ℝ (Fin (n-1))`,
with the inclusion `s⁻¹(0) ↪ E` a smooth embedding. This is `N = PD(a)`. -/

section PoincareDual

open SKEFTHawking.SmithRegularValueGeneral
open SKEFTHawking.SmithRegularValue (zeroLocus)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} (c : SignCocycle E ι)

/-- The **section transversality** hypothesis (transversality to the zero section): the coordinate
function `sectionCoord σ` of the section is a `C^∞` submersion, i.e. it is `C^∞` and its derivative is
surjective (nonzero, as a map `E → ℝ`) at every point of the zero locus. This is exactly the
hypothesis a *generic* section satisfies (Thom transversality); it is the analytic input that makes
`N = PD(a)` a smooth submanifold. -/
structure SectionTransverse (σ : E → c.TotalSpace) : Prop where
  /-- The section is base-point preserving. -/
  isSection : c.IsSection σ
  /-- The coordinate function is `C^∞`. -/
  contDiff : ContDiff ℝ ⊤ (c.sectionCoord σ)
  /-- The coordinate function is a submersion on its zero locus (transverse to the zero section). -/
  submersion : ∀ x ∈ c.sectionZeroLocus σ,
    LinearMap.range (fderiv ℝ (c.sectionCoord σ) x : E →ₗ[ℝ] ℝ) = ⊤

/-- **`N = PD(a)` is a `C^∞` manifold (the regular-value theorem applied to a transverse section).**
The section zero locus `s⁻¹(0) ⊆ E` of `L_a`, when the section is transverse to the zero section
(`SectionTransverse`), is a charted space over the fixed Euclidean model
`EuclideanSpace ℝ (Fin (finrank E - 1))` and a `C^∞` manifold of codimension 1 — directly via
`SmithRegularValueGeneral.levelSetIsManifold`. This is the genuine Poincaré-dual submanifold. -/
theorem sectionZeroLocus_isManifold (σ : E → c.TotalSpace) (h : SectionTransverse c σ) :
    @IsManifold ℝ _ (euclideanModel E) _ _ (euclideanModel E) _
      (modelWithCornersSelf ℝ (euclideanModel E)) ⊤ (zeroLocus (c.sectionCoord σ)) _
      (levelSetChartedSpace (c.sectionCoord σ) h.contDiff h.submersion) :=
  levelSetIsManifold (c.sectionCoord σ) h.contDiff h.submersion

/-- The charted-space structure on `N = PD(a)` over the fixed Euclidean codim-1 model. -/
@[reducible] noncomputable def sectionZeroLocusChartedSpace (σ : E → c.TotalSpace)
    (h : SectionTransverse c σ) :
    ChartedSpace (euclideanModel E) (zeroLocus (c.sectionCoord σ)) :=
  levelSetChartedSpace (c.sectionCoord σ) h.contDiff h.submersion

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The inclusion `N = PD(a) ↪ E` is a topological embedding.** -/
theorem sectionZeroLocus_isEmbedding_subtypeVal (σ : E → c.TotalSpace) :
    Topology.IsEmbedding (Subtype.val : zeroLocus (c.sectionCoord σ) → E) :=
  isEmbedding_subtypeVal (c.sectionCoord σ)

/-- **The inclusion `N = PD(a) ↪ E` is `C^∞`** — together with the topological embedding, `PD(a)` is
a *smoothly embedded* codim-1 submanifold of `E`. Via `SmithRegularValueGeneral.contMDiff_subtypeVal`
applied to the transverse section's coordinate function. -/
theorem sectionZeroLocus_contMDiff_subtypeVal (σ : E → c.TotalSpace) (h : SectionTransverse c σ) :
    letI := levelSetChartedSpace (c.sectionCoord σ) h.contDiff h.submersion
    ContMDiff (modelWithCornersSelf ℝ (euclideanModel E)) (modelWithCornersSelf ℝ E) ⊤
      (fun x : zeroLocus (c.sectionCoord σ) => (x : E)) :=
  contMDiff_subtypeVal (c.sectionCoord σ) h.contDiff h.submersion

/-- The codimension of `N = PD(a)` in `E` is exactly 1 (the Euclidean model has dimension
`finrank E - 1`): the dimension drop `d ↦ d - 1` the Smith map `s : Ω_d → Ω_{d-1}` produces. Stated
via the model dimension being `finrank E - 1` (when `E` is nonzero-dimensional). -/
theorem sectionZeroLocus_codim_one (hE : 0 < Module.finrank ℝ E) :
    Module.finrank ℝ (euclideanModel E) + 1 = Module.finrank ℝ E := by
  simp only [euclideanModel, finrank_euclideanSpace, Fintype.card_fin]
  omega

end PoincareDual

/-! ## §5. Stiefel–Whitney inheritance `w₁(N) = a`, `w₂(N) = w₂(M) − a²`, and `w₂(N) = 0`

The tangent bundle of the Poincaré-dual submanifold splits `TM|_N = TN ⊕ L_a|_N`, with `L_a|_N` the
restriction of the line bundle built in §2. Its first Stiefel–Whitney class is the restricted class
`w₁(L_a|_N) = a|_N =: b ∈ H¹(N; ℤ/2)` (so `w₁(N) = a|_N`). The Whitney sum formula then gives the
degree-2 inheritance `w₂(N) = w₂(M)|_N + b²`, which under the Spin-ℤ₄ constraint `w₂(M)|_N = b²`
vanishes (`b² + b² = 0`), so `N = PD(a)` is Pin⁺. This §re-exports the genuine mod-2 mechanism of
`SymTFT/SmithMechanism.lean` into the line-bundle setting, tying the present `L_a`/zero-locus
construction to the SW obstruction. The cup-product / restriction-map content is the same tracked
predicate-substrate gap as `StiefelWhitney.lean` (module docstring). -/

section StiefelWhitneyInheritance

open SKEFTHawking.SymTFT

/-- **The Stiefel–Whitney inheritance `w₂(N) = 0` for `N = PD(a)`.** Given that `N` carries a
Stiefel–Whitney structure with `b := w₁(L_a|_N)` (the restricted first class of the §2 line bundle,
i.e. `w₁(N) = a|_N`) and `c := w₂(M)|_N`, the Whitney split identity `w₂(N) = c + b²` and the
Spin-ℤ₄ constraint `c = b²` force `w₂(N) = b² + b² = 0` — so `N = PD(a)` admits a Pin⁺ structure.
This is `SymTFT.smith_w2_vanishes` instantiated for the line-bundle Poincaré dual: `w₂(N) = w₂(M) − a²`
specialised to `w₂(M) = a²`. -/
theorem sectionZeroLocus_w2_vanishes {N : Type*} [HasStiefelWhitney N]
    (b : CohomologyMod2 N 1) (c : CohomologyMod2 N 2)
    (hWhitney : HasStiefelWhitney.w (M := N) 2 = c + HasStiefelWhitney.cupSquare b)
    (hSpinZ4 : c = HasStiefelWhitney.cupSquare b) :
    IsPinPlusObstruction N :=
  smith_w2_vanishes b c hWhitney hSpinZ4

/-- **The generator `[RP⁵] ↦ [RP⁴] = PD(α)` is Pin⁺ by the line-bundle Smith mechanism.** With the
real line bundle `L_α` over `RP⁵` (`w₁ = α`), its zero-locus Poincaré dual `RP⁴ = PD(α)` inherits
`w₂(RP⁴) = w₂(RP⁵)|_{RP⁴} + α² = α² + α² = 0` (mod-2 binomials `C(6,2)=1`, `C(5,2)=0`), hence is Pin⁺.
Re-exports `SymTFT.smith_RP4_isPinPlus_via_mechanism` for the line-bundle construction. -/
theorem PD_RP4_isPinPlus : IsPinPlusObstruction RP4 :=
  smith_RP4_isPinPlus_via_mechanism

end StiefelWhitneyInheritance

end

end SKEFTHawking.SmithLineBundle
