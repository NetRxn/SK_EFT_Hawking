import Mathlib
import SKEFTHawking.PinPlusCharPairData
import SKEFTHawking.PoincareDualityConstruct

/-!
# The Wu-sector split for bundled characteristic pairs (hcolD brick B0)

The opening brick of the hcolD staged-bordism lane (the dC / `SectorIsGeometric` arc): expose the
**v₂ split** on a bundled carrier. For `str : CharPairStrBundled I s`, the `hchar` tie says the
pushed-forward surface class `emb₊[Σ] ∈ H₂(s.M;ℤ/2)` represents the carrier's **Wu (cup-square)
functional** `a ↦ μ(a ⌣ a)` under the Kronecker pairing. Combined with Kronecker faithfulness
(`homology_eq_zero_of_kroneckerH` — a cohomology-separating-functional argument, hypothesis-free
over the field `ℤ/2`), this gives the exact dichotomy the Kirby–Taylor §5 terminal move branches
on:

* `emb₊[Σ] = 0` ⟺ the Wu functional vanishes identically (`WuNullCarrier`) — the sector where a
  same-carrier characteristic cap is homologically unobstructed;
* `emb₊[Σ] ≠ 0` ⟺ some `a` has `μ(a ⌣ a) = 1` — the sector where the KT move MUST change the
  carrier topology (the `ℝP⁴` fake-class lesson: `μ(x² ⌣ x²) = 1` forces a nonzero pushed class).

Downstream (B1/B2 of the hcolD brick table): `WuNullCarrier` is the branch hypothesis for the
`RankZeroSurfaceBoundingDatum` cap construction, and its negation routes to the
`TerminalCharacteristicExtensionDatum` topology-changing endpoint.
-/

namespace SKEFTHawking.PinPlusKTWuSectorSplit

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularPD4Instances SKEFTHawking.PoincareDualityWu
open SKEFTHawking.PoincareDualityConstruct
open SKEFTHawking.PinPlusCharPairData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
variable {s : SingularManifold PUnit k I}

/-- The pushed-forward characteristic-surface class `emb₊[Σ] ∈ H₂(s.M;ℤ/2)` of a bundled carrier —
the object whose vanishing the Wu-sector split classifies. -/
noncomputable def pushedSurfClass (str : CharPairStrBundled I s) :
    SingularHomologyMod2.Homology (TopCat.of s.M) 2 :=
  SingularFunctoriality.Homology.map
    (⟨str.emb, str.embSmooth.continuous⟩ :
      C(↑(TopCat.of str.surf.M), ↑(TopCat.of s.M))) 2 str.surfClass

/-- **`WuNullCarrier`** — the carrier's Wu (cup-square) functional vanishes identically:
`μ(a ⌣ a) = 0` for every `a ∈ H²(s.M;ℤ/2)`. The named branch hypothesis of the KT §5 terminal
move: on a `WuNullCarrier` a same-carrier characteristic cap is homologically unobstructed, while
on its negation the terminal bordism must change the carrier (hcolD bricks B1 vs B2). -/
def WuNullCarrier (_str : CharPairStrBundled I s) [T2Space s.M] [Nonempty s.M] : Prop :=
  ∀ a : SingularCohomologyMod2.Cohomology (TopCat.of s.M) 2,
    (poincareDual4Mid_of_closed (M := s.M)).mu (cupH24 a a) = 0

/-- **The Wu-sector split (hcolD B0)**: the pushed-forward characteristic-surface class vanishes
iff the carrier's Wu functional vanishes identically. Forward: `hchar` reads each `μ(a ⌣ a)` off
the Kronecker pairing against `emb₊[Σ]`, and pairing against `0` is `0`. Backward: if every
cohomology class pairs to zero against `emb₊[Σ]` (via `hchar` again), Kronecker faithfulness
(`homology_eq_zero_of_kroneckerH` — the separating-functional argument over `ℤ/2`) forces
`emb₊[Σ] = 0`. Substantive: the backward direction is exactly the "characteristic class is
homologically visible" content that killed the rank-0 fake-class exhibit on `ℝP⁴`. -/
theorem pushedSurfClass_eq_zero_iff_wuNull (str : CharPairStrBundled I s)
    [T2Space s.M] [Nonempty s.M] :
    pushedSurfClass str = 0 ↔ WuNullCarrier str := by
  constructor
  · intro h a
    rw [← str.hchar a]
    show SingularHomologyMod2.kroneckerH 2 a (pushedSurfClass str) = 0
    rw [h, map_zero]
  · intro h
    exact homology_eq_zero_of_kroneckerH 2 (pushedSurfClass str)
      (fun ω => (str.hchar ω).trans (h ω))

/-- The topology-changing sector, consumer-shaped: a single witness `a₀` with `μ(a₀ ⌣ a₀) ≠ 0`
forces the pushed surface class to be nonzero — no characteristic surface on this carrier is
null-homologous, so the KT terminal move cannot cap in place (brick-B2 routing). The `ℝP⁴`
generator `x²` is the canonical instance. -/
theorem pushedSurfClass_ne_zero_of_wu_witness (str : CharPairStrBundled I s)
    [T2Space s.M] [Nonempty s.M]
    (a₀ : SingularCohomologyMod2.Cohomology (TopCat.of s.M) 2)
    (ha₀ : (poincareDual4Mid_of_closed (M := s.M)).mu (cupH24 a₀ a₀) ≠ 0) :
    pushedSurfClass str ≠ 0 := by
  intro h
  exact ha₀ (((pushedSurfClass_eq_zero_iff_wuNull str).mp h) a₀)

/-- A carrier admitting an **empty** characteristic surface (i.e. `surfClass = 0` — in particular
any bundled structure whose `surf` is the empty 2-manifold) is `WuNullCarrier`: the Wu functional
vanishes identically. This is the "spin-ish ⟹ v₂ = 0" reading of `hchar`, the B1-branch entry
fact — plumbing over the split, recorded as the named handle B1 consumes. -/
theorem wuNull_of_surfClass_eq_zero (str : CharPairStrBundled I s)
    [T2Space s.M] [Nonempty s.M] (h0 : str.surfClass = 0) : WuNullCarrier str :=
  (pushedSurfClass_eq_zero_iff_wuNull str).mp
    (by unfold pushedSurfClass; rw [h0, map_zero])

/-- The contrapositive package for the `ℝP⁴`-type obstruction, stated on the split's vocabulary:
a Wu witness rules out ANY bundled structure carrying a null-homologous (in particular empty)
characteristic surface on this carrier. Strengthens `pushedSurfClass_ne_zero_of_wu_witness` to the
`surfClass`-level statement the fake-class kill used. -/
theorem surfClass_pushforward_witness (str : CharPairStrBundled I s)
    [T2Space s.M] [Nonempty s.M]
    (a₀ : SingularCohomologyMod2.Cohomology (TopCat.of s.M) 2)
    (ha₀ : (poincareDual4Mid_of_closed (M := s.M)).mu (cupH24 a₀ a₀) ≠ 0) :
    str.surfClass ≠ 0 := by
  intro h0
  exact pushedSurfClass_ne_zero_of_wu_witness str a₀ ha₀
    (by unfold pushedSurfClass; rw [h0, map_zero])

end SKEFTHawking.PinPlusKTWuSectorSplit
