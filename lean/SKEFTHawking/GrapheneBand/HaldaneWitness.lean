import SKEFTHawking.GrapheneBand.DiracExpansion
import SKEFTHawking.TopologicalBand.BlochFHS
import SKEFTHawking.TopologicalBand.BlochFrameOfD

/-!
# The Haldane Chern witness and the cone Berry phase (Phase 6ED, Wave 3)

Waves 1–2 built graphene's honeycomb band structure — the structure factor, its Dirac points, the
linear dispersion, the mass gap. Phase 6CA built the *abstract* two-band Chern machinery — the
`blochPauli` `d·σ` substrate and the exact Fukui–Hatsugai–Suzuki lattice Chern number. This wave
closes the loop between them: **a named lattice model with a kernel-checked nonzero topological
invariant.**

## What ships

* **`coneBerryPhase_pi`** — the sublattice-pseudospin Berry phase of the *gapless* cone is exactly
  `π`, on a four-point loop enclosing the `K` Dirac point of Wave 1. Its winding is
  `coneWinding_two_pi` (`2π`); the contrast pair `flatWinding_zero` / `flatLoopBerryPhase_zero`
  shows a non-winding loop of the same construction carries `0`.
* **`haldaneFrame_latticeChern_eq_neg_one`** — the Haldane model at `t = t₂ = 1`, `φ = π/2`,
  `m = 1`, sampled on a `4 × 4` Brillouin torus, has FHS lattice Chern number `−1`. This is the
  repo's **first** nontrivial concrete Chern frame (see the coordination note below).
* **`haldane_trivial_phase_chern_zero`** — the same model at `m = 6`, outside the analytic window
  `|m| < 3√3 |t₂ sin φ|` of `haldane_mass_inversion_iff`, has `0`.
* **`haldane_massInversion_not_sufficient_at_N4`** — the same model at `m = 5`, **inside** that
  window, *also* has `0`. See the next section: this is the honest relationship between the
  invariant and the phase boundary, and it is not the one a first reading suggests.

## What the witness/anti-witness pair does and does not say

**Mass inversion is NOT SUFFICIENT for the `4 × 4` invariant to be nonzero.** The converse
direction — necessity, i.e. "invariant nonzero ⟹ masses inverted" — is **NOT proved here or
anywhere in this development**; it is sampled at the single point `m = 6`. (Scope corrected
2026-07-31 after a D11 Stage-13 BLOCKER: this header previously asserted necessity in bold, which
is the first substantive claim a reader meets, while the theorem docstrings below correctly
disclaim it.) It is
tempting — and wrong — to read the `m = 1` / `m = 6` pair as a classification, i.e. "the invariant
is `−1` inside the mass-inversion window and `0` outside it". The two sampled masses are consistent
with that reading, and nothing else is:

* the analytic window is `|m| < 3√3 ≈ 5.1962`;
* the **`4 × 4` lattice** transition sits at `|m| ≈ 3.3177`, strictly *inside* it;
* so on roughly 36 % of the window — every `m` with `3.318 ≲ |m| < 5.196` — the Dirac masses invert
  while `blochLatticeChern` reads `0`. `haldane_massInversion_not_sufficient_at_N4` pins this at
  `m = 5` with a kernel-checked `0` and a `norm_num`-backed `|5| < 3√3`.

This is **not** a degeneracy or a gauge artefact: the frame stays admissible across the whole range
(the north-pole condition and the overlap nonvanishing both hold at `m = 5`), so the `0` is a
genuine value of the invariant on that frame.

The cause is structural and grid-dependent. The `4 × 4` grid never samples `K` or `K′`, and its
extremal `haldaneNNN` is `±2` against the true `±3√3/2 ≈ ±2.598`, so the lattice sees a *smaller*
effective window than the continuum. The transition converges to `3√3` from below as `N` grows
(`N = 4 → 3.318`, `N = 8 → 4.805`, `N = 16 → 5.085`, `N = 32 → 5.170`), which is the expected FHS
behaviour, not a defect — but it means **no statement here may be phrased as "exactly where the
Dirac masses invert" at any fixed `N`.** `haldane_mass_inversion_iff` is a biconditional about the
**sign product of the two Dirac masses** and the analytic window; it says nothing about any Chern
number, and in particular does not supply the necessity direction. (Corrected 2026-07-31: this
sentence previously pointed at that lemma as "the correct necessary direction" and cited a
docstring sentence which the same remediation had already deleted.)

*(The "classification" framing was shipped on 2026-07-28 and retracted on 2026-07-29 after a
numerical audit located the `N = 4` transition. The theorems were all true; the prose around them
was not.)*

## Why no transcendental evaluation is needed (the architectural point)

`BlochFHS.lean` used to warn that a nontrivial frame-derived Chern value "requires the QWZ
transcendental evaluation (`Complex.arg` of `sin/cos` at generic momenta)". That would be true of
*evaluating* the plaquette phases, but `latticeChern` never needs their values. It is
`−∑ branchIndex (rawCurl)`, a sum of **integers**, and `∑ rawCurl = 0` by torus telescoping. So the
whole invariant is carried by *which `2π`-window* each raw curl falls in — a **bounding** problem,
not an evaluation problem. (That warning has been corrected in `BlochFHS.lean` accordingly.)

The machinery this needs is **model-independent and no longer lives here.** It was promoted on
2026-07-29 to:

* **`TopologicalBand.ArgSectors`** — the rational-enclosure `arg` sector calculus
  (`arg_cell_A`/`_B`/`_C`/`_D`, `abs_arg_lt_pi_div_four`, `branchIndex_eq_{zero,one}_of`), built on
  `Complex.tan_arg` and `Real.arctan` monotonicity, whose side-conditions are radical-free
  comparisons of a number's real and imaginary parts;
* **`TopologicalBand.BlochFrameOfD`** — the `d`-field → frame adapter (`lbVec`, `blochFrameOfD`,
  `linkArg_blochFrameOfD`) and the narrow-link triviality criterion
  (`blochLatticeChern_eq_zero_of_narrow{,_D}`).

Neither mentions graphene, so a later square-lattice (QWZ) spike consumes them directly instead of
importing this module.

At `N = 4` the momenta are `0, π/2, π, 3π/2`, so every `d`-vector in the table is *integral* and
each computation needs only four-digit enclosures of a handful of surds — but **which** surds
depends on the mass: `√2, √6, √10, √26` at `m = 1`, `√2, √26, √30, √34, √82` at `m = 5`, and
`√5, √37, √41, √45, √101` at `m = 6` (plus `√3` from the sector reference angles). The tightest
inequality in the `m = 1` argument (`19 − 6√10 > 0`, i.e. `361 > 360`) has slack `0.026`, and the
tightest window placement there has `1.64 rad` of margin. **No `native_decide`, no `Complex.arg`
evaluation, no new axioms.**

Separately: the link phases at `N = 4` are not rational multiples of `π` as far as we can tell, but
that is an unproven number-theoretic aside and nothing below depends on it — the point of the
sector calculus is precisely that it never has to decide such a question.

## Grid choice

`N = 4`. The constraint is **admissibility, and it is arithmetic in `N`:** whenever `3 ∣ N` the grid
samples the Dirac points `K = (2π/3, 4π/3)` and `K′`, where the `d`-vector is purely `±d₃`. At the
Dirac point carrying the *negative* mass the vector sits on the south pole, so `‖d‖ + d₃ = 0`, the
`lbVec` gauge is singular (`lbVec ![0,0,−c] = ![0,0]` for `c > 0`), and an overlap vanishes — the
frame is not admissible at all. This kills `N = 3`, `6`, `12`, `24`, … *(An earlier version of this
note attributed `N = 3`'s failure to a plaquette landing on the branch cut, and a companion roadmap
table offered `6 × 6` as a clean alternative. Both were wrong: the cause is Dirac-point sampling,
and `6 × 6` fails for exactly the same reason. Corrected 2026-07-29.)*

`N = 4` is therefore the smallest admissible grid (`N = 5`, `8`, `16`, `32` are also admissible);
exactly one of its sixteen plaquettes carries a branch correction.

## Sign convention

The value is `−1`, not `+1`. `FHSLatticeGauge` freezes `latticeChern = −∑ plaquetteBranch` (so that
`∑ plaquetteArg = 2π · latticeChern`), and the single nonzero branch index here is `+1`. The
overall sign is the orientation convention's, not the physics': `φ ↦ −φ` reverses the
time-reversal-breaking flux and flips it.

## 6CA coordination

**Guardrail branch B applies.** The separately-gated QWZ (square-lattice) spike has not landed, so
this Haldane witness is the repo's first nontrivial concrete Chern frame. The adapter it needed is
**not** duplicated per model: `blochFrameOfD`, the sector calculus and
`blochLatticeChern_eq_zero_of_narrow` were promoted into `TopologicalBand/` (see above) precisely so
that a QWZ spike consumes them without importing graphene. The roadmap guardrail against duplicated
adapter machinery is thereby satisfied structurally rather than by convention.

**Gauge independence.** `blochLatticeChern` is invariant under a per-site rephasing of the frame
(`TopologicalBand.blochLatticeChern_rephase`), so the `−1` below is a property of the sampled band,
not of the particular `lbVec` representative chosen to compute it.

**⚠ Guardrail (inherited from Waves 1–2).** Every statement is about the *stated* Haldane
tight-binding model on a *stated* finite grid. The `latticeChern` integer is the FHS lattice
invariant; it is not claimed equal to any continuum first Chern class (that comparison is a separate
deferred analytic program, per `FHSLatticeGauge`'s scope note). No claim about devices, transport,
or fabrication.

**Publication target:** bundle **D11**.
-/

-- This file is dominated by ~120 mechanically parallel lemmas (16 `d`-vector table entries, 64 link
-- brackets, 16 plaquettes, 8 loop-vertex evaluations) that deliberately share one tactic shape and
-- one `simp` set. Two style linters fire on exactly that uniformity: where a shared `simp` set
-- happens not to be needed at some index, and where `norm_num <;> nlinarith` happens to leave
-- exactly one goal. Family-wide uniformity is worth more here than per-index minimality.
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace SKEFTHawking.GrapheneBand

open Complex Real Matrix SKEFTHawking.Topological SKEFTHawking.TopologicalBand
open scoped BigOperators


/-! ## The Haldane model -/

/-- **The next-nearest-neighbour phase sum** `g(θ) = sin θ₁ + sin(θ₂ − θ₁) − sin θ₂`, the
antisymmetric triangular-sublattice sum whose value at the two Dirac points is `±3√3/2`. -/
noncomputable def haldaneNNN (θ : ℝ × ℝ) : ℝ :=
  Real.sin θ.1 + Real.sin (θ.2 - θ.1) - Real.sin θ.2

/-! ### The chart bridge: `haldaneNNN` IS the physical next-nearest-neighbour sum

Wave 1 remediated an exposure in which `structureFactor` was described in honeycomb-geometric terms
with no chart hypothesis, by shipping `IsHoneycombChart` / `IsHoneycombNeighbours` and the bridge
`neighbourSum_eq_structureFactor`. `haldaneNNN` reintroduces exactly that exposure one layer up: it
is described as "the antisymmetric triangular-sublattice sum", which is a geometric claim about
*vectors*, while the definition is a formula in Bloch phases. The three declarations below close
the gap the same way Wave 1 did. -/

/-- The three **next-nearest-neighbour** (triangular-sublattice) vectors of a honeycomb chart:
`b₁ = a₁`, `b₂ = a₂ − a₁`, `b₃ = −a₂`. These are the hops `haldaneNNN` sums over, and their
orientation is what fixes the sign of the time-reversal-breaking term. -/
def nnnVecs (a₁ a₂ : ℝ × ℝ) : Fin 3 → ℝ × ℝ := ![a₁, a₂ - a₁, -a₂]

/-- The three next-nearest-neighbour hops **close into a triangle**, `b₁ + b₂ + b₃ = 0`. This is
why the sum is antisymmetric under `k ↦ −k` and hence why it can carry a time-reversal-breaking
phase at all. -/
theorem nnnVecs_sum_zero (a₁ a₂ : ℝ × ℝ) :
    nnnVecs a₁ a₂ 0 + nnnVecs a₁ a₂ 1 + nnnVecs a₁ a₂ 2 = 0 := by
  simp [nnnVecs, Prod.ext_iff]

/-- **The bridge.** In the chart coordinates `θᵢ = ⟨k, aᵢ⟩`, the formula `haldaneNNN` *is* the
physical next-nearest-neighbour phase sum `Σⱼ sin⟨k, bⱼ⟩` — the object the Haldane Hamiltonian's
`t₂ e^{iφ}` term actually contributes. This is the `haldaneNNN` analogue of Wave 1's
`neighbourSum_eq_structureFactor`, and it is what licenses the geometric language in the
definition's docstring.

The **orientation** `(a₁, a₂ − a₁, −a₂)` is the geometric input the docstring's sign convention
depends on: replacing it by the reversed triple negates `haldaneNNN`, which is the `φ ↦ −φ` flip
that flips the Chern number. Naming the triple is what makes that convention checkable rather than
ambiguous. -/
theorem haldaneNNN_eq_nnnSum (a₁ a₂ k : ℝ × ℝ) :
    haldaneNNN (planeDot k a₁, planeDot k a₂)
      = ∑ j : Fin 3, Real.sin (planeDot k (nnnVecs a₁ a₂ j)) := by
  simp only [haldaneNNN, nnnVecs, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, planeDot]
  rw [show k.1 * (a₂ - a₁).1 + k.2 * (a₂ - a₁).2
        = (k.1 * a₂.1 + k.2 * a₂.2) - (k.1 * a₁.1 + k.2 * a₁.2) by simp [Prod.fst_sub, Prod.snd_sub]; ring,
    show k.1 * (-a₂).1 + k.2 * (-a₂).2 = -(k.1 * a₂.1 + k.2 * a₂.2) by simp; ring,
    Real.sin_neg]
  ring

/-- **The next-nearest-neighbour set of a honeycomb chart is itself a 120° triple** — equal lengths,
pairwise `120°`. So `haldaneNNN` really does sum over the *triangular sublattice* of the honeycomb,
and "antisymmetric triangular-sublattice sum" is a theorem about this file's own objects rather than
a description.

Together with `haldaneNNN_eq_nnnSum` this is the chart hypothesis Wave 1's remediation asks for: a
consumer identifying a physical device with this model declares `IsHoneycombChart (a₁, a₂)`, and
everything geometric said about `haldaneNNN` then follows. -/
theorem isHoneycombNeighbours_nnnVecs {a₁ a₂ : ℝ × ℝ} (h : IsHoneycombChart a₁ a₂) :
    IsHoneycombNeighbours (nnnVecs a₁ a₂) := by
  obtain ⟨hne, hlen, hang⟩ := h
  simp only [planeDot] at hlen hang
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [nnnVecs, planeDot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg,
      Prod.snd_neg] <;>
    first
      | exact hne
      | nlinarith [hlen, hang]

/-- **The Haldane `d`-vector.** Wave 1's chiral nearest-neighbour honeycomb `d` (scaled by the
hopping `t`) plus a `d₃` built from the sublattice mass `m` and the complex next-nearest-neighbour
hopping `t₂ e^{iφ}`:

    d(θ) = ( t·Re f(θ), −t·Im f(θ), m − 2 t₂ sin φ · g(θ) ).

The `φ`-dependent part is the time-reversal-breaking term; it is what makes the two Dirac masses
differ and therefore what a nonzero Chern number needs. The identity (Haldane `d₀`) piece
`2 t₂ cos φ ∑ cos` is omitted: it shifts both bands equally and changes neither the eigenvectors
nor any Chern number, and `blochPauli` carries no identity component by design. -/
noncomputable def haldaneD (t t₂ φ m : ℝ) (θ : ℝ × ℝ) : Fin 3 → ℝ :=
  ![t * (structureFactor θ).re, -(t * (structureFactor θ).im),
    m - 2 * t₂ * Real.sin φ * haldaneNNN θ]

/-- **Wave-1 compatibility.** With no next-nearest-neighbour phase and no mass, the Haldane
`d`-vector *is* Wave 1's honeycomb `d`-vector — so this model genuinely extends the graphene
band structure rather than replacing it. -/
theorem haldaneD_eq_honeycombD (t₂ : ℝ) (θ : ℝ × ℝ) :
    haldaneD 1 t₂ 0 0 θ = honeycombD θ := by
  unfold haldaneD honeycombD
  rw [Real.sin_zero]
  norm_num

theorem haldaneNNN_diracK : haldaneNNN diracK = 3 * Real.sqrt 3 / 2 := by
  have e1 : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
    rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  have e2 : Real.sin (4 * π / 3) = -(Real.sqrt 3 / 2) := by
    rw [show (4 * π / 3 : ℝ) = π / 3 + π by ring, Real.sin_add_pi, Real.sin_pi_div_three]
  show Real.sin (2 * π / 3) + Real.sin (4 * π / 3 - 2 * π / 3) - Real.sin (4 * π / 3) = _
  rw [show (4 * π / 3 - 2 * π / 3 : ℝ) = 2 * π / 3 by ring, e1, e2]
  ring

theorem haldaneNNN_diracK' : haldaneNNN diracK' = -(3 * Real.sqrt 3 / 2) := by
  have e1 : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
    rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  have e2 : Real.sin (4 * π / 3) = -(Real.sqrt 3 / 2) := by
    rw [show (4 * π / 3 : ℝ) = π / 3 + π by ring, Real.sin_add_pi, Real.sin_pi_div_three]
  have e3 : Real.sin (2 * π / 3 - 4 * π / 3) = -(Real.sqrt 3 / 2) := by
    rw [show (2 * π / 3 - 4 * π / 3 : ℝ) = -(2 * π / 3) by ring, Real.sin_neg, e1]
  show Real.sin (4 * π / 3) + Real.sin (2 * π / 3 - 4 * π / 3) - Real.sin (2 * π / 3) = _
  rw [e1, e2, e3]
  ring

/-- **The Dirac mass at `K`** is `m − 3√3 t₂ sin φ` — the whole `d`-vector collapses to its third
component there, because Wave 1's structure factor vanishes at `K`. -/
theorem haldaneD_diracK (t t₂ φ m : ℝ) :
    haldaneD t t₂ φ m diracK = ![0, 0, m - 3 * Real.sqrt 3 * t₂ * Real.sin φ] := by
  unfold haldaneD
  rw [honeycomb_gapless_at_diracK, haldaneNNN_diracK]
  norm_num
  ring

/-- **The Dirac mass at `K'`** is `m + 3√3 t₂ sin φ`: the *opposite* `t₂ sin φ` shift. The two
Dirac points see opposite masses — the entire mechanism of the Haldane phase. -/
theorem haldaneD_diracK' (t t₂ φ m : ℝ) :
    haldaneD t t₂ φ m diracK' = ![0, 0, m + 3 * Real.sqrt 3 * t₂ * Real.sin φ] := by
  unfold haldaneD
  rw [honeycomb_gapless_at_diracK', haldaneNNN_diracK']
  norm_num
  ring

/-- The gap at `K` is exactly `2|m − 3√3 t₂ sin φ|`. -/
theorem haldane_gap_diracK (t t₂ φ m : ℝ) :
    2 * Real.sqrt (dNormSq (haldaneD t t₂ φ m diracK))
      = 2 * |m - 3 * Real.sqrt 3 * t₂ * Real.sin φ| := by
  rw [haldaneD_diracK]
  unfold dNormSq
  norm_num [Real.sqrt_sq_eq_abs, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- The gap at `K'` is exactly `2|m + 3√3 t₂ sin φ|`. -/
theorem haldane_gap_diracK' (t t₂ φ m : ℝ) :
    2 * Real.sqrt (dNormSq (haldaneD t t₂ φ m diracK'))
      = 2 * |m + 3 * Real.sqrt 3 * t₂ * Real.sin φ| := by
  rw [haldaneD_diracK']
  unfold dNormSq
  norm_num [Real.sqrt_sq_eq_abs, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- **The topological window, as a mass inversion.** The two Dirac masses have *opposite signs*
exactly when `|m| < 3√3 |t₂ sin φ|`. This is a biconditional about the **sign product of the two
Dirac masses** and the window — it says nothing about any Chern number.

⚠️ Scope corrected 2026-07-31 (D11 Stage-13). This docstring previously added "the Chern number can
only be nonzero inside this window", i.e. the *necessity* direction. That is **not proved here or
anywhere in this development** — only sampled. The witness/anti-witness pair below is sampled on
either side of the window; sampling is not a necessity proof. -/
theorem haldane_mass_inversion_iff (t t₂ φ m : ℝ) :
    haldaneD t t₂ φ m diracK 2 * haldaneD t t₂ φ m diracK' 2 < 0
      ↔ |m| < |3 * Real.sqrt 3 * t₂ * Real.sin φ| := by
  rw [haldaneD_diracK, haldaneD_diracK']
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  set c := 3 * Real.sqrt 3 * t₂ * Real.sin φ with hc
  constructor
  · intro h
    nlinarith [sq_abs m, sq_abs c, abs_nonneg m, abs_nonneg c]
  · intro h
    nlinarith [sq_abs m, sq_abs c, abs_nonneg m, abs_nonneg c]

/-! ## The `4 × 4` discretized Brillouin torus -/

/-- The Bloch phase sampled at vertex `j` of a length-4 cycle: `θ = 2π j / 4 = π j / 2`. -/
noncomputable def bzPhase (j : ZMod 4) : ℝ := Real.pi * (j.val : ℝ) / 2

/-- The `4 × 4` Brillouin-zone sample point of a torus vertex. -/
noncomputable def bzPoint (k : Torus 4 4) : ℝ × ℝ := (bzPhase k.1, bzPhase k.2)

/-- **The Haldane `d`-field on the `4 × 4` discretized Brillouin torus** at the declared
parameters `t = t₂ = 1`, `φ = π/2`, with the mass `m` left free. -/
noncomputable def haldaneD44 (m : ℝ) (k : Torus 4 4) : Fin 3 → ℝ :=
  haldaneD 1 1 (Real.pi / 2) m (bzPoint k)

/-- The `4 × 4` Haldane `d`-field, expanded into base trigonometric values (the
next-nearest-neighbour term's angle difference is opened with `Real.sin_sub`, so every entry is a
value of `sin`/`cos` at one of the four sampled phases). -/
theorem haldaneD44_eq (m : ℝ) (k : Torus 4 4) :
    haldaneD44 m k
      = ![1 + Real.cos (bzPhase k.1) + Real.cos (bzPhase k.2),
          -(Real.sin (bzPhase k.1) + Real.sin (bzPhase k.2)),
          m - 2 * (Real.sin (bzPhase k.1)
              + (Real.sin (bzPhase k.2) * Real.cos (bzPhase k.1)
                  - Real.cos (bzPhase k.2) * Real.sin (bzPhase k.1))
              - Real.sin (bzPhase k.2))] := by
  unfold haldaneD44 haldaneD haldaneNNN bzPoint
  rw [Real.sin_pi_div_two, structureFactor_re, structureFactor_im, Real.sin_sub]
  norm_num

theorem bzPhase_zero : bzPhase 0 = 0 := by
  rw [bzPhase, show ((0 : ZMod 4)).val = 0 from rfl]; norm_num

theorem bzPhase_one : bzPhase 1 = Real.pi / 2 := by
  rw [bzPhase, show ((1 : ZMod 4)).val = 1 from rfl]; norm_num

theorem bzPhase_two : bzPhase 2 = Real.pi := by
  rw [bzPhase, show ((2 : ZMod 4)).val = 2 from rfl]; push_cast; ring

theorem bzPhase_three : bzPhase 3 = 3 * Real.pi / 2 := by
  rw [bzPhase, show ((3 : ZMod 4)).val = 3 from rfl]; push_cast; ring

theorem sin_three_pi_div_two : Real.sin (3 * Real.pi / 2) = -1 := by
  rw [show (3 * Real.pi / 2 : ℝ) = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi,
    Real.sin_pi_div_two]

theorem cos_three_pi_div_two : Real.cos (3 * Real.pi / 2) = 0 := by
  rw [show (3 * Real.pi / 2 : ℝ) = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi,
    Real.cos_pi_div_two, neg_zero]

/-! ### The `d`-vector table on the 16 sampled momenta

Every entry is `haldaneD44 m` evaluated by the base trigonometric values. The pattern of the third
components — `m`, `m − 4`, `m + 4` — is the discretized image of the `±3√3 t₂ sin φ` Dirac-mass
splitting of `haldaneD_diracK`/`haldaneD_diracK'`. -/

theorem hD44_00 (m : ℝ) : haldaneD44 m (0, 0) = ![3, 0, m] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_zero]

theorem hD44_01 (m : ℝ) : haldaneD44 m (0, 1) = ![2, -1, m] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_zero, bzPhase_one]

theorem hD44_02 (m : ℝ) : haldaneD44 m (0, 2) = ![1, 0, m] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_zero, bzPhase_two]

theorem hD44_03 (m : ℝ) : haldaneD44 m (0, 3) = ![2, 1, m] := by
  rw [haldaneD44_eq]
  norm_num [bzPhase_zero, bzPhase_three, sin_three_pi_div_two, cos_three_pi_div_two]

theorem hD44_10 (m : ℝ) : haldaneD44 m (1, 0) = ![2, -1, m] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_zero, bzPhase_one]

theorem hD44_11 (m : ℝ) : haldaneD44 m (1, 1) = ![1, -2, m] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_one]

theorem hD44_12 (m : ℝ) : haldaneD44 m (1, 2) = ![0, -1, m - 4] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_one, bzPhase_two]

theorem hD44_13 (m : ℝ) : haldaneD44 m (1, 3) = ![1, 0, m - 4] := by
  rw [haldaneD44_eq]
  norm_num [bzPhase_one, bzPhase_three, sin_three_pi_div_two, cos_three_pi_div_two]

theorem hD44_20 (m : ℝ) : haldaneD44 m (2, 0) = ![1, 0, m] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_zero, bzPhase_two]

theorem hD44_21 (m : ℝ) : haldaneD44 m (2, 1) = ![0, -1, m + 4] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_one, bzPhase_two]

theorem hD44_22 (m : ℝ) : haldaneD44 m (2, 2) = ![-1, 0, m] := by
  rw [haldaneD44_eq]; norm_num [bzPhase_two]

theorem hD44_23 (m : ℝ) : haldaneD44 m (2, 3) = ![0, 1, m - 4] := by
  rw [haldaneD44_eq]
  norm_num [bzPhase_two, bzPhase_three, sin_three_pi_div_two, cos_three_pi_div_two]

theorem hD44_30 (m : ℝ) : haldaneD44 m (3, 0) = ![2, 1, m] := by
  rw [haldaneD44_eq]
  norm_num [bzPhase_zero, bzPhase_three, sin_three_pi_div_two, cos_three_pi_div_two]

theorem hD44_31 (m : ℝ) : haldaneD44 m (3, 1) = ![1, 0, m + 4] := by
  rw [haldaneD44_eq]
  norm_num [bzPhase_one, bzPhase_three, sin_three_pi_div_two, cos_three_pi_div_two]

theorem hD44_32 (m : ℝ) : haldaneD44 m (3, 2) = ![0, 1, m + 4] := by
  rw [haldaneD44_eq]
  norm_num [bzPhase_two, bzPhase_three, sin_three_pi_div_two, cos_three_pi_div_two]

theorem hD44_33 (m : ℝ) : haldaneD44 m (3, 3) = ![1, 2, m] := by
  rw [haldaneD44_eq]
  norm_num [bzPhase_three, sin_three_pi_div_two, cos_three_pi_div_two]

/-! ### Link overlaps on the 4×4 torus

`hLink m μ k` is the raw lower-band overlap across the `μ`-link at `k`. The four *cell* lemmas
below are the workhorses: each takes the two `d`-vector evaluations plus three numeric
side-conditions and returns a closed `π/6`-wide bracket for the link's argument. Every one of the
32 links is one application. -/

/-- The raw lower-band overlap across the `μ`-link at `k`. -/
noncomputable def hLink (m : ℝ) (μ : Fin 2) (k : Torus 4 4) : ℂ :=
  frameOverlap (lbVec (haldaneD44 m k)) (lbVec (haldaneD44 m (shift 4 4 μ k)))

theorem hLink_re {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3]) :
    (hLink m μ k).re = a1 * b1 + a2 * b2
      + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
        * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)) := by
  rw [hLink, hs, lbOverlap_re, hk, hk']
  simp [dNormSq]

theorem hLink_im {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3]) :
    (hLink m μ k).im = a2 * b1 - a1 * b2 := by
  rw [hLink, hs, lbOverlap_im, hk, hk']
  simp

/-- The overlap is nonzero whenever its imaginary part is. -/
theorem hLink_ne_zero_of_im {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3])
    (h : a2 * b1 - a1 * b2 ≠ 0) : hLink m μ k ≠ 0 := by
  intro hz
  exact h (by rw [← hLink_im hs hk hk', hz, Complex.zero_im])

/-- Link bracket, **cell A**: `arg ∈ [0, π/6]`. -/
theorem hLink_cellA {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3])
    (h0 : 0 < a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
            * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)))
    (h1 : 0 ≤ a2 * b1 - a1 * b2)
    (h2 : Real.sqrt 3 * (a2 * b1 - a1 * b2)
            < a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
              * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2))) :
    0 ≤ (hLink m μ k).arg ∧ (hLink m μ k).arg ≤ Real.pi / 6 := by
  have hre := hLink_re hs hk hk'
  have him := hLink_im hs hk hk'
  obtain ⟨p, q⟩ := arg_cell_A (z := hLink m μ k) (by rw [hre]; exact h0) (by rw [him]; exact h1)
    (by rw [hre, him]; exact h2)
  exact ⟨p, q.le⟩

/-- Link bracket, **cell B**: `arg ∈ [−π/6, 0]`. -/
theorem hLink_cellB {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3])
    (h0 : 0 < a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
            * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)))
    (h1 : a2 * b1 - a1 * b2 ≤ 0)
    (h2 : -(a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
              * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)))
            < Real.sqrt 3 * (a2 * b1 - a1 * b2)) :
    -(Real.pi / 6) ≤ (hLink m μ k).arg ∧ (hLink m μ k).arg ≤ 0 := by
  have hre := hLink_re hs hk hk'
  have him := hLink_im hs hk hk'
  obtain ⟨p, q⟩ := arg_cell_B (z := hLink m μ k) (by rw [hre]; exact h0) (by rw [him]; exact h1)
    (by rw [hre, him]; exact h2)
  exact ⟨p.le, q⟩

/-- Link bracket, **cell C**: `arg ∈ [π/4, π/2]`. -/
theorem hLink_cellC {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3])
    (h0 : 0 < a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
            * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)))
    (h2 : a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
              * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2))
            < a2 * b1 - a1 * b2) :
    Real.pi / 4 ≤ (hLink m μ k).arg ∧ (hLink m μ k).arg ≤ Real.pi / 2 := by
  have hre := hLink_re hs hk hk'
  have him := hLink_im hs hk hk'
  obtain ⟨p, q⟩ := arg_cell_C (z := hLink m μ k) (by rw [hre]; exact h0)
    (by rw [hre, him]; exact h2)
  exact ⟨p.le, q.le⟩

/-- Link bracket, **cell D**: `arg ∈ [−π/2, −π/3]`. -/
theorem hLink_cellD {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3])
    (h0 : 0 < a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
            * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)))
    (h2 : a2 * b1 - a1 * b2
            < -(Real.sqrt 3 * (a1 * b1 + a2 * b2 + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
              * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2))))) :
    -(Real.pi / 2) ≤ (hLink m μ k).arg ∧ (hLink m μ k).arg ≤ -(Real.pi / 3) := by
  have hre := hLink_re hs hk hk'
  have him := hLink_im hs hk hk'
  obtain ⟨p, q⟩ := arg_cell_D (z := hLink m μ k) (by rw [hre]; exact h0)
    (by rw [hre, him]; exact h2)
  exact ⟨p.le, q.le⟩

/-- Narrow link (`|arg| < π/4`) from `|Im| < Re`. -/
theorem hLink_narrow {m : ℝ} {μ : Fin 2} {k k' : Torus 4 4} {a1 a2 a3 b1 b2 b3 : ℝ}
    (hs : shift 4 4 μ k = k')
    (hk : haldaneD44 m k = ![a1, a2, a3]) (hk' : haldaneD44 m k' = ![b1, b2, b3])
    (h : |a2 * b1 - a1 * b2| < a1 * b1 + a2 * b2
            + (a3 + Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2))
              * (b3 + Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2))) :
    |(hLink m μ k).arg| < Real.pi / 4 := by
  have hre := hLink_re hs hk hk'
  have him := hLink_im hs hk hk'
  refine abs_arg_lt_pi_div_four (z := hLink m μ k) ?_ ?_
  · rw [hre]; exact lt_of_le_of_lt (abs_nonneg _) h
  · rw [hre, him]; exact h

/-! ### Rational enclosures of the radicals that occur

Every `d`-vector on the 4×4 grid at the declared parameters is integral, so `‖d‖ = √n` for an
integer `n`. These are the only irrational quantities in the whole Chern computation, and four-digit
rational enclosures are ample: the tightest inequality in the argument has slack `0.026`. -/

theorem sqrt2_lb : (1.4142 : ℝ) < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem sqrt2_ub : Real.sqrt 2 < 1.4143 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
theorem sqrt3_lb : (1.7320 : ℝ) < Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem sqrt3_ub : Real.sqrt 3 < 1.7321 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
theorem sqrt6_lb : (2.4494 : ℝ) < Real.sqrt 6 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem sqrt6_ub : Real.sqrt 6 < 2.4495 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
theorem sqrt10_lb : (3.1622 : ℝ) < Real.sqrt 10 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem sqrt10_ub : Real.sqrt 10 < 3.1623 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
theorem sqrt26_lb : (5.0990 : ℝ) < Real.sqrt 26 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem sqrt26_ub : Real.sqrt 26 < 5.0991 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

/-- The north-pole condition `‖d‖ + d₃ > 0`, read off an explicit table entry. -/
theorem hpos_of_table {m : ℝ} {k : Torus 4 4} {a1 a2 a3 : ℝ}
    (hk : haldaneD44 m k = ![a1, a2, a3])
    (h : 0 < Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) + a3) :
    0 < Real.sqrt (dNormSq (haldaneD44 m k)) + (haldaneD44 m k) 2 := by
  rw [hk]; simpa [dNormSq] using h

/-! ### The trivial phase `m = 6` (outside the window: `6 > 3√3 ≈ 5.196`) -/

theorem haldane6_pos : ∀ k : Torus 4 4,
    0 < Real.sqrt (dNormSq (haldaneD44 6 k)) + (haldaneD44 6 k) 2 := by
  intro k
  fin_cases k
  · exact hpos_of_table (hD44_00 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_01 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_02 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_03 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_10 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_11 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_12 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_13 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_20 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_21 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_22 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_23 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_30 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_31 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_32 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_33 _) (by norm_num <;> positivity)

theorem haldane6_link_ne : ∀ (μ : Fin 2) (k : Torus 4 4), hLink 6 μ k ≠ 0 := by
  intro μ k
  fin_cases μ <;> fin_cases k
  · exact hLink_ne_zero_of_im (by decide) (hD44_00 6) (hD44_10 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_01 6) (hD44_11 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_02 6) (hD44_12 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_03 6) (hD44_13 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_10 6) (hD44_20 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_11 6) (hD44_21 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_12 6) (hD44_22 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_13 6) (hD44_23 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_20 6) (hD44_30 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_21 6) (hD44_31 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_22 6) (hD44_32 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_23 6) (hD44_33 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_30 6) (hD44_00 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_31 6) (hD44_01 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_32 6) (hD44_02 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_33 6) (hD44_03 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_00 6) (hD44_01 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_01 6) (hD44_02 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_02 6) (hD44_03 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_03 6) (hD44_00 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_10 6) (hD44_11 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_11 6) (hD44_12 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_12 6) (hD44_13 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_13 6) (hD44_10 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_20 6) (hD44_21 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_21 6) (hD44_22 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_22 6) (hD44_23 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_23 6) (hD44_20 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_30 6) (hD44_31 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_31 6) (hD44_32 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_32 6) (hD44_33 6) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_33 6) (hD44_30 6) (by norm_num)

theorem haldane6_link_narrow :
    ∀ (μ : Fin 2) (k : Torus 4 4), |(hLink 6 μ k).arg| < Real.pi / 4 := by
  intro μ k
  fin_cases μ <;> fin_cases k
  · exact hLink_narrow (by decide) (hD44_00 6) (hD44_10 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (45 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (45 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_01 6) (hD44_11 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_02 6) (hD44_12 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (37 : ℝ), Real.sqrt_nonneg (5 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (37 : ℝ)) (Real.sqrt_nonneg (5 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_03 6) (hD44_13 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (5 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (5 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_10 6) (hD44_20 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (37 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (37 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_11 6) (hD44_21 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (101 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (101 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_12 6) (hD44_22 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (37 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (5 : ℝ)) (Real.sqrt_nonneg (37 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_13 6) (hD44_23 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (5 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (5 : ℝ)) (Real.sqrt_nonneg (5 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_20 6) (hD44_30 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (37 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (37 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_21 6) (hD44_31 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (101 : ℝ), Real.sqrt_nonneg (101 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (101 : ℝ)) (Real.sqrt_nonneg (101 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_22 6) (hD44_32 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (37 : ℝ), Real.sqrt_nonneg (101 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (37 : ℝ)) (Real.sqrt_nonneg (101 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_23 6) (hD44_33 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (5 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_30 6) (hD44_00 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (45 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (45 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_31 6) (hD44_01 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (101 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (101 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_32 6) (hD44_02 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (101 : ℝ), Real.sqrt_nonneg (37 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (101 : ℝ)) (Real.sqrt_nonneg (37 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_33 6) (hD44_03 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_00 6) (hD44_01 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (45 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (45 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_01 6) (hD44_02 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (37 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (37 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_02 6) (hD44_03 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (37 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (37 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_03 6) (hD44_00 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (45 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (45 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_10 6) (hD44_11 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_11 6) (hD44_12 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (5 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (5 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_12 6) (hD44_13 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (5 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (5 : ℝ)) (Real.sqrt_nonneg (5 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_13 6) (hD44_10 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (5 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_20 6) (hD44_21 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (37 : ℝ), Real.sqrt_nonneg (101 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (37 : ℝ)) (Real.sqrt_nonneg (101 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_21 6) (hD44_22 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (101 : ℝ), Real.sqrt_nonneg (37 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (101 : ℝ)) (Real.sqrt_nonneg (37 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_22 6) (hD44_23 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (37 : ℝ), Real.sqrt_nonneg (5 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (37 : ℝ)) (Real.sqrt_nonneg (5 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_23 6) (hD44_20 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (37 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (5 : ℝ)) (Real.sqrt_nonneg (37 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_30 6) (hD44_31 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (101 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (101 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_31 6) (hD44_32 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (101 : ℝ), Real.sqrt_nonneg (101 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (101 : ℝ)) (Real.sqrt_nonneg (101 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_32 6) (hD44_33 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (101 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (101 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_33 6) (hD44_30 6)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (41 : ℝ), Real.sqrt_nonneg (41 : ℝ),
        mul_nonneg (Real.sqrt_nonneg (41 : ℝ)) (Real.sqrt_nonneg (41 : ℝ))])

/-! ### Inside the window but still trivial: `m = 5` (`5 < 3√3 ≈ 5.196`) -/

theorem haldane5_pos : ∀ k : Torus 4 4,
    0 < Real.sqrt (dNormSq (haldaneD44 5 k)) + (haldaneD44 5 k) 2 := by
  intro k
  fin_cases k
  · exact hpos_of_table (hD44_00 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_01 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_02 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_03 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_10 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_11 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_12 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_13 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_20 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_21 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_22 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_23 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_30 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_31 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_32 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_33 _) (by norm_num <;> positivity)

theorem haldane5_link_ne : ∀ (μ : Fin 2) (k : Torus 4 4), hLink 5 μ k ≠ 0 := by
  intro μ k
  fin_cases μ <;> fin_cases k
  · exact hLink_ne_zero_of_im (by decide) (hD44_00 5) (hD44_10 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_01 5) (hD44_11 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_02 5) (hD44_12 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_03 5) (hD44_13 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_10 5) (hD44_20 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_11 5) (hD44_21 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_12 5) (hD44_22 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_13 5) (hD44_23 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_20 5) (hD44_30 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_21 5) (hD44_31 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_22 5) (hD44_32 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_23 5) (hD44_33 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_30 5) (hD44_00 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_31 5) (hD44_01 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_32 5) (hD44_02 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_33 5) (hD44_03 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_00 5) (hD44_01 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_01 5) (hD44_02 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_02 5) (hD44_03 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_03 5) (hD44_00 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_10 5) (hD44_11 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_11 5) (hD44_12 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_12 5) (hD44_13 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_13 5) (hD44_10 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_20 5) (hD44_21 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_21 5) (hD44_22 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_22 5) (hD44_23 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_23 5) (hD44_20 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_30 5) (hD44_31 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_31 5) (hD44_32 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_32 5) (hD44_33 5) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_33 5) (hD44_30 5) (by norm_num)

theorem haldane5_link_narrow :
    ∀ (μ : Fin 2) (k : Torus 4 4), |(hLink 5 μ k).arg| < Real.pi / 4 := by
  intro μ k
  fin_cases μ <;> fin_cases k
  · exact hLink_narrow (by decide) (hD44_00 5) (hD44_10 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (34 : ℝ), Real.sqrt_nonneg (30 : ℝ), mul_nonneg (Real.sqrt_nonneg (34 : ℝ)) (Real.sqrt_nonneg (30 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_01 5) (hD44_11 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (30 : ℝ), Real.sqrt_nonneg (30 : ℝ), mul_nonneg (Real.sqrt_nonneg (30 : ℝ)) (Real.sqrt_nonneg (30 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_02 5) (hD44_12 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (26 : ℝ), Real.sqrt_nonneg (2 : ℝ), mul_nonneg (Real.sqrt_nonneg (26 : ℝ)) (Real.sqrt_nonneg (2 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_03 5) (hD44_13 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (30 : ℝ), Real.sqrt_nonneg (2 : ℝ), mul_nonneg (Real.sqrt_nonneg (30 : ℝ)) (Real.sqrt_nonneg (2 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_10 5) (hD44_20 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (30 : ℝ), Real.sqrt_nonneg (26 : ℝ), mul_nonneg (Real.sqrt_nonneg (30 : ℝ)) (Real.sqrt_nonneg (26 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_11 5) (hD44_21 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (30 : ℝ), Real.sqrt_nonneg (82 : ℝ), mul_nonneg (Real.sqrt_nonneg (30 : ℝ)) (Real.sqrt_nonneg (82 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_12 5) (hD44_22 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (26 : ℝ), mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (26 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_13 5) (hD44_23 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (2 : ℝ), mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (2 : ℝ)), Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)])
  · exact hLink_narrow (by decide) (hD44_20 5) (hD44_30 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (26 : ℝ), Real.sqrt_nonneg (30 : ℝ), mul_nonneg (Real.sqrt_nonneg (26 : ℝ)) (Real.sqrt_nonneg (30 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_21 5) (hD44_31 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (82 : ℝ), Real.sqrt_nonneg (82 : ℝ), mul_nonneg (Real.sqrt_nonneg (82 : ℝ)) (Real.sqrt_nonneg (82 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_22 5) (hD44_32 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (26 : ℝ), Real.sqrt_nonneg (82 : ℝ), mul_nonneg (Real.sqrt_nonneg (26 : ℝ)) (Real.sqrt_nonneg (82 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_23 5) (hD44_33 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (30 : ℝ), mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (30 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_30 5) (hD44_00 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (30 : ℝ), Real.sqrt_nonneg (34 : ℝ), mul_nonneg (Real.sqrt_nonneg (30 : ℝ)) (Real.sqrt_nonneg (34 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_31 5) (hD44_01 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (82 : ℝ), Real.sqrt_nonneg (30 : ℝ), mul_nonneg (Real.sqrt_nonneg (82 : ℝ)) (Real.sqrt_nonneg (30 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_32 5) (hD44_02 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (82 : ℝ), Real.sqrt_nonneg (26 : ℝ), mul_nonneg (Real.sqrt_nonneg (82 : ℝ)) (Real.sqrt_nonneg (26 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_33 5) (hD44_03 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (30 : ℝ), Real.sqrt_nonneg (30 : ℝ), mul_nonneg (Real.sqrt_nonneg (30 : ℝ)) (Real.sqrt_nonneg (30 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_00 5) (hD44_01 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (34 : ℝ), Real.sqrt_nonneg (30 : ℝ), mul_nonneg (Real.sqrt_nonneg (34 : ℝ)) (Real.sqrt_nonneg (30 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_01 5) (hD44_02 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (30 : ℝ), Real.sqrt_nonneg (26 : ℝ), mul_nonneg (Real.sqrt_nonneg (30 : ℝ)) (Real.sqrt_nonneg (26 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_02 5) (hD44_03 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (26 : ℝ), Real.sqrt_nonneg (30 : ℝ), mul_nonneg (Real.sqrt_nonneg (26 : ℝ)) (Real.sqrt_nonneg (30 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_03 5) (hD44_00 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (30 : ℝ), Real.sqrt_nonneg (34 : ℝ), mul_nonneg (Real.sqrt_nonneg (30 : ℝ)) (Real.sqrt_nonneg (34 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_10 5) (hD44_11 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (30 : ℝ), Real.sqrt_nonneg (30 : ℝ), mul_nonneg (Real.sqrt_nonneg (30 : ℝ)) (Real.sqrt_nonneg (30 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_11 5) (hD44_12 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (30 : ℝ), Real.sqrt_nonneg (2 : ℝ), mul_nonneg (Real.sqrt_nonneg (30 : ℝ)) (Real.sqrt_nonneg (2 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_12 5) (hD44_13 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (2 : ℝ), mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (2 : ℝ)), Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)])
  · exact hLink_narrow (by decide) (hD44_13 5) (hD44_10 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (30 : ℝ), mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (30 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_20 5) (hD44_21 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (26 : ℝ), Real.sqrt_nonneg (82 : ℝ), mul_nonneg (Real.sqrt_nonneg (26 : ℝ)) (Real.sqrt_nonneg (82 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_21 5) (hD44_22 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (82 : ℝ), Real.sqrt_nonneg (26 : ℝ), mul_nonneg (Real.sqrt_nonneg (82 : ℝ)) (Real.sqrt_nonneg (26 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_22 5) (hD44_23 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (26 : ℝ), Real.sqrt_nonneg (2 : ℝ), mul_nonneg (Real.sqrt_nonneg (26 : ℝ)) (Real.sqrt_nonneg (2 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_23 5) (hD44_20 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (26 : ℝ), mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (26 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_30 5) (hD44_31 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (30 : ℝ), Real.sqrt_nonneg (82 : ℝ), mul_nonneg (Real.sqrt_nonneg (30 : ℝ)) (Real.sqrt_nonneg (82 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_31 5) (hD44_32 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (82 : ℝ), Real.sqrt_nonneg (82 : ℝ), mul_nonneg (Real.sqrt_nonneg (82 : ℝ)) (Real.sqrt_nonneg (82 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_32 5) (hD44_33 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (82 : ℝ), Real.sqrt_nonneg (30 : ℝ), mul_nonneg (Real.sqrt_nonneg (82 : ℝ)) (Real.sqrt_nonneg (30 : ℝ))])
  · exact hLink_narrow (by decide) (hD44_33 5) (hD44_30 5)
      (by norm_num <;> nlinarith [Real.sqrt_nonneg (30 : ℝ), Real.sqrt_nonneg (30 : ℝ), mul_nonneg (Real.sqrt_nonneg (30 : ℝ)) (Real.sqrt_nonneg (30 : ℝ))])

/-! ### The topological phase `m = 1` (inside the window: `1 < 3√3`) -/

theorem haldane1_pos : ∀ k : Torus 4 4,
    0 < Real.sqrt (dNormSq (haldaneD44 1 k)) + (haldaneD44 1 k) 2 := by
  intro k
  fin_cases k
  · exact hpos_of_table (hD44_00 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_01 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_02 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_03 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_10 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_11 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_12 _) (by norm_num <;> nlinarith [sqrt10_lb])
  · exact hpos_of_table (hD44_13 _) (by norm_num <;> nlinarith [sqrt10_lb])
  · exact hpos_of_table (hD44_20 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_21 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_22 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_23 _) (by norm_num <;> nlinarith [sqrt10_lb])
  · exact hpos_of_table (hD44_30 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_31 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_32 _) (by norm_num <;> positivity)
  · exact hpos_of_table (hD44_33 _) (by norm_num <;> positivity)

theorem haldane1_link_ne : ∀ (μ : Fin 2) (k : Torus 4 4), hLink 1 μ k ≠ 0 := by
  intro μ k
  fin_cases μ <;> fin_cases k
  · exact hLink_ne_zero_of_im (by decide) (hD44_00 1) (hD44_10 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_01 1) (hD44_11 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_02 1) (hD44_12 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_03 1) (hD44_13 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_10 1) (hD44_20 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_11 1) (hD44_21 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_12 1) (hD44_22 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_13 1) (hD44_23 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_20 1) (hD44_30 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_21 1) (hD44_31 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_22 1) (hD44_32 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_23 1) (hD44_33 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_30 1) (hD44_00 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_31 1) (hD44_01 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_32 1) (hD44_02 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_33 1) (hD44_03 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_00 1) (hD44_01 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_01 1) (hD44_02 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_02 1) (hD44_03 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_03 1) (hD44_00 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_10 1) (hD44_11 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_11 1) (hD44_12 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_12 1) (hD44_13 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_13 1) (hD44_10 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_20 1) (hD44_21 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_21 1) (hD44_22 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_22 1) (hD44_23 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_23 1) (hD44_20 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_30 1) (hD44_31 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_31 1) (hD44_32 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_32 1) (hD44_33 1) (by norm_num)
  · exact hLink_ne_zero_of_im (by decide) (hD44_33 1) (hD44_30 1) (by norm_num)

/-- **The topological Haldane frame**: `t = t₂ = 1`, `φ = π/2`, `m = 1`. -/
noncomputable def haldaneFrameTopo : BlochLowerBandFrame 4 4 :=
  blochFrameOfD (haldaneD44 1) haldane1_pos haldane1_link_ne

/-- **The trivial-phase Haldane frame**: same hoppings, `m = 6` (outside the window). -/
noncomputable def haldaneFrameTrivial : BlochLowerBandFrame 4 4 :=
  blochFrameOfD (haldaneD44 6) haldane6_pos haldane6_link_ne

/-- **The `m = 5` frame** — *inside* the analytic mass-inversion window (`5 < 3√3 ≈ 5.196`), yet
its `4 × 4` FHS invariant is `0`. Same hoppings as the other two frames. -/
noncomputable def haldaneFrame5 : BlochLowerBandFrame 4 4 :=
  blochFrameOfD (haldaneD44 5) haldane5_pos haldane5_link_ne

theorem rawCurl_topo (k : Torus 4 4) :
    rawCurl 4 4 (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) k
      = (hLink 1 0 k).arg + (hLink 1 1 (shift 4 4 0 k)).arg
        - (hLink 1 0 (shift 4 4 1 k)).arg - (hLink 1 1 k).arg := by
  unfold rawCurl haldaneFrameTopo
  rw [linkArg_blochFrameOfD, linkArg_blochFrameOfD, linkArg_blochFrameOfD,
    linkArg_blochFrameOfD]
  rfl

/-! #### Per-link argument brackets (32 links, four sector cells) -/

/-- `μ=0` link at `(0, 0)` → `(1, 0)`: cell A (arg ≈ 8.383°). -/
theorem argL000 : 0 ≤ (hLink 1 0 (0, 0)).arg ∧ (hLink 1 0 (0, 0)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_00 1) (hD44_10 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(0, 1)` → `(1, 1)`: cell A (arg ≈ 10.686°). -/
theorem argL001 : 0 ≤ (hLink 1 0 (0, 1)).arg ∧ (hLink 1 0 (0, 1)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_01 1) (hD44_11 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(0, 2)` → `(1, 2)`: cell C (arg ≈ 68.606°). -/
theorem argL002 : Real.pi / 4 ≤ (hLink 1 0 (0, 2)).arg ∧ (hLink 1 0 (0, 2)).arg ≤ Real.pi / 2 :=
  hLink_cellC (by decide) (hD44_02 1) (hD44_12 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])

/-- `μ=0` link at `(0, 3)` → `(1, 3)`: cell A (arg ≈ 21.339°). -/
theorem argL003 : 0 ≤ (hLink 1 0 (0, 3)).arg ∧ (hLink 1 0 (0, 3)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_03 1) (hD44_13 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(1, 0)` → `(2, 0)`: cell B (arg ≈ -5.530°). -/
theorem argL010 : -(Real.pi / 6) ≤ (hLink 1 0 (1, 0)).arg ∧ (hLink 1 0 (1, 0)).arg ≤ 0 :=
  hLink_cellB (by decide) (hD44_10 1) (hD44_20 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(1, 1)` → `(2, 1)`: cell A (arg ≈ 1.555°). -/
theorem argL011 : 0 ≤ (hLink 1 0 (1, 1)).arg ∧ (hLink 1 0 (1, 1)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_11 1) (hD44_21 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(1, 2)` → `(2, 2)`: cell C (arg ≈ 68.606°). -/
theorem argL012 : Real.pi / 4 ≤ (hLink 1 0 (1, 2)).arg ∧ (hLink 1 0 (1, 2)).arg ≤ Real.pi / 2 :=
  hLink_cellC (by decide) (hD44_12 1) (hD44_22 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])

/-- `μ=0` link at `(1, 3)` → `(2, 3)`: cell D (arg ≈ -88.492°). -/
theorem argL013 : -(Real.pi / 2) ≤ (hLink 1 0 (1, 3)).arg ∧ (hLink 1 0 (1, 3)).arg ≤ -(Real.pi / 3) :=
  hLink_cellD (by decide) (hD44_13 1) (hD44_23 1)
    (by norm_num <;> nlinarith [sqrt10_lb, sqrt10_ub])
    (by norm_num <;> nlinarith [sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(2, 0)` → `(3, 0)`: cell B (arg ≈ -5.530°). -/
theorem argL020 : -(Real.pi / 6) ≤ (hLink 1 0 (2, 0)).arg ∧ (hLink 1 0 (2, 0)).arg ≤ 0 :=
  hLink_cellB (by decide) (hD44_20 1) (hD44_30 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(2, 1)` → `(3, 1)`: cell B (arg ≈ -0.562°). -/
theorem argL021 : -(Real.pi / 6) ≤ (hLink 1 0 (2, 1)).arg ∧ (hLink 1 0 (2, 1)).arg ≤ 0 :=
  hLink_cellB (by decide) (hD44_21 1) (hD44_31 1)
    (by norm_num <;> nlinarith [sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(2, 2)` → `(3, 2)`: cell A (arg ≈ 2.349°). -/
theorem argL022 : 0 ≤ (hLink 1 0 (2, 2)).arg ∧ (hLink 1 0 (2, 2)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_22 1) (hD44_32 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(2, 3)` → `(3, 3)`: cell A (arg ≈ 21.339°). -/
theorem argL023 : 0 ≤ (hLink 1 0 (2, 3)).arg ∧ (hLink 1 0 (2, 3)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_23 1) (hD44_33 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(3, 0)` → `(0, 0)`: cell A (arg ≈ 8.383°). -/
theorem argL030 : 0 ≤ (hLink 1 0 (3, 0)).arg ∧ (hLink 1 0 (3, 0)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_30 1) (hD44_00 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(3, 1)` → `(0, 1)`: cell A (arg ≈ 1.555°). -/
theorem argL031 : 0 ≤ (hLink 1 0 (3, 1)).arg ∧ (hLink 1 0 (3, 1)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_31 1) (hD44_01 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(3, 2)` → `(0, 2)`: cell A (arg ≈ 2.349°). -/
theorem argL032 : 0 ≤ (hLink 1 0 (3, 2)).arg ∧ (hLink 1 0 (3, 2)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_32 1) (hD44_02 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=0` link at `(3, 3)` → `(0, 3)`: cell A (arg ≈ 10.686°). -/
theorem argL033 : 0 ≤ (hLink 1 0 (3, 3)).arg ∧ (hLink 1 0 (3, 3)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_33 1) (hD44_03 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(0, 0)` → `(0, 1)`: cell A (arg ≈ 8.383°). -/
theorem argL100 : 0 ≤ (hLink 1 1 (0, 0)).arg ∧ (hLink 1 1 (0, 0)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_00 1) (hD44_01 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(0, 1)` → `(0, 2)`: cell B (arg ≈ -5.530°). -/
theorem argL101 : -(Real.pi / 6) ≤ (hLink 1 1 (0, 1)).arg ∧ (hLink 1 1 (0, 1)).arg ≤ 0 :=
  hLink_cellB (by decide) (hD44_01 1) (hD44_02 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(0, 2)` → `(0, 3)`: cell B (arg ≈ -5.530°). -/
theorem argL102 : -(Real.pi / 6) ≤ (hLink 1 1 (0, 2)).arg ∧ (hLink 1 1 (0, 2)).arg ≤ 0 :=
  hLink_cellB (by decide) (hD44_02 1) (hD44_03 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(0, 3)` → `(0, 0)`: cell A (arg ≈ 8.383°). -/
theorem argL103 : 0 ≤ (hLink 1 1 (0, 3)).arg ∧ (hLink 1 1 (0, 3)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_03 1) (hD44_00 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(1, 0)` → `(1, 1)`: cell A (arg ≈ 10.686°). -/
theorem argL110 : 0 ≤ (hLink 1 1 (1, 0)).arg ∧ (hLink 1 1 (1, 0)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_10 1) (hD44_11 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(1, 1)` → `(1, 2)`: cell A (arg ≈ 21.339°). -/
theorem argL111 : 0 ≤ (hLink 1 1 (1, 1)).arg ∧ (hLink 1 1 (1, 1)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_11 1) (hD44_12 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(1, 2)` → `(1, 3)`: cell D (arg ≈ -88.492°). -/
theorem argL112 : -(Real.pi / 2) ≤ (hLink 1 1 (1, 2)).arg ∧ (hLink 1 1 (1, 2)).arg ≤ -(Real.pi / 3) :=
  hLink_cellD (by decide) (hD44_12 1) (hD44_13 1)
    (by norm_num <;> nlinarith [sqrt10_lb, sqrt10_ub])
    (by norm_num <;> nlinarith [sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(1, 3)` → `(1, 0)`: cell A (arg ≈ 21.339°). -/
theorem argL113 : 0 ≤ (hLink 1 1 (1, 3)).arg ∧ (hLink 1 1 (1, 3)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_13 1) (hD44_10 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt10_lb, sqrt10_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(2, 0)` → `(2, 1)`: cell A (arg ≈ 2.349°). -/
theorem argL120 : 0 ≤ (hLink 1 1 (2, 0)).arg ∧ (hLink 1 1 (2, 0)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_20 1) (hD44_21 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(2, 1)` → `(2, 2)`: cell A (arg ≈ 2.349°). -/
theorem argL121 : 0 ≤ (hLink 1 1 (2, 1)).arg ∧ (hLink 1 1 (2, 1)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_21 1) (hD44_22 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(2, 2)` → `(2, 3)`: cell C (arg ≈ 68.606°). -/
theorem argL122 : Real.pi / 4 ≤ (hLink 1 1 (2, 2)).arg ∧ (hLink 1 1 (2, 2)).arg ≤ Real.pi / 2 :=
  hLink_cellC (by decide) (hD44_22 1) (hD44_23 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])

/-- `μ=1` link at `(2, 3)` → `(2, 0)`: cell C (arg ≈ 68.606°). -/
theorem argL123 : Real.pi / 4 ≤ (hLink 1 1 (2, 3)).arg ∧ (hLink 1 1 (2, 3)).arg ≤ Real.pi / 2 :=
  hLink_cellC (by decide) (hD44_23 1) (hD44_20 1)
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])
    (by norm_num <;> nlinarith [sqrt2_lb, sqrt2_ub, sqrt10_lb, sqrt10_ub])

/-- `μ=1` link at `(3, 0)` → `(3, 1)`: cell A (arg ≈ 1.555°). -/
theorem argL130 : 0 ≤ (hLink 1 1 (3, 0)).arg ∧ (hLink 1 1 (3, 0)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_30 1) (hD44_31 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(3, 1)` → `(3, 2)`: cell B (arg ≈ -0.562°). -/
theorem argL131 : -(Real.pi / 6) ≤ (hLink 1 1 (3, 1)).arg ∧ (hLink 1 1 (3, 1)).arg ≤ 0 :=
  hLink_cellB (by decide) (hD44_31 1) (hD44_32 1)
    (by norm_num <;> nlinarith [sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(3, 2)` → `(3, 3)`: cell A (arg ≈ 1.555°). -/
theorem argL132 : 0 ≤ (hLink 1 1 (3, 2)).arg ∧ (hLink 1 1 (3, 2)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_32 1) (hD44_33 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt26_lb, sqrt26_ub, sqrt3_lb, sqrt3_ub])

/-- `μ=1` link at `(3, 3)` → `(3, 0)`: cell A (arg ≈ 10.686°). -/
theorem argL133 : 0 ≤ (hLink 1 1 (3, 3)).arg ∧ (hLink 1 1 (3, 3)).arg ≤ Real.pi / 6 :=
  hLink_cellA (by decide) (hD44_33 1) (hD44_30 1)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub])
    (by norm_num)
    (by norm_num <;> nlinarith [sqrt6_lb, sqrt6_ub, sqrt3_lb, sqrt3_ub])

/-! #### Per-plaquette branch indices -/

theorem pb1_00 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (0, 0) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((0 : ZMod 4), (0 : ZMod 4)) = ((1 : ZMod 4), (0 : ZMod 4)) from by decide,
    show shift 4 4 1 ((0 : ZMod 4), (0 : ZMod 4)) = ((0 : ZMod 4), (1 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL000.1, argL000.2, argL110.1, argL110.2, argL001.1, argL001.2,
      argL100.1, argL100.2, Real.pi_pos])
    (by linarith [argL000.1, argL000.2, argL110.1, argL110.2, argL001.1, argL001.2,
      argL100.1, argL100.2, Real.pi_pos])

theorem pb1_01 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (0, 1) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((0 : ZMod 4), (1 : ZMod 4)) = ((1 : ZMod 4), (1 : ZMod 4)) from by decide,
    show shift 4 4 1 ((0 : ZMod 4), (1 : ZMod 4)) = ((0 : ZMod 4), (2 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL001.1, argL001.2, argL111.1, argL111.2, argL002.1, argL002.2,
      argL101.1, argL101.2, Real.pi_pos])
    (by linarith [argL001.1, argL001.2, argL111.1, argL111.2, argL002.1, argL002.2,
      argL101.1, argL101.2, Real.pi_pos])

theorem pb1_02 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (0, 2) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((0 : ZMod 4), (2 : ZMod 4)) = ((1 : ZMod 4), (2 : ZMod 4)) from by decide,
    show shift 4 4 1 ((0 : ZMod 4), (2 : ZMod 4)) = ((0 : ZMod 4), (3 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL002.1, argL002.2, argL112.1, argL112.2, argL003.1, argL003.2,
      argL102.1, argL102.2, Real.pi_pos])
    (by linarith [argL002.1, argL002.2, argL112.1, argL112.2, argL003.1, argL003.2,
      argL102.1, argL102.2, Real.pi_pos])

theorem pb1_03 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (0, 3) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((0 : ZMod 4), (3 : ZMod 4)) = ((1 : ZMod 4), (3 : ZMod 4)) from by decide,
    show shift 4 4 1 ((0 : ZMod 4), (3 : ZMod 4)) = ((0 : ZMod 4), (0 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL003.1, argL003.2, argL113.1, argL113.2, argL000.1, argL000.2,
      argL103.1, argL103.2, Real.pi_pos])
    (by linarith [argL003.1, argL003.2, argL113.1, argL113.2, argL000.1, argL000.2,
      argL103.1, argL103.2, Real.pi_pos])

theorem pb1_10 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (1, 0) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((1 : ZMod 4), (0 : ZMod 4)) = ((2 : ZMod 4), (0 : ZMod 4)) from by decide,
    show shift 4 4 1 ((1 : ZMod 4), (0 : ZMod 4)) = ((1 : ZMod 4), (1 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL010.1, argL010.2, argL120.1, argL120.2, argL011.1, argL011.2,
      argL110.1, argL110.2, Real.pi_pos])
    (by linarith [argL010.1, argL010.2, argL120.1, argL120.2, argL011.1, argL011.2,
      argL110.1, argL110.2, Real.pi_pos])

theorem pb1_11 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (1, 1) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((1 : ZMod 4), (1 : ZMod 4)) = ((2 : ZMod 4), (1 : ZMod 4)) from by decide,
    show shift 4 4 1 ((1 : ZMod 4), (1 : ZMod 4)) = ((1 : ZMod 4), (2 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL011.1, argL011.2, argL121.1, argL121.2, argL012.1, argL012.2,
      argL111.1, argL111.2, Real.pi_pos])
    (by linarith [argL011.1, argL011.2, argL121.1, argL121.2, argL012.1, argL012.2,
      argL111.1, argL111.2, Real.pi_pos])

theorem pb1_12 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (1, 2) = 1 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((1 : ZMod 4), (2 : ZMod 4)) = ((2 : ZMod 4), (2 : ZMod 4)) from by decide,
    show shift 4 4 1 ((1 : ZMod 4), (2 : ZMod 4)) = ((1 : ZMod 4), (3 : ZMod 4)) from by decide]
  exact branchIndex_eq_one_of
    (by linarith [argL012.1, argL012.2, argL122.1, argL122.2, argL013.1, argL013.2,
      argL112.1, argL112.2, Real.pi_pos])
    (by linarith [argL012.1, argL012.2, argL122.1, argL122.2, argL013.1, argL013.2,
      argL112.1, argL112.2, Real.pi_pos])

theorem pb1_13 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (1, 3) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((1 : ZMod 4), (3 : ZMod 4)) = ((2 : ZMod 4), (3 : ZMod 4)) from by decide,
    show shift 4 4 1 ((1 : ZMod 4), (3 : ZMod 4)) = ((1 : ZMod 4), (0 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL013.1, argL013.2, argL123.1, argL123.2, argL010.1, argL010.2,
      argL113.1, argL113.2, Real.pi_pos])
    (by linarith [argL013.1, argL013.2, argL123.1, argL123.2, argL010.1, argL010.2,
      argL113.1, argL113.2, Real.pi_pos])

theorem pb1_20 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (2, 0) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((2 : ZMod 4), (0 : ZMod 4)) = ((3 : ZMod 4), (0 : ZMod 4)) from by decide,
    show shift 4 4 1 ((2 : ZMod 4), (0 : ZMod 4)) = ((2 : ZMod 4), (1 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL020.1, argL020.2, argL130.1, argL130.2, argL021.1, argL021.2,
      argL120.1, argL120.2, Real.pi_pos])
    (by linarith [argL020.1, argL020.2, argL130.1, argL130.2, argL021.1, argL021.2,
      argL120.1, argL120.2, Real.pi_pos])

theorem pb1_21 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (2, 1) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((2 : ZMod 4), (1 : ZMod 4)) = ((3 : ZMod 4), (1 : ZMod 4)) from by decide,
    show shift 4 4 1 ((2 : ZMod 4), (1 : ZMod 4)) = ((2 : ZMod 4), (2 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL021.1, argL021.2, argL131.1, argL131.2, argL022.1, argL022.2,
      argL121.1, argL121.2, Real.pi_pos])
    (by linarith [argL021.1, argL021.2, argL131.1, argL131.2, argL022.1, argL022.2,
      argL121.1, argL121.2, Real.pi_pos])

theorem pb1_22 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (2, 2) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((2 : ZMod 4), (2 : ZMod 4)) = ((3 : ZMod 4), (2 : ZMod 4)) from by decide,
    show shift 4 4 1 ((2 : ZMod 4), (2 : ZMod 4)) = ((2 : ZMod 4), (3 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL022.1, argL022.2, argL132.1, argL132.2, argL023.1, argL023.2,
      argL122.1, argL122.2, Real.pi_pos])
    (by linarith [argL022.1, argL022.2, argL132.1, argL132.2, argL023.1, argL023.2,
      argL122.1, argL122.2, Real.pi_pos])

theorem pb1_23 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (2, 3) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((2 : ZMod 4), (3 : ZMod 4)) = ((3 : ZMod 4), (3 : ZMod 4)) from by decide,
    show shift 4 4 1 ((2 : ZMod 4), (3 : ZMod 4)) = ((2 : ZMod 4), (0 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL023.1, argL023.2, argL133.1, argL133.2, argL020.1, argL020.2,
      argL123.1, argL123.2, Real.pi_pos])
    (by linarith [argL023.1, argL023.2, argL133.1, argL133.2, argL020.1, argL020.2,
      argL123.1, argL123.2, Real.pi_pos])

theorem pb1_30 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (3, 0) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((3 : ZMod 4), (0 : ZMod 4)) = ((0 : ZMod 4), (0 : ZMod 4)) from by decide,
    show shift 4 4 1 ((3 : ZMod 4), (0 : ZMod 4)) = ((3 : ZMod 4), (1 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL030.1, argL030.2, argL100.1, argL100.2, argL031.1, argL031.2,
      argL130.1, argL130.2, Real.pi_pos])
    (by linarith [argL030.1, argL030.2, argL100.1, argL100.2, argL031.1, argL031.2,
      argL130.1, argL130.2, Real.pi_pos])

theorem pb1_31 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (3, 1) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((3 : ZMod 4), (1 : ZMod 4)) = ((0 : ZMod 4), (1 : ZMod 4)) from by decide,
    show shift 4 4 1 ((3 : ZMod 4), (1 : ZMod 4)) = ((3 : ZMod 4), (2 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL031.1, argL031.2, argL101.1, argL101.2, argL032.1, argL032.2,
      argL131.1, argL131.2, Real.pi_pos])
    (by linarith [argL031.1, argL031.2, argL101.1, argL101.2, argL032.1, argL032.2,
      argL131.1, argL131.2, Real.pi_pos])

theorem pb1_32 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (3, 2) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((3 : ZMod 4), (2 : ZMod 4)) = ((0 : ZMod 4), (2 : ZMod 4)) from by decide,
    show shift 4 4 1 ((3 : ZMod 4), (2 : ZMod 4)) = ((3 : ZMod 4), (3 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL032.1, argL032.2, argL102.1, argL102.2, argL033.1, argL033.2,
      argL132.1, argL132.2, Real.pi_pos])
    (by linarith [argL032.1, argL032.2, argL102.1, argL102.2, argL033.1, argL033.2,
      argL132.1, argL132.2, Real.pi_pos])

theorem pb1_33 : plaquetteBranch 4 4
    (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) (3, 3) = 0 := by
  unfold plaquetteBranch
  rw [rawCurl_topo,
    show shift 4 4 0 ((3 : ZMod 4), (3 : ZMod 4)) = ((0 : ZMod 4), (3 : ZMod 4)) from by decide,
    show shift 4 4 1 ((3 : ZMod 4), (3 : ZMod 4)) = ((3 : ZMod 4), (0 : ZMod 4)) from by decide]
  exact branchIndex_eq_zero_of
    (by linarith [argL033.1, argL033.2, argL103.1, argL103.2, argL030.1, argL030.2,
      argL133.1, argL133.2, Real.pi_pos])
    (by linarith [argL033.1, argL033.2, argL103.1, argL103.2, argL030.1, argL030.2,
      argL133.1, argL133.2, Real.pi_pos])

theorem plaquetteBranch_topo (k : Torus 4 4) :
    plaquetteBranch 4 4 (linkOfFrame haldaneFrameTopo.toAdmissibleBandFrame) k
      = if k = ((1 : ZMod 4), (2 : ZMod 4)) then 1 else 0 := by
  fin_cases k
  · rw [if_neg (by decide)]; exact pb1_00
  · rw [if_neg (by decide)]; exact pb1_01
  · rw [if_neg (by decide)]; exact pb1_02
  · rw [if_neg (by decide)]; exact pb1_03
  · rw [if_neg (by decide)]; exact pb1_10
  · rw [if_neg (by decide)]; exact pb1_11
  · rw [if_pos (by decide)]; exact pb1_12
  · rw [if_neg (by decide)]; exact pb1_13
  · rw [if_neg (by decide)]; exact pb1_20
  · rw [if_neg (by decide)]; exact pb1_21
  · rw [if_neg (by decide)]; exact pb1_22
  · rw [if_neg (by decide)]; exact pb1_23
  · rw [if_neg (by decide)]; exact pb1_30
  · rw [if_neg (by decide)]; exact pb1_31
  · rw [if_neg (by decide)]; exact pb1_32
  · rw [if_neg (by decide)]; exact pb1_33


/-! ## Headline: the two-phase Chern classification -/


/-- **The trivial phase carries no Chern number.** At `m = 6` — outside the topological window
`|m| < 3√3 ≈ 5.196` of `haldane_mass_inversion_iff` — every one of the 32 nearest-neighbour
overlaps on the `4 × 4` Brillouin torus is narrow, so no plaquette carries a branch correction. -/
theorem haldane_trivial_phase_chern_zero :
    blochLatticeChern haldaneFrameTrivial.toAdmissibleBandFrame = 0 :=
  blochLatticeChern_eq_zero_of_narrow_D _ _ _ haldane6_link_narrow

/-- **The Haldane Chern witness.** At the declared parameters `t = t₂ = 1`, `φ = π/2`, `m = 1` —
inside the topological window — the lower-band frame on the `4 × 4` discretized Brillouin torus has
FHS lattice Chern number `−1`.

Exactly **one** of the sixteen plaquettes (the one at `k = (1, 2)`) carries a branch correction, and
it carries `+1`; `latticeChern = −∑ plaquetteBranch` (the repo's frozen orientation convention, fixed
so that `∑ plaquetteArg = 2π · latticeChern`) then gives `−1`. The overall sign is the convention's,
not the physics': replacing `φ = π/2` by `φ = −π/2` reverses the time-reversal-breaking flux and
flips it.

**This is a witness, NOT a classification.** It is *not* the case that the invariant is `−1`
throughout the mass-inversion window of `haldane_mass_inversion_iff` and `0` outside it: at this
grid the transition sits at `|m| ≈ 3.3177`, strictly inside the analytic window `|m| < 3√3 ≈
5.1962`, and `haldane_massInversion_not_sufficient_at_N4` exhibits `m = 5` inside the window with
invariant `0`. So mass inversion is **not sufficient** at `N = 4`. Necessity is **not proved** — it
is sampled at `m = 6` only; see the module header. (Scope corrected 2026-07-31, D11 Stage-13: this
docstring is the one a referee reaches from the paper's citation of this theorem, and it previously
asserted the unproved necessity half.)
*(The classification framing was retracted on 2026-07-29.)* -/
theorem haldaneFrame_latticeChern_eq_neg_one :
    blochLatticeChern haldaneFrameTopo.toAdmissibleBandFrame = -1 := by
  unfold blochLatticeChern latticeChern
  rw [Finset.sum_congr rfl (fun k _ => plaquetteBranch_topo k)]
  decide

/-- The three sampled masses against the analytic window `|m| < 3√3 |t₂ sin φ|`: `1` and `5` are
inside, `6` is outside. The `norm_num`-backed numeric facts that make the sample points meaningful.
`3√3 ≈ 5.1962`. -/
theorem haldane_window_bounds :
    |(1 : ℝ)| < |3 * Real.sqrt 3 * 1 * Real.sin (Real.pi / 2)| ∧
      |(5 : ℝ)| < |3 * Real.sqrt 3 * 1 * Real.sin (Real.pi / 2)| ∧
      ¬ |(6 : ℝ)| < |3 * Real.sqrt 3 * 1 * Real.sin (Real.pi / 2)| := by
  rw [Real.sin_pi_div_two]
  have h1 : (0 : ℝ) < 3 * Real.sqrt 3 * 1 * 1 := by positivity
  rw [abs_of_pos h1]
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_pos (by norm_num : (0:ℝ) < 1)]; nlinarith [sqrt3_lb]
  · rw [abs_of_pos (by norm_num : (0:ℝ) < 5)]; nlinarith [sqrt3_lb]
  · rw [abs_of_pos (by norm_num : (0:ℝ) < 6), not_lt]; nlinarith [sqrt3_ub]

/-- **Mass inversion is NOT SUFFICIENT for a nonzero `4 × 4` invariant.**

⚠️ Scope corrected 2026-07-31 (D11 Stage-13). This headline previously read "NECESSARY BUT NOT
SUFFICIENT". Only the *insufficiency* half is proved — by the single anti-witness below. Necessity
is **not** formalized anywhere in this development; it rests on sampling, and the D11 draft says so
explicitly. A referee following the paper's citation must not land on a stronger claim than the
statement carries.

At `m = 5` the two Dirac masses of `haldane_mass_inversion_iff` genuinely have opposite signs — `5`
is inside the analytic window `|m| < 3√3 ≈ 5.1962` — and yet the `4 × 4` FHS lattice Chern number is
`0`. So the analytic phase boundary does **not** locate the lattice transition at this grid: the
lattice transition sits at `|m| ≈ 3.3177`, and on the whole interval `3.318 ≲ |m| < 5.196` (about
36 % of the window) the invariant already reads `0`.

This is the theorem that makes the wave's claims falsifiable in the right direction. It replaces a
`haldane_mass_inversion_iff` shipped on 2026-07-28, which asserted the two-sided
correspondence; that statement was true only because it quantified over the two sampled masses `1`
and `6`, and its proof was `iff_of_true (by decide) …` / `iff_of_false …` — both sides closed
propositions with known truth values, hence no content beyond the four theorems it cited.

The mechanism is grid discretization, not a degeneracy: the frame is admissible throughout
(`haldane5_pos`, `haldane5_link_ne` discharge the north-pole and overlap conditions), so this `0` is
a real value of the invariant. The `4 × 4` grid never samples `K`/`K′` and its extremal `haldaneNNN`
is `±2` against the true `±3√3/2 ≈ ±2.598`, so it sees a smaller window than the continuum; the
transition converges to `3√3` from below as `N` grows. -/
theorem haldane_massInversion_not_sufficient_at_N4 :
    haldaneD 1 1 (Real.pi / 2) 5 diracK 2 * haldaneD 1 1 (Real.pi / 2) 5 diracK' 2 < 0 ∧
      blochLatticeChern haldaneFrame5.toAdmissibleBandFrame = 0 := by
  refine ⟨?_, blochLatticeChern_eq_zero_of_narrow_D _ _ _ haldane5_link_narrow⟩
  rw [haldane_mass_inversion_iff]
  exact haldane_window_bounds.2.1

/-- **The `−1` is gauge-independent.** `blochLatticeChern` is invariant under an arbitrary pointwise
`Circle` rephasing of the frame (`blochLatticeChern_rephase`), so the witness value is a property of
the sampled lower band rather than of the particular `lbVec` representative used to compute it.

This is a *call*, not a docstring reference: without it the file imported the gauge-invariance
headline and never used it. -/
theorem haldaneFrame_latticeChern_gauge_independent (φ : Torus 4 4 → Circle) :
    blochLatticeChern (rephase φ haldaneFrameTopo.toAdmissibleBandFrame) = -1 := by
  rw [blochLatticeChern_rephase, haldaneFrame_latticeChern_eq_neg_one]

/-! ## The gapless cone's Berry phase

UNKNOWN-2 is resolved in favour of the **discretized principal-branch form**, matching
`FHSLatticeGauge`'s style and this file's Chern machinery: a closed loop of sampled states carries
the Wilson-loop phase `arg ∏ ⟨u_j, u_{j+1}⟩`, and its pseudospin winding is the sum of the
principal-branch phase increments `arg (⟨f_j, f_{j+1}⟩)` of the (massless) structure factor. No
continuum line integral is used; the repo deliberately avoids that machinery.

The loop is the `π/2`-diamond centred on the `K` Dirac point of Wave 1. -/

/-- The **discrete Wilson-loop (Berry) phase** of a cyclic family of states: the argument of the
product of consecutive overlaps around the loop. -/
noncomputable def wilsonLoopArg {M n : ℕ} [NeZero M] (u : Fin M → Fin n → ℂ) : ℝ :=
  Complex.arg (∏ j : Fin M, frameOverlap (u j) (u (j + 1)))

/-- Polar certificate for an argument: `z = r(cos θ + i sin θ)` with `r > 0` and `θ ∈ (−π, π]`. -/
theorem arg_eq_of_polar {θ r : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) {z : ℂ}
    (hre : z.re = r * Real.cos θ) (him : z.im = r * Real.sin θ) : z.arg = θ := by
  have hz : z = (r : ℂ) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I) := by
    apply Complex.ext <;>
      simp [hre, him, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
        Complex.sin_ofReal_im]
  rw [hz, Complex.arg_real_mul _ hr]
  exact Complex.arg_cos_add_sin_mul_I hθ

theorem principal_add_two_pi (θ : ℝ) : principal (θ + 2 * Real.pi) = principal θ := by
  unfold principal
  rw [show θ + 2 * Real.pi = θ + 1 • (2 * Real.pi) by simp]
  exact toIocMod_add_zsmul _ _ _ 1

/-- **The transition amplitude carries the principal-branch phase increment.** For nonzero `a, b`,
`arg (conj a · b)` is exactly the principal reduction of `arg b − arg a`. This is what licenses
calling the sum below a *principal-branch winding*: it is the same branch discipline
`FHSLatticeGauge` uses for the plaquette field strength. -/
theorem arg_conj_mul_eq_principal_sub {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Complex.arg ((starRingEnd ℂ) a * b) = principal (Complex.arg b - Complex.arg a) := by
  have hca : (starRingEnd ℂ) a ≠ 0 := by simpa using ha
  rw [arg_mul_eq_principal_add _ _ hca hb, Complex.arg_conj]
  rcases eq_or_ne (Complex.arg a) Real.pi with h | h
  · rw [if_pos h, h, show Real.pi + Complex.arg b = (Complex.arg b - Real.pi) + 2 * Real.pi by ring,
      principal_add_two_pi]
  · rw [if_neg h]; ring_nf

/-! ### The four-point loop around `K` -/

/-- The `π/2`-diamond centred on the `K` Dirac point, traversed counterclockwise in the Bloch-phase
plane. Its four vertices are `K ± (π/2, 0)` and `K ± (0, π/2)`; `K` is their centroid, so the loop
genuinely encircles the cone rather than merely sampling four states. -/
noncomputable def coneLoop : Fin 4 → ℝ × ℝ
  | 0 => (diracK.1 + Real.pi / 2, diracK.2)
  | 1 => (diracK.1, diracK.2 + Real.pi / 2)
  | 2 => (diracK.1 - Real.pi / 2, diracK.2)
  | 3 => (diracK.1, diracK.2 - Real.pi / 2)

private theorem cos_2pi3 : Real.cos (2 * Real.pi / 3) = -(1/2) := by
  rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]

private theorem sin_2pi3 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
    Real.sin_pi_div_three]

private theorem cos_4pi3 : Real.cos (4 * Real.pi / 3) = -(1/2) := by
  rw [show (4 * Real.pi / 3 : ℝ) = Real.pi / 3 + Real.pi by ring, Real.cos_add_pi,
    Real.cos_pi_div_three]

private theorem sin_4pi3 : Real.sin (4 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
  rw [show (4 * Real.pi / 3 : ℝ) = Real.pi / 3 + Real.pi by ring, Real.sin_add_pi,
    Real.sin_pi_div_three]

/-- The structure factor at the four loop vertices. Writing `p = (1+√3)/2`, `q = (1−√3)/2`, the
four values are `q − ip`, `p − iq`, `p + iq`, `q + ip` — all of modulus `√2`, and their phases
advance monotonically around the circle. -/
theorem coneLoop_re_0 : (structureFactor (coneLoop 0)).re = (1 - Real.sqrt 3) / 2 := by
  simp only [coneLoop, structureFactor_re, diracK, Real.cos_add, Real.cos_sub,
    Real.cos_pi_div_two, Real.sin_pi_div_two, cos_2pi3, sin_2pi3, cos_4pi3, sin_4pi3]
  ring

theorem coneLoop_im_0 : (structureFactor (coneLoop 0)).im = -((1 + Real.sqrt 3) / 2) := by
  simp only [coneLoop, structureFactor_im, diracK, Real.sin_add, Real.sin_sub,
    Real.cos_pi_div_two, Real.sin_pi_div_two, cos_2pi3, sin_2pi3, cos_4pi3, sin_4pi3]
  ring

theorem coneLoop_re_1 : (structureFactor (coneLoop 1)).re = (1 + Real.sqrt 3) / 2 := by
  simp only [coneLoop, structureFactor_re, diracK, Real.cos_add, Real.cos_sub,
    Real.cos_pi_div_two, Real.sin_pi_div_two, cos_2pi3, sin_2pi3, cos_4pi3, sin_4pi3]
  ring

theorem coneLoop_im_1 : (structureFactor (coneLoop 1)).im = -((1 - Real.sqrt 3) / 2) := by
  simp only [coneLoop, structureFactor_im, diracK, Real.sin_add, Real.sin_sub,
    Real.cos_pi_div_two, Real.sin_pi_div_two, cos_2pi3, sin_2pi3, cos_4pi3, sin_4pi3]
  ring

theorem coneLoop_re_2 : (structureFactor (coneLoop 2)).re = (1 + Real.sqrt 3) / 2 := by
  simp only [coneLoop, structureFactor_re, diracK, Real.cos_add, Real.cos_sub,
    Real.cos_pi_div_two, Real.sin_pi_div_two, cos_2pi3, sin_2pi3, cos_4pi3, sin_4pi3]
  ring

theorem coneLoop_im_2 : (structureFactor (coneLoop 2)).im = (1 - Real.sqrt 3) / 2 := by
  simp only [coneLoop, structureFactor_im, diracK, Real.sin_add, Real.sin_sub,
    Real.cos_pi_div_two, Real.sin_pi_div_two, cos_2pi3, sin_2pi3, cos_4pi3, sin_4pi3]
  ring

theorem coneLoop_re_3 : (structureFactor (coneLoop 3)).re = (1 - Real.sqrt 3) / 2 := by
  simp only [coneLoop, structureFactor_re, diracK, Real.cos_add, Real.cos_sub,
    Real.cos_pi_div_two, Real.sin_pi_div_two, cos_2pi3, sin_2pi3, cos_4pi3, sin_4pi3]
  ring

theorem coneLoop_im_3 : (structureFactor (coneLoop 3)).im = (1 + Real.sqrt 3) / 2 := by
  simp only [coneLoop, structureFactor_im, diracK, Real.sin_add, Real.sin_sub,
    Real.cos_pi_div_two, Real.sin_pi_div_two, cos_2pi3, sin_2pi3, cos_4pi3, sin_4pi3]
  ring
/-! ### Moduli and overlaps on the loop -/

/-- The overlap of two massless-honeycomb lower-band states, in structure-factor data.
For the chiral (`d₃ = 0`) model the raw lower-band vector is `v(θ) = (f(θ), −|f(θ)|)`. -/
theorem lbOv_cone_re (θ θ' : ℝ × ℝ) :
    (frameOverlap (lbVec (honeycombD θ)) (lbVec (honeycombD θ'))).re
      = (structureFactor θ).re * (structureFactor θ').re
        + (structureFactor θ).im * (structureFactor θ').im
        + ‖structureFactor θ‖ * ‖structureFactor θ'‖ := by
  rw [lbOverlap_re, honeycomb_energy_eq, honeycomb_energy_eq]
  simp only [honeycombD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem lbOv_cone_im (θ θ' : ℝ × ℝ) :
    (frameOverlap (lbVec (honeycombD θ)) (lbVec (honeycombD θ'))).im
      = (structureFactor θ).re * (structureFactor θ').im
        - (structureFactor θ).im * (structureFactor θ').re := by
  rw [lbOverlap_im]
  simp only [honeycombD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

private theorem sq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
private theorem sq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem coneLoop_norm_0 : ‖structureFactor (coneLoop 0)‖ = Real.sqrt 2 := by
  rw [Complex.norm_def, Complex.normSq_apply, coneLoop_re_0, coneLoop_im_0]
  congr 1; nlinarith [sq3]

theorem coneLoop_norm_1 : ‖structureFactor (coneLoop 1)‖ = Real.sqrt 2 := by
  rw [Complex.norm_def, Complex.normSq_apply, coneLoop_re_1, coneLoop_im_1]
  congr 1; nlinarith [sq3]

theorem coneLoop_norm_2 : ‖structureFactor (coneLoop 2)‖ = Real.sqrt 2 := by
  rw [Complex.norm_def, Complex.normSq_apply, coneLoop_re_2, coneLoop_im_2]
  congr 1; nlinarith [sq3]

theorem coneLoop_norm_3 : ‖structureFactor (coneLoop 3)‖ = Real.sqrt 2 := by
  rw [Complex.norm_def, Complex.normSq_apply, coneLoop_re_3, coneLoop_im_3]
  congr 1; nlinarith [sq3]

theorem coneOv_0 : frameOverlap (lbVec (honeycombD (coneLoop 0)))
    (lbVec (honeycombD (coneLoop 1))) = 1 + (Real.sqrt 3 : ℝ) * Complex.I := by
  rw [Complex.ext_iff]
  refine ⟨?_, ?_⟩
  · rw [lbOv_cone_re, coneLoop_re_0, coneLoop_im_0, coneLoop_re_1, coneLoop_im_1,
      coneLoop_norm_0, coneLoop_norm_1]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [sq3, sq2]
  · rw [lbOv_cone_im, coneLoop_re_0, coneLoop_im_0, coneLoop_re_1, coneLoop_im_1]
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [sq3]

theorem coneOv_1 : frameOverlap (lbVec (honeycombD (coneLoop 1)))
    (lbVec (honeycombD (coneLoop 2))) = ((2 + Real.sqrt 3 : ℝ) : ℂ) - Complex.I := by
  refine Complex.ext ?_ ?_
  · rw [lbOv_cone_re, coneLoop_re_1, coneLoop_im_1, coneLoop_re_2, coneLoop_im_2,
      coneLoop_norm_1, coneLoop_norm_2]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero]
    nlinarith [sq3, sq2]
  · rw [lbOv_cone_im, coneLoop_re_1, coneLoop_im_1, coneLoop_re_2, coneLoop_im_2]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.I_im, zero_sub]
    nlinarith [sq3]

theorem coneOv_2 : frameOverlap (lbVec (honeycombD (coneLoop 2)))
    (lbVec (honeycombD (coneLoop 3))) = 1 + (Real.sqrt 3 : ℝ) * Complex.I := by
  rw [Complex.ext_iff]
  refine ⟨?_, ?_⟩
  · rw [lbOv_cone_re, coneLoop_re_2, coneLoop_im_2, coneLoop_re_3, coneLoop_im_3,
      coneLoop_norm_2, coneLoop_norm_3]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [sq3, sq2]
  · rw [lbOv_cone_im, coneLoop_re_2, coneLoop_im_2, coneLoop_re_3, coneLoop_im_3]
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [sq3]

theorem coneOv_3 : frameOverlap (lbVec (honeycombD (coneLoop 3)))
    (lbVec (honeycombD (coneLoop 0))) = ((2 - Real.sqrt 3 : ℝ) : ℂ) + Complex.I := by
  refine Complex.ext ?_ ?_
  · rw [lbOv_cone_re, coneLoop_re_3, coneLoop_im_3, coneLoop_re_0, coneLoop_im_0,
      coneLoop_norm_3, coneLoop_norm_0]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
    nlinarith [sq3, sq2]
  · rw [lbOv_cone_im, coneLoop_re_3, coneLoop_im_3, coneLoop_re_0, coneLoop_im_0]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]
    nlinarith [sq3]

/-- The Wilson-loop product around the cone is the **negative rational** `−16`. -/
theorem coneWilson_prod :
    (∏ j : Fin 4, frameOverlap (lbVec (honeycombD (coneLoop j)))
      (lbVec (honeycombD (coneLoop (j + 1))))) = -16 := by
  rw [Fin.prod_univ_four]
  rw [show ((0 : Fin 4) + 1) = 1 from rfl, show ((1 : Fin 4) + 1) = 2 from rfl,
    show ((2 : Fin 4) + 1) = 3 from rfl, show ((3 : Fin 4) + 1) = 0 from rfl]
  rw [coneOv_0, coneOv_1, coneOv_2, coneOv_3]
  set t : ℂ := ((Real.sqrt 3 : ℝ) : ℂ) with ht
  have h3 : t ^ 2 = 3 := by
    rw [ht, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
  have hA : (1 + t * Complex.I) * (1 + t * Complex.I) = -2 + 2 * t * Complex.I := by
    linear_combination (-1 : ℂ) * h3 + t ^ 2 * Complex.I_sq
  have hB : (2 + t - Complex.I) * (2 - t + Complex.I) = 2 + 2 * t * Complex.I := by
    linear_combination (-1 : ℂ) * h3 + (-1 : ℂ) * Complex.I_sq
  have hC : (-2 + 2 * t * Complex.I) * (2 + 2 * t * Complex.I) = -16 := by
    linear_combination (-4 : ℂ) * h3 + 4 * t ^ 2 * Complex.I_sq
  calc (1 + t * Complex.I) * (((2 + Real.sqrt 3 : ℝ) : ℂ) - Complex.I) * (1 + t * Complex.I)
        * (((2 - Real.sqrt 3 : ℝ) : ℂ) + Complex.I)
      = ((1 + t * Complex.I) * (1 + t * Complex.I))
          * ((2 + t - Complex.I) * (2 - t + Complex.I)) := by rw [ht]; push_cast; ring
    _ = (-2 + 2 * t * Complex.I) * (2 + 2 * t * Complex.I) := by rw [hA, hB]
    _ = -16 := hC

/-- **The cone Berry phase is exactly `π`.** The Wilson loop of the lower-band states around the
`π/2`-diamond enclosing the `K` Dirac point has argument `π` — the sublattice-pseudospin Berry
phase of the gapless Dirac cone. The product is the negative rational `−16`, so the value is exact,
not an enclosure. -/
theorem coneBerryPhase_pi :
    wilsonLoopArg (fun j : Fin 4 => lbVec (honeycombD (coneLoop j))) = Real.pi := by
  unfold wilsonLoopArg
  rw [coneWilson_prod, Complex.arg_eq_pi_iff]
  norm_num

/-! ### The pseudospin winding -/

theorem transAmp_re (a b : ℂ) : ((starRingEnd ℂ) a * b).re = a.re * b.re + a.im * b.im := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

theorem transAmp_im (a b : ℂ) : ((starRingEnd ℂ) a * b).im = a.re * b.im - a.im * b.re := by
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring

theorem coneLoop_ne_zero (j : Fin 4) : structureFactor (coneLoop j) ≠ 0 := by
  intro h
  have hn : ‖structureFactor (coneLoop j)‖ = Real.sqrt 2 := by
    fin_cases j
    exacts [coneLoop_norm_0, coneLoop_norm_1, coneLoop_norm_2, coneLoop_norm_3]
  rw [h, norm_zero] at hn
  exact absurd hn.symm (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

private theorem cos_5pi6 : Real.cos (5 * Real.pi / 6) = -(Real.sqrt 3 / 2) := by
  rw [show (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_six]

private theorem sin_5pi6 : Real.sin (5 * Real.pi / 6) = 1 / 2 := by
  rw [show (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 by ring, Real.sin_pi_sub,
    Real.sin_pi_div_six]

theorem coneArg_01 : Complex.arg ((starRingEnd ℂ) (structureFactor (coneLoop 0))
    * structureFactor (coneLoop 1)) = 2 * Real.pi / 3 := by
  refine arg_eq_of_polar (r := 2) (by norm_num)
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ ?_ ?_
  · rw [transAmp_re, coneLoop_re_0, coneLoop_im_0, coneLoop_re_1, coneLoop_im_1, cos_2pi3]
    nlinarith [sq3]
  · rw [transAmp_im, coneLoop_re_0, coneLoop_im_0, coneLoop_re_1, coneLoop_im_1, sin_2pi3]
    nlinarith [sq3]

theorem coneArg_12 : Complex.arg ((starRingEnd ℂ) (structureFactor (coneLoop 1))
    * structureFactor (coneLoop 2)) = -(Real.pi / 6) := by
  refine arg_eq_of_polar (r := 2) (by norm_num)
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ ?_ ?_
  · rw [transAmp_re, coneLoop_re_1, coneLoop_im_1, coneLoop_re_2, coneLoop_im_2, Real.cos_neg,
      Real.cos_pi_div_six]
    nlinarith [sq3]
  · rw [transAmp_im, coneLoop_re_1, coneLoop_im_1, coneLoop_re_2, coneLoop_im_2, Real.sin_neg,
      Real.sin_pi_div_six]
    nlinarith [sq3]

theorem coneArg_23 : Complex.arg ((starRingEnd ℂ) (structureFactor (coneLoop 2))
    * structureFactor (coneLoop 3)) = 2 * Real.pi / 3 := by
  refine arg_eq_of_polar (r := 2) (by norm_num)
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ ?_ ?_
  · rw [transAmp_re, coneLoop_re_2, coneLoop_im_2, coneLoop_re_3, coneLoop_im_3, cos_2pi3]
    nlinarith [sq3]
  · rw [transAmp_im, coneLoop_re_2, coneLoop_im_2, coneLoop_re_3, coneLoop_im_3, sin_2pi3]
    nlinarith [sq3]

theorem coneArg_30 : Complex.arg ((starRingEnd ℂ) (structureFactor (coneLoop 3))
    * structureFactor (coneLoop 0)) = 5 * Real.pi / 6 := by
  refine arg_eq_of_polar (r := 2) (by norm_num)
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ ?_ ?_
  · rw [transAmp_re, coneLoop_re_3, coneLoop_im_3, coneLoop_re_0, coneLoop_im_0, cos_5pi6]
    nlinarith [sq3]
  · rw [transAmp_im, coneLoop_re_3, coneLoop_im_3, coneLoop_re_0, coneLoop_im_0, sin_5pi6]
    nlinarith [sq3]

/-- **The sublattice pseudospin winds exactly once around the cone.** The four principal-branch
increments of the structure-factor phase around the `π/2`-diamond enclosing `K` are
`2π/3, −π/6, 2π/3, 5π/6`, and they sum to `2π`.

This is the discretized winding number `+1` of the Dirac cone — the topological charge that
`coneBerryPhase_pi` converts into the Berry phase `π`. -/
theorem coneWinding_two_pi :
    principal (Complex.arg (structureFactor (coneLoop 1))
        - Complex.arg (structureFactor (coneLoop 0)))
      + principal (Complex.arg (structureFactor (coneLoop 2))
        - Complex.arg (structureFactor (coneLoop 1)))
      + principal (Complex.arg (structureFactor (coneLoop 3))
        - Complex.arg (structureFactor (coneLoop 2)))
      + principal (Complex.arg (structureFactor (coneLoop 0))
        - Complex.arg (structureFactor (coneLoop 3)))
      = 2 * Real.pi := by
  rw [← arg_conj_mul_eq_principal_sub (coneLoop_ne_zero 0) (coneLoop_ne_zero 1),
    ← arg_conj_mul_eq_principal_sub (coneLoop_ne_zero 1) (coneLoop_ne_zero 2),
    ← arg_conj_mul_eq_principal_sub (coneLoop_ne_zero 2) (coneLoop_ne_zero 3),
    ← arg_conj_mul_eq_principal_sub (coneLoop_ne_zero 3) (coneLoop_ne_zero 0),
    coneArg_01, coneArg_12, coneArg_23, coneArg_30]
  ring

/-- **The sampling is nowhere near the branch cut.** Every one of the four principal-branch
increments around the cone loop keeps a margin of at least `π/6` from `±π`:

    |Δⱼ| + π/6  ≤  π      for each j,

with equality at `j = 3` (`Δ₃ = 5π/6`), so `π/6` is the *tight* margin. The four increments are
`2π/3, −π/6, 2π/3, 5π/6`.

**What this does and does not certify.** A four-point sampling of a loop reports the wrong winding
when some edge's true phase change exceeds `π` and gets folded back — the aliasing failure mode. An
increment sitting *at* `±π` is the marginal case where that folding is undetectable; this theorem
rules that case out quantitatively, so `coneWinding_two_pi` is not a knife-edge reading. It does
**not** amount to a proof that the continuous path between samples carries no extra winding — that
would need a bound on `‖f‖` along the edges, which is a genuine analytic program this wave does not
open. The honest status is: non-marginal, not certified alias-free. -/
theorem coneWinding_increments_off_branch_cut (j : Fin 4) :
    |principal (Complex.arg (structureFactor (coneLoop (j + 1)))
        - Complex.arg (structureFactor (coneLoop j)))| + Real.pi / 6 ≤ Real.pi := by
  have hpi := Real.pi_pos
  fin_cases j
  · show |principal (Complex.arg (structureFactor (coneLoop 1))
        - Complex.arg (structureFactor (coneLoop 0)))| + Real.pi / 6 ≤ Real.pi
    rw [← arg_conj_mul_eq_principal_sub (coneLoop_ne_zero 0) (coneLoop_ne_zero 1), coneArg_01,
      abs_of_nonneg (by linarith)]
    linarith
  · show |principal (Complex.arg (structureFactor (coneLoop 2))
        - Complex.arg (structureFactor (coneLoop 1)))| + Real.pi / 6 ≤ Real.pi
    rw [← arg_conj_mul_eq_principal_sub (coneLoop_ne_zero 1) (coneLoop_ne_zero 2), coneArg_12,
      abs_of_nonpos (by linarith)]
    linarith
  · show |principal (Complex.arg (structureFactor (coneLoop 3))
        - Complex.arg (structureFactor (coneLoop 2)))| + Real.pi / 6 ≤ Real.pi
    rw [← arg_conj_mul_eq_principal_sub (coneLoop_ne_zero 2) (coneLoop_ne_zero 3), coneArg_23,
      abs_of_nonneg (by linarith)]
    linarith
  · show |principal (Complex.arg (structureFactor (coneLoop 0))
        - Complex.arg (structureFactor (coneLoop 3)))| + Real.pi / 6 ≤ Real.pi
    rw [← arg_conj_mul_eq_principal_sub (coneLoop_ne_zero 3) (coneLoop_ne_zero 0), coneArg_30,
      abs_of_nonneg (by linarith)]
    linarith

/-! ### Contrast: a non-winding loop has Berry phase `0` -/

/-- A three-point loop through Γ and the two `M` points. It does **not** enclose a Dirac point and
its pseudospin does not wind: all three structure-factor values are positive reals. -/
noncomputable def flatLoop : Fin 3 → ℝ × ℝ
  | 0 => gammaPoint
  | 1 => mPoint
  | 2 => (0, Real.pi)

theorem flatLoop_f_0 : structureFactor (flatLoop 0) = 3 := structureFactor_gamma
theorem flatLoop_f_1 : structureFactor (flatLoop 1) = 1 := structureFactor_mPoint

theorem flatLoop_f_2 : structureFactor (flatLoop 2) = 1 := by
  show structureFactor (0, Real.pi) = 1
  unfold structureFactor
  simp [Complex.exp_mul_I]

theorem flatLoop_ov (j j' : Fin 3) (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hj : structureFactor (flatLoop j) = (x : ℂ)) (hj' : structureFactor (flatLoop j') = (y : ℂ)) :
    frameOverlap (lbVec (honeycombD (flatLoop j))) (lbVec (honeycombD (flatLoop j')))
      = ((2 * x * y : ℝ) : ℂ) := by
  refine Complex.ext ?_ ?_
  · rw [lbOv_cone_re, hj, hj']
    simp [Complex.norm_real, abs_of_pos hx, abs_of_pos hy]
    ring
  · rw [lbOv_cone_im, hj, hj']
    simp

/-- **The non-winding loop carries Berry phase `0`.** Same construction, same band, but the
pseudospin phase never turns: the Wilson product is the positive rational `72`.

**What the contrast establishes — precisely.** Together with `coneBerryPhase_pi` this shows the `π`
is *discriminating*: it separates a loop that encloses a Dirac point from one that does not, rather
than being produced by the four-point construction itself. It does **not** show the `π` is free of
*discretization* error. On this loop `f` is a positive real at all three vertices, so every phase
increment is `0`; a loop that cannot turn at all cannot detect undersampling, and contrasting
against it tests **winding**, not sampling density. The sampling-related guarantee is the separate
`coneWinding_increments_off_branch_cut` (every cone increment keeps a tight `π/6` margin from the
branch cut), and even that certifies non-marginality rather than freedom from aliasing.

*(An earlier version of this docstring claimed the contrast made the `π` "not an artefact of the
discretization". Corrected 2026-07-29: it makes it not an artefact of the **construction**.)* -/
theorem flatLoopBerryPhase_zero :
    wilsonLoopArg (fun j : Fin 3 => lbVec (honeycombD (flatLoop j))) = 0 := by
  unfold wilsonLoopArg
  rw [Fin.prod_univ_three, show ((0 : Fin 3) + 1) = 1 from rfl,
    show ((1 : Fin 3) + 1) = 2 from rfl, show ((2 : Fin 3) + 1) = 0 from rfl,
    flatLoop_ov 0 1 3 1 (by norm_num) (by norm_num) (by rw [flatLoop_f_0]; norm_num)
      (by rw [flatLoop_f_1]; norm_num),
    flatLoop_ov 1 2 1 1 (by norm_num) (by norm_num) (by rw [flatLoop_f_1]; norm_num)
      (by rw [flatLoop_f_2]; norm_num),
    flatLoop_ov 2 0 1 3 (by norm_num) (by norm_num) (by rw [flatLoop_f_2]; norm_num)
      (by rw [flatLoop_f_0]; norm_num)]
  norm_num

theorem principal_zero : principal 0 = 0 := by
  have h := principal_add_branch 0
  rw [branchIndex_zero] at h
  simpa using h

/-- **The non-winding loop's pseudospin does not turn.** All three structure-factor values are
positive reals, so every principal-branch increment is `0` and the winding is `0` — against the
cone's `2π` (`coneWinding_two_pi`). The winding, not the Berry phase, is where the two loops
actually differ; the phase difference `π` vs `0` follows. -/
theorem flatWinding_zero :
    principal (Complex.arg (structureFactor (flatLoop 1))
        - Complex.arg (structureFactor (flatLoop 0)))
      + principal (Complex.arg (structureFactor (flatLoop 2))
        - Complex.arg (structureFactor (flatLoop 1)))
      + principal (Complex.arg (structureFactor (flatLoop 0))
        - Complex.arg (structureFactor (flatLoop 2)))
      = 0 := by
  have a0 : Complex.arg (structureFactor (flatLoop 0)) = 0 := by
    rw [flatLoop_f_0]; exact Complex.arg_ofReal_of_nonneg (by norm_num)
  have a1 : Complex.arg (structureFactor (flatLoop 1)) = 0 := by
    rw [flatLoop_f_1, Complex.arg_one]
  have a2 : Complex.arg (structureFactor (flatLoop 2)) = 0 := by
    rw [flatLoop_f_2, Complex.arg_one]
  rw [a0, a1, a2, sub_zero, principal_zero]
  ring

end SKEFTHawking.GrapheneBand
