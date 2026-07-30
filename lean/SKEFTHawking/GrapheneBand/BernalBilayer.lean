import SKEFTHawking.GrapheneBand.DiracExpansion

/-!
# Bernal-stacked bilayer graphene: quadratic band touching and the field-tunable gap
(Phase 6ED, Wave 4)

Waves 1–3 built the *monolayer*: the honeycomb structure factor and its Dirac zero set (Wave 1),
the linear dispersion with an explicit remainder (Wave 2), and the Haldane Chern witness (Wave 3).
This wave supplies the other electronic structure the graphene corpus cites — **Bernal (AB) bilayer**
— whose two headline properties are qualitatively *unlike* the monolayer's:

* at zero interlayer bias the low bands touch **quadratically**, not linearly, and
* a perpendicular displacement field **opens a gap** — electrical gap tunability (shared with
  rhombohedral ABC multilayers, not unique to the bilayer). The repo's analog-fluid side
  (`DiracFluidWKB`, `GrapheneNoiseFormula`) specifies a *bilayer* de Laval nozzle, so this is the
  band structure those modules are implicitly about.

## The model, and why everything here is polynomial

In the sublattice basis `(A1, B1, A2, B2)` with intralayer hopping element `f`, dimer (interlayer)
coupling `γ`, and interlayer bias `±u` (so the full bias is `U = 2u`):

    H = [  u    f    0    0  ]
        [  f̄    u    γ    0  ]
        [  0    γ   −u    f  ]
        [  0    0    f̄   −u  ]

`B1` and `A2` are the dimer sites (coupled by `γ`); `A1` and `B2` are the non-dimer sites that carry
the low-energy bands. **Both layers carry `f`, not `f̄`**: in AB stacking the two layers are the same
honeycomb in the same orientation, so their A→B bond vectors coincide (McCann–Koshino Eq. (16)).
Getting this wrong is invisible to the spectrum — see the chirality section.

The whole wave rests on one computation, `bernal_det_eq`: the 4×4 secular determinant collapses to a
**quadratic in `w = E² − u²`**,

    det (H − E) = w² − (γ² + 2x)·w + x·(x − 4u²),      x = ‖f‖².

So no eigenvalue machinery and no `Complex.arg` sector calculus are needed — every band statement
below is a statement about the roots of one real quadratic, provable by polynomial arithmetic.
(`Real.sqrt` appears only inside two existence witnesses, never in a bound.) That is a deliberate
architectural choice: Wave 3 paid a heavy price for transcendental `arg` evaluation, and this wave
is designed so the same content is reachable by `nlinarith`.

## What is proved

**The polynomial is the spectrum, not a lookalike.** `bernal_eigenvector_iff` proves that `E` is a
root of the secular quadratic exactly when it carries a nonzero Bloch eigenvector of the matrix, so
every root statement below is a statement about the model's bands; `bernal_touching_of_eigenvector`
and `bernal_field_gap_of_eigenvector` are the eigenvector-level forms a consumer should cite.
`bernal_secular_discrim_nonneg` gives nonnegative discriminant (both `w`-roots real) and
`bernal_bands_real` closes the remaining step (`u² + w ≥ 0`), so all four band energies are real.

**Chirality — the invariant a determinant cannot see.** `bernal_chirality_two` proves the exact
`J = 2` relation `E·(γ·v_A1 − f·v_A2) = −f²·v_B2` for every eigenvector (McCann–Koshino Eq. (40)).
`bernal_spectrum_not_determine_model` is the companion negative result: `bernalBlochSwapped` — the
same matrix with layer 2 conjugated — is *also* Hermitian and has the *identical* characteristic
polynomial at every parameter point, yet `bernalSwapped_chirality_zero` gives it the phase-blind
coefficient `f·f̄` instead of `f²`. So the spectrum does not determine the model. This section exists
because the first pass of this file shipped the conjugated matrix and every spectral gate passed.

**Zero bias (`u = 0`) — the quadratic touching.** The low root obeys the two-sided *global*
enclosure `x²/γ² − 2x³/γ⁴ ≤ w ≤ x²/γ²` (`bernal_lowRoot_enclosure`), i.e. `E ≈ ‖f‖²/γ`. Converted to
an energy statement with an explicit remainder on a stated ball,
`|E| ∈ [x/γ − 2x²/γ³, x/γ]` for `x ≤ γ²/2` (`bernal_touching_energy_enclosure`); the non-vacuity
witness `bernal_touching_not_exact_in_ball` sits **inside** that ball, and
`bernal_touching_witness_exists` exhibits the root `w = (3 − 2√2)/4` so the witness is not vacuous.
The contrast with the monolayer is a theorem: `bernal_sub_linear_of_monolayer` instantiates at an
actual honeycomb momentum and concludes against Wave 1's own `honeycomb_energy_eq`.
`bernal_touching_ratio_le` bounds `w/x` by `x/γ²` — a ratio of *squared* energies, so it vanishes
linearly in `x` and hence quadratically in momentum; a Dirac cone would hold it at a constant.

**Nonzero bias — the gap, and the Mexican hat.** Every band energy satisfies
`u²γ² ≤ E²·(γ² + 4u²)` (`bernal_field_gap`), strictly positive for `u ≠ 0`
(`bernal_field_gap_pos`), and that floor is **attained** (`bernal_field_gap_attained`);
`bernal_halfGapSq_isLeast` packages the two into a genuine `IsLeast`. The proof is a perfect-square
identity: `(γ²+4u²)²·Q(m) = (2u²(γ²+2u²) − (γ²+4u²)x)²`.

> **Convention — half-gap versus full gap.** `u²γ²/(γ²+4u²)` is `min E²`, the **half**-gap squared.
> The **full** band gap is `2·min|E|`, whose square is `4u²γ²/(γ²+4u²) = U²γ²/(γ²+U²)` in the bias
> variable `U = 2u` (`bernal_fullGapSq_eq`) — the published `U_g = |U|γ₁/√(γ₁²+U²)`. The two differ
> by a factor 4; every statement in this file uses the half-gap unless it says otherwise.

**The naive claim is refuted.** The gap is *not* the bias `U`: `bernal_mexicanHat` exhibits a
strictly positive momentum where `E² < u²`, so the band minimum sits at finite momentum and the true
gap is strictly below `|U|`. Shipping the gap theorem without this would leave the phase asserting
the textbook-wrong "gap = bias".

## Scope discipline

Theorems are about the stated 4×4 lattice Hamiltonian. Identifying `γ`, `f`, or `u` with any
physical sample (measured dimer coupling, hopping energy, applied displacement field) is a
consumer-side hypothesis, per the phase's standing guardrail. `bernalEffectiveMass` is the one place
a physical parametrization appears; it is stated *parametrically* and made load-bearing by
`bernal_effectiveMass_eq` (which calls Wave 2's `fermiVelocity`), `bernal_effectiveMass_dispersion`
(which proves the `E = ℏ²p²/(2m*)` reading), and `bernal_lowBand_effectiveMass` (which chains it to
an actual band energy with an explicit remainder).
-/

namespace SKEFTHawking.GrapheneBand

open Complex Real SKEFTHawking.Topological

/-! ## The Hamiltonian and its secular polynomial -/

/-- The Bernal (AB-stacked) bilayer Bloch Hamiltonian in the sublattice basis `(A1, B1, A2, B2)`.
`u` is the half-bias (the full interlayer bias is `U = 2u`), `γ` the dimer coupling, `f` the
intralayer hopping element (Wave 1's `structureFactor`, optionally scaled by the hopping `t`). -/
noncomputable def bernalBloch (u γ : ℝ) (f : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(u : ℂ), f, 0, 0;
     (starRingEnd ℂ) f, (u : ℂ), (γ : ℂ), 0;
     0, (γ : ℂ), (-u : ℂ), f;
     0, 0, (starRingEnd ℂ) f, (-u : ℂ)]

/-- **The conjugated look-alike** — the same matrix with layer 2's intralayer element conjugated.
In AB stacking both layers are the *same* honeycomb in the *same* orientation, so their A→B bond
vectors coincide and the layer-2 element is `f`, not `f̄`; this object is therefore **not** a Bernal
bilayer (it is layer 2 with its sublattices exchanged). It is shipped deliberately, as the
counterexample carrier for `bernal_spectrum_not_determine_model`: it is Hermitian, and it has the
*identical* characteristic polynomial, yet its low-energy chirality is `0` rather than `2`. -/
noncomputable def bernalBlochSwapped (u γ : ℝ) (f : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(u : ℂ), f, 0, 0;
     (starRingEnd ℂ) f, (u : ℂ), (γ : ℂ), 0;
     0, (γ : ℂ), (-u : ℂ), (starRingEnd ℂ) f;
     0, 0, f, (-u : ℂ)]

/-- The secular polynomial of `bernalBloch`, as a quadratic in `w = E² − u²` with `x = ‖f‖²`.
This is the object every band theorem in this file is about. -/
def bernalSecular (u γ x w : ℝ) : ℝ :=
  w ^ 2 - (γ ^ 2 + 2 * x) * w + x * (x - 4 * u ^ 2)

/-- **Laplace expansion of a 4×4 determinant along the first row.** Mathlib ships `det_fin_one`
through `det_fin_three` and stops; this is the missing fourth case, stated for a general
`CommRing`. It is Mathlib-grade infrastructure with no project-specific content and is the only
reason `bernal_det_eq` is a two-line proof. -/
theorem det_fin_four {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
      M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) - M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
          + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1))
    - M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) - M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
          + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0))
    + M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) - M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
          + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))
    - M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) - M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)
          + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- `bernalBloch` is Hermitian, so it is a legitimate quantum Hamiltonian. Note this is forced by
the conjugate pairing *within* each 2×2 block and does **not** pin down the layer-2 orientation —
`bernalBlochSwapped` is equally Hermitian, which is precisely what gives
`bernal_spectrum_not_determine_model` its force. -/
theorem bernalBloch_isHermitian (u γ : ℝ) (f : ℂ) : (bernalBloch u γ f).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bernalBloch, Matrix.conjTranspose_apply, Complex.conj_ofReal]

/-- **The secular collapse.** The 4×4 determinant is a quadratic in `w = E² − u²`. Everything else
in this file is polynomial arithmetic on this identity. -/
theorem bernal_det_eq (u γ E : ℝ) (f : ℂ) :
    (bernalBloch u γ f - (E : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)).det
      = ((bernalSecular u γ (normSq f) (E ^ 2 - u ^ 2) : ℝ) : ℂ) := by
  have hff : f * (starRingEnd ℂ) f = ((normSq f : ℝ) : ℂ) := by
    rw [mul_comm, Complex.normSq_eq_conj_mul_self]
  have hM : bernalBloch u γ f - (E : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) =
      !![(u : ℂ) - E, f, 0, 0;
         (starRingEnd ℂ) f, (u : ℂ) - E, (γ : ℂ), 0;
         0, (γ : ℂ), -(u : ℂ) - E, f;
         0, 0, (starRingEnd ℂ) f, -(u : ℂ) - E] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bernalBloch]
  rw [hM, det_fin_four]
  simp only [bernalSecular, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val]
  push_cast
  linear_combination (-2 * ((E : ℂ) ^ 2 - (u : ℂ) ^ 2) + f * (starRingEnd ℂ) f
    + ((normSq f : ℝ) : ℂ) - 4 * (u : ℂ) ^ 2) * hff

/-- **Both `w`-roots are real.** The secular quadratic in `w` has nonnegative discriminant
`γ⁴ + 4x(γ² + 4u²)` for every `x ≥ 0`. Note this gives reality of the roots *in `w`*; reality of the
band energies themselves additionally needs `u² + w ≥ 0`, which is `bernal_bands_real` below. -/
theorem bernal_secular_discrim_nonneg (u γ x : ℝ) (hx : 0 ≤ x) :
    0 ≤ (γ ^ 2 + 2 * x) ^ 2 - 4 * (x * (x - 4 * u ^ 2)) := by
  have hexp : (γ ^ 2 + 2 * x) ^ 2 - 4 * (x * (x - 4 * u ^ 2))
      = γ ^ 4 + 4 * x * (γ ^ 2 + 4 * u ^ 2) := by ring
  rw [hexp]
  positivity

/-- **The four band energies are real.** Closing the step `bernal_secular_discrim_nonneg` leaves
open: every root `w` of the secular quadratic satisfies `u² + w ≥ 0`, so `E = ±√(u² + w)` is real.
Holds for **every** `γ` — no positivity hypothesis is needed, since at `γ = 0` the roots are
`x ± 2u√x` and `u² + w = (u ∓ √x)² ≥ 0` regardless. -/
theorem bernal_bands_real (u γ x w : ℝ) (hx : 0 ≤ x)
    (hw : bernalSecular u γ x w = 0) : 0 ≤ u ^ 2 + w := by
  by_contra hcon
  push Not at hcon
  -- If `u² + w < 0` the quadratic's value at `w` is strictly positive, contradicting `= 0`.
  unfold bernalSecular at hw
  nlinarith [hw, hx, sq_nonneg (w - u ^ 2), sq_nonneg w, sq_nonneg u, sq_nonneg (w + u ^ 2),
    mul_nonneg hx hx, sq_nonneg (x - u ^ 2), sq_nonneg γ]

/-- **The bridge from the polynomial to actual eigenvectors.** `E` carries a nonzero Bloch
eigenvector of `bernalBloch` exactly when it is a root of the secular quadratic. Without this every
theorem below would be a statement about a polynomial that merely *resembles* a band structure;
with it, they are statements about the model's spectrum. -/
theorem bernal_eigenvector_iff (u γ E : ℝ) (f : ℂ) :
    (∃ v ≠ 0, (bernalBloch u γ f - (E : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)).mulVec v = 0)
      ↔ bernalSecular u γ (normSq f) (E ^ 2 - u ^ 2) = 0 := by
  rw [Matrix.exists_mulVec_eq_zero_iff, bernal_det_eq]
  exact_mod_cast Complex.ofReal_eq_zero

/-! ## Chirality: the invariant the determinant cannot see

The four theorems below exist because of a defect found in adversarial review: the first pass of
`bernalBloch` had layer 2's intralayer element conjugated, which is **not** Bernal stacking, and
*every* spectral check passed anyway — the characteristic polynomial is identical under that swap.
Only an eigenvector-level invariant separates the two models. Standing lesson for any future
multi-band Hamiltonian in this project: verify a winding / Berry-phase / chirality statement against
the primary source, not just the spectrum. -/

/-- **Chirality 2, exactly.** For any eigenvector of the unbiased bilayer, the `A1` and `B2`
amplitudes are tied to each other through `f²` — the `J = 2` structure of McCann–Koshino Eq. (40).
This is an *exact* consequence of the four eigenvector equations, with no dimer-elimination
approximation: it is obtained by substituting the `A2` row into the `A1` row. -/
theorem bernal_chirality_two (γ E : ℝ) (f : ℂ) (v : Fin 4 → ℂ)
    (hv : (bernalBloch 0 γ f).mulVec v = (E : ℂ) • v) :
    (E : ℂ) * ((γ : ℂ) * v 0 - f * v 2) = -(f ^ 2) * v 3 := by
  have h0 := congrFun hv 0
  have h2 := congrFun hv 2
  simp only [bernalBloch, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val, Pi.smul_apply, smul_eq_mul] at h0 h2
  push_cast at h0 h2 ⊢
  linear_combination -(γ : ℂ) * h0 + f * h2

/-- The mirror identity on the other sublattice: `B2` and `A1` are tied through `f̄²`. -/
theorem bernal_chirality_two' (γ E : ℝ) (f : ℂ) (v : Fin 4 → ℂ)
    (hv : (bernalBloch 0 γ f).mulVec v = (E : ℂ) • v) :
    (E : ℂ) * ((γ : ℂ) * v 3 - (starRingEnd ℂ) f * v 1) = -((starRingEnd ℂ) f ^ 2) * v 0 := by
  have h3 := congrFun hv 3
  have h1 := congrFun hv 1
  simp only [bernalBloch, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val, Pi.smul_apply, smul_eq_mul] at h1 h3
  push_cast at h1 h3 ⊢
  linear_combination (starRingEnd ℂ) f * h1 - (γ : ℂ) * h3

/-- **The look-alike has chirality 0.** The same substitution on `bernalBlochSwapped` produces
`f·f̄ = ‖f‖²` — a *real, phase-blind* coefficient — where the genuine bilayer produces `f²`. -/
theorem bernalSwapped_chirality_zero (γ E : ℝ) (f : ℂ) (v : Fin 4 → ℂ)
    (hv : (bernalBlochSwapped 0 γ f).mulVec v = (E : ℂ) • v) :
    (E : ℂ) * ((γ : ℂ) * v 0 - f * v 2) = -(f * (starRingEnd ℂ) f) * v 3 := by
  have h0 := congrFun hv 0
  have h2 := congrFun hv 2
  simp only [bernalBlochSwapped, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Pi.smul_apply,
    smul_eq_mul] at h0 h2
  push_cast at h0 h2 ⊢
  linear_combination -(γ : ℂ) * h0 + f * h2

/-- **The spectrum does not determine the model.** `bernalBlochSwapped` has the *same*
characteristic polynomial as `bernalBloch` at every parameter point — so it passes every spectral
test in this file, including the exact gap and the quadratic touching — yet the two matrices are
different, and their chirality coefficients (`f²` versus `f·f̄`) differ at, e.g., `f = i`.

This is the kernel-checked form of the review finding: *a determinant-level gate cannot certify a
multi-band model's identification.* -/
theorem bernal_spectrum_not_determine_model :
    (∀ u γ : ℝ, ∀ f : ℂ, (bernalBlochSwapped u γ f).IsHermitian)
      ∧ (∀ u γ E : ℝ, ∀ f : ℂ,
        (bernalBlochSwapped u γ f - (E : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)).det
          = (bernalBloch u γ f - (E : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)).det)
      ∧ bernalBlochSwapped 0 1 Complex.I ≠ bernalBloch 0 1 Complex.I
      ∧ (Complex.I : ℂ) ^ 2 ≠ Complex.I * (starRingEnd ℂ) Complex.I := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u γ f
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bernalBlochSwapped, Matrix.conjTranspose_apply, Complex.conj_ofReal]
  · intro u γ E f
    rw [bernal_det_eq]
    have hff : f * (starRingEnd ℂ) f = ((normSq f : ℝ) : ℂ) := by
      rw [mul_comm, Complex.normSq_eq_conj_mul_self]
    have hM : bernalBlochSwapped u γ f - (E : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) =
        !![(u : ℂ) - E, f, 0, 0;
           (starRingEnd ℂ) f, (u : ℂ) - E, (γ : ℂ), 0;
           0, (γ : ℂ), -(u : ℂ) - E, (starRingEnd ℂ) f;
           0, 0, f, -(u : ℂ) - E] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [bernalBlochSwapped]
    rw [hM, det_fin_four]
    simp only [bernalSecular, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val]
    push_cast
    linear_combination (-2 * ((E : ℂ) ^ 2 - (u : ℂ) ^ 2) + f * (starRingEnd ℂ) f
      + ((normSq f : ℝ) : ℂ) - 4 * (u : ℂ) ^ 2) * hff
  · intro hcon
    have h := congrFun (congrFun hcon 2) 3
    simp [bernalBloch, bernalBlochSwapped, Complex.ext_iff] at h
    norm_num at h
  · simp [Complex.ext_iff]
    norm_num

/-! ## Zero bias: the quadratic band touching -/

/-- At zero bias the secular quadratic has nonnegative roots (its product of roots is `x² ≥ 0` and
its sum `γ² + 2x > 0`). -/
theorem bernal_root_nonneg (γ x w : ℝ) (hγ : 0 < γ) (hx : 0 ≤ x)
    (hw : bernalSecular 0 γ x w = 0) : 0 ≤ w := by
  by_contra h
  push Not at h
  have h1 : 0 < -w := by linarith
  have h2 : 0 < (γ ^ 2 + 2 * x) * (-w) := by positivity
  unfold bernalSecular at hw
  nlinarith [sq_nonneg w, sq_nonneg x]

/-- **The quadratic band touching, as a global two-sided enclosure of the low root.** With `w` the
smaller root of the zero-bias secular quadratic (`2w ≤ γ² + 2x` selects it),

    x²/γ² − 2x³/γ⁴  ≤  w  ≤  x²/γ².

Both bounds hold for **all** `x ≥ 0` — there is no validity ball at the root level, and no
`O`-notation anywhere: the remainder constant is `2`. -/
theorem bernal_lowRoot_enclosure (γ x w : ℝ) (hγ : 0 < γ) (hx : 0 ≤ x)
    (hw : bernalSecular 0 γ x w = 0) (hlow : 2 * w ≤ γ ^ 2 + 2 * x) :
    x ^ 2 / γ ^ 2 - 2 * x ^ 3 / γ ^ 4 ≤ w ∧ w ≤ x ^ 2 / γ ^ 2 := by
  have hγ2 : (0 : ℝ) < γ ^ 2 := by positivity
  have hγ4 : (0 : ℝ) < γ ^ 4 := by positivity
  have hw0 : 0 ≤ w := bernal_root_nonneg γ x w hγ hx hw
  unfold bernalSecular at hw
  -- The root equation in product form: `w·(γ² + 2x − w) = x²`.
  have hprod : w * (γ ^ 2 + 2 * x - w) = x ^ 2 := by nlinarith [hw]
  -- `w ≤ 2x`: otherwise `x² = w(γ²+2x−w) ≥ w² > 4x² ≥ x²`.
  have hw2x : w ≤ 2 * x := by
    by_contra hcon
    push Not at hcon
    nlinarith [hprod, hlow, hw0, hx, sq_nonneg (w - 2 * x), sq_nonneg x]
  -- Upper bound, denominator-free: `γ²·w ≤ x²`.
  have hup : γ ^ 2 * w ≤ x ^ 2 := by nlinarith [hprod, hw0, hw2x]
  constructor
  · rw [div_sub_div _ _ (ne_of_gt hγ2) (ne_of_gt hγ4), div_le_iff₀ (by positivity)]
    -- `γ⁴w = γ²(x² − 2xw + w²)`, and `2γ²xw ≤ 2x³` from `hup`.
    nlinarith [hup, hx, hγ2, sq_nonneg w, mul_nonneg hx hw0,
      mul_le_mul_of_nonneg_left hup hx, mul_nonneg (mul_nonneg hx hw0) hw0]
  · rw [le_div_iff₀ hγ2]
    linarith [hup]

/-- The same content as an **energy** statement: at zero bias the band energy squared is enclosed
between `(x/γ)² − 2x³/γ⁴` and `(x/γ)²`. -/
theorem bernal_touching_energy_sq (γ x E : ℝ) (hγ : 0 < γ) (hx : 0 ≤ x)
    (hE : bernalSecular 0 γ x (E ^ 2) = 0) (hlow : 2 * E ^ 2 ≤ γ ^ 2 + 2 * x) :
    (x / γ) ^ 2 - 2 * x ^ 3 / γ ^ 4 ≤ E ^ 2 ∧ E ^ 2 ≤ (x / γ) ^ 2 := by
  have h := bernal_lowRoot_enclosure γ x (E ^ 2) hγ hx hE hlow
  rw [div_pow]
  exact h

/-- **The enclosure, stated about the matrix rather than the polynomial.** Same conclusion as
`bernal_touching_energy_sq`, but the hypothesis is that `E` actually carries a nonzero Bloch
eigenvector of `bernalBloch 0 γ f` — routed through `bernal_eigenvector_iff`. This is the form a
consumer should cite; the polynomial-level versions are the working lemmas behind it. -/
theorem bernal_touching_of_eigenvector (γ E : ℝ) (f : ℂ) (hγ : 0 < γ)
    (hev : ∃ v ≠ 0, (bernalBloch 0 γ f - (E : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)).mulVec v = 0)
    (hlow : 2 * E ^ 2 ≤ γ ^ 2 + 2 * normSq f) :
    (normSq f / γ) ^ 2 - 2 * normSq f ^ 3 / γ ^ 4 ≤ E ^ 2
      ∧ E ^ 2 ≤ (normSq f / γ) ^ 2 := by
  have hroot : bernalSecular 0 γ (normSq f) (E ^ 2) = 0 := by
    have := (bernal_eigenvector_iff 0 γ E f).mp hev
    simpa using this
  exact bernal_touching_energy_sq γ (normSq f) E hγ (normSq_nonneg f) hroot hlow

/-- **"Quadratic, not linear", quantified.** The ratio of *squared* band energies, bilayer to
monolayer, is `w/x`, and it is bounded by `x/γ²` — so it vanishes linearly in `x`, hence
**quadratically in momentum**. A Dirac cone would hold this ratio at a positive constant. -/
theorem bernal_touching_ratio_le (γ x w : ℝ) (hγ : 0 < γ) (hx : 0 < x)
    (hw : bernalSecular 0 γ x w = 0) (hlow : 2 * w ≤ γ ^ 2 + 2 * x) :
    w / x ≤ x / γ ^ 2 := by
  obtain ⟨_, hhi⟩ := bernal_lowRoot_enclosure γ x w hγ hx.le hw hlow
  have hγ2 : (0 : ℝ) < γ ^ 2 := by positivity
  rw [le_div_iff₀ hγ2] at hhi
  rw [div_le_div_iff₀ hx hγ2]
  nlinarith [hhi]

/-- **The explicit-remainder form on a stated ball.** For `x ≤ γ²/2` the band energy sits within
`2x²/γ³` of `x/γ`:  `x/γ − 2x²/γ³ ≤ |E| ≤ x/γ`. The remainder is *quadratic in `x`*, hence quartic
in momentum — the precise sense in which the touching is quadratic. -/
theorem bernal_touching_energy_enclosure (γ x E : ℝ) (hγ : 0 < γ) (hx : 0 ≤ x)
    (hball : x ≤ γ ^ 2 / 2) (hE : bernalSecular 0 γ x (E ^ 2) = 0)
    (hlow : 2 * E ^ 2 ≤ γ ^ 2 + 2 * x) :
    x / γ - 2 * x ^ 2 / γ ^ 3 ≤ |E| ∧ |E| ≤ x / γ := by
  obtain ⟨hlo, hhi⟩ := bernal_touching_energy_sq γ x E hγ hx hE hlow
  have hxγ : 0 ≤ x / γ := by positivity
  constructor
  · rcases le_or_gt (x / γ - 2 * x ^ 2 / γ ^ 3) 0 with h | h
    · exact h.trans (abs_nonneg E)
    · have hsq : (x / γ - 2 * x ^ 2 / γ ^ 3) ^ 2 ≤ E ^ 2 := by
        -- The squared leading form is below the enclosure's lower endpoint, by `2x³(γ² − 2x)/γ⁶`,
        -- which is nonnegative exactly on the stated ball `x ≤ γ²/2`.
        have key : (x / γ - 2 * x ^ 2 / γ ^ 3) ^ 2 ≤ (x / γ) ^ 2 - 2 * x ^ 3 / γ ^ 4 := by
          rw [← sub_nonneg]
          have hEq : (x / γ) ^ 2 - 2 * x ^ 3 / γ ^ 4 - (x / γ - 2 * x ^ 2 / γ ^ 3) ^ 2
              = (2 * x ^ 3 * (γ ^ 2 - 2 * x)) / γ ^ 6 := by
            field_simp; ring
          rw [hEq]
          apply div_nonneg _ (by positivity)
          have : (0 : ℝ) ≤ γ ^ 2 - 2 * x := by linarith
          positivity
        linarith [key, hlo]
      nlinarith [abs_nonneg E, sq_abs E, h]
  · have hsq : E ^ 2 ≤ (x / γ) ^ 2 := hhi
    nlinarith [abs_nonneg E, sq_abs E, hxγ]

/-- **Non-vacuity, stated where the theorem applies.** At `γ = 1`, `x = 1/4` — *inside* the ball
`x ≤ γ²/2 = 1/2` of `bernal_touching_energy_enclosure` — the leading term `x/γ` is not the exact
band energy: the low root is strictly below `x²/γ² = 1/16`. So the remainder term is doing work, and
the enclosure is not a restatement of an equality. -/
theorem bernal_touching_not_exact_in_ball (w : ℝ)
    (hw : bernalSecular 0 1 (1 / 4) w = 0) (hlow : 2 * w ≤ 1 ^ 2 + 2 * (1 / 4)) :
    w < 1 / 16 := by
  unfold bernalSecular at hw
  nlinarith [sq_nonneg (w - 1 / 16), sq_nonneg w]

/-- **The witness above is not vacuous** — the root it hypothesises exists, and is exhibited:
`w = (3 − 2√2)/4 ≈ 0.0429`, the genuine low root at `γ = 1`, `x = 1/4`. It sits strictly below the
leading term `x²/γ² = 1/16 = 0.0625` and strictly above the enclosure's lower endpoint
`1/16 − 2·(1/4)³ = 1/32`, so the two-sided enclosure is doing real work at this point. Without this
existence statement `bernal_touching_not_exact_in_ball` could have been vacuously true. -/
theorem bernal_touching_witness_exists :
    ∃ w : ℝ, bernalSecular 0 1 (1 / 4) w = 0 ∧ 2 * w ≤ 1 ^ 2 + 2 * (1 / 4)
      ∧ 1 / 32 < w ∧ w < 1 / 16 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hlb : (1.41 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hub : Real.sqrt 2 < 1.415 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  refine ⟨(3 - 2 * Real.sqrt 2) / 4, ?_, by nlinarith, by nlinarith, by nlinarith⟩
  unfold bernalSecular
  nlinarith [h2]

/-- **Quadratic, not linear — the contrast with the monolayer is a theorem.** The monolayer band
energy at the same hopping element is `‖f‖ = √x` (Wave 1's `honeycomb_energy_eq`). For `0 < x < γ²`
the bilayer low band lies **strictly below** it, and the ratio degrades without bound as `x → 0`.
This is what distinguishes a quadratic touching from a Dirac cone. -/
theorem bernal_sub_linear_of_small (γ x w : ℝ) (hγ : 0 < γ) (hx : 0 < x) (hxγ : x < γ ^ 2)
    (hw : bernalSecular 0 γ x w = 0) (hlow : 2 * w ≤ γ ^ 2 + 2 * x) : w < x := by
  obtain ⟨_, hhi⟩ := bernal_lowRoot_enclosure γ x w hγ hx.le hw hlow
  have : x ^ 2 / γ ^ 2 < x := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **The monolayer contrast, at an actual honeycomb momentum.** `bernal_sub_linear_of_small` is
stated over an abstract `x`; this instantiates it at `x = ‖f(θ)‖²` and concludes against the
*monolayer's own* band energy, obtained by calling Wave 1's `honeycomb_energy_eq` and
`dNormSq_honeycombD` rather than restating them. Away from the Dirac points and inside `‖f‖² < γ²`,
the bilayer band sits strictly below the monolayer band. -/
theorem bernal_sub_linear_of_monolayer (γ : ℝ) (θ : ℝ × ℝ) (w : ℝ) (hγ : 0 < γ)
    (hf : structureFactor θ ≠ 0) (hxγ : Complex.normSq (structureFactor θ) < γ ^ 2)
    (hw : bernalSecular 0 γ (Complex.normSq (structureFactor θ)) w = 0)
    (hlow : 2 * w ≤ γ ^ 2 + 2 * Complex.normSq (structureFactor θ)) :
    Real.sqrt w < Real.sqrt (dNormSq (honeycombD θ)) := by
  have hx : 0 < Complex.normSq (structureFactor θ) := by
    simpa using (Complex.normSq_pos).mpr hf
  have hlt := bernal_sub_linear_of_small γ (Complex.normSq (structureFactor θ)) w hγ hx hxγ hw hlow
  have hmono : Real.sqrt (dNormSq (honeycombD θ)) = ‖structureFactor θ‖ := honeycomb_energy_eq θ
  rw [hmono, Complex.norm_def]
  exact Real.sqrt_lt_sqrt (bernal_root_nonneg γ _ w hγ hx.le hw) hlt

/-! ## Nonzero bias: the gap, its exactness, and the Mexican hat -/

/-- **The field-induced gap.** For any `x ≥ 0` and any band energy `E`,

    u²·γ²  ≤  E²·(γ² + 4u²),

i.e. `|E| ≥ |u|·γ/√(γ² + 4u²) > 0` whenever `u ≠ 0`: a nonzero interlayer bias gaps the spectrum.
Stated denominator-free. The proof is the perfect-square identity
`(γ²+4u²)²·Q(m) = (2u²(γ²+2u²) − (γ²+4u²)x)²` at the floor value `m = −4u⁴/(γ²+4u²)`. -/
theorem bernal_field_gap (u γ x E : ℝ) (hγ : 0 < γ) (hx : 0 ≤ x)
    (hE : bernalSecular u γ x (E ^ 2 - u ^ 2) = 0) :
    u ^ 2 * γ ^ 2 ≤ E ^ 2 * (γ ^ 2 + 4 * u ^ 2) := by
  have hcpos : (0 : ℝ) < γ ^ 2 + 4 * u ^ 2 := by positivity
  unfold bernalSecular at hE
  by_contra hcon
  push Not at hcon
  -- Abbreviations: `A = c·w` (the scaled root), `B = −4u⁴` (the scaled floor), `K = (γ²+2x)·c`.
  set c : ℝ := γ ^ 2 + 4 * u ^ 2 with hc
  set A : ℝ := c * (E ^ 2 - u ^ 2) with hA
  set B : ℝ := -(4 * u ^ 4) with hB
  set K : ℝ := (γ ^ 2 + 2 * x) * c with hK
  -- `A < B` is exactly the assumed gap violation, rescaled by `c > 0`.
  have hAB : A < B := by rw [hA, hB, hc]; nlinarith [hcon, hcpos]
  -- The root equation, scaled by `c²`.
  have hroot : A ^ 2 - K * A + c ^ 2 * (x * (x - 4 * u ^ 2)) = 0 := by
    rw [hA, hK, hc]; linear_combination (γ ^ 2 + 4 * u ^ 2) ^ 2 * hE
  -- **The perfect square.** At the floor value the same expression is a square, hence `≥ 0`.
  have hfloor : B ^ 2 - K * B + c ^ 2 * (x * (x - 4 * u ^ 2))
      = (2 * u ^ 2 * (γ ^ 2 + 2 * u ^ 2) - c * x) ^ 2 := by rw [hB, hK, hc]; ring
  -- Subtracting: `(A − B)·(A + B − K) = −(square) ≤ 0`, and `A − B < 0`, so `A + B ≥ K ≥ 0`.
  have hdiff : (A - B) * (A + B - K) = -((2 * u ^ 2 * (γ ^ 2 + 2 * u ^ 2) - c * x) ^ 2) := by
    linear_combination hroot - hfloor
  have hKnn : 0 ≤ K := by rw [hK, hc]; positivity
  have hBnp : B ≤ 0 := by rw [hB]; nlinarith [sq_nonneg (u ^ 2)]
  nlinarith [hdiff, hAB, hKnn, hBnp, sq_nonneg (2 * u ^ 2 * (γ ^ 2 + 2 * u ^ 2) - c * x)]

/-- **The gap floor is attained**, so `bernal_field_gap` is the *exact* spectral gap rather than a
bound. The minimum sits at `x* = 2u²(γ²+2u²)/(γ²+4u²)`, which is strictly positive for `u ≠ 0` —
the band edge is at finite momentum. -/
theorem bernal_field_gap_attained (u γ : ℝ) (hγ : 0 < γ) :
    ∃ x ≥ 0, ∃ E : ℝ, bernalSecular u γ x (E ^ 2 - u ^ 2) = 0
      ∧ E ^ 2 * (γ ^ 2 + 4 * u ^ 2) = u ^ 2 * γ ^ 2 := by
  set c : ℝ := γ ^ 2 + 4 * u ^ 2 with hc
  have hcpos : 0 < c := by positivity
  refine ⟨2 * u ^ 2 * (γ ^ 2 + 2 * u ^ 2) / c, by positivity,
    Real.sqrt (u ^ 2 * γ ^ 2 / c), ?_, ?_⟩
  · have hsq : Real.sqrt (u ^ 2 * γ ^ 2 / c) ^ 2 = u ^ 2 * γ ^ 2 / c :=
      Real.sq_sqrt (by positivity)
    unfold bernalSecular
    rw [hsq]
    field_simp
    ring
  · have hsq : Real.sqrt (u ^ 2 * γ ^ 2 / c) ^ 2 = u ^ 2 * γ ^ 2 / c :=
      Real.sq_sqrt (by positivity)
    rw [hsq]
    field_simp

/-- **The squared gap is a `IsLeast`, not merely a bound.** Combining `bernal_field_gap` (every band
energy clears the floor) with `bernal_field_gap_attained` (some band energy sits on it), the value
`u²γ²/(γ²+4u²)` is the exact minimum of `E²` over the whole band structure. This is the theorem the
module docstring's "exact spectral gap" claim rests on. -/
theorem bernal_halfGapSq_isLeast (u γ : ℝ) (hγ : 0 < γ) :
    IsLeast {s : ℝ | ∃ x, 0 ≤ x ∧ ∃ E : ℝ, bernalSecular u γ x (E ^ 2 - u ^ 2) = 0 ∧ s = E ^ 2}
      (u ^ 2 * γ ^ 2 / (γ ^ 2 + 4 * u ^ 2)) := by
  have hcpos : (0 : ℝ) < γ ^ 2 + 4 * u ^ 2 := by positivity
  constructor
  · obtain ⟨x, hx, E, hroot, hval⟩ := bernal_field_gap_attained u γ hγ
    exact ⟨x, hx, E, hroot, by field_simp; linarith [hval]⟩
  · rintro s ⟨x, hx, E, hroot, rfl⟩
    rw [div_le_iff₀ hcpos]
    linarith [bernal_field_gap u γ x E hγ hx hroot]

/-- **The gap is strictly positive for a nonzero bias** — the AC's `U ≠ 0 → gapped`, which
`bernal_field_gap` states only as a floor that degenerates to `0 ≤ E²γ²` at `u = 0`. -/
theorem bernal_field_gap_pos (u γ x E : ℝ) (hγ : 0 < γ) (hu : u ≠ 0) (hx : 0 ≤ x)
    (hE : bernalSecular u γ x (E ^ 2 - u ^ 2) = 0) : 0 < E ^ 2 := by
  have hfloor := bernal_field_gap u γ x E hγ hx hE
  have hu2 : 0 < u ^ 2 := by positivity
  have hnum : 0 < u ^ 2 * γ ^ 2 := by positivity
  nlinarith [hfloor, hnum, sq_nonneg E, sq_nonneg u]

/-- **The biased gap, stated about the matrix rather than the polynomial** — the counterpart of
`bernal_touching_of_eigenvector` for the gapped case, routed through `bernal_eigenvector_iff`. This
is what licenses calling `u²γ²/(γ²+4u²)` a *spectral* gap. -/
theorem bernal_field_gap_of_eigenvector (u γ E : ℝ) (f : ℂ) (hγ : 0 < γ)
    (hev : ∃ v ≠ 0, (bernalBloch u γ f - (E : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)).mulVec v = 0) :
    u ^ 2 * γ ^ 2 ≤ E ^ 2 * (γ ^ 2 + 4 * u ^ 2) :=
  bernal_field_gap u γ (normSq f) E hγ (normSq_nonneg f)
    ((bernal_eigenvector_iff u γ E f).mp hev)

/-- **The naive "gap = bias" claim is FALSE — the Mexican hat.** At the Dirac point (`x = 0`) the
band energy is exactly the half-bias `|u|`, so a first-pass reading gives gap `= 2|u| = |U|`. But
there is a **strictly positive** momentum where `E² < u²`: the band minimum is a ring at finite
momentum, and the true gap `|U|γ/√(γ²+U²)` is strictly below `|U|`. -/
theorem bernal_mexicanHat (u γ : ℝ) (hγ : 0 < γ) (hu : u ≠ 0) :
    ∃ x > 0, ∃ E : ℝ, bernalSecular u γ x (E ^ 2 - u ^ 2) = 0 ∧ E ^ 2 < u ^ 2 := by
  set c : ℝ := γ ^ 2 + 4 * u ^ 2 with hc
  have hcpos : 0 < c := by positivity
  have hu2 : 0 < u ^ 2 := by positivity
  refine ⟨2 * u ^ 2 * (γ ^ 2 + 2 * u ^ 2) / c, by positivity,
    Real.sqrt (u ^ 2 * γ ^ 2 / c), ?_, ?_⟩
  · have hsq : Real.sqrt (u ^ 2 * γ ^ 2 / c) ^ 2 = u ^ 2 * γ ^ 2 / c :=
      Real.sq_sqrt (by positivity)
    unfold bernalSecular
    rw [hsq]
    field_simp
    ring
  · have hsq : Real.sqrt (u ^ 2 * γ ^ 2 / c) ^ 2 = u ^ 2 * γ ^ 2 / c :=
      Real.sq_sqrt (by positivity)
    rw [hsq, div_lt_iff₀ hcpos]
    nlinarith [hu2, sq_nonneg u]

/-- **At the Dirac point the gap IS the bias.** `x = 0` gives band energies `E² = u²` (the low pair)
and `E² = u² + γ²` (the dimer pair). Together with `bernal_mexicanHat` this pins the failure of the
naive claim to *finite momentum*, not to the `K` point. -/
theorem bernal_diracPoint_energies (u γ E : ℝ) :
    bernalSecular u γ 0 (E ^ 2 - u ^ 2) = 0 ↔ E ^ 2 = u ^ 2 ∨ E ^ 2 = u ^ 2 + γ ^ 2 := by
  unfold bernalSecular
  constructor
  · intro h
    have h' : (E ^ 2 - u ^ 2) * (E ^ 2 - u ^ 2 - γ ^ 2) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linarith
    · right; linarith
  · rintro (h | h) <;> rw [h] <;> ring

/-- **A concrete `norm_num` witness for the Mexican hat.** At `γ = 1`, `u = 1/2` (bias `U = 1`), the
momentum `x = 3/8` carries the band energy `E² = 1/8`, strictly below the Dirac-point value
`u² = 1/4`. The gap is suppressed to `1/√2` of the naive value — a 29% error, not a rounding
detail. -/
theorem bernal_mexicanHat_witness :
    bernalSecular (1 / 2) 1 (3 / 8) (1 / 8 - (1 / 2) ^ 2) = 0 ∧ (1 : ℝ) / 8 < (1 / 2 : ℝ) ^ 2 := by
  refine ⟨?_, by norm_num⟩
  unfold bernalSecular
  norm_num

/-- **Leading-order enclosure of the gap.** The exact squared gap `u²γ²/(γ²+4u²)` is enclosed by
`u²(1 − 4u²/γ²) ≤ gap² ≤ u²`: to leading order in the bias it is the half-bias `|u|`, with the
Mexican-hat suppression appearing at relative order `u²/γ²`. -/
theorem bernal_gap_enclosure (u γ : ℝ) (hγ : 0 < γ) :
    u ^ 2 * (1 - 4 * u ^ 2 / γ ^ 2) ≤ u ^ 2 * γ ^ 2 / (γ ^ 2 + 4 * u ^ 2)
      ∧ u ^ 2 * γ ^ 2 / (γ ^ 2 + 4 * u ^ 2) ≤ u ^ 2 := by
  have hc : (0 : ℝ) < γ ^ 2 + 4 * u ^ 2 := by positivity
  have hγ2 : (0 : ℝ) < γ ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ hc]
    have : u ^ 2 * (1 - 4 * u ^ 2 / γ ^ 2) * (γ ^ 2 + 4 * u ^ 2)
        = u ^ 2 * γ ^ 2 - 16 * u ^ 6 / γ ^ 2 := by field_simp; ring
    rw [this]
    have : (0 : ℝ) ≤ 16 * u ^ 6 / γ ^ 2 := by positivity
    linarith
  · rw [div_le_iff₀ hc]
    nlinarith [sq_nonneg u, sq_nonneg (u ^ 2)]

/-! ## The bridge to Waves 1–2: effective mass -/

/-- The band-edge effective mass of the bilayer's quadratic touching, in the parametrization of
Wave 2 (`t` the hopping, `a_CC` the nearest-neighbour distance, `ℏ` reduced Planck). The claim that
this is the mass for which the low band reads `E = ℏ²‖p‖²/(2 m*)` is **proved** in
`bernal_effectiveMass_dispersion`, not left to the docstring. -/
noncomputable def bernalEffectiveMass (γ t a_CC ℏ : ℝ) : ℝ :=
  2 * ℏ ^ 2 * γ / (9 * t ^ 2 * a_CC ^ 2)

/-- **The effective mass earns its name.** Feeding the Wave-2 slope `‖f‖ = (3/2)·t·a_CC·‖p‖`
(`dispersion_slope_of_neighbours`) into the leading term `x/γ` of the quadratic touching produces
exactly `ℏ²‖p‖²/(2·m*)` with `m* = bernalEffectiveMass`. Without this, `bernalEffectiveMass` would
be a definition whose docstring asserted a dispersion relation the module never proved. -/
theorem bernal_effectiveMass_dispersion (γ t a_CC ℏ p : ℝ) (hγ : 0 < γ) (ht : t ≠ 0)
    (ha : a_CC ≠ 0) (hℏ : ℏ ≠ 0) :
    (3 / 2 * t * a_CC * p) ^ 2 / γ = ℏ ^ 2 * p ^ 2 / (2 * bernalEffectiveMass γ t a_CC ℏ) := by
  unfold bernalEffectiveMass
  field_simp
  ring

/-- **The effective mass, chained to an actual band energy.** This is the theorem the definition
exists for: feeding the Wave-2 slope into `bernal_touching_energy_enclosure` bounds the *band
energy* `|E|` between `ℏ²p²/(2m*)` and that value minus an explicit `2x²/γ³`, on the stated ball.
Without it `bernalEffectiveMass` would be a definition disconnected from every band theorem in the
file — the "defining-the-conclusion" anti-pattern. -/
theorem bernal_lowBand_effectiveMass (γ t a_CC ℏ p E : ℝ) (hγ : 0 < γ) (ht : t ≠ 0)
    (ha : a_CC ≠ 0) (hℏ : ℏ ≠ 0)
    (hball : (3 / 2 * t * a_CC * p) ^ 2 ≤ γ ^ 2 / 2)
    (hE : bernalSecular 0 γ ((3 / 2 * t * a_CC * p) ^ 2) (E ^ 2) = 0)
    (hlow : 2 * E ^ 2 ≤ γ ^ 2 + 2 * (3 / 2 * t * a_CC * p) ^ 2) :
    ℏ ^ 2 * p ^ 2 / (2 * bernalEffectiveMass γ t a_CC ℏ)
        - 2 * ((3 / 2 * t * a_CC * p) ^ 2) ^ 2 / γ ^ 3 ≤ |E|
      ∧ |E| ≤ ℏ ^ 2 * p ^ 2 / (2 * bernalEffectiveMass γ t a_CC ℏ) := by
  obtain ⟨hlo, hhi⟩ := bernal_touching_energy_enclosure γ ((3 / 2 * t * a_CC * p) ^ 2) E hγ
    (by positivity) hball hE hlow
  rw [← bernal_effectiveMass_dispersion γ t a_CC ℏ p hγ ht ha hℏ]
  exact ⟨hlo, hhi⟩

/-- **The full gap, in McCann–Koshino's bias variable `U = 2u`.** Every other gap statement in this
file is about `min E²`, i.e. the *half*-gap squared; the full band gap is twice `min |E|`. In the
`U` variable this is `U²γ²/(γ²+U²)`, matching the published closed form
`U_g = |U|γ₁/√(γ₁²+U²)` exactly. Shipped because the module previously quoted both conventions in
prose without a theorem separating them — a factor of 4 in the squared quantity. -/
theorem bernal_fullGapSq_eq (u γ : ℝ) (hγ : 0 < γ) :
    4 * (u ^ 2 * γ ^ 2 / (γ ^ 2 + 4 * u ^ 2))
      = (2 * u) ^ 2 * γ ^ 2 / (γ ^ 2 + (2 * u) ^ 2) := by
  have hc : (0 : ℝ) < γ ^ 2 + 4 * u ^ 2 := by positivity
  field_simp
  ring

/-- **The textbook relation `m* = γ₁ / (2 v_F²)` — and the bridge that makes Wave 2 load-bearing
here.** The effective mass is not an independent parameter: it is the dimer coupling divided by
twice the squared *monolayer* Fermi velocity, which this proof obtains by calling Wave 2's
`fermiVelocity` rather than restating its value. -/
theorem bernal_effectiveMass_eq (γ t a_CC ℏ : ℝ) (ht : t ≠ 0) (ha : a_CC ≠ 0) (hℏ : ℏ ≠ 0) :
    bernalEffectiveMass γ t a_CC ℏ = γ / (2 * (fermiVelocity t a_CC ℏ) ^ 2) := by
  unfold bernalEffectiveMass fermiVelocity
  field_simp
  ring

end SKEFTHawking.GrapheneBand
