/-
Phase 6p Wave 2d.3-followup: Qubit Bloch-sphere balanced commutator (D-N §4.1 Eq. 10-13).

The Dawson-Nielsen Lemma 2 (qubit case) ships the *explicit balanced commutator
decomposition* used in the SK recursive step.  For the Z-axis (coordinate) case
H = θ·σ_z, the construction is:

  F = √(θ/2) · σ_y    (hermitian, ‖F‖ ≤ √(θ/2))
  G = √(θ/2) · σ_x    (hermitian, ‖G‖ ≤ √(θ/2))

and direct computation (using `comm_σ_x_σ_y` from `PauliMatrices.lean`) gives

  F·G − G·F  =  −(2·(θ/2)·i) • σ_z  =  −(θ·i) • σ_z  =  −i·H.

With  V := exp(iF), W := exp(iG),  the order-2 BCH expansion yields

  V·W·V†·W†  ≈  exp([iF, iG])  =  exp(−[F,G])  =  exp(i·θ·σ_z)  =  U  ✓

(the cubic-order remainder is bounded by `bch_order_2_cubic_thm` at K = 320,
applied with δ = √(θ/2) ≤ √(1/2) for θ ≤ 1).  Norms ‖F‖, ‖G‖ ≤ √(θ/2) ≤ √θ
when θ ≤ 1, matching D-N Eq. (11): the balanced commutator F, G have norm
on the order of √‖H‖.

**Scope of this wave (2d.3-followup, ~200 LoC):**

  - **Coordinate (Z-axis) case fully proved** — substantive content via
    `comm_σ_x_σ_y` (Pauli substrate already in `PauliMatrices.lean`) plus
    explicit norm bounds via `Matrix.linfty_opNorm_def`.

  - **General-axis case** (H = θ·(n·σ) for arbitrary unit n ∈ ℝ³) is
    documented as a predicate-level statement; full proof requires SU(2)
    Bloch parametrization + Pauli identity [a·σ, b·σ] = 2i(a×b)·σ, which
    is genuinely new Mathlib substrate (~200-400 LoC of additional work).
    Deferred to a follow-up sub-wave; the predicate is named so Wave
    2d.5-followup-full can quantify over it directly.

**Pipeline Invariant compliance:**
  - Zero new project-local axioms (the construction is fully constructive,
    grounded in `PauliMatrices.comm_σ_x_σ_y` + standard Mathlib norm theory).
  - Zero `maxHeartbeats` overrides; proofs decomposed into ≤30-line bodies.
  - Cross-module bridge integrity: `import SKEFTHawking.PauliMatrices` and
    the body calls `comm_σ_x_σ_y` substantively (not just docstring).

References:
  - Dawson & Nielsen, arXiv:quant-ph/0505030 §4.1 Eq. 10-13 (Lemma 2).
  - `SKEFTHawking.PauliMatrices` — σ_x, σ_y, σ_z + `comm_σ_x_σ_y`.
  - `SKEFTHawking.MatrixBCHCubic.bch_order_2_cubic_thm` — order-2 BCH bound.
-/

import Mathlib
import SKEFTHawking.PauliMatrices

set_option autoImplicit false

namespace SKEFTHawking.FKLW

open SKEFTHawking Matrix Complex

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Pauli matrix `linftyOpNorm` upper bounds

The L∞→L∞ operator norm (`linftyOpNorm` = row-max-sum) of each Pauli matrix
is bounded by 1.  Equality holds, but for the balanced-commutator
construction we only need the ≤ direction (giving `‖α • σ‖ ≤ |α|`).
-/

/-- `‖σ_x‖ ≤ 1` under `linftyOpNorm`. -/
theorem σ_x_norm_le_one : ‖σ_x‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  have h : (Finset.univ.sup fun i : Fin 2 => ∑ j, ‖σ_x i j‖₊) ≤ 1 := by
    refine Finset.sup_le fun i _ => ?_
    fin_cases i
    · show ∑ j, ‖σ_x 0 j‖₊ ≤ 1; simp [σ_x, Fin.sum_univ_two]
    · show ∑ j, ‖σ_x 1 j‖₊ ≤ 1; simp [σ_x, Fin.sum_univ_two]
  exact_mod_cast h

/-- `‖σ_y‖ ≤ 1` under `linftyOpNorm`. -/
theorem σ_y_norm_le_one : ‖σ_y‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  have h : (Finset.univ.sup fun i : Fin 2 => ∑ j, ‖σ_y i j‖₊) ≤ 1 := by
    refine Finset.sup_le fun i _ => ?_
    fin_cases i
    · show ∑ j, ‖σ_y 0 j‖₊ ≤ 1; simp [σ_y, Fin.sum_univ_two]
    · show ∑ j, ‖σ_y 1 j‖₊ ≤ 1; simp [σ_y, Fin.sum_univ_two]
  exact_mod_cast h

/-- `‖σ_z‖ ≤ 1` under `linftyOpNorm`. -/
theorem σ_z_norm_le_one : ‖σ_z‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  have h : (Finset.univ.sup fun i : Fin 2 => ∑ j, ‖σ_z i j‖₊) ≤ 1 := by
    refine Finset.sup_le fun i _ => ?_
    fin_cases i
    · show ∑ j, ‖σ_z 0 j‖₊ ≤ 1; simp [σ_z, Fin.sum_univ_two]
    · show ∑ j, ‖σ_z 1 j‖₊ ≤ 1; simp [σ_z, Fin.sum_univ_two]
  exact_mod_cast h

/-! ## 2. Scalar-times-Pauli norm bound

For α : ℝ, `‖(α : ℂ) • σ‖ ≤ |α|` for each Pauli σ.  Derived from the
unit-norm bounds above via the scalar-multiplication norm law.
-/

/-- `‖(α : ℂ) • σ_x‖ ≤ |α|`. -/
theorem smul_σ_x_norm_le (α : ℝ) : ‖(α : ℂ) • σ_x‖ ≤ |α| := by
  rw [norm_smul]
  have h1 : ‖(α : ℂ)‖ = |α| := by simp [Complex.norm_real]
  rw [h1]
  have h2 : |α| * ‖σ_x‖ ≤ |α| * 1 :=
    mul_le_mul_of_nonneg_left σ_x_norm_le_one (abs_nonneg α)
  linarith

/-- `‖(α : ℂ) • σ_y‖ ≤ |α|`. -/
theorem smul_σ_y_norm_le (α : ℝ) : ‖(α : ℂ) • σ_y‖ ≤ |α| := by
  rw [norm_smul]
  have h1 : ‖(α : ℂ)‖ = |α| := by simp [Complex.norm_real]
  rw [h1]
  have h2 : |α| * ‖σ_y‖ ≤ |α| * 1 :=
    mul_le_mul_of_nonneg_left σ_y_norm_le_one (abs_nonneg α)
  linarith

/-- `‖(α : ℂ) • σ_z‖ ≤ |α|`. -/
theorem smul_σ_z_norm_le (α : ℝ) : ‖(α : ℂ) • σ_z‖ ≤ |α| := by
  rw [norm_smul]
  have h1 : ‖(α : ℂ)‖ = |α| := by simp [Complex.norm_real]
  rw [h1]
  have h2 : |α| * ‖σ_z‖ ≤ |α| * 1 :=
    mul_le_mul_of_nonneg_left σ_z_norm_le_one (abs_nonneg α)
  linarith

/-! ## 3. Hermiticity of `(α : ℂ) • σ` for real `α`

The hermiticity of `(α : ℂ) • σ_i` for `α : ℝ` follows from `σ_i.IsHermitian`
plus `conj (α : ℂ) = α` (since real-cast-to-complex is fixed by conjugation).
-/

/-- For real `α`, `(α : ℂ) • σ_x` is Hermitian. -/
theorem smul_σ_x_isHermitian (α : ℝ) : ((α : ℂ) • σ_x).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, σ_x_hermitian]
  simp [Complex.conj_ofReal]

/-- `σ_y` is Hermitian (inline; not in `PauliMatrices.lean` because the
σ_y entries (`i`, `-i`) require a small ring-tactic to discharge). -/
theorem σ_y_hermitian : σ_y.conjTranspose = σ_y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ_y, conjTranspose]

/-- For real `α`, `(α : ℂ) • σ_y` is Hermitian. -/
theorem smul_σ_y_isHermitian (α : ℝ) : ((α : ℂ) • σ_y).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, σ_y_hermitian]
  simp [Complex.conj_ofReal]

/-- For real `α`, `(α : ℂ) • σ_z` is Hermitian. -/
theorem smul_σ_z_isHermitian (α : ℝ) : ((α : ℂ) • σ_z).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, σ_z_hermitian]
  simp [Complex.conj_ofReal]

/-! ## 4. The balanced-commutator core identity

For real `α`, the matrix commutator of `(α : ℂ) • σ_y` and `(α : ℂ) • σ_x`
equals `−(2·α²·i) • σ_z`.  This is the SUBSTANTIVE content of D-N Lemma 2
in the Z-axis (coordinate) case.
-/

/-- **Balanced-commutator core identity (Z-axis coordinate case).**
For any `α : ℝ`,

  `[α·σ_y, α·σ_x] = α·σ_y · α·σ_x − α·σ_x · α·σ_y = −(2·α²·i) • σ_z`.

Combining with `H := θ·σ_z` and `α := √(θ/2)`, we get
`[F, G] = −(θ·i) • σ_z = −i·H`, matching D-N Eq. (12). -/
theorem balanced_commutator_z_core (α : ℝ) :
    ((α : ℂ) • σ_y) * ((α : ℂ) • σ_x) - ((α : ℂ) • σ_x) * ((α : ℂ) • σ_y)
      = (-(2 * α^2 * Complex.I)) • σ_z := by
  have h_yx_xy : σ_y * σ_x - σ_x * σ_y = (-(2 * Complex.I)) • σ_z := by
    have h := comm_σ_x_σ_y
    rw [show σ_y * σ_x - σ_x * σ_y = -(σ_x * σ_y - σ_y * σ_x) from by rw [neg_sub]]
    rw [h, neg_smul]
  calc ((α : ℂ) • σ_y) * ((α : ℂ) • σ_x) - ((α : ℂ) • σ_x) * ((α : ℂ) • σ_y)
      = ((α : ℂ) * (α : ℂ)) • (σ_y * σ_x - σ_x * σ_y) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul]
    _ = ((α : ℂ) * (α : ℂ)) • ((-(2 * Complex.I)) • σ_z) := by rw [h_yx_xy]
    _ = ((α : ℂ) * (α : ℂ) * (-(2 * Complex.I))) • σ_z := by rw [smul_smul]
    _ = (-(2 * α^2 * Complex.I)) • σ_z := by
        congr 1
        ring

/-! ## 5. D-N Lemma 2: Z-axis balanced commutator decomposition

For any θ ∈ [0, 1], setting

  F := √(θ/2) · σ_y,    G := √(θ/2) · σ_x,    H := θ · σ_z

yields F, G hermitian, ‖F‖, ‖G‖ ≤ √(θ/2), and  F·G − G·F = −i·H.

The statement is packaged as a substantive existence theorem so downstream
(Wave 2d.5-followup-full) can directly compose with `bch_order_2_cubic_thm`.
-/

/-- **D-N Lemma 2 (Z-axis case, substantive).** For any `θ : ℝ` with
`0 ≤ θ ≤ 1`, there exist hermitian `F, G : Matrix (Fin 2) (Fin 2) ℂ` with
`‖F‖, ‖G‖ ≤ Real.sqrt (θ/2)` such that

  `F · G − G · F = −(θ · Complex.I) • σ_z = −i · H`

where `H := (θ : ℂ) • σ_z` is the target traceless hermitian Z-axis matrix.

The explicit witnesses are `F := √(θ/2) • σ_y`, `G := √(θ/2) • σ_x`.  This
is **D-N Eq. (10-13) for the Z-axis coordinate case**.  The general
axis case (n ∈ ℝ³ unit vector) factors through this via SU(2) rotation
and is documented as a predicate-level scaffold (Wave 2d.3-followup-general). -/
theorem qubit_balanced_commutator_z_axis
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (_hθ_le_one : θ ≤ 1) :
    ∃ (F G : Matrix (Fin 2) (Fin 2) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧
      ‖F‖ ≤ Real.sqrt (θ/2) ∧ ‖G‖ ≤ Real.sqrt (θ/2) ∧
      F * G - G * F = (-(θ * Complex.I)) • σ_z := by
  set α := Real.sqrt (θ/2)
  have hα_nn : 0 ≤ α := Real.sqrt_nonneg _
  have hα_sq : α^2 = θ/2 := by
    rw [sq]; exact Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ θ/2)
  refine ⟨(α : ℂ) • σ_y, (α : ℂ) • σ_x, ?_, ?_, ?_, ?_, ?_⟩
  · exact smul_σ_y_isHermitian α
  · exact smul_σ_x_isHermitian α
  · have := smul_σ_y_norm_le α; rwa [abs_of_nonneg hα_nn] at this
  · have := smul_σ_x_norm_le α; rwa [abs_of_nonneg hα_nn] at this
  · rw [balanced_commutator_z_core α]
    congr 1
    have h2α2 : (2 * α^2 : ℝ) = θ := by rw [hα_sq]; ring
    rw [show (2 : ℂ) * (α : ℂ)^2 = ((2 * α^2 : ℝ) : ℂ) from by push_cast; ring]
    rw [h2α2]

/-! ## 5b. X-axis + Y-axis coordinate cases (Phase 6t Wave 2 strengthening 2026-05-22 PM)

These are symmetric counterparts of `balanced_commutator_z_core` +
`qubit_balanced_commutator_z_axis` for the X-axis and Y-axis targets,
using `comm_σ_y_σ_z` (= 2i·σ_x) and `comm_σ_z_σ_x` (= 2i·σ_y)
respectively. They close 2 of the 3 axis-coordinate gaps in
`BalancedCommutatorGeneralAxisGroup` (Wave 2-followup retains the
genuinely general-axis case via SU(2) Bloch parametrization). -/

/-- **Balanced-commutator core identity (X-axis coordinate case).**
For any `α : ℝ`,

  `[α·σ_z, α·σ_y] = α·σ_z · α·σ_y − α·σ_y · α·σ_z = −(2·α²·i) • σ_x`.

Combining with `H := θ·σ_x` and `α := √(θ/2)`, we get
`[F, G] = −(θ·i) • σ_x = −i·H`. -/
theorem balanced_commutator_x_core (α : ℝ) :
    ((α : ℂ) • σ_z) * ((α : ℂ) • σ_y) - ((α : ℂ) • σ_y) * ((α : ℂ) • σ_z)
      = (-(2 * α^2 * Complex.I)) • σ_x := by
  have h_zy_yz : σ_z * σ_y - σ_y * σ_z = (-(2 * Complex.I)) • σ_x := by
    have h := comm_σ_y_σ_z
    rw [show σ_z * σ_y - σ_y * σ_z = -(σ_y * σ_z - σ_z * σ_y) from by rw [neg_sub]]
    rw [h, neg_smul]
  calc ((α : ℂ) • σ_z) * ((α : ℂ) • σ_y) - ((α : ℂ) • σ_y) * ((α : ℂ) • σ_z)
      = ((α : ℂ) * (α : ℂ)) • (σ_z * σ_y - σ_y * σ_z) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul]
    _ = ((α : ℂ) * (α : ℂ)) • ((-(2 * Complex.I)) • σ_x) := by rw [h_zy_yz]
    _ = ((α : ℂ) * (α : ℂ) * (-(2 * Complex.I))) • σ_x := by rw [smul_smul]
    _ = (-(2 * α^2 * Complex.I)) • σ_x := by
        congr 1
        ring

/-- **Balanced-commutator core identity (Y-axis coordinate case).**
For any `α : ℝ`,

  `[α·σ_x, α·σ_z] = α·σ_x · α·σ_z − α·σ_z · α·σ_x = −(2·α²·i) • σ_y`.

Combining with `H := θ·σ_y` and `α := √(θ/2)`, we get
`[F, G] = −(θ·i) • σ_y = −i·H`. -/
theorem balanced_commutator_y_core (α : ℝ) :
    ((α : ℂ) • σ_x) * ((α : ℂ) • σ_z) - ((α : ℂ) • σ_z) * ((α : ℂ) • σ_x)
      = (-(2 * α^2 * Complex.I)) • σ_y := by
  have h_xz_zx : σ_x * σ_z - σ_z * σ_x = (-(2 * Complex.I)) • σ_y := by
    have h := comm_σ_z_σ_x
    rw [show σ_x * σ_z - σ_z * σ_x = -(σ_z * σ_x - σ_x * σ_z) from by rw [neg_sub]]
    rw [h, neg_smul]
  calc ((α : ℂ) • σ_x) * ((α : ℂ) • σ_z) - ((α : ℂ) • σ_z) * ((α : ℂ) • σ_x)
      = ((α : ℂ) * (α : ℂ)) • (σ_x * σ_z - σ_z * σ_x) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul]
    _ = ((α : ℂ) * (α : ℂ)) • ((-(2 * Complex.I)) • σ_y) := by rw [h_xz_zx]
    _ = ((α : ℂ) * (α : ℂ) * (-(2 * Complex.I))) • σ_y := by rw [smul_smul]
    _ = (-(2 * α^2 * Complex.I)) • σ_y := by
        congr 1
        ring

/-- **D-N Lemma 2 (X-axis case, substantive).** Symmetric counterpart of
`qubit_balanced_commutator_z_axis` for the X-axis target. -/
theorem qubit_balanced_commutator_x_axis
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (_hθ_le_one : θ ≤ 1) :
    ∃ (F G : Matrix (Fin 2) (Fin 2) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧
      ‖F‖ ≤ Real.sqrt (θ/2) ∧ ‖G‖ ≤ Real.sqrt (θ/2) ∧
      F * G - G * F = (-(θ * Complex.I)) • σ_x := by
  set α := Real.sqrt (θ/2)
  have hα_nn : 0 ≤ α := Real.sqrt_nonneg _
  have hα_sq : α^2 = θ/2 := by
    rw [sq]; exact Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ θ/2)
  refine ⟨(α : ℂ) • σ_z, (α : ℂ) • σ_y, ?_, ?_, ?_, ?_, ?_⟩
  · exact smul_σ_z_isHermitian α
  · exact smul_σ_y_isHermitian α
  · have := smul_σ_z_norm_le α; rwa [abs_of_nonneg hα_nn] at this
  · have := smul_σ_y_norm_le α; rwa [abs_of_nonneg hα_nn] at this
  · rw [balanced_commutator_x_core α]
    congr 1
    have h2α2 : (2 * α^2 : ℝ) = θ := by rw [hα_sq]; ring
    rw [show (2 : ℂ) * (α : ℂ)^2 = ((2 * α^2 : ℝ) : ℂ) from by push_cast; ring]
    rw [h2α2]

/-- **D-N Lemma 2 (Y-axis case, substantive).** Symmetric counterpart of
`qubit_balanced_commutator_z_axis` for the Y-axis target. -/
theorem qubit_balanced_commutator_y_axis
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (_hθ_le_one : θ ≤ 1) :
    ∃ (F G : Matrix (Fin 2) (Fin 2) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧
      ‖F‖ ≤ Real.sqrt (θ/2) ∧ ‖G‖ ≤ Real.sqrt (θ/2) ∧
      F * G - G * F = (-(θ * Complex.I)) • σ_y := by
  set α := Real.sqrt (θ/2)
  have hα_nn : 0 ≤ α := Real.sqrt_nonneg _
  have hα_sq : α^2 = θ/2 := by
    rw [sq]; exact Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ θ/2)
  refine ⟨(α : ℂ) • σ_x, (α : ℂ) • σ_z, ?_, ?_, ?_, ?_, ?_⟩
  · exact smul_σ_x_isHermitian α
  · exact smul_σ_z_isHermitian α
  · have := smul_σ_x_norm_le α; rwa [abs_of_nonneg hα_nn] at this
  · have := smul_σ_z_norm_le α; rwa [abs_of_nonneg hα_nn] at this
  · rw [balanced_commutator_y_core α]
    congr 1
    have h2α2 : (2 * α^2 : ℝ) = θ := by rw [hα_sq]; ring
    rw [show (2 : ℂ) * (α : ℂ)^2 = ((2 * α^2 : ℝ) : ℂ) from by push_cast; ring]
    rw [h2α2]

/-! ## 5c. Cross-product to commutator bridge — Pauli-linear-combination form
    (Phase 6t Wave 2-followup substrate 2026-05-22 PM post-compact)

The 𝔰𝔲(2) Lie algebra has the structure constants `[σ_i, σ_j] = 2i·ε_{ijk}·σ_k`,
which in Pauli-coordinate notation gives the bridge:

  `[a·σ̄, b·σ̄] = 2i·(a × b)·σ̄`

where `a, b ∈ ℝ³` (the Pauli coefficient vectors), `×` is the standard ℝ³ cross
product, and `σ̄ = (σ_x, σ_y, σ_z)`. This is the load-bearing identity for
discharging `BalancedCommutatorGeneralAxisGroup` via the Pauli-coordinate
construction: given target -i·θ·H = -i·θ·h·σ̄, find F̂ × Ĝ = -(θ/2)·h, choose
F̂, Ĝ from the perpendicular plane to h, and apply this bridge.

Mathlib upstream-PR candidate: any field's σ-like structure constants admit
the same cross-product factorization. -/

/-- **Cross-product to commutator bridge (Mathlib upstream-PR candidate)**:
for any real Pauli coefficient vectors `a, b ∈ ℝ³`, the commutator of the
corresponding 𝔰𝔲(2) elements factors through the standard ℝ³ cross product:

  `[a₁·σ_x + a₂·σ_y + a₃·σ_z, b₁·σ_x + b₂·σ_y + b₃·σ_z] = 2i·((a×b)₁·σ_x + (a×b)₂·σ_y + (a×b)₃·σ_z)`

where `(a × b)_1 = a₂b₃ - a₃b₂`, etc.

Proof strategy: per-entry computation via `ext + fin_cases + simp + ring`,
following the established Pauli-matrix proof pattern from `comm_σ_x_σ_y` etc.
This is the load-bearing substrate for the Wave 2-followup general-axis
discharge of `BalancedCommutatorGeneralAxisGroup`. -/
theorem pauli_linear_commutator_eq
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) :
    (((a₁ : ℂ) • σ_x + (a₂ : ℂ) • σ_y + (a₃ : ℂ) • σ_z) *
        ((b₁ : ℂ) • σ_x + (b₂ : ℂ) • σ_y + (b₃ : ℂ) • σ_z) -
      ((b₁ : ℂ) • σ_x + (b₂ : ℂ) • σ_y + (b₃ : ℂ) • σ_z) *
        ((a₁ : ℂ) • σ_x + (a₂ : ℂ) • σ_y + (a₃ : ℂ) • σ_z))
    = (2 * Complex.I) •
        ((((a₂ * b₃ - a₃ * b₂) : ℝ) : ℂ) • σ_x +
         (((a₃ * b₁ - a₁ * b₃) : ℝ) : ℂ) • σ_y +
         (((a₁ * b₂ - a₂ * b₁) : ℝ) : ℂ) • σ_z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ_x, σ_y, σ_z, Matrix.sub_apply, Matrix.smul_apply, Complex.ext_iff,
          smul_eq_mul] <;>
    refine ⟨?_, ?_⟩ <;> ring

/-! ## 5d. Pauli-linear-combination linftyOp norm bound
    (Phase 6t Wave 2-followup substrate 2026-05-22 PM post-compact, Task #44)

The exact linftyOp operator norm of a real-linear combination of Pauli matrices
is `‖a·σ_x + b·σ_y + c·σ_z‖_linftyOp = |c| + √(a²+b²)`. This module ships the
upper-bound direction (`≤`), which is the form load-bearing for the Wave
2-followup general-axis discharge of `BalancedCommutatorGeneralAxisGroup`.

Computation: M := a·σ_x + b·σ_y + c·σ_z has matrix entries
  M[0][0] = c,     M[0][1] = a - ib
  M[1][0] = a + ib, M[1][1] = -c
Row 0 sum of norms: |c| + |a - ib| = |c| + √(a²+b²)
Row 1 sum of norms: |a + ib| + |-c| = √(a²+b²) + |c|
sup over rows = |c| + √(a²+b²).

Mathlib upstream-PR candidate: the natural generalization for `n×n` Hermitian
matrices over ℂ admits a similar entrywise/spectral-norm correspondence. -/

/-- **Pauli-linear-combination linftyOp norm bound (`≤` direction)**:
for any real `a, b, c`,

  `‖a·σ_x + b·σ_y + c·σ_z‖_linftyOp ≤ |c| + √(a²+b²)`.

This is the load-bearing tight-bound substrate for the Wave 2-followup
general-axis discharge of `BalancedCommutatorGeneralAxisGroup`.

Proof strategy: compute the explicit matrix entries, evaluate each row's
sum of entry-norms, and apply `Matrix.linfty_opNorm_def` + `Finset.sup_le`. -/
theorem pauli_linear_norm_le (a b c : ℝ) :
    ‖((a : ℂ) • σ_x + (b : ℂ) • σ_y + (c : ℂ) • σ_z :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ |c| + Real.sqrt (a^2 + b^2) := by
  set M : Matrix (Fin 2) (Fin 2) ℂ :=
    (a : ℂ) • σ_x + (b : ℂ) • σ_y + (c : ℂ) • σ_z with hM_def
  have h_rhs_nn : (0 : ℝ) ≤ |c| + Real.sqrt (a^2 + b^2) := by
    have h1 : 0 ≤ |c| := abs_nonneg c
    have h2 : 0 ≤ Real.sqrt (a^2 + b^2) := Real.sqrt_nonneg _
    linarith
  have h_norm_real_c : ‖(c : ℂ)‖ = |c| := by simp [Complex.norm_real]
  have h_norm_aib_sub : ‖(a : ℂ) - (b : ℂ) * Complex.I‖ = Real.sqrt (a^2 + b^2) := by
    rw [Complex.norm_def]
    congr 1
    simp [Complex.normSq, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h_norm_aib_add : ‖(a : ℂ) + (b : ℂ) * Complex.I‖ = Real.sqrt (a^2 + b^2) := by
    rw [Complex.norm_def]
    congr 1
    simp [Complex.normSq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h_row0 : ‖M 0 0‖ + ‖M 0 1‖ ≤ |c| + Real.sqrt (a^2 + b^2) := by
    have h_M00 : M 0 0 = (c : ℂ) := by
      simp [hM_def, σ_x, σ_y, σ_z, smul_eq_mul]
    have h_M01 : M 0 1 = (a : ℂ) - (b : ℂ) * Complex.I := by
      simp [hM_def, σ_x, σ_y, σ_z, smul_eq_mul]
      ring
    rw [h_M00, h_M01, h_norm_real_c, h_norm_aib_sub]
  have h_row1 : ‖M 1 0‖ + ‖M 1 1‖ ≤ |c| + Real.sqrt (a^2 + b^2) := by
    have h_M10 : M 1 0 = (a : ℂ) + (b : ℂ) * Complex.I := by
      simp [hM_def, σ_x, σ_y, σ_z, smul_eq_mul]
    have h_M11 : M 1 1 = -(c : ℂ) := by
      simp [hM_def, σ_x, σ_y, σ_z, smul_eq_mul]
    rw [h_M10, h_M11, norm_neg, h_norm_real_c, h_norm_aib_add]
    linarith
  rw [Matrix.linfty_opNorm_def]
  rw [show (|c| + Real.sqrt (a^2 + b^2) : ℝ) =
      ((|c| + Real.sqrt (a^2 + b^2)).toNNReal : ℝ) from
      (Real.coe_toNNReal _ h_rhs_nn).symm]
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro i _
  rw [show (|c| + Real.sqrt (a^2 + b^2)).toNNReal =
      ⟨|c| + Real.sqrt (a^2 + b^2), h_rhs_nn⟩ from
      Real.toNNReal_of_nonneg h_rhs_nn]
  rw [← NNReal.coe_le_coe]
  have h_coe : ((∑ j : Fin 2, ‖M i j‖₊ : NNReal) : ℝ) = ∑ j, ‖M i j‖ := by
    push_cast; rfl
  rw [h_coe, Fin.sum_univ_two]
  match i with
  | 0 => exact h_row0
  | 1 => exact h_row1

/-! ## 5e. Pauli-coordinate extraction for Hermitian traceless 2×2 matrices
    (Phase 6t Wave 2-followup substrate 2026-05-22 PM post-compact, Task #45)

Any 2×2 Hermitian traceless matrix `H : Matrix (Fin 2) (Fin 2) ℂ` decomposes as
`H = a·σ_x + b·σ_y + c·σ_z` for unique reals `(a, b, c)`. The closed-form
extraction is:

  a := (H 0 1).re    (real part of off-diagonal)
  b := -(H 0 1).im   (negated imaginary part of off-diagonal)
  c := (H 0 0).re    (real diagonal entry)

This is the load-bearing substrate for the Wave 2-followup general-axis
discharge of `BalancedCommutatorGeneralAxisGroup`: given an arbitrary
Hermitian traceless `H` of unit linftyOp-norm, we obtain Pauli coefficients
`(a, b, c)` to feed into the constructive perpendicular-vector machinery.

Mathlib upstream-PR candidate: the natural generalization to the basis of
generalized Gell-Mann matrices admits a similar extraction. -/

/-- **Pauli coordinate extraction (Mathlib upstream-PR candidate)**: any 2×2
Hermitian traceless matrix decomposes as `(H 0 1).re·σ_x + (-(H 0 1).im)·σ_y
+ (H 0 0).re·σ_z`.

Proof: by entrywise computation. Uses `Matrix.IsHermitian.apply` to give
`H i j = star (H j i)`, which forces the diagonal entries to be real and
the off-diagonal entries to be complex conjugates of each other. Combined
with tracelessness `H 0 0 + H 1 1 = 0`, the four matrix entries match the
Pauli expansion entry by entry. -/
theorem pauli_decomp_of_hermitian_traceless
    (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H.IsHermitian) (htr : H.trace = 0) :
    H = ((H 0 1).re : ℂ) • σ_x + (-(H 0 1).im : ℂ) • σ_y + ((H 0 0).re : ℂ) • σ_z := by
  have h_swap : ∀ i j : Fin 2, H i j = star (H j i) := fun i j => (hH.apply i j).symm
  have h_00_real : (H 0 0).im = 0 := by
    have h := h_swap 0 0
    have h_im_eq : (H 0 0).im = -(H 0 0).im := by
      have := congrArg Complex.im h
      simp at this
      exact this
    linarith
  have h_11_eq : H 1 1 = -(H 0 0) := by
    have h_trace_eq : H.trace = H 0 0 + H 1 1 := by
      simp [Matrix.trace, Fin.sum_univ_two]
    have : H 0 0 + H 1 1 = 0 := by rw [← h_trace_eq]; exact htr
    linear_combination this
  ext i j
  rcases i with ⟨ki, hki⟩
  rcases j with ⟨kj, hkj⟩
  interval_cases ki <;> interval_cases kj <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, σ_x, σ_y, σ_z,
               Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
               Matrix.cons_val_fin_one]
  · apply Complex.ext
    · simp
    · show (H ⟨0, hki⟩ ⟨0, hkj⟩).im = _
      have : H ⟨0, hki⟩ ⟨0, hkj⟩ = H 0 0 := rfl
      rw [this]
      simp [h_00_real]
  · have : H ⟨0, hki⟩ ⟨1, hkj⟩ = H 0 1 := rfl
    rw [this]
    apply Complex.ext
    · simp
    · simp
  · have h_eq : H ⟨1, hki⟩ ⟨0, hkj⟩ = H 1 0 := rfl
    rw [h_eq, h_swap 1 0]
    apply Complex.ext
    · simp
    · simp
  · have h_eq : H ⟨1, hki⟩ ⟨1, hkj⟩ = H 1 1 := rfl
    rw [h_eq, h_11_eq]
    apply Complex.ext
    · simp
    · simp [h_00_real]

/-! ## 6. Predicate-level scaffold for general-axis case (deferred)

The general-axis case `H = θ · (n_x σ_x + n_y σ_y + n_z σ_z)` for unit
`n ∈ ℝ³` reduces to the Z-axis case via SU(2) rotation:

  ∃ R ∈ SU(2): R · σ_z · R† = n·σ  (Bloch sphere homogeneity)

and then  `F := R · √(θ/2)σ_y · R†`,  `G := R · √(θ/2)σ_x · R†`  works.

The SU(2) Bloch parametrization is genuinely new substrate (~200-400 LoC
incl. the SO(3)-cover map + Euler angle decomposition).  We document the
**predicate** here; the substantive proof is deferred. -/

/-- Predicate-level scaffold for D-N Lemma 2 (general axis).  For any
traceless hermitian `H : Matrix (Fin 2) (Fin 2) ℂ` with `‖H‖ ≤ 1`,
there exist hermitian `F, G` with `‖F‖, ‖G‖ ≤ Real.sqrt (‖H‖ / 2)` such
that `F · G − G · F = -Complex.I • H`.

**Status:** predicate-only.  The Z-axis case is proved by
`qubit_balanced_commutator_z_axis`; the general case factors through
SU(2) rotation and is deferred to Wave 2d.3-followup-general. -/
def QubitBalancedCommutatorGeneralAxis : Prop :=
  ∀ (H : Matrix (Fin 2) (Fin 2) ℂ), H.IsHermitian → H.trace = 0 → ‖H‖ ≤ 1 →
    ∃ (F G : Matrix (Fin 2) (Fin 2) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧
      ‖F‖ ≤ Real.sqrt (‖H‖ / 2) ∧ ‖G‖ ≤ Real.sqrt (‖H‖ / 2) ∧
      F * G - G * F = -(Complex.I) • H

/-! ## 7. Module summary

`QubitBalancedCommutator.lean` (Phase 6p Wave 2d.3-followup, 2026-05-14):
qubit Bloch-sphere balanced commutator (D-N §4.1 Eq. 10-13) — the
substantive Lemma 2 content for the Z-axis coordinate case.

**Shipped (zero new axioms):**
  - **§1**: `σ_{x,y,z}_norm_le_one` — Pauli `linftyOpNorm` ≤ 1 (3 thms).
  - **§2**: `smul_σ_{x,y,z}_norm_le` — `‖(α : ℂ) • σ‖ ≤ |α|` (3 thms).
  - **§3**: `smul_σ_{x,y,z}_isHermitian` — hermiticity for real α (3 thms).
  - **§4**: `balanced_commutator_z_core` — the core identity
    `[α·σ_y, α·σ_x] = -(2·α²·i) • σ_z` via `comm_σ_x_σ_y` substantively.
  - **§5**: `qubit_balanced_commutator_z_axis` — **the substantive D-N
    Lemma 2 ship** (Z-axis case).  Existence of `F = √(θ/2)·σ_y`,
    `G = √(θ/2)·σ_x` with the required hermiticity + norm + commutator
    identity, for any `θ ∈ [0, 1]`.
  - **§6**: `QubitBalancedCommutatorGeneralAxis` — predicate scaffold
    for the general-axis case (deferred ~200-400 LoC of SU(2)/SO(3)
    cover substrate).

**Substantive content:**
  (a) D-N Lemma 2 explicit construction proved for the coordinate case.
  (b) Pauli `linftyOpNorm` ≤ 1 (3 results, new Mathlib-grade substrate).
  (c) Scalar-multiplication hermiticity for real α (3 results).
  (d) Predicate-level scaffold for general-axis case.

**Cross-module bridge integrity** (Stage-3a pipeline check #6):
  - imports `SKEFTHawking.PauliMatrices` and the proof of
    `balanced_commutator_z_core` substantively calls `comm_σ_x_σ_y`
    (not just docstring reference).
  - imports needed for downstream: `Wave 2d.5-followup-full` can compose
    `qubit_balanced_commutator_z_axis` with `MatrixBCHCubic.bch_order_2_cubic_thm`
    to produce a single recursive SK step in the Z-axis coordinate case.

**Pipeline-Invariant compliance:**
  - Zero new project-local axioms (constructive proof grounded in
    `PauliMatrices.comm_σ_x_σ_y` + Mathlib norm theory).
  - Zero `maxHeartbeats` overrides; proofs ≤30 lines each.
  - Pipeline Invariant #15 (no new axioms without sign-off) ✓.
-/

end SKEFTHawking.FKLW
