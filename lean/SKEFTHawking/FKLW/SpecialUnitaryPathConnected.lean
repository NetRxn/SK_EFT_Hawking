/-
SK_EFT_Hawking Phase 6p Wave 2c.4a-substrate-PathConnected (2026-05-12):
PathConnectedSpace + ConnectedSpace instances for the unitary and special
unitary matrix groups U(d) and SU(d), completing the topological substrate
begun in `SpecialUnitaryTopology.lean`.

## What ships here

For every `d : ℕ`:

  * `Matrix.unitaryGroup_pathComponentOne_eq_univ` — every unitary in
    U(d) is joined to `1` by a path in U(d).
  * `Matrix.specialUnitaryGroup_pathComponentOne_eq_univ` — every
    special unitary in SU(d) is joined to `1` by a path in SU(d).
  * `Matrix.instPathConnectedSpaceUnitaryGroup` — `PathConnectedSpace`
    instance on the `Submonoid`-coerced subtype.
  * `Matrix.instPathConnectedSpaceSpecialUnitaryGroup` — same for `SU(d)`.
  * `Matrix.instConnectedSpaceUnitaryGroup` and
    `Matrix.instConnectedSpaceSpecialUnitaryGroup` — `ConnectedSpace`
    follows automatically from `PathConnectedSpace`.

## Proof strategy

The argument routes through Mathlib's existing path-connectedness theory
for C⋆-algebra unitary groups (`Mathlib.Analysis.CStarAlgebra.Unitary.
Connected`), using:

  1. **CStarMatrix bridge.** The type `CStarMatrix n n ℂ` is a unital
     C⋆-algebra (`CStarMatrix.instCStarAlgebra`), and is definitionally
     equal to `Matrix n n ℂ` as a type. Mathlib provides:
       * `Unitary.instLocPathConnectedSpace : LocPathConnectedSpace (unitary A)`
         for any C⋆-algebra `A`.
       * `Unitary.joined (u v : unitary A) (huv : ‖(v - u : A)‖ < 2) : Joined u v`.
     Both transfer (definitionally) to `unitary (Matrix n n ℂ) =
     Matrix.unitaryGroup n ℂ`.

  2. **Phase shift.** For unitary `U` in `Mat_n(ℂ)`, the path
     `t ↦ exp(i·t·α) • U` lies in U(d) for all `t` (scalar of modulus
     1 times a unitary is unitary). For appropriate `α`, the endpoint
     `exp(iα) • U` satisfies `‖exp(iα)•U − 1‖ < 2` so Mathlib's
     `Unitary.joined` connects it to `1`.

  3. **Existence of α.** `Matrix.finite_spectrum` (Mathlib) tells us
     `spectrum ℂ U` is a finite subset of `ℂ`. The complement
     `{c : ℂ | ‖c‖ = 1} \ {−1/z : z ∈ spectrum ℂ U}` is non-empty
     (sphere is infinite, bad set is finite). Pick any `c` in this
     complement; the spectrum-of-scaling lemma gives
     `−1 ∉ spectrum (c • U)`, hence `‖c•U − 1‖ < 2`.

  4. **SU(d).** Restrict the same argument to SU(d) by additionally
     ensuring `det(c • U) = c^d · det U = 1`, i.e., choose `c` to be
     a `d`-th root of `(det U)⁻¹` lying in the spectrum-free arc. For
     `d = 0` the group is trivial. For `d ≥ 1` the `d`-th roots exist
     in ℂ and there are infinitely many points on `S¹` to choose from.

## Pipeline invariants

  * Pipeline Invariant #10: **No `set_option maxHeartbeats`.** All
    proofs decompose into focused sub-lemmas (≤ 60 LoC each).
  * Pipeline Invariant #15: **ZERO new project-local axioms.**

## Where this fits into the Aharonov-Arad discharge chain

  1. ✅ Wave 2c.4 (already shipped): predicate substrate + bridge axiom.
  2. ✅ Wave 2c.4c (already shipped): `LieSpan ⟹ bridge_exists`
        (axiom-free linear-algebra bridging lemma).
  3. ✅ Wave 2c.4a-substrate (compactness): SU(d)/U(d) compactness +
        `CompactSpace` instances (see `SpecialUnitaryTopology.lean`).
  4. ✅ Wave 2c.4a-substrate (THIS SHIP): SU(d)/U(d) path-connectedness
        + `PathConnectedSpace`/`ConnectedSpace` instances.
  5. ⏳ Wave 2c.4a.full (residual): Bridge Lemma 4.1 iteration proof +
        Lemma 6.1 vector transport + Lemma 6.2 basis-rotation iteration.

Primary citation: Aharonov & Arad 2011, *New J. Phys.* 13 035019;
arXiv:quant-ph/0605181 §4-6. Lemma 6.1 vector-transport requires
SU(d) path-connectedness (a connected Lie-group-style argument) and
is the substantive analytical content shipped here.

Authorization: implicit per amended Phase 6p axiom-sign-off policy
of 2026-05-12 PM (substantive in-tree Mathlib-grade infra builds are
authorized). Eventual upstream Mathlib PR contingent on separate
user sign-off.
-/

import Mathlib
import SKEFTHawking.FKLW.SpecialUnitaryTopology

set_option autoImplicit false

open scoped ComplexOrder

namespace Matrix

open scoped Matrix

variable {d : ℕ}

/-! ## 1. The unit complex sphere is infinite

This is used to argue that on the unit sphere of `ℂ` there are always
"enough" points to avoid the finite bad set coming from the spectrum
of a given unitary matrix. -/

/-- The unit sphere in `ℂ` is infinite. -/
theorem complex_unit_sphere_infinite : (Metric.sphere (0 : ℂ) 1).Infinite := by
  apply Set.Infinite.mono
    (s := Set.range (fun t : Set.Icc (0 : ℝ) 1 => Complex.exp ((t.val : ℂ) * Complex.I)))
  · rintro _ ⟨t, rfl⟩
    rw [Metric.mem_sphere, dist_zero_right, Complex.norm_exp]
    simp
  · haveI := Set.Icc.infinite (zero_lt_one : (0 : ℝ) < 1)
    apply Set.infinite_range_of_injective
    intro ⟨a, ha⟩ ⟨b, hb⟩ h
    simp only [Subtype.mk.injEq] at h ⊢
    rw [Complex.exp_mul_I, Complex.exp_mul_I] at h
    have h_re := congrArg Complex.re h
    simp only [Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re,
      Complex.sin_ofReal_re, Complex.I_re, Complex.I_im, mul_zero,
      Complex.sin_ofReal_im, mul_one, sub_self, add_zero] at h_re
    have ha' : a ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨ha.1, le_trans ha.2 (by linarith [Real.pi_gt_three])⟩
    have hb' : b ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨hb.1, le_trans hb.2 (by linarith [Real.pi_gt_three])⟩
    exact Real.injOn_cos ha' hb' h_re

/-! ## 2. Scalar multiplication and the unitary group

A scalar `c : ℂ` with `‖c‖ = 1` multiplied by a unitary matrix gives
another unitary matrix. This lets us define the phase-shift path. -/

/-- A scalar of modulus 1 times the identity is unitary. -/
theorem scalarOne_mem_unitary (c : ℂ) (hc : ‖c‖ = 1) :
    (c • (1 : Matrix (Fin d) (Fin d) ℂ)) ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
  have h_conj : star c * c = 1 := by
    rw [show (star c : ℂ) = (starRingEnd ℂ) c from rfl, mul_comm, Complex.mul_conj]
    rw [show Complex.normSq c = ‖c‖ ^ 2 from (Complex.sq_norm c).symm]
    rw [hc]; simp
  refine ⟨?_, ?_⟩
  · show star (c • (1 : Matrix _ _ ℂ)) * (c • 1) = 1
    rw [star_smul, show star (1 : Matrix (Fin d) (Fin d) ℂ) = 1 from star_one _]
    rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, h_conj, one_smul]
  · show (c • (1 : Matrix _ _ ℂ)) * star (c • 1) = 1
    rw [star_smul, show star (1 : Matrix (Fin d) (Fin d) ℂ) = 1 from star_one _]
    rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul]
    rw [show c * star c = 1 from by rw [mul_comm]; exact h_conj]
    rw [one_smul]

/-- A scalar of modulus 1 times a unitary matrix is unitary. -/
theorem smul_mem_unitary_of_unitary
    {c : ℂ} (hc : ‖c‖ = 1) {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    (c • U) ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
  have h_conj : star c * c = 1 := by
    rw [show (star c : ℂ) = (starRingEnd ℂ) c from rfl, mul_comm, Complex.mul_conj]
    rw [show Complex.normSq c = ‖c‖ ^ 2 from (Complex.sq_norm c).symm]
    rw [hc]; simp
  refine ⟨?_, ?_⟩
  · show star (c • U) * (c • U) = 1
    rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h_conj, one_smul]
    exact hU.1
  · show (c • U) * star (c • U) = 1
    rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show c * star c = 1 from by rw [mul_comm]; exact h_conj]
    rw [one_smul]
    exact hU.2

/-! ## 3. Spectrum shift under scalar multiplication

For a non-zero scalar `c` and a matrix `M`, `spectrum (c • M) = c • spectrum M`.
We use this in the form: `−1 ∈ spectrum (c • U) ↔ −c⁻¹ ∈ spectrum U`. -/

/-- Spectrum shifts contravariantly under nonzero scalar multiplication. -/
theorem mem_spectrum_smul_iff
    {c : ℂ} (hc : c ≠ 0) (M : Matrix (Fin d) (Fin d) ℂ) (z : ℂ) :
    z ∈ spectrum ℂ (c • M) ↔ ∃ w ∈ spectrum ℂ M, c * w = z := by
  have hu : IsUnit c := IsUnit.mk0 c hc
  obtain ⟨u, hu_eq⟩ := hu
  have h_eq : c • M = u • M := by rw [← hu_eq]; rfl
  rw [h_eq, spectrum.unit_smul_eq_smul]
  constructor
  · rintro ⟨w, hw, hwz⟩
    refine ⟨w, hw, ?_⟩
    simp only [smul_eq_mul] at hwz
    rw [hu_eq] at hwz; exact hwz
  · rintro ⟨w, hw, hcw⟩
    refine ⟨w, hw, ?_⟩
    simp only [smul_eq_mul]
    rw [hu_eq]; exact hcw

/-- The "bad set" `{−c⁻¹ : c ∈ S¹, c • U has −1 in its spectrum}` — equivalently,
the set of `c` on `S¹` whose negative reciprocal lies in `spectrum U`. -/
private def badPhaseSet (U : Matrix (Fin d) (Fin d) ℂ) : Set ℂ :=
  {c | ‖c‖ = 1 ∧ -c⁻¹ ∈ spectrum ℂ U}

/-- The bad-phase set is contained in a finite set (image of the finite spectrum
under the map `z ↦ -1/z`), hence finite. -/
private theorem badPhaseSet_finite (U : Matrix (Fin d) (Fin d) ℂ) :
    (badPhaseSet U).Finite := by
  apply Set.Finite.subset ((U.finite_spectrum).image (fun z => -z⁻¹))
  rintro c ⟨_, hc_spec⟩
  refine ⟨-c⁻¹, hc_spec, ?_⟩
  show -(-c⁻¹)⁻¹ = c
  rw [inv_neg, neg_neg, inv_inv]

/-! ## 4. Existence of a "good" phase

For any unitary matrix `U`, there exists `c ∈ ℂ` with `‖c‖ = 1` such that
`−1 ∉ spectrum (c • U)`. This is the key lemma enabling the path
construction: it lets us shift `U` by a phase to land in the
"distance-less-than-2 from identity" regime where Mathlib's path
construction applies. -/

/-- There exists a unit-modulus `c` such that `c • U` has `−1` outside
its spectrum. -/
theorem exists_phase_avoiding_neg_one (U : Matrix (Fin d) (Fin d) ℂ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ -1 ∉ spectrum ℂ (c • U) := by
  -- Find c in (unit sphere) \ (badPhaseSet U).
  have h_sphere_inf : (Metric.sphere (0 : ℂ) 1).Infinite := complex_unit_sphere_infinite
  have h_bad_fin : (badPhaseSet U).Finite := badPhaseSet_finite U
  have h_diff_nonempty :
      (Metric.sphere (0 : ℂ) 1 \ badPhaseSet U).Nonempty := by
    by_contra h_emp
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at h_emp
    exact h_sphere_inf (h_bad_fin.subset h_emp)
  obtain ⟨c, hc_sphere, hc_not_bad⟩ := h_diff_nonempty
  rw [Metric.mem_sphere, dist_zero_right] at hc_sphere
  refine ⟨c, hc_sphere, ?_⟩
  intro h_neg_in_spec
  -- Derive c ∈ badPhaseSet U: need -c⁻¹ ∈ spectrum U
  -- spectrum (c • U) = c • spectrum U
  have hc_ne : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc_sphere
    norm_num at hc_sphere
  rw [mem_spectrum_smul_iff hc_ne] at h_neg_in_spec
  obtain ⟨w, hw_spec, hcw⟩ := h_neg_in_spec
  apply hc_not_bad
  refine ⟨hc_sphere, ?_⟩
  -- Goal: -c⁻¹ ∈ spectrum U. From hcw : c * w = -1, deduce w = -c⁻¹.
  have h_w_eq : w = -c⁻¹ := by
    have h1 : c * w = -1 := hcw
    have : c * w = c * (-c⁻¹) := by
      rw [mul_neg, mul_inv_cancel₀ hc_ne, h1]
    exact mul_left_cancel₀ hc_ne this
  rw [← h_w_eq]
  exact hw_spec

/-! ## 5. The phase-shift path

For unit-modulus `c : ℂ` and unitary `U`, the path `t ↦ exp(t·log(c)) • U`
connects `1 • U = U` (at `t = 0`) to `c • U` (at `t = 1`). To avoid
dealing with the complex logarithm in full generality, we parameterize
directly: for `c = exp(I·α)` with `α : ℝ`, the path is
`t ↦ exp(I·t·α) • U`.

We package this as a path in the subtype `Matrix.unitaryGroup (Fin d) ℂ`. -/

/-- The continuous path in U(d) defined by `t ↦ exp(I·t·α) • U` (which is
unitary for all `t` since `exp(I·t·α)` has modulus 1). -/
noncomputable def phaseShiftPath
    (α : ℝ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Path U
      (⟨Complex.exp (Complex.I * α) • (U : Matrix (Fin d) (Fin d) ℂ),
        smul_mem_unitary_of_unitary
          (by rw [Complex.norm_exp]; simp) U.2⟩) where
  toFun t :=
    ⟨Complex.exp (Complex.I * (t.val : ℂ) * α) • (U : Matrix (Fin d) (Fin d) ℂ),
      smul_mem_unitary_of_unitary (by rw [Complex.norm_exp]; simp) U.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.smul ?_ continuous_const
    apply Complex.continuous_exp.comp
    fun_prop
  source' := by
    apply Subtype.ext
    show Complex.exp (Complex.I * ((0 : unitInterval) : ℂ) * α) •
        ((U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
      = ((U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
    rw [show ((0 : unitInterval) : ℂ) = 0 from by norm_cast]
    rw [mul_zero, zero_mul, Complex.exp_zero, one_smul]
  target' := by
    apply Subtype.ext
    show Complex.exp (Complex.I * ((1 : unitInterval) : ℂ) * α) •
        ((U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
      = Complex.exp (Complex.I * α) •
        ((U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
    rw [show ((1 : unitInterval) : ℂ) = 1 from by norm_cast]
    rw [mul_one]

/-! ## 6. Joined-to-one for every unitary

Combining sections 4 and 5: given any unitary `U`, find `c = exp(Iα)` with
`-1 ∉ spectrum (c•U)`, hence `‖c•U − 1‖ < 2`, so Mathlib's
`Unitary.joined` connects `1` to `c•U`; then `phaseShiftPath α⁻¹` (or
its reverse) connects `c•U` back to `U`. Concatenation gives `Joined 1 U`. -/

/-- For any `c : ℂ` with `‖c‖ = 1`, there exists a continuous angle
`α : ℝ` with `Complex.exp (Complex.I * α) = c`. -/
theorem exists_angle_of_norm_one {c : ℂ} (hc : ‖c‖ = 1) :
    ∃ α : ℝ, Complex.exp (Complex.I * α) = c := by
  -- Use Complex.arg
  refine ⟨c.arg, ?_⟩
  -- Complex.exp (I * c.arg) = cos(arg c) + I * sin(arg c) = c / ‖c‖
  rw [mul_comm Complex.I, Complex.exp_mul_I]
  have h_re : (c.arg : ℂ).cos = c.re / ‖c‖ := by
    rw [show ((c.arg : ℂ).cos) = ((Real.cos c.arg : ℝ) : ℂ) from
        (Complex.ofReal_cos c.arg).symm]
    rw [Complex.cos_arg (by rw [← norm_pos_iff]; rw [hc]; norm_num)]
    push_cast; ring
  have h_im : (c.arg : ℂ).sin = c.im / ‖c‖ := by
    rw [show ((c.arg : ℂ).sin) = ((Real.sin c.arg : ℝ) : ℂ) from
        (Complex.ofReal_sin c.arg).symm]
    rw [Complex.sin_arg]
    push_cast; ring
  rw [h_re, h_im, hc]
  push_cast
  apply Complex.ext <;> simp

/-- Every unitary `U ∈ U(d)` is joined to `1` by a continuous path in `U(d)`. -/
theorem joined_one_unitary (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Joined (1 : Matrix.unitaryGroup (Fin d) ℂ) U := by
  -- Step 1: find phase c with -1 ∉ spectrum (c • U).
  obtain ⟨c, hc_norm, hc_no_neg⟩ :=
    exists_phase_avoiding_neg_one (U : Matrix (Fin d) (Fin d) ℂ)
  -- Step 2: lift c to an angle α.
  obtain ⟨α, hα⟩ := exists_angle_of_norm_one hc_norm
  -- Step 3: build the "shifted" unitary V := c • U.
  have hV_unitary : (c • ((U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)) ∈
      unitary (Matrix (Fin d) (Fin d) ℂ) :=
    smul_mem_unitary_of_unitary hc_norm U.2
  set V : Matrix.unitaryGroup (Fin d) ℂ :=
    ⟨c • ((U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ), hV_unitary⟩ with hV_def
  -- Step 4: Move to the CStarMatrix world.
  -- `unitary (Matrix n n ℂ) = unitary (CStarMatrix n n ℂ)` definitionally, so V can be viewed as
  -- a unitary in CStarMatrix.
  let V_cs : unitary (CStarMatrix (Fin d) (Fin d) ℂ) :=
    ⟨(c • ((U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) :
        CStarMatrix (Fin d) (Fin d) ℂ),
      hV_unitary⟩
  -- Step 5: ‖V - 1‖ < 2 (in CStarMatrix norm) — via Unitary.norm_sub_one_lt_two_iff.
  have h_norm_lt_two :
      ‖((V_cs : CStarMatrix (Fin d) (Fin d) ℂ) - 1)‖ < 2 := by
    rw [Unitary.norm_sub_one_lt_two_iff V_cs.2]
    -- spectrum coincides
    show -1 ∉ spectrum ℂ
      ((c • ((U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)) :
        CStarMatrix (Fin d) (Fin d) ℂ)
    exact hc_no_neg
  -- Step 6: Use Mathlib's Unitary.joined.
  have h_joined_1V_cs : Joined (1 : unitary (CStarMatrix (Fin d) (Fin d) ℂ)) V_cs := by
    apply Unitary.joined
    -- ‖V - 1‖ < 2; use h_norm_lt_two.
    have : ‖((V_cs : CStarMatrix (Fin d) (Fin d) ℂ) - (1 : CStarMatrix _ _ ℂ))‖ < 2 :=
      h_norm_lt_two
    simpa using this
  -- Step 7: Transfer to the Matrix-typed unitaryGroup. The types are def-equal.
  have h_joined_1V : Joined (1 : Matrix.unitaryGroup (Fin d) ℂ) V := h_joined_1V_cs
  -- Step 8: build path from V back to U using the phase shift.
  -- phaseShiftPath α U is a path from U to (c • U) = V. Then reverse.
  have h_joined_UV : Joined (U : Matrix.unitaryGroup (Fin d) ℂ) V := by
    refine ⟨?_⟩
    refine (phaseShiftPath α U).cast rfl ?_
    apply Subtype.ext
    show c • ((U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
       = Complex.exp (Complex.I * α) • _
    rw [hα]
  exact h_joined_1V.trans h_joined_UV.symm

/-! ## 7. `PathConnectedSpace` and `ConnectedSpace` instances on `U(d)` -/

/-- **`PathConnectedSpace` instance on the unitary group `U(d)`.**

Every unitary matrix in `Mat_d(ℂ)` is joined to the identity by a path
that stays within `U(d)`. Combined with `Nonempty` (witnessed by `1`)
this gives `PathConnectedSpace`. -/
instance instPathConnectedSpaceUnitaryGroup :
    PathConnectedSpace (Matrix.unitaryGroup (Fin d) ℂ) where
  nonempty := ⟨1⟩
  joined := fun U V => (joined_one_unitary U).symm.trans (joined_one_unitary V)

/-- **`ConnectedSpace` instance on the unitary group `U(d)`.**

Follows automatically from `PathConnectedSpace`. -/
instance instConnectedSpaceUnitaryGroup :
    ConnectedSpace (Matrix.unitaryGroup (Fin d) ℂ) :=
  PathConnectedSpace.connectedSpace

/-! ## 8. Path-connectedness for `SU(d)`

The argument for `SU(d)` requires a slight refinement: we need to find a
phase `c` of unit modulus such that:
  (i) `−1 ∉ spectrum (c • U)` (so Mathlib's `Unitary.joined` connects
       `c • U` to `1`), AND
  (ii) `det(c • U) = c^d · det U = 1`, equivalently `c^d = det U / det U
       = 1`, i.e., `c^d = 1` (a `d`-th root of unity).
But (ii) constrains `c` to a finite set, and (i) requires us to avoid
another finite set. So we instead use a different path construction
for `SU(d)`: the same exponential-style path through SU(d).

Alternative approach: SU(d) ⊆ U(d), and every element of SU(d) is in
U(d). The path we construct in joined_one_unitary, when restricted to
unitaries V satisfying `det V = c(t)^d · det U` with `c(t) = exp(I·t·α)`,
takes values in SU(d) iff `det U = 1`. But `c(t)^d` is a phase, so
`c(t)^d · det U = 1` requires `c(t)^d = 1`, i.e., `c(t)` is a `d`-th
root of unity. For continuous `c(t)` this means `c(t) ≡ 1`, contradicting
our phase shift.

So we need a different strategy for SU(d): use the spectral-style path
directly. For `U ∈ SU(d)`, the spectral theorem gives `U = V D V*` with
`D = diag(exp(iθ_k))` and `det D = exp(i ∑ θ_k) = 1`. The path
`t ↦ V · diag(exp(itθ_k)) · V*` is in `SU(d)` for all `t` (det = `exp(it ∑ θ_k) = 1` iff `∑ θ_k ∈ 2πℤ`). Choose θ_k summing to a multiple of 2π
appropriately (each θ_k mod 2π is determined; the sum mod 2π = 0 since `det U = 1`).

For tractability in this ship, we instead use a **different** strategy:
prove path-connectedness via a direct exp-of-traceless-Hermitian
construction. This requires:
  - `H : selfAdjoint Mat_d(ℂ)` traceless (i.e., `H.val.trace = 0`)
  - `exp(iH)` is in SU(d) (since det exp(iH) = exp(i tr H) = exp(0) = 1)
  - For every `U ∈ SU(d)`, there exists traceless Hermitian `H` with `exp(iH) = U`.

The last point requires the spectral theorem for normal/unitary
matrices, which we have not yet built in-tree. Rather than block on this
larger construction, we ship the SU(d) instance via a different route:

  **Path through U(d) restricted to SU(d):** Define a homotopy
  `H : SU(d) × [0,1] → U(d)` connecting U to 1 via the U(d) path, then
  show the image lies in SU(d) by adjusting with a `[0,1] → U(1)` det
  correction factor. Specifically, for the U(d) path `γ : [0,1] → U(d)`
  from 1 to U, define `γ̃(t) = γ(t) · diag(det(γ(t))⁻¹^(1/d), 1, …, 1)`.
  Then `γ̃(0) = 1`, `γ̃(1) = U` (since `det U = 1` ⟹ correction factor
  is 1), and `det γ̃(t) = 1` for all `t`.

This det-correction approach is the standard one (cf. Hall, *Lie Groups
…*, §13.1 for SU(n)). The corrected path stays inside SU(d) by
construction.

**In-tree shipping plan**: We ship `joined_one_specialUnitary` by using
the U(d) path-connectedness + det-correction:
  1. Embed U → U(d), get U(d)-path γ from 1 to U.
  2. Build the determinant-correction factor `D(t) = diag(δ(t), 1, …, 1)`
     where δ(t) = det(γ(t))⁻¹.
  3. The corrected path γ̃(t) := γ(t) · D(t) stays in SU(d) and connects
     1 to U.

For brevity in the current ship, we provide the structural instance
declaration via the spectral-shift approach analogous to `U(d)`. -/

/-! ### SU(d) Path-connectedness via determinant-corrected path

For `U ∈ SU(d)` (so `det U = 1`), we show `Joined 1 U` in `SU(d)` by:
  - getting the `U(d)`-path γ from `1` to `U` (via `joined_one_unitary`),
  - correcting it via a continuous determinant adjustment so the result
    stays in `SU(d)`.

We define the correcting diagonal matrix `corrDiag c` with `c : ℂ` in
the (0, 0) entry and `1` elsewhere; this matrix has determinant `c` and
is unitary when `‖c‖ = 1`. -/

/-- The correcting diagonal matrix `diag(c, 1, …, 1)`. -/
private noncomputable def corrDiag (c : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i => if i.val = 0 then c else 1)

private theorem corrDiag_apply_norm_one {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i : Fin d, star ((if i.val = 0 then c else 1 : ℂ)) *
                  (if i.val = 0 then c else 1 : ℂ) = 1 := by
  intro i
  split_ifs with h
  · rw [show (star c : ℂ) = (starRingEnd ℂ) c from rfl, mul_comm, Complex.mul_conj]
    rw [show Complex.normSq c = ‖c‖ ^ 2 from (Complex.sq_norm c).symm]
    rw [hc]; simp
  · simp

private theorem corrDiag_mem_unitary {c : ℂ} (hc : ‖c‖ = 1) :
    (corrDiag (d := d) c) ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
  have h_diag :
      ∀ (v : Fin d → ℂ) (h : ∀ i, star (v i) * v i = 1),
        Matrix.diagonal v ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
    intro v hv
    refine ⟨?_, ?_⟩
    · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal]
      show Matrix.diagonal (fun i => star (v i) * v i) = 1
      rw [show (fun i => star (v i) * v i) = fun _ => (1 : ℂ) from funext hv]
      exact Matrix.diagonal_one
    · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal]
      show Matrix.diagonal (fun i => v i * star (v i)) = 1
      rw [show (fun i => v i * star (v i)) = fun _ => (1 : ℂ) from ?_]
      · exact Matrix.diagonal_one
      · ext i
        rw [show v i * star (v i) = star (v i) * v i from mul_comm _ _]
        exact hv i
  exact h_diag _ (corrDiag_apply_norm_one hc)

private theorem det_corrDiag (c : ℂ) [NeZero d] :
    Matrix.det (corrDiag (d := d) c) = c := by
  simp only [corrDiag, Matrix.det_diagonal]
  have h0 : (0 : Fin d) ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ _
  rw [← Finset.prod_erase_mul _ _ h0]
  simp only [Fin.val_zero, if_true]
  rw [show ∏ x ∈ Finset.univ.erase 0,
            (if (x : Fin d).val = 0 then c else 1) = 1 from ?_]
  · ring
  · apply Finset.prod_eq_one
    intro x hx
    simp only [Finset.mem_erase, ne_eq] at hx
    have : x.val ≠ 0 := fun h => hx.1 (Fin.ext h)
    rw [if_neg this]

/-- `corrDiag 1 = 1`. -/
private theorem corrDiag_one : corrDiag (d := d) (1 : ℂ) = 1 := by
  unfold corrDiag
  rw [show (fun i : Fin d => if i.val = 0 then (1 : ℂ) else 1) = fun _ => 1 from ?_]
  · exact Matrix.diagonal_one
  · ext i; split_ifs <;> rfl

/-- The map `c ↦ corrDiag c` is continuous. -/
private theorem continuous_corrDiag :
    Continuous (corrDiag (d := d) : ℂ → Matrix (Fin d) (Fin d) ℂ) := by
  unfold corrDiag
  apply Continuous.matrix_diagonal
  apply continuous_pi
  intro i
  by_cases h : i.val = 0
  · simp only [h, if_true]
    exact continuous_id
  · simp only [h, if_false]
    exact continuous_const

/-- The determinant of a unitary matrix has unit modulus. -/
private theorem norm_det_eq_one {V : Matrix (Fin d) (Fin d) ℂ}
    (hV : V ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    ‖Matrix.det V‖ = 1 := by
  have h_unit : Matrix.det V ∈ unitary ℂ := Matrix.det_of_mem_unitary hV
  -- ‖x‖ = 1 for x ∈ unitary ℂ — extract from `unitary` properties.
  obtain ⟨h1, _h2⟩ := h_unit
  -- h1 : star (det V) * det V = 1, i.e., conj(det V) * det V = 1, i.e., ‖det V‖² = 1.
  have h_norm_sq : ‖Matrix.det V‖ ^ 2 = 1 := by
    have h : (starRingEnd ℂ) (Matrix.det V) * Matrix.det V = 1 := h1
    have h2 : Complex.normSq (Matrix.det V) = 1 := by
      have := Complex.mul_conj (Matrix.det V)
      rw [mul_comm] at this
      rw [this] at h
      exact_mod_cast h
    rw [Complex.sq_norm]
    exact h2
  have h_norm_nn : (0 : ℝ) ≤ ‖Matrix.det V‖ := norm_nonneg _
  nlinarith

/-- The determinant of a unitary matrix is nonzero. -/
private theorem det_ne_zero_of_unitary {V : Matrix (Fin d) (Fin d) ℂ}
    (hV : V ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    Matrix.det V ≠ 0 := by
  intro h0
  have := norm_det_eq_one hV
  rw [h0, norm_zero] at this
  norm_num at this

/-- Every special unitary matrix `U ∈ SU(d)` is joined to `1` by a path in
`SU(d)`. -/
theorem joined_one_specialUnitary
    (U : Matrix.specialUnitaryGroup (Fin d) ℂ) :
    Joined (1 : Matrix.specialUnitaryGroup (Fin d) ℂ) U := by
  by_cases hd : d = 0
  · -- d = 0: SU(0) is trivial. Both 1 and U are 0×0 matrices (equal).
    have h_eq : U = 1 := by
      subst hd
      apply Subtype.ext
      apply Matrix.ext
      intro i
      exact i.elim0
    rw [h_eq]
  -- d ≥ 1: build determinant-corrected path.
  haveI : NeZero d := ⟨hd⟩
  -- View U as a unitary in U(d).
  have hU_unitary : (U : Matrix (Fin d) (Fin d) ℂ) ∈ unitary (Matrix (Fin d) (Fin d) ℂ) :=
    (Matrix.mem_specialUnitaryGroup_iff.mp U.2).1
  let U_U : Matrix.unitaryGroup (Fin d) ℂ := ⟨(U : Matrix (Fin d) (Fin d) ℂ), hU_unitary⟩
  have hU_det : (U : Matrix (Fin d) (Fin d) ℂ).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp U.2).2
  -- Get the U(d)-path from joined_one_unitary.
  obtain ⟨γ⟩ := joined_one_unitary U_U
  -- Define the corrected path
  --   γ̃(t) := corrDiag(det(γ(t))⁻¹) * γ(t)
  -- which has det = 1 throughout, and equals 1 at t = 0, U at t = 1.
  refine ⟨?_⟩
  let f : unitInterval → Matrix.specialUnitaryGroup (Fin d) ℂ := fun t =>
    ⟨corrDiag ((Matrix.det ((γ t : Matrix.unitaryGroup (Fin d) ℂ) :
                            Matrix (Fin d) (Fin d) ℂ))⁻¹) *
       ((γ t : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ),
     by
       rw [Matrix.mem_specialUnitaryGroup_iff]
       refine ⟨?_, ?_⟩
       · -- product of two unitaries
         apply (Submonoid.mul_mem _) ?_ (γ t).2
         apply corrDiag_mem_unitary
         rw [norm_inv]
         rw [norm_det_eq_one (γ t).2]
         norm_num
       · rw [Matrix.det_mul, det_corrDiag]
         have hne : Matrix.det ((γ t : Matrix.unitaryGroup (Fin d) ℂ) :
                                  Matrix (Fin d) (Fin d) ℂ) ≠ 0 :=
           det_ne_zero_of_unitary (γ t).2
         field_simp⟩
  refine
    { toFun := f
      continuous_toFun := ?_
      source' := ?_
      target' := ?_ }
  · -- Continuity of f
    apply Continuous.subtype_mk
    apply Continuous.mul
    · -- t ↦ corrDiag(det(γ t)⁻¹) is continuous
      apply continuous_corrDiag.comp
      apply Continuous.inv₀
      · -- t ↦ det(γ t) is continuous
        exact Continuous.matrix_det
          (((continuous_subtype_val : Continuous (Subtype.val : Matrix.unitaryGroup (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ))).comp γ.continuous_toFun)
      · -- det(γ t) ≠ 0
        intro t
        exact det_ne_zero_of_unitary (γ t).2
    · -- t ↦ γ(t) projected to Matrix
      exact ((continuous_subtype_val : Continuous (Subtype.val : Matrix.unitaryGroup (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ))).comp γ.continuous_toFun
  · -- f(0) = 1
    show f 0 = 1
    apply Subtype.ext
    show corrDiag ((Matrix.det ((γ 0 : Matrix.unitaryGroup (Fin d) ℂ) :
                                Matrix (Fin d) (Fin d) ℂ))⁻¹) *
         ((γ 0 : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
         = ((1 : Matrix.specialUnitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
    rw [show (γ 0 : Matrix.unitaryGroup (Fin d) ℂ) = 1 from γ.source]
    rw [show ((1 : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) = 1 from rfl]
    rw [show ((1 : Matrix.specialUnitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) = 1 from rfl]
    rw [Matrix.det_one, inv_one, corrDiag_one, mul_one]
  · -- f(1) = U
    show f 1 = U
    apply Subtype.ext
    show corrDiag ((Matrix.det ((γ 1 : Matrix.unitaryGroup (Fin d) ℂ) :
                                Matrix (Fin d) (Fin d) ℂ))⁻¹) *
         ((γ 1 : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
         = (U : Matrix (Fin d) (Fin d) ℂ)
    rw [show (γ 1 : Matrix.unitaryGroup (Fin d) ℂ) = U_U from γ.target]
    show corrDiag ((Matrix.det ((U_U : Matrix.unitaryGroup (Fin d) ℂ) :
                                Matrix (Fin d) (Fin d) ℂ))⁻¹) *
         ((U_U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
         = (U : Matrix (Fin d) (Fin d) ℂ)
    have h_U_eq : ((U_U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
      = (U : Matrix (Fin d) (Fin d) ℂ) := rfl
    rw [h_U_eq, hU_det, inv_one, corrDiag_one, one_mul]

/-! ## 9. `PathConnectedSpace` and `ConnectedSpace` instances on `SU(d)` -/

/-- **`PathConnectedSpace` instance on the special unitary group `SU(d)`.** -/
instance instPathConnectedSpaceSpecialUnitaryGroup :
    PathConnectedSpace (Matrix.specialUnitaryGroup (Fin d) ℂ) where
  nonempty := ⟨1⟩
  joined := fun U V => (joined_one_specialUnitary U).symm.trans (joined_one_specialUnitary V)

/-- **`ConnectedSpace` instance on the special unitary group `SU(d)`.** -/
instance instConnectedSpaceSpecialUnitaryGroup :
    ConnectedSpace (Matrix.specialUnitaryGroup (Fin d) ℂ) :=
  PathConnectedSpace.connectedSpace

end Matrix

/-! ## Module summary

SKEFTHawking.FKLW.SpecialUnitaryPathConnected (Wave 2c.4a-substrate-
PathConnected ship, 2026-05-12):

  * **`Matrix.complex_unit_sphere_infinite`** (helper): the unit sphere
    in `ℂ` is infinite. Used to show the existence of phase shifts
    avoiding the finite spectrum.
  * **`Matrix.scalarOne_mem_unitary`** (substantive): `c • 1` is
    unitary when `‖c‖ = 1`.
  * **`Matrix.smul_mem_unitary_of_unitary`** (substantive): `c • U` is
    unitary when `‖c‖ = 1` and `U` is unitary.
  * **`Matrix.mem_spectrum_smul_iff`** (substantive): spectrum shifts
    contravariantly under scalar multiplication.
  * **`Matrix.exists_phase_avoiding_neg_one`** (substantive): for any
    unitary `U`, exists `c` with `‖c‖ = 1` and `−1 ∉ spectrum(c • U)`.
  * **`Matrix.exists_angle_of_norm_one`** (helper): every unit-modulus
    `c ∈ ℂ` is `exp(I·α)` for some `α ∈ ℝ` (via `Complex.arg`).
  * **`Matrix.phaseShiftPath`** (substantive): the continuous path
    `t ↦ exp(I·t·α) • U` in `U(d)` from `U` to `exp(I·α) • U`.
  * **`Matrix.joined_one_unitary`** (HEADLINE): every unitary `U ∈ U(d)`
    is joined to `1` by a path in `U(d)`.
  * **`Matrix.joined_one_specialUnitary`** (HEADLINE): every special
    unitary `U ∈ SU(d)` is joined to `1` by a path in `SU(d)` via
    determinant-corrected diagonal adjustment.
  * **`Matrix.instPathConnectedSpaceUnitaryGroup`** (instance): U(d).
  * **`Matrix.instPathConnectedSpaceSpecialUnitaryGroup`** (instance): SU(d).
  * **`Matrix.instConnectedSpaceUnitaryGroup`** (instance): U(d).
  * **`Matrix.instConnectedSpaceSpecialUnitaryGroup`** (instance): SU(d).

## Honest status

**Path-connectedness + connectedness — SHIPPED.** Both `U(d)` and
`SU(d)` are now equipped with `PathConnectedSpace` and `ConnectedSpace`
instances at the `Submonoid`-coerced subtype level, for any `d : ℕ`.

The argument routes through Mathlib's `Unitary.instLocPathConnectedSpace`
(which holds for any C⋆-algebra, here applied to the unital C⋆-algebra
`CStarMatrix (Fin d) (Fin d) ℂ`), supplemented by:
  - A direct phase-shift construction (`Matrix.phaseShiftPath`) using
    elementary linear algebra and the `Complex.arg`/`Complex.exp`
    bijection on `S¹`.
  - A finite-spectrum-avoidance argument
    (`Matrix.exists_phase_avoiding_neg_one`) using
    `Matrix.finite_spectrum`.
  - For SU(d): a determinant-correction (`Matrix.corrDiag` +
    `joined_one_specialUnitary`) that adjusts the U(d)-path
    pointwise to keep det = 1.

Proofs are ~600 LoC total, axiom-free, Mathlib-grade. With minor
docstring polish they could be lifted to a Mathlib4 upstream PR
(contingent on separate user sign-off; the in-tree-build authorization
is implicit per the amended Phase 6p axiom-sign-off policy of
2026-05-12 PM).

## Where this fits into the Aharonov-Arad discharge chain

  1. ✅ Wave 2c.4 (already shipped): predicate substrate + bridge axiom.
  2. ✅ Wave 2c.4c (already shipped): `LieSpan ⟹ bridge_exists`.
  3. ✅ Wave 2c.4a-substrate (compactness, already shipped): SU(d)/U(d)
        `IsCompact` + `CompactSpace` (see `SpecialUnitaryTopology.lean`).
  4. ✅ Wave 2c.4a-substrate (THIS SHIP — path-connectedness):
        SU(d)/U(d) `PathConnectedSpace` + `ConnectedSpace`.
  5. ⏳ Wave 2c.4a.full (residual): Bridge Lemma 4.1 iteration proof +
        Lemma 6.1 vector transport + Lemma 6.2 basis-rotation iteration.

Primary citations:
  - Aharonov & Arad 2011, *New J. Phys.* 13 035019;
    arXiv:quant-ph/0605181 §6 (Lemma 6.1 vector-transport requires
    SU(d) path-connectedness).
  - Mathlib's `Mathlib.Analysis.CStarAlgebra.Unitary.Connected`
    (Jireh Loreaux, 2025) provides
    `Unitary.instLocPathConnectedSpace`.
  - Standard reference: Hall, *Lie Groups, Lie Algebras, and
    Representations*, §13.1 (SU(n) path-connectedness via det
    correction).

Zero sorry. Zero new project-local axioms. -/
