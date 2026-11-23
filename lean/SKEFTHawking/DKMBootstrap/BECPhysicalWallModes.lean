import SKEFTHawking.DKMBootstrap.BECWallParity

/-!
# Physical one-dimensional wall modes

The carrier is Lebesgue L² on `(0,T/2)`, for positive doubled period `T`.
`odd = false` selects the even (Neumann) realization and includes frequency zero;
`odd = true` selects the odd (Dirichlet) realization and excludes frequency zero.
Positive Fourier pairs are multiplied by `sqrt 2` before the accepted half-interval
unitary is applied. The odd family retains the constant unit phase of the Fourier
difference. Higher products and maximal Sobolev trace domains are separate constructions.
-/

noncomputable section
open Complex MeasureTheory
namespace SKEFTHawking.DKMBootstrap.BECPhysicalWallModes
open BECWallParity BECPeriodicCommutator

/-- `true` denotes odd parity, `false` even parity. -/
def sign (odd : Bool) : ℂ := if odd then -1 else 1

@[simp] theorem sign_sq (odd : Bool) : sign odd ^ 2 = 1 := by
  cases odd <;> norm_num [sign]

/-- Nonnegative even frequencies, strictly positive odd frequencies. -/
abbrev Index (odd : Bool) := {n : ℕ // odd = true → 0 < n}

/-- Even frequencies are numbered starting at zero. -/
def evenIndex (n : ℕ) : Index false := ⟨n, by simp⟩

/-- Odd frequencies are numbered starting at one. -/
def oddIndex (n : ℕ) : Index true := ⟨n + 1, by omega⟩

/-- The zero mode is unchanged; each positive projected pair is normalized by `sqrt 2`. -/
def normalization (n : ℕ) : ℂ := if n = 0 then 1 else (Real.sqrt 2 : ℂ)

theorem normalization_ne_zero (n : ℕ) : normalization n ≠ 0 := by
  unfold normalization
  split_ifs
  · exact one_ne_zero
  · exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))

variable (T : ℝ) [Fact (0 < T)]

/-- Normalized vector in the original finite Fourier parity core. -/
def coreMode (odd : Bool) (n : Index odd) : parityCore T (sign odd) :=
  normalization n.val • parityMode T (sign odd) (sign_sq odd) (n.val : ℤ)

/-- The actual physical interval L² wall mode. -/
def wallMode (odd : Bool) (n : Index odd) : HalfSpace T :=
  halfUnitary T (sign odd) (sign_sq odd) (coreMode T odd n)

/-- Explicit Fourier pair in the ambient normalized Haar carrier. -/
theorem coe_coreMode (odd : Bool) (n : Index odd) :
    ((coreMode T odd n : paritySpace T (sign odd)) : ModeSpace T) =
      normalization n.val • ((1 / 2 : ℂ) •
        (mode T (n.val : ℤ) + sign odd • mode T (-(n.val : ℤ)))) := by
  simp only [coreMode, Submodule.coe_smul, coe_parityMode]

/-- Continuous Fourier pair before physical half-interval restriction. -/
def circlePair (odd : Bool) (n : Index odd) : C(AddCircle T, ℂ) :=
  normalization n.val • ((1 / 2 : ℂ) •
    (fourier (n.val : ℤ) + sign odd • fourier (-(n.val : ℤ))))

theorem circlePair_toLp (odd : Bool) (n : Index odd) :
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (circlePair T odd n) =
      ((coreMode T odd n : paritySpace T (sign odd)) : ModeSpace T) := by
  rw [coe_coreMode]
  simp only [circlePair, map_smul, map_add, mode, fourierLp]

/-- The chosen continuous physical representative; arbitrary Lp representatives agree a.e. -/
def wallRepresentative (odd : Bool) (n : Index odd) (x : ℝ) : ℂ :=
  ((Real.sqrt (T / 2))⁻¹ : ℂ) * circlePair T odd n (x : AddCircle T)

omit [Fact (0 < T)] in
/-- Continuity belongs to the chosen representative, rather than every Lp representative. -/
theorem wallRepresentative_continuous (odd : Bool) (n : Index odd) :
    Continuous (wallRepresentative T odd n) :=
  continuous_const.mul ((circlePair T odd n).continuous.comp (AddCircle.continuous_mk' T))

theorem wallMode_ae (odd : Bool) (n : Index odd) :
    (wallMode T odd n : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioo 0 (T / 2))]
      wallRepresentative T odd n := by
  have hp : (((coreMode T odd n : paritySpace T (sign odd)) : ModeSpace T) :
      AddCircle T → ℂ) =ᵐ[AddCircle.haarAddCircle] circlePair T odd n := by
    rw [← circlePair_toLp]
    exact ContinuousMap.coeFn_toLp _ _
  rw [← volume_ae_eq_haar T] at hp
  filter_upwards [halfUnitary_ae T (sign odd) (sign_sq odd) (coreMode T odd n),
    ae_half_of_volume T hp] with x hx hp
  exact hx.trans (congrArg (fun z : ℂ ↦ ((Real.sqrt (T / 2))⁻¹ : ℂ) * z) hp)

/-- Inner products are computed from the actual four Fourier-pair terms. -/
theorem coreMode_inner (odd : Bool) (n m : Index odd) :
    inner ℂ (coreMode T odd n : paritySpace T (sign odd))
      (coreMode T odd m : paritySpace T (sign odd)) = if n = m then 1 else 0 := by
  change inner ℂ
    ((coreMode T odd n : paritySpace T (sign odd)) : ModeSpace T)
    ((coreMode T odd m : paritySpace T (sign odd)) : ModeSpace T) = _
  rw [coe_coreMode, coe_coreMode]
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    orthonormal_iff_ite.mp (modes_orthonormal T)]
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := n.property
  have hm := m.property
  by_cases he : n = m
  · subst m
    by_cases hz : n.val = 0
    · have ho : odd = false := by cases odd <;> simp_all
      norm_num [normalization, hz, ho, sign, map_ofNat]
    · have hne : (n.val : ℤ) ≠ -(n.val : ℤ) := by omega
      have hne' : -(n.val : ℤ) ≠ (n.val : ℤ) := Ne.symm hne
      cases odd <;>
        norm_num [normalization, hz, sign, hne, hne', map_ofNat] <;>
        linear_combination hs / 2
  · have hnm : n.val ≠ m.val := fun h ↦ he (Subtype.ext h)
    have h1 : (n.val : ℤ) ≠ (m.val : ℤ) := by omega
    have h2 : (n.val : ℤ) ≠ -(m.val : ℤ) := by omega
    have h3 : -(n.val : ℤ) ≠ (m.val : ℤ) := by omega
    have h4 : -(n.val : ℤ) ≠ -(m.val : ℤ) := by omega
    simp [he, h1, h2, h3, h4]

/-- Orthonormality on the genuine physical interval carrier. -/
theorem wallMode_orthonormal (odd : Bool) : Orthonormal ℂ (wallMode T odd) := by
  rw [orthonormal_iff_ite]
  intro n m
  change inner ℂ (halfUnitary T (sign odd) (sign_sq odd) _)
    (halfUnitary T (sign odd) (sign_sq odd) _) = _
  rw [LinearIsometryEquiv.inner_map_map]
  exact coreMode_inner T odd n m

/-- Negative Fourier indices give the same pair up to the parity sign. -/
theorem parityMode_neg (odd : Bool) (n : ℤ) :
    (parityMode T (sign odd) (sign_sq odd) (-n) : paritySpace T (sign odd)) =
      sign odd • (parityMode T (sign odd) (sign_sq odd) n : paritySpace T (sign odd)) := by
  apply Subtype.ext
  simp only [Submodule.coe_smul, coe_parityMode, neg_neg]
  cases odd <;> simp only [sign, Bool.false_eq_true, ↓reduceIte,
    neg_smul, one_smul] <;> module

/-- The accepted parity core is the span of all projected original Fourier characters. -/
theorem parityCore_eq_span (odd : Bool) :
    parityCore T (sign odd) = Submodule.span ℂ
      (Set.range fun n : ℤ ↦
        (parityMode T (sign odd) (sign_sq odd) n : paritySpace T (sign odd))) := by
  calc
    parityCore T (sign odd) =
        (trigDomain T).map (projectionInto T (sign odd) (sign_sq odd)).toLinearMap :=
      parityCore_eq_projected T (sign odd) (sign_sq odd)
    _ = _ := by rw [trigDomain_eq_span, Submodule.map_span, ← Set.range_comp]; rfl

/-- A valid nonnegative projected character belongs to the normalized mode span. -/
theorem parityMode_nat_mem_span (odd : Bool) (n : Index odd) :
    (parityMode T (sign odd) (sign_sq odd) (n.val : ℤ) : paritySpace T (sign odd)) ∈
      Submodule.span ℂ (Set.range fun m : Index odd ↦
        (coreMode T odd m : paritySpace T (sign odd))) := by
  have h := Submodule.subset_span (R := ℂ)
    (Set.mem_range_self (f := fun m : Index odd ↦
      (coreMode T odd m : paritySpace T (sign odd))) n)
  have hh := Submodule.smul_mem _ (normalization n.val)⁻¹ h
  simpa only [coreMode, Submodule.coe_smul, smul_smul,
    inv_mul_cancel₀ (normalization_ne_zero n.val), one_smul] using hh

/-- Removing negative duplicates and the vanishing odd zero mode preserves the genuine span. -/
theorem parityMode_mem_span (odd : Bool) (n : ℤ) :
    (parityMode T (sign odd) (sign_sq odd) n : paritySpace T (sign odd)) ∈
      Submodule.span ℂ (Set.range fun m : Index odd ↦
        (coreMode T odd m : paritySpace T (sign odd))) := by
  have hp (k : ℕ) :
      (parityMode T (sign odd) (sign_sq odd) (k : ℤ) : paritySpace T (sign odd)) ∈
        Submodule.span ℂ (Set.range fun m : Index odd ↦
          (coreMode T odd m : paritySpace T (sign odd))) := by
    by_cases hk : odd = true → 0 < k
    · exact parityMode_nat_mem_span T odd ⟨k, hk⟩
    · have ho : odd = true := by cases odd <;> simp_all
      have hz : k = 0 := by simp_all
      have he : (parityMode T (sign odd) (sign_sq odd) (k : ℤ) :
          paritySpace T (sign odd)) = 0 := by
        apply Subtype.ext
        simp [coe_parityMode, ho, hz, sign]
      rw [he]
      exact Submodule.zero_mem _
  by_cases hn : 0 ≤ n
  · simpa only [Int.toNat_of_nonneg hn] using hp n.toNat
  · have he : n = -(((-n).toNat : ℕ) : ℤ) := by omega
    rw [he, parityMode_neg]
    exact Submodule.smul_mem _ _ (hp (-n).toNat)

/-- The normalized, nonredundant family spans exactly the original finite parity core. -/
theorem coreMode_span (odd : Bool) :
    Submodule.span ℂ (Set.range fun n : Index odd ↦
      (coreMode T odd n : paritySpace T (sign odd))) = parityCore T (sign odd) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    exact (coreMode T odd n).property
  · apply (parityCore_eq_span T odd).le.trans
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    exact parityMode_mem_span T odd n

/-- Density follows from the projected original Fourier span, without a completeness premise. -/
theorem coreMode_dense (odd : Bool) :
    (Submodule.span ℂ (Set.range fun n : Index odd ↦
      (coreMode T odd n : paritySpace T (sign odd)))).topologicalClosure = ⊤ := by
  rw [coreMode_span]
  exact parityCore_dense T (sign odd) (sign_sq odd)

/-- The physical interval family has dense algebraic span in actual Lebesgue L². -/
theorem wallMode_dense (odd : Bool) :
    (Submodule.span ℂ (Set.range (wallMode T odd))).topologicalClosure = ⊤ := by
  let U := (halfUnitary T (sign odd) (sign_sq odd)).toContinuousLinearEquiv
  have hd : DenseRange U.toContinuousLinearMap := U.surjective.denseRange
  have h := hd.topologicalClosure_map_submodule (coreMode_dense T odd)
  rw [Submodule.map_span, ← Set.range_comp] at h
  exact h

/-- Usable Hilbert basis, constructed from the proved physical family and dense span. -/
def wallBasis (odd : Bool) : HilbertBasis (Index odd) ℂ (HalfSpace T) :=
  HilbertBasis.mk (wallMode_orthonormal T odd) (wallMode_dense T odd).ge

@[simp] theorem coe_wallBasis (odd : Bool) : ⇑(wallBasis T odd) = wallMode T odd :=
  HilbertBasis.coe_mk _ _

/-- Canonical finite-core domain vector for the already accepted physical wall kinetic. -/
def modeDomain (a : ℝ) (odd : Bool) (n : Index odd) :
    (halfKinetic T (scale T a) (sign odd) (sign_sq odd)).domain :=
  halfKineticDomain T (scale T a) (sign odd) (sign_sq odd)
    (parityClosureCore T (scale T a) (sign odd) (coreMode T odd n))

@[simp] theorem coe_modeDomain (a : ℝ) (odd : Bool) (n : Index odd) :
    (modeDomain T a odd n : HalfSpace T) = wallMode T odd n := rfl

/-- Every physical mode belongs to the existing closed wall kinetic domain. -/
theorem wallMode_mem_domain (a : ℝ) (odd : Bool) (n : Index odd) :
    wallMode T odd n ∈ (halfKinetic T (scale T a) (sign odd) (sign_sq odd)).domain :=
  (modeDomain T a odd n).property

/-- Closing the original parity operator preserves its paired eigenaction. -/
theorem closure_coreMode_action (c : ℝ) (odd : Bool) (n : Index odd) :
    (parityPMap T c (sign odd)).closure
      (parityClosureCore T c (sign odd) (coreMode T odd n)) =
      ((c : ℂ) * (n.val : ℂ) ^ 2) •
        (coreMode T odd n : paritySpace T (sign odd)) := by
  have h := ((parityPMap T c (sign odd)).le_closure.2
    (x := coreMode T odd n)
    (y := parityClosureCore T c (sign odd) (coreMode T odd n)) rfl).symm
  rw [h]
  change parityKinetic T c (sign odd) (coreMode T odd n) = _
  simp only [coreMode, map_smul, parityKinetic_parityMode, Int.cast_natCast,
    Submodule.coe_smul]
  module

/-- Exact eigenaction with the physical interval scale `a (π/(T/2))² n²`. -/
theorem wallMode_action (a : ℝ) (odd : Bool) (n : Index odd) :
    halfKinetic T (scale T a) (sign odd) (sign_sq odd) (modeDomain T a odd n) =
      ((a * (Real.pi / (T / 2)) ^ 2 * (n.val : ℝ) ^ 2 : ℝ) : ℂ) •
        wallMode T odd n := by
  rw [modeDomain, halfKinetic_apply, closure_coreMode_action, map_smul]
  rw [halfKinetic_scale]
  push_cast
  rfl

end SKEFTHawking.DKMBootstrap.BECPhysicalWallModes
