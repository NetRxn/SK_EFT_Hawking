import SKEFTHawking.DKMBootstrap.BECProductL2

/-!
# Finite spectral wall kinetics on physical product L²

The full, nonredundant wall products supply the finite spectral coordinates. Permutations act
on those actual L² vectors by inverse reindexing of labels. The normalized continuous group
average takes values in the actual bosonic fixed subspace. Averaged products are generators,
with no orthonormality assertion. The initial kinetic domain is the finite fixed span. Shifted
finite preimages give a self-adjoint closure with that graph core. No maximal Sobolev trace
characterization, interacting Hamiltonian or Fock self-adjointness is asserted.
-/

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate

namespace SKEFTHawking.DKMBootstrap.BECProductWallKinetic

open BECBosonicSectors BECProductL2 BECPhysicalWallModes

section Averaging

variable (l r : ℝ) (N : ℕ)

/-- Bounded normalized finite group average on physical product L². -/
def average : ConfigurationHilbert l r N →L[ℂ] ConfigurationHilbert l r N :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin N),
      (permutationUnitary l r σ).toLinearIsometry.toContinuousLinearMap

theorem average_apply (u : ConfigurationHilbert l r N) :
    average l r N u = (Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ •
      ∑ σ : Equiv.Perm (Fin N), permutationUnitary l r σ u := by
  simp only [average, smul_apply, sum_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]

/-- Left translation merely reindexes the finite group sum. -/
theorem permutation_average (τ : Equiv.Perm (Fin N)) (u : ConfigurationHilbert l r N) :
    permutationUnitary l r τ (average l r N u) = average l r N u := by
  rw [average_apply, map_smul, map_sum]
  congr 1
  simp only [← permutationUnitary_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ ↦ rfl)

theorem average_mem (u : ConfigurationHilbert l r N) :
    average l r N u ∈ bosonicSubspace l r N :=
  (mem_bosonicSubspace_iff l r _).mpr (fun τ ↦ permutation_average l r N τ u)

/-- Normalization works also in the vacuum sector, since every permutation group is nonempty. -/
theorem average_eq_self (u : BosonicHilbert l r N) :
    average l r N (u : ConfigurationHilbert l r N) = u := by
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hu := (mem_bosonicSubspace_iff l r
    (u : ConfigurationHilbert l r N)).mp u.2
  rw [average_apply]
  simp only [hu, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- The average valued in the actual fixed Hilbert subspace. -/
def averageInto : ConfigurationHilbert l r N →L[ℂ] BosonicHilbert l r N :=
  (average l r N).codRestrict _ (average_mem l r N)

theorem averageInto_surjective : Function.Surjective (averageInto l r N) := by
  intro u
  exact ⟨u, Subtype.ext (average_eq_self l r N u)⟩

theorem average_range : (average l r N).toLinearMap.range =
    (bosonicSubspace l r N).toSubmodule := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    exact average_mem l r N u
  · intro u hu
    exact ⟨u, average_eq_self l r N ⟨u, hu⟩⟩

end Averaging

variable (T : ℝ) [Fact (0 < T)] (odd : Bool) (N : ℕ)

/-- A physical product label, with the accepted odd/even one-coordinate indexing. -/
abbrev Label := Fin N → Index odd

/-- The real sum of the eigenvalues in `BECPhysicalWallModes.wallMode_action`. -/
def eigenvalue (a : ℝ) (n : Label odd N) : ℝ :=
  ∑ i, a * (Real.pi / (T / 2)) ^ 2 * ((n i).val : ℝ) ^ 2

omit [Fact (0 < T)] in
theorem eigenvalue_permutation (a : ℝ) (σ : Equiv.Perm (Fin N)) (n : Label odd N) :
    eigenvalue T odd N a (n ∘ σ.symm) = eigenvalue T odd N a n := by
  unfold eigenvalue
  exact Fintype.sum_equiv σ.symm _ _ (fun _ ↦ rfl)

/-- The actual coordinate pullback acts on product labels by the inverse permutation. -/
theorem permutation_wallProduct (σ : Equiv.Perm (Fin N)) (n : Label odd N) :
    permutationUnitary 0 (T / 2) σ (wallProduct T odd N n) =
      wallProduct T odd N (n ∘ σ.symm) := by
  apply Lp.ext
  have h := ((reindex_measurePreserving 0 (T / 2) σ).symm _).quasiMeasurePreserving.ae_eq
    (wallProduct_ae T odd N n)
  filter_upwards [permutationUnitary_ae 0 (T / 2) σ (wallProduct T odd N n), h,
    wallProduct_ae T odd N (n ∘ σ.symm)] with x hx hn hm
  rw [hx, hm]
  change wallProduct T odd N n ((reindex σ).symm x) = _
  dsimp only [Function.comp_def] at hn
  rw [hn]
  exact Fintype.prod_equiv σ _ _ (fun i ↦ by
    change wallRepresentative T odd (n i) (x (σ i)) = _
    simp)

/-- Synthesis uses the proved complete orthonormal physical product family. -/
def synthesis : (Label odd N →₀ ℂ) →ₗ[ℂ] ConfigurationHilbert 0 (T / 2) N :=
  Finsupp.linearCombination ℂ (wallProduct T odd N)

theorem synthesis_injective : Function.Injective (synthesis T odd N) :=
  (wallProduct_orthonormal T odd N).linearIndependent

/-- Actual finite physical product span. -/
def core : Submodule ℂ (ConfigurationHilbert 0 (T / 2) N) := (synthesis T odd N).range

theorem core_eq_span : core T odd N = Submodule.span ℂ (Set.range (wallProduct T odd N)) :=
  Finsupp.range_linearCombination ℂ

theorem core_dense : (core T odd N).topologicalClosure = ⊤ := by
  rw [core_eq_span]
  exact wallProduct_dense T odd N

/-- Unique finite coefficients, before any group averaging. -/
def coreEquiv : (Label odd N →₀ ℂ) ≃ₗ[ℂ] core T odd N :=
  LinearEquiv.ofInjective (synthesis T odd N) (synthesis_injective T odd N)

@[simp] theorem coe_coreEquiv (v : Label odd N →₀ ℂ) :
    (coreEquiv T odd N v : ConfigurationHilbert 0 (T / 2) N) = synthesis T odd N v := rfl

/-- A full product mode regarded as an element of the finite domain. -/
def coreMode (n : Label odd N) : core T odd N := coreEquiv T odd N (Finsupp.single n 1)

@[simp] theorem coe_coreMode (n : Label odd N) :
    (coreMode T odd N n : ConfigurationHilbert 0 (T / 2) N) = wallProduct T odd N n := by
  simp [coreMode, synthesis]

/-- The real finite diagonal preserves finite support. -/
def kineticCoeffs (a : ℝ) : (Label odd N →₀ ℂ) →ₗ[ℂ] (Label odd N →₀ ℂ) :=
  Finsupp.linearCombination ℂ
    (fun n ↦ (eigenvalue T odd N a n : ℂ) • Finsupp.single n 1)

/-- Spectral kinetic on the actual physical product span. -/
def kinetic (a : ℝ) : core T odd N →ₗ[ℂ] core T odd N :=
  (coreEquiv T odd N).toLinearMap ∘ₗ kineticCoeffs T odd N a ∘ₗ
    (coreEquiv T odd N).symm.toLinearMap

theorem kinetic_coreMode (a : ℝ) (n : Label odd N) :
    kinetic T odd N a (coreMode T odd N n) =
      (eigenvalue T odd N a n : ℂ) • coreMode T odd N n := by
  simp only [kinetic, coreMode, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, kineticCoeffs, Finsupp.linearCombination_single,
    one_smul, map_smul]

/-- On each product generator the spectral action equals the sum of the accepted
one-coordinate wall actions, placed in the actual continuous coordinate product. -/
theorem kinetic_coreMode_coordinate_action (a : ℝ) (n : Label odd N) :
    (kinetic T odd N a (coreMode T odd N n) : ConfigurationHilbert 0 (T / 2) N) =
      ∑ i : Fin N, product (Function.update (fun j ↦ wallMode T odd (n j)) i
        (BECWallParity.halfKinetic T (BECPeriodicCommutator.scale T a)
          (sign odd) (sign_sq odd) (modeDomain T a odd (n i)))) := by
  rw [kinetic_coreMode, Submodule.coe_smul, coe_coreMode]
  symm
  calc
    _ = ∑ i : Fin N,
        ((a * (Real.pi / (T / 2)) ^ 2 * ((n i).val : ℝ) ^ 2 : ℝ) : ℂ) •
          wallProduct T odd N n := by
      apply Finset.sum_congr rfl
      intro i _
      rw [wallMode_action]
      erw [product_update_smul]
      rw [Function.update_eq_self]
      rfl
    _ = _ := by
      rw [← Finset.sum_smul]
      congr 1
      simp only [eigenvalue, Complex.ofReal_sum]

/-- Single finite coefficients are scalar multiples of the full product modes. -/
theorem coreEquiv_single (n : Label odd N) (b : ℂ) :
    coreEquiv T odd N (Finsupp.single n b) = b • coreMode T odd N n := by
  rw [coreMode, ← map_smul]
  simp

/-- A permutation preserves the actual finite span. -/
theorem permutation_mem_core (σ : Equiv.Perm (Fin N))
    {u : ConfigurationHilbert 0 (T / 2) N} (hu : u ∈ core T odd N) :
    permutationUnitary 0 (T / 2) σ u ∈ core T odd N := by
  rw [core_eq_span] at hu ⊢
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨n, rfl⟩ := hu
    rw [permutation_wallProduct]
    exact Submodule.subset_span (Set.mem_range_self _)
  | zero => simp
  | add u v _ _ hu hv => simpa only [map_add] using Submodule.add_mem _ hu hv
  | smul b u _ hu => simpa only [map_smul] using Submodule.smul_mem _ b hu

/-- Restriction of the actual coordinate unitary to the finite domain. -/
def corePermutation (σ : Equiv.Perm (Fin N)) : core T odd N →ₗ[ℂ] core T odd N :=
  (((permutationUnitary 0 (T / 2) σ).toLinearEquiv.toLinearMap).comp
    (core T odd N).subtype).codRestrict _ (fun u ↦ permutation_mem_core T odd N σ u.2)

@[simp] theorem coe_corePermutation (σ : Equiv.Perm (Fin N)) (u : core T odd N) :
    (corePermutation T odd N σ u : ConfigurationHilbert 0 (T / 2) N) =
      permutationUnitary 0 (T / 2) σ u := rfl

theorem corePermutation_coreMode (σ : Equiv.Perm (Fin N)) (n : Label odd N) :
    corePermutation T odd N σ (coreMode T odd N n) =
      coreMode T odd N (n ∘ σ.symm) := by
  apply Subtype.ext
  simpa only [coe_corePermutation, coe_coreMode] using permutation_wallProduct T odd N σ n

/-- Commutation uses the actual inverse-label action and the real eigenvalue sum. -/
theorem kinetic_corePermutation (a : ℝ) (σ : Equiv.Perm (Fin N)) (u : core T odd N) :
    kinetic T odd N a (corePermutation T odd N σ u) =
      corePermutation T odd N σ (kinetic T odd N a u) := by
  obtain ⟨v, rfl⟩ := (coreEquiv T odd N).surjective u
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single n b =>
    simp only [coreEquiv_single, map_smul, corePermutation_coreMode, kinetic_coreMode,
      eigenvalue_permutation]

/-- Averaging preserves the original finite product core. -/
theorem average_mem_core (u : core T odd N) :
    average 0 (T / 2) N (u : ConfigurationHilbert 0 (T / 2) N) ∈ core T odd N := by
  rw [average_apply]
  apply Submodule.smul_mem
  exact Submodule.sum_mem _ (fun σ _ ↦ permutation_mem_core T odd N σ u.2)

/-- The finite core average has the same normalization as the bounded ambient average. -/
def coreAverage : core T odd N →ₗ[ℂ] core T odd N :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin N), corePermutation T odd N σ

@[simp] theorem coe_coreAverage (u : core T odd N) :
    (coreAverage T odd N u : ConfigurationHilbert 0 (T / 2) N) =
      average 0 (T / 2) N (u : ConfigurationHilbert 0 (T / 2) N) := by
  simp only [coreAverage, LinearMap.smul_apply, LinearMap.sum_apply, Submodule.coe_smul,
    Submodule.coe_sum, coe_corePermutation, average_apply]

theorem kinetic_coreAverage (a : ℝ) (u : core T odd N) :
    kinetic T odd N a (coreAverage T odd N u) =
      coreAverage T odd N (kinetic T odd N a u) := by
  simp only [coreAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    kinetic_corePermutation]

/-- The partial kinetic in full physical product L². -/
def kineticPMap (a : ℝ) :
    ConfigurationHilbert 0 (T / 2) N →ₗ.[ℂ] ConfigurationHilbert 0 (T / 2) N where
  domain := core T odd N
  toFun := (core T odd N).subtype.comp (kinetic T odd N a)

/-- Symmetry follows from the full orthonormal product family and real eigenvalues. -/
theorem kineticPMap_symmetric (a : ℝ) : DFT.IsSymmetricPMap (kineticPMap T odd N a) := by
  intro u w
  obtain ⟨v, rfl⟩ := (coreEquiv T odd N).surjective u
  obtain ⟨z, rfl⟩ := (coreEquiv T odd N).surjective w
  change inner ℂ (kinetic T odd N a (coreEquiv T odd N v) :
      ConfigurationHilbert 0 (T / 2) N) (coreEquiv T odd N z) =
    inner ℂ (coreEquiv T odd N v : ConfigurationHilbert 0 (T / 2) N)
      (kinetic T odd N a (coreEquiv T odd N z))
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, Submodule.coe_add, inner_add_left, hv, hw]
  | single n b =>
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add, Submodule.coe_add, inner_add_right, hv, hw]
    | single m d =>
      simp only [coreEquiv_single, map_smul, kinetic_coreMode, Submodule.coe_smul,
        coe_coreMode, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
      rw [orthonormal_iff_ite.mp (wallProduct_orthonormal T odd N)]
      split_ifs with h
      · subst m; ring
      · simp

/-- The actual bosonic finite domain is the ambient finite span pulled back by inclusion. -/
def bosonicCore : Submodule ℂ (BosonicHilbert 0 (T / 2) N) :=
  (core T odd N).comap (bosonicSubspace 0 (T / 2) N).toSubmodule.subtype

/-- Averaging describes precisely the finite fixed core, without claiming a basis of averages. -/
theorem bosonicCore_eq_averaged : bosonicCore T odd N =
    (core T odd N).map (averageInto 0 (T / 2) N).toLinearMap := by
  apply le_antisymm
  · intro u hu
    exact ⟨u, hu, Subtype.ext (average_eq_self 0 (T / 2) N u)⟩
  · rintro u ⟨v, hv, rfl⟩
    exact average_mem_core T odd N ⟨v, hv⟩

theorem bosonicCore_dense : (bosonicCore T odd N).topologicalClosure = ⊤ := by
  rw [bosonicCore_eq_averaged]
  exact (averageInto_surjective 0 (T / 2) N).denseRange.topologicalClosure_map_submodule
    (core_dense T odd N)

/-- The finite kinetic preserves the actual bosonic fixed condition. -/
theorem kinetic_mem_bosonic (a : ℝ) (u : core T odd N)
    (hu : (u : ConfigurationHilbert 0 (T / 2) N) ∈ bosonicSubspace 0 (T / 2) N) :
    (kinetic T odd N a u : ConfigurationHilbert 0 (T / 2) N) ∈
      bosonicSubspace 0 (T / 2) N := by
  rw [mem_bosonicSubspace_iff] at hu ⊢
  intro σ
  have hp : corePermutation T odd N σ u = u := Subtype.ext (hu σ)
  change (corePermutation T odd N σ (kinetic T odd N a u) :
    ConfigurationHilbert 0 (T / 2) N) = _
  rw [← kinetic_corePermutation, hp]

/-- Inclusion of the finite fixed core into the ambient finite domain. -/
def coreInclusion : bosonicCore T odd N →ₗ[ℂ] core T odd N where
  toFun u := ⟨u.1.1, u.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inherited kinetic takes values in the actual fixed Hilbert space. -/
def bosonicKinetic (a : ℝ) : bosonicCore T odd N →ₗ[ℂ] BosonicHilbert 0 (T / 2) N :=
  (((core T odd N).subtype.comp (kinetic T odd N a)).comp
    (coreInclusion T odd N)).codRestrict _
      (fun u ↦ kinetic_mem_bosonic T odd N a _ u.1.2)

@[simp] theorem coe_bosonicKinetic (a : ℝ) (u : bosonicCore T odd N) :
    (bosonicKinetic T odd N a u : ConfigurationHilbert 0 (T / 2) N) =
      (kinetic T odd N a (coreInclusion T odd N u) :
        ConfigurationHilbert 0 (T / 2) N) := rfl

/-- The bosonic finite spectral operator with its actual finite fixed domain. -/
def bosonicPMap (a : ℝ) :
    BosonicHilbert 0 (T / 2) N →ₗ.[ℂ] BosonicHilbert 0 (T / 2) N where
  domain := bosonicCore T odd N
  toFun := bosonicKinetic T odd N a

/-- Symmetry is inherited from the ambient real diagonal, using the actual subspace inner product. -/
theorem bosonicPMap_symmetric (a : ℝ) : DFT.IsSymmetricPMap (bosonicPMap T odd N a) := by
  intro u v
  exact kineticPMap_symmetric T odd N a (coreInclusion T odd N u) (coreInclusion T odd N v)

theorem bosonicPMap_dense (a : ℝ) :
    Dense ((bosonicPMap T odd N a).domain : Set (BosonicHilbert 0 (T / 2) N)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr (bosonicCore_dense T odd N)

/-- The nonreal shift on the original ambient finite product domain. -/
def shiftedKinetic (a μ : ℝ) : core T odd N →ₗ[ℂ] ConfigurationHilbert 0 (T / 2) N :=
  (core T odd N).subtype.comp (kinetic T odd N a) -
    (Complex.I * (μ : ℂ)) • (core T odd N).subtype

omit [Fact (0 < T)] in
/-- A nonzero imaginary shift cannot vanish on a real spectral eigenvalue. -/
theorem kinetic_shift_ne_zero (a μ : ℝ) (hμ : μ ≠ 0) (n : Label odd N) :
    (eigenvalue T odd N a n : ℂ) - Complex.I * (μ : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  exact hμ hi

/-- Dividing a single coefficient constructs an actual finite shifted preimage. -/
theorem shiftedKinetic_mode_preimage (a μ : ℝ) (hμ : μ ≠ 0) (n : Label odd N) :
    shiftedKinetic T odd N a μ
      (((eigenvalue T odd N a n : ℂ) - Complex.I * (μ : ℂ))⁻¹ • coreMode T odd N n) =
        wallProduct T odd N n := by
  have hn := kinetic_shift_ne_zero T odd N a μ hμ n
  simp only [shiftedKinetic, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_smul, kinetic_coreMode, Submodule.subtype_apply,
    coe_coreMode]
  rw [← sub_smul]
  simp [smul_smul, hn]

/-- Finite linearity solves every finite target, without a convergence assertion. -/
theorem core_le_shiftedKinetic_range (a μ : ℝ) (hμ : μ ≠ 0) :
    core T odd N ≤ (shiftedKinetic T odd N a μ).range := by
  apply (core_eq_span T odd N).le.trans
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact ⟨_, shiftedKinetic_mode_preimage T odd N a μ hμ n⟩

/-- The normalized finite average commutes with the actual shifted finite kinetic. -/
theorem shiftedKinetic_coreAverage (a μ : ℝ) (u : core T odd N) :
    shiftedKinetic T odd N a μ (coreAverage T odd N u) =
      average 0 (T / 2) N (shiftedKinetic T odd N a μ u) := by
  simp only [shiftedKinetic, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, Submodule.subtype_apply, kinetic_coreAverage, coe_coreAverage,
    map_sub, map_smul]

/-- Averaging a finite ambient solution solves each finite bosonic target. -/
theorem bosonic_shifted_preimage (a μ : ℝ) (hμ : μ ≠ 0) (v : bosonicCore T odd N) :
    ∃ u : (bosonicPMap T odd N a).domain,
      bosonicPMap T odd N a u - (Complex.I * (μ : ℂ)) •
        (u : BosonicHilbert 0 (T / 2) N) = v := by
  obtain ⟨x, hx⟩ := core_le_shiftedKinetic_range T odd N a μ hμ v.2
  let u : bosonicCore T odd N :=
    ⟨averageInto 0 (T / 2) N (x : ConfigurationHilbert 0 (T / 2) N),
      average_mem_core T odd N x⟩
  have he : coreInclusion T odd N u = coreAverage T odd N x := by
    apply Subtype.ext
    exact (coe_coreAverage T odd N x).symm
  have hu : (u.1 : ConfigurationHilbert 0 (T / 2) N) =
      (coreAverage T odd N x : ConfigurationHilbert 0 (T / 2) N) :=
    (coe_coreAverage T odd N x).symm
  refine ⟨u, Subtype.ext ?_⟩
  change (bosonicKinetic T odd N a u : ConfigurationHilbert 0 (T / 2) N) -
    (Complex.I * (μ : ℂ)) • (u.1 : ConfigurationHilbert 0 (T / 2) N) = _
  rw [coe_bosonicKinetic, he, hu]
  change shiftedKinetic T odd N a μ (coreAverage T odd N x) = _
  rw [shiftedKinetic_coreAverage, hx]
  exact average_eq_self 0 (T / 2) N v.1

/-- The nonzero imaginary shifted ranges are dense in the actual bosonic Hilbert space. -/
theorem bosonicPMap_dense_shifted_range (a μ : ℝ) (hμ : μ ≠ 0) :
    Dense {w : BosonicHilbert 0 (T / 2) N | ∃ u : (bosonicPMap T odd N a).domain,
      bosonicPMap T odd N a u - (Complex.I * (μ : ℂ)) •
        (u : BosonicHilbert 0 (T / 2) N) = w} := by
  apply (bosonicPMap_dense T odd N a).mono
  intro w hw
  exact bosonic_shifted_preimage T odd N a μ hμ ⟨w, hw⟩

/-- Essential self-adjointness of the physical product spectral kinetic on its finite fixed core. -/
theorem bosonicPMap_closure_selfAdjoint (a : ℝ) :
    IsSelfAdjoint (bosonicPMap T odd N a).closure :=
  DFT.isSelfAdjoint_closure_of_dense_range (bosonicPMap_symmetric T odd N a)
    (bosonicPMap_dense T odd N a) one_ne_zero
    (bosonicPMap_dense_shifted_range T odd N a 1 one_ne_zero)
    (bosonicPMap_dense_shifted_range T odd N a (-1) (by norm_num))

/-- The actual finite fixed domain is a graph core for that self-adjoint closure. -/
theorem bosonicPMap_closure_hasCore (a : ℝ) :
    (bosonicPMap T odd N a).closure.HasCore (bosonicCore T odd N) :=
  (bosonicPMap T odd N a).closureHasCore

end SKEFTHawking.DKMBootstrap.BECProductWallKinetic
