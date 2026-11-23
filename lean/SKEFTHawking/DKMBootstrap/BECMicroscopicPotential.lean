import SKEFTHawking.DKMBootstrap.BECMicroscopicDensity

/-!
# Real microscopic potentials on actual bosonic sectors

For smooth real `V,U : ℝ → ℝ`, the symbol is the one-body sum plus one half of
all ordered distinct pairs. Evenness of `U` identifies the latter with the unordered
`i < j` sum; reindexing never assumes that a permutation preserves this order.
Compact interval bounds suffice: no global bound on either profile is needed.
The operators below are actual L∞ times L² multiplication on restricted product
Lebesgue measure, restricted to the closed bosonic carrier. These are fixed-sector
bounded symmetric potentials, with exact vacuum and one-particle controls. No
higher-particle kinetic operator, self-adjoint Hamiltonian or Fock closure is asserted.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace SKEFTHawking.DKMBootstrap.BECMicroscopicPotential

open BECBosonicSectors BECMicroscopicDensity

/-- Complex embedding of a smooth real profile, for the existing density/wall APIs. -/
def realProfile (V : ℝ → ℝ) (t : ℝ) : ℂ := V t

theorem realProfile_smooth (V : ℝ → ℝ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (realProfile V) :=
  Complex.ofRealCLM.contDiff.comp hV

/-- The actual real one-body sum. -/
def oneBodySymbol {N : ℕ} (V : ℝ → ℝ) (x : Configuration N) : ℝ := ∑ i, V (x i)

/-- Each unordered pair is counted twice before the factor one half. -/
def pairSymbol {N : ℕ} (U : ℝ → ℝ) (x : Configuration N) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else U (x i - x j)

/-- Real microscopic potential before passage to a.e. equivalence classes. -/
def potentialSymbol {N : ℕ} (V U : ℝ → ℝ) (x : Configuration N) : ℂ :=
  (oneBodySymbol V x + pairSymbol U x : ℝ)

theorem oneBodySymbol_density {N : ℕ} (V : ℝ → ℝ) (x : Configuration N) :
    (oneBodySymbol V x : ℂ) = densitySymbol (realProfile V) x := by
  simp [oneBodySymbol, densitySymbol, realProfile]

theorem oneBodySymbol_permute {N : ℕ} (V : ℝ → ℝ)
    (σ : Equiv.Perm (Fin N)) (x : Configuration N) :
    oneBodySymbol V (fun i ↦ x (σ i)) = oneBodySymbol V x :=
  Equiv.sum_comp σ (fun i ↦ V (x i))

/-- Both indices are reindexed bijectively; no ordering on pairs enters this proof. -/
theorem pairSymbol_permute {N : ℕ} (U : ℝ → ℝ)
    (σ : Equiv.Perm (Fin N)) (x : Configuration N) :
    pairSymbol U (fun i ↦ x (σ i)) = pairSymbol U x := by
  unfold pairSymbol
  congr 1
  calc
    (∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else U (x (σ i) - x (σ j))) =
        ∑ i : Fin N, ∑ j : Fin N,
          if σ i = σ j then 0 else U (x (σ i) - x (σ j)) := by simp only [σ.injective.eq_iff]
    _ = ∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else U (x i - x j) := by
      calc
        _ = ∑ i : Fin N, ∑ j : Fin N,
            if σ i = j then 0 else U (x (σ i) - x j) :=
          Finset.sum_congr rfl (fun i _ ↦ Equiv.sum_comp σ
            (fun j ↦ if σ i = j then 0 else U (x (σ i) - x j)))
        _ = _ := Equiv.sum_comp σ
          (fun i ↦ ∑ j : Fin N, if i = j then 0 else U (x i - x j))

theorem potentialSymbol_permute {N : ℕ} (V U : ℝ → ℝ)
    (σ : Equiv.Perm (Fin N)) (x : Configuration N) :
    potentialSymbol V U (fun i ↦ x (σ i)) = potentialSymbol V U x := by
  simp only [potentialSymbol, oneBodySymbol_permute, pairSymbol_permute]

theorem pairSymbol_zero (U : ℝ → ℝ) (x : Configuration 0) : pairSymbol U x = 0 := by
  simp [pairSymbol]

/-- Cancellation holds for every interaction profile, including nonzero even ones. -/
theorem pairSymbol_one (U : ℝ → ℝ) (x : Configuration 1) : pairSymbol U x = 0 := by
  simp [pairSymbol]

theorem potentialSymbol_zero (V U : ℝ → ℝ) (x : Configuration 0) :
    potentialSymbol V U x = 0 := by simp [potentialSymbol, oneBodySymbol, pairSymbol_zero]

theorem potentialSymbol_one (V U : ℝ → ℝ) (x : Configuration 1) :
    potentialSymbol V U x = realProfile V (x 0) := by
  simp [potentialSymbol, oneBodySymbol, pairSymbol_one, realProfile]

theorem potentialSymbol_real {N : ℕ} (V U : ℝ → ℝ) (x : Configuration N) :
    (starRingEnd ℂ) (potentialSymbol V U x) = potentialSymbol V U x := by
  simp [potentialSymbol]

theorem potentialSymbol_continuous {N : ℕ} (V U : ℝ → ℝ)
    (hV : Continuous V) (hU : Continuous U) : Continuous (potentialSymbol (N := N) V U) := by
  unfold potentialSymbol oneBodySymbol pairSymbol
  have hp (i j : Fin N) : Continuous
      (fun x : Configuration N ↦ if i = j then (0 : ℝ) else U (x i - x j)) := by
    split_ifs <;> fun_prop
  exact Complex.continuous_ofReal.comp
    ((continuous_finsetSum _ (fun i _ ↦ hV.comp (continuous_apply i))).add
      (continuous_const.mul (continuous_finsetSum _ (fun i _ ↦
        continuous_finsetSum _ (fun j _ ↦ hp i j)))))

/-- The exact number of distinct ordered partners per particle is `N - 1`. -/
theorem pairSymbol_norm_le {N : ℕ} (U : ℝ → ℝ) (l r C : ℝ)
    (hC : ∀ t ∈ Icc (l - r) (r - l), ‖U t‖ ≤ C) (x : Configuration N)
    (hx : ∀ i, x i ∈ Ioo l r) :
    ‖pairSymbol U x‖ ≤ (1 / 2 : ℝ) * ((N : ℝ) * (N - 1 : ℕ) * C) := by
  have hterm (i j : Fin N) :
      ‖(if i = j then 0 else U (x i - x j))‖ ≤ if i = j then 0 else C := by
    split_ifs with hij
    · simp
    · exact hC _ ⟨by linarith [(hx i).1, (hx j).2],
        by linarith [(hx i).2, (hx j).1]⟩
  have hrow (i : Fin N) : (∑ j : Fin N, if i = j then (0 : ℝ) else C) =
      (N - 1 : ℕ) * C := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [ite_true, add_zero]
    rw [Finset.sum_congr rfl (fun j hj ↦ if_neg (Ne.symm (Finset.mem_erase.mp hj).1))]
    simp
  calc
    ‖pairSymbol U x‖ = (1 / 2 : ℝ) * ‖∑ i : Fin N, ∑ j : Fin N,
        if i = j then 0 else U (x i - x j)‖ := by
      rw [pairSymbol, norm_mul]; norm_num
    _ ≤ (1 / 2 : ℝ) * ∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else C := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ ↦
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ ↦ hterm i j))))
    _ = (1 / 2 : ℝ) * ((N : ℝ) * (N - 1 : ℕ) * C) := by simp_rw [hrow]; simp [mul_assoc]

theorem potentialSymbol_norm_le {N : ℕ} (V U : ℝ → ℝ) (l r A B : ℝ)
    (hA : ∀ t ∈ Icc l r, ‖V t‖ ≤ A)
    (hB : ∀ t ∈ Icc (l - r) (r - l), ‖U t‖ ≤ B)
    (x : Configuration N) (hx : ∀ i, x i ∈ Ioo l r) :
    ‖potentialSymbol V U x‖ ≤ (N : ℝ) * A + (1 / 2 : ℝ) * ((N : ℝ) * (N - 1 : ℕ) * B) := by
  have hone : ‖oneBodySymbol V x‖ ≤ (N : ℝ) * A := by
    exact (norm_sum_le _ _).trans (by
      simpa using Finset.sum_le_sum (s := Finset.univ)
        (fun i _ ↦ hA _ ⟨(hx i).1.le, (hx i).2.le⟩))
  simpa only [potentialSymbol, Complex.norm_real] using
    (norm_add_le (oneBodySymbol V x) (pairSymbol U x)).trans
      (add_le_add hone (pairSymbol_norm_le U l r B hB x hx))

/-- Smooth real profiles are essentially bounded on the actual finite box. -/
theorem potentialSymbol_memLp_top (l r : ℝ) (N : ℕ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) :
    MemLp (potentialSymbol (N := N) V U) ⊤ (configurationMeasure l r N) := by
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hV.continuous.continuousOn
    (s := Icc l r)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hU.continuous.continuousOn
    (s := Icc (l - r) (r - l))
  apply memLp_top_of_bound
    (potentialSymbol_continuous V U hV.continuous hU.continuous).aestronglyMeasurable
    ((N : ℝ) * A + (1 / 2 : ℝ) * ((N : ℝ) * (N - 1 : ℕ) * B))
  rw [configurationMeasure_eq_restrict]
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi (fun _ ↦ measurableSet_Ioo))]
    with x hx
  exact potentialSymbol_norm_le V U l r A B hA hB x
    (fun i ↦ hx i (mem_univ i))

/-- Genuine bounded configuration multiplication, obtained by Hölder's inequality. -/
def configurationPotential (l r : ℝ) (N : ℕ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) :
    ConfigurationHilbert l r N →L[ℂ] ConfigurationHilbert l r N :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (configurationMeasure l r N) ⊤ 2 2
    ((potentialSymbol_memLp_top l r N V U hV hU).toLp (potentialSymbol V U))

theorem configurationPotential_ae (l r : ℝ) (N : ℕ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (u : ConfigurationHilbert l r N) :
    (configurationPotential l r N V U hV hU u : Configuration N → ℂ)
      =ᵐ[configurationMeasure l r N] fun x ↦ potentialSymbol V U x * u x := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    ((potentialSymbol_memLp_top l r N V U hV hU).toLp (potentialSymbol V U)) u (r := 2)
  filter_upwards [h, (potentialSymbol_memLp_top l r N V U hV hU).coeFn_toLp]
    with x hx hc
  exact hx.trans (congrArg (fun b : ℂ ↦ b * u x) hc)

/-- Pointwise permutation symmetry descends to the actual closed L² fixed space. -/
theorem configurationPotential_mem_bosonicSubspace (l r : ℝ) (N : ℕ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (u : ConfigurationHilbert l r N)
    (hu : u ∈ bosonicSubspace l r N) :
    configurationPotential l r N V U hV hU u ∈ bosonicSubspace l r N := by
  apply (mem_bosonicSubspace_iff_ae l r _).mpr
  intro σ
  have hp := ((reindex_measurePreserving l r σ).symm (reindex σ)).quasiMeasurePreserving.ae
    (configurationPotential_ae l r N V U hV hU u)
  have huσ := (mem_bosonicSubspace_iff_ae l r u).mp hu σ
  filter_upwards [hp, configurationPotential_ae l r N V U hV hU u, huσ] with x hx hy hz
  change configurationPotential l r N V U hV hU u (fun i ↦ x (σ i)) =
    potentialSymbol V U (fun i ↦ x (σ i)) * u (fun i ↦ x (σ i)) at hx
  rw [hx, potentialSymbol_permute, hz, hy]

/-- Restriction of actual multiplication, with full domain on the closed bosonic carrier.
Evenness is only needed for the unordered-pair interpretation, not this construction. -/
def sectorPotential (l r : ℝ) (N : ℕ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) :
    BosonicHilbert l r N →L[ℂ] BosonicHilbert l r N :=
  (configurationPotential l r N V U hV hU).restrict
    (fun u hu ↦ configurationPotential_mem_bosonicSubspace l r N V U hV hU u hu)

theorem sectorPotential_coe (l r : ℝ) (N : ℕ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (u : BosonicHilbert l r N) :
    (sectorPotential l r N V U hV hU u : ConfigurationHilbert l r N) =
      configurationPotential l r N V U hV hU u := rfl

theorem sectorPotential_ae (l r : ℝ) (N : ℕ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (u : BosonicHilbert l r N) :
    ((sectorPotential l r N V U hV hU u : ConfigurationHilbert l r N) : Configuration N → ℂ)
      =ᵐ[configurationMeasure l r N]
        fun x ↦ potentialSymbol V U x * (u : ConfigurationHilbert l r N) x :=
  configurationPotential_ae l r N V U hV hU u

theorem configurationPotential_norm_le (l r : ℝ) (N : ℕ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (A B : ℝ)
    (hA : ∀ t ∈ Icc l r, ‖V t‖ ≤ A)
    (hB : ∀ t ∈ Icc (l - r) (r - l), ‖U t‖ ≤ B)
    (u : ConfigurationHilbert l r N) :
    ‖configurationPotential l r N V U hV hU u‖ ≤
      ((N : ℝ) * A + (1 / 2 : ℝ) * ((N : ℝ) * (N - 1 : ℕ) * B)) * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have hbox : ∀ᵐ x ∂configurationMeasure l r N, ∀ i, x i ∈ Ioo l r := by
    rw [configurationMeasure_eq_restrict]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi (fun _ ↦ measurableSet_Ioo))]
      with x hx
    exact fun i ↦ hx i (mem_univ i)
  filter_upwards [configurationPotential_ae l r N V U hV hU u, hbox] with x hx hbox
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (potentialSymbol_norm_le V U l r A B hA hB x hbox)
    (norm_nonneg _)

/-- Finite sector bound; the explicit quadratic dependence makes no uniform Fock claim. -/
theorem sectorPotential_opNorm_le (l r : ℝ) (N : ℕ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (A B : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ t ∈ Icc l r, ‖V t‖ ≤ A)
    (hB : ∀ t ∈ Icc (l - r) (r - l), ‖U t‖ ≤ B) :
    ‖sectorPotential l r N V U hV hU‖ ≤
      (N : ℝ) * A + (1 / 2 : ℝ) * ((N : ℝ) * (N - 1 : ℕ) * B) := by
  apply (sectorPotential l r N V U hV hU).opNorm_le_bound
    (by positivity)
  intro u
  exact configurationPotential_norm_le l r N V U hV hU A B hA hB u

/-- Reality of the actual multiplier proves symmetry in product Lebesgue L². -/
theorem configurationPotential_symmetric (l r : ℝ) (N : ℕ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (u v : ConfigurationHilbert l r N) :
    inner ℂ (configurationPotential l r N V U hV hU u) v =
      inner ℂ u (configurationPotential l r N V U hV hU v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [configurationPotential_ae l r N V U hV hU u,
    configurationPotential_ae l r N V U hV hU v] with x hu hv
  rw [hu, hv]
  simp only [RCLike.inner_apply, map_mul, potentialSymbol_real]
  ring

theorem sectorPotential_symmetric (l r : ℝ) (N : ℕ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) :
    (sectorPotential l r N V U hV hU).toLinearMap.IsSymmetric := by
  intro u v
  exact configurationPotential_symmetric l r N V U hV hU u v

/-- The vacuum potential is zero on every vector of the actual vacuum carrier. -/
theorem sectorPotential_vacuum (l r : ℝ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (u : BosonicHilbert l r 0) :
    sectorPotential l r 0 V U hV hU u = 0 := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [sectorPotential_ae l r 0 V U hV hU u,
    Lp.coeFn_zero ℂ 2 (configurationMeasure l r 0)] with x hx hz
  rw [potentialSymbol_zero, zero_mul] at hx
  exact hx.trans hz.symm

/-- Actual N=1 equality with the already constructed microscopic density multiplier. -/
theorem sectorPotential_one_density (l r : ℝ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (u : BosonicHilbert l r 1) :
    sectorPotential l r 1 V U hV hU u =
      sectorDensity l r 1 (realProfile V) (realProfile_smooth V hV) u := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [sectorPotential_ae l r 1 V U hV hU u,
    sectorDensity_ae l r 1 (realProfile V) (realProfile_smooth V hV) u] with x hp hd
  rw [hp, potentialSymbol_one, hd, densitySymbol_one]

/-- Exact intertwining with the accepted real wall potential; U remains arbitrary. -/
theorem sectorPotential_one_intervalUnitary (T : ℝ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U)
    (u : BECInteriorCommutator.IntervalHilbert 0 (T / 2)) :
    sectorPotential 0 (T / 2) 1 V U hV hU (intervalBosonicUnitary 0 (T / 2) u) =
      intervalBosonicUnitary 0 (T / 2)
        (BECWallParity.intervalMultiplier T (realProfile V) (realProfile_smooth V hV) u) := by
  rw [sectorPotential_one_density]
  exact sectorDensity_one_intervalUnitary T (realProfile V) (realProfile_smooth V hV) u

theorem sectorPotential_one_conjugate (T : ℝ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U)
    (u : BECInteriorCommutator.IntervalHilbert 0 (T / 2)) :
    (intervalBosonicUnitary 0 (T / 2)).symm
      (sectorPotential 0 (T / 2) 1 V U hV hU (intervalBosonicUnitary 0 (T / 2) u)) =
        BECWallParity.intervalMultiplier T (realProfile V) (realProfile_smooth V hV) u := by
  rw [sectorPotential_one_intervalUnitary, LinearIsometryEquiv.symm_apply_apply]

/-- The N=1 symmetry is also the accepted wall symmetry under the actual unitary. -/
theorem sectorPotential_one_wall_symmetric (T : ℝ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U)
    (u v : BECInteriorCommutator.IntervalHilbert 0 (T / 2)) :
    inner ℂ (sectorPotential 0 (T / 2) 1 V U hV hU
      (intervalBosonicUnitary 0 (T / 2) u)) (intervalBosonicUnitary 0 (T / 2) v) =
    inner ℂ (intervalBosonicUnitary 0 (T / 2) u)
      (sectorPotential 0 (T / 2) 1 V U hV hU (intervalBosonicUnitary 0 (T / 2) v)) := by
  rw [sectorPotential_one_intervalUnitary, sectorPotential_one_intervalUnitary,
    (intervalBosonicUnitary 0 (T / 2)).inner_map_map,
    (intervalBosonicUnitary 0 (T / 2)).inner_map_map]
  exact BECWallParity.intervalMultiplier_symmetric T (realProfile V) (realProfile_smooth V hV)
    (fun x ↦ by simp [realProfile]) u v

/-- Conventional unordered sum, used only after proving its equality to the ordered formula. -/
def unorderedPairSymbol {N : ℕ} (U : ℝ → ℝ) (x : Configuration N) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, if i < j then U (x i - x j) else 0

/-- Evenness identifies the two orientations. A permutation need not preserve `<`. -/
theorem pairSymbol_eq_unordered {N : ℕ} (U : ℝ → ℝ) (hEven : Function.Even U)
    (x : Configuration N) : pairSymbol U x = unorderedPairSymbol U x := by
  have hsplit :
      (∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else U (x i - x j)) =
        (∑ i : Fin N, ∑ j : Fin N, if i < j then U (x i - x j) else 0) +
        (∑ i : Fin N, ∑ j : Fin N, if j < i then U (x i - x j) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt_of_ge h.le]
    · simp [h]
    · simp [h, h.ne', not_lt_of_ge h.le]
  have hswap :
      (∑ i : Fin N, ∑ j : Fin N, if j < i then U (x i - x j) else 0) =
        ∑ i : Fin N, ∑ j : Fin N, if i < j then U (x i - x j) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · rw [← neg_sub (x i) (x j), hEven]
    · rfl
  rw [pairSymbol, hsplit, hswap, unorderedPairSymbol]
  ring

/-- Unordered-pair invariance is a consequence of equality with the ordered sum. -/
theorem unorderedPairSymbol_permute {N : ℕ} (U : ℝ → ℝ) (hEven : Function.Even U)
    (σ : Equiv.Perm (Fin N)) (x : Configuration N) :
    unorderedPairSymbol U (fun i ↦ x (σ i)) = unorderedPairSymbol U x := by
  rw [← pairSymbol_eq_unordered U hEven, ← pairSymbol_eq_unordered U hEven,
    pairSymbol_permute]

/-- At two particles a nonzero even interaction survives with precisely one copy. -/
theorem pairSymbol_two (U : ℝ → ℝ) (hEven : Function.Even U) (x : Configuration 2) :
    pairSymbol U x = U (x 0 - x 1) := by
  rw [pairSymbol_eq_unordered U hEven]
  simp [unorderedPairSymbol, Fin.sum_univ_two]

/-- A positive constant pair-energy shift, with zero force, is an exact two-particle control. -/
theorem nonzero_constant_interaction (g : ℝ) (hg : 0 < g) :
    ContDiff ℝ ∞ (fun _ : ℝ ↦ g) ∧ Function.Even (fun _ : ℝ ↦ g) ∧
      (∀ t : ℝ, 0 < (fun _ : ℝ ↦ g) t) ∧
      (∀ x : Configuration 2, pairSymbol (fun _ ↦ g) x = g) := by
  refine ⟨contDiff_const, fun _ ↦ rfl, fun _ ↦ hg, fun x ↦ ?_⟩
  exact pairSymbol_two (fun _ ↦ g) (fun _ ↦ rfl) x

/-- With U=0, the actual total operator is exactly the accepted summed density for real V. -/
theorem sectorPotential_no_pair (l r : ℝ) (N : ℕ) (V : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (u : BosonicHilbert l r N) :
    sectorPotential l r N V (fun _ ↦ 0) hV contDiff_const u =
      sectorDensity l r N (realProfile V) (realProfile_smooth V hV) u := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [sectorPotential_ae l r N V (fun _ ↦ 0) hV contDiff_const u,
    sectorDensity_ae l r N (realProfile V) (realProfile_smooth V hV) u] with x hp hd
  rw [hp, hd]
  congr 1
  simpa [potentialSymbol, pairSymbol] using oneBodySymbol_density V x

/-- At N=2 a constant nonzero pair interaction is actual scalar multiplication on L². -/
theorem sectorPotential_two_constant_pair (l r g : ℝ) (u : BosonicHilbert l r 2) :
    sectorPotential l r 2 (fun _ ↦ 0) (fun _ ↦ g) contDiff_const contDiff_const u =
      (g : ℂ) • u := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [sectorPotential_ae l r 2 (fun _ ↦ 0) (fun _ ↦ g)
    contDiff_const contDiff_const u, Lp.coeFn_smul (g : ℂ)
      (u : ConfigurationHilbert l r 2)] with x hp hs
  change _ = ((g : ℂ) • (u : ConfigurationHilbert l r 2)) x
  rw [hp, hs]
  simp [potentialSymbol, oneBodySymbol, pairSymbol_two (fun _ ↦ g) (fun _ ↦ rfl)]

/-- Smooth even Gaussian pair profile. For `g > 0` it is bounded, positive and nonconstant. -/
def gaussianInteraction (g : ℝ) (t : ℝ) : ℝ := g * Real.exp (-(t ^ 2))

theorem gaussianInteraction_smooth (g : ℝ) : ContDiff ℝ ∞ (gaussianInteraction g) := by
  unfold gaussianInteraction
  fun_prop

theorem gaussianInteraction_even (g : ℝ) : Function.Even (gaussianInteraction g) := by
  intro t
  simp [gaussianInteraction]

theorem gaussianInteraction_pos (g : ℝ) (hg : 0 < g) (t : ℝ) :
    0 < gaussianInteraction g t := mul_pos hg (Real.exp_pos _)

theorem gaussianInteraction_bound (g : ℝ) (hg : 0 ≤ g) (t : ℝ) :
    ‖gaussianInteraction g t‖ ≤ g := by
  unfold gaussianInteraction
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg (Real.exp_pos _).le)]
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg t))
  exact (mul_le_mul_of_nonneg_left he hg).trans_eq (mul_one g)

/-- This admissible U is genuinely nonconstant and does not vanish at contact. -/
theorem gaussianInteraction_nonconstant (g : ℝ) (hg : 0 < g) :
    gaussianInteraction g 1 < gaussianInteraction g 0 ∧ gaussianInteraction g 0 = g := by
  have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  simp only [gaussianInteraction, one_pow, zero_pow (by decide : 2 ≠ 0), neg_zero,
    Real.exp_zero, mul_one]
  exact ⟨by nlinarith, trivial⟩

/-- Positive interval volume gives a genuinely nonzero bosonic L² vector, at every N. -/
theorem exists_nonzero_sector (l r : ℝ) (hlr : l < r) (N : ℕ) :
    ∃ u : BosonicHilbert l r N, u ≠ 0 := by
  letI : IsFiniteMeasure (configurationMeasure l r N) := by
    unfold configurationMeasure
    infer_instance
  let h := memLp_const (μ := configurationMeasure l r N) (p := 2) (1 : ℂ)
  let ψ : ConfigurationHilbert l r N := h.toLp (fun _ ↦ (1 : ℂ))
  have hψ : (ψ : Configuration N → ℂ) =ᵐ[configurationMeasure l r N] fun _ ↦ 1 :=
    h.coeFn_toLp
  have hbos : ψ ∈ bosonicSubspace l r N := by
    apply (mem_bosonicSubspace_iff_ae l r ψ).mpr
    intro σ
    have hp := ((reindex_measurePreserving l r σ).symm (reindex σ)).quasiMeasurePreserving.ae
      hψ
    filter_upwards [hp, hψ] with x hx hy
    exact hx.trans hy.symm
  refine ⟨⟨ψ, hbos⟩, ?_⟩
  intro hz
  have hz' : ψ = 0 := congrArg Subtype.val hz
  have hae : (fun _ : Configuration N ↦ (1 : ℂ)) =ᵐ[configurationMeasure l r N] 0 :=
    hψ.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hz')
  have hmass : configurationMeasure l r N univ ≠ 0 := by
    rw [configurationMeasure_univ]
    exact pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hlr)))
  apply hmass
  simpa using (ae_iff.mp hae)

/-- A positive constant pair-energy shift gives a nonzero operator on the two-particle sector. -/
theorem sectorPotential_two_constant_pair_ne_zero (l r g : ℝ) (hlr : l < r) (hg : 0 < g) :
    sectorPotential l r 2 (fun _ ↦ 0) (fun _ ↦ g) contDiff_const contDiff_const ≠ 0 := by
  obtain ⟨u, hu⟩ := exists_nonzero_sector l r hlr 2
  intro hz
  have hs : (g : ℂ) • u = 0 := by
    rw [← sectorPotential_two_constant_pair, hz]
    rfl
  rcases smul_eq_zero.mp hs with h | h
  · exact (Complex.ofReal_ne_zero.mpr hg.ne') h
  · exact hu h

end SKEFTHawking.DKMBootstrap.BECMicroscopicPotential
