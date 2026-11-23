import SKEFTHawking.DKMBootstrap.BECBosonicSectors
import SKEFTHawking.DKMBootstrap.BECWallParity

/-!
# Summed microscopic density on the actual bosonic sectors

The observable is multiplication by `∑ i, f (x i)` on restricted product Lebesgue L².
Smoothness gives boundedness on the finite interval; Hölder multiplication preserves the
closed permutation fixed space. The one-particle identification uses the actual evaluation
unitary and agrees with the wall multiplier. These are fixed-sector bounded operators;
no uniform bound in particle number or higher-sector Hamiltonian is asserted here.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace SKEFTHawking.DKMBootstrap.BECMicroscopicDensity

open BECBosonicSectors

/-- The physical one-body density summed over all particles. -/
def densitySymbol {N : ℕ} (f : ℝ → ℂ) (x : Configuration N) : ℂ := ∑ i, f (x i)

theorem densitySymbol_zero (f : ℝ → ℂ) (x : Configuration 0) :
    densitySymbol f x = 0 := by simp [densitySymbol]

theorem densitySymbol_one (f : ℝ → ℂ) (x : Configuration 1) :
    densitySymbol f x = f (x 0) := by simp [densitySymbol]

theorem densitySymbol_const (N : ℕ) (b : ℂ) (x : Configuration N) :
    densitySymbol (fun _ ↦ b) x = b * (N : ℂ) := by
  simp [densitySymbol, mul_comm]

/-- Reindexing a finite sum proves pointwise symmetry, before taking L² classes. -/
theorem densitySymbol_permute {N : ℕ} (f : ℝ → ℂ)
    (σ : Equiv.Perm (Fin N)) (x : Configuration N) :
    densitySymbol f (fun i ↦ x (σ i)) = densitySymbol f x :=
  Equiv.sum_comp σ (fun i ↦ f (x i))

theorem densitySymbol_continuous {N : ℕ} (f : ℝ → ℂ) (hf : Continuous f) :
    Continuous (densitySymbol (N := N) f) := by
  unfold densitySymbol
  fun_prop

/-- The pointwise sector bound retains its explicit linear dependence on particle number. -/
theorem densitySymbol_norm_le {N : ℕ} (f : ℝ → ℂ) (l r C : ℝ)
    (hC : ∀ t ∈ Icc l r, ‖f t‖ ≤ C) (x : Configuration N)
    (hx : ∀ i, x i ∈ Ioo l r) :
    ‖densitySymbol f x‖ ≤ (N : ℝ) * C := by
  calc
    ‖densitySymbol f x‖ ≤ ∑ i : Fin N, ‖f (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum (fun i _ ↦ hC _ ⟨(hx i).1.le, (hx i).2.le⟩)
    _ = (N : ℝ) * C := by simp

/-- Compact-interval boundedness is used on the actual restricted product measure. -/
theorem densitySymbol_memLp_top (l r : ℝ) (N : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) : MemLp (densitySymbol (N := N) f) ⊤
      (configurationMeasure l r N) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuous.continuousOn
    (s := Icc l r)
  apply memLp_top_of_bound (densitySymbol_continuous f hf.continuous).aestronglyMeasurable
    ((N : ℝ) * C)
  rw [configurationMeasure_eq_restrict]
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi (fun _ ↦ measurableSet_Ioo))]
    with x hx
  exact densitySymbol_norm_le f l r C hC x (fun i ↦ hx i (mem_univ i))

/-- Actual bounded L∞ times L² multiplication on configuration volume. -/
def configurationDensity (l r : ℝ) (N : ℕ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    ConfigurationHilbert l r N →L[ℂ] ConfigurationHilbert l r N :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (configurationMeasure l r N) ⊤ 2 2
    ((densitySymbol_memLp_top l r N f hf).toLp (densitySymbol f))

theorem configurationDensity_ae (l r : ℝ) (N : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (u : ConfigurationHilbert l r N) :
    (configurationDensity l r N f hf u : Configuration N → ℂ)
      =ᵐ[configurationMeasure l r N] fun x ↦ densitySymbol f x * u x := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    ((densitySymbol_memLp_top l r N f hf).toLp (densitySymbol f)) u (r := 2)
  filter_upwards [h, (densitySymbol_memLp_top l r N f hf).coeFn_toLp] with x hx hc
  exact hx.trans (congrArg (fun b : ℂ ↦ b * u x) hc)

/-- A physical interval bound yields the expected `N C` bound on actual L² output. -/
theorem configurationDensity_norm_le (l r : ℝ) (N : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (C : ℝ) (hC : ∀ t ∈ Icc l r, ‖f t‖ ≤ C)
    (u : ConfigurationHilbert l r N) :
    ‖configurationDensity l r N f hf u‖ ≤ ((N : ℝ) * C) * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have hbox : ∀ᵐ x ∂configurationMeasure l r N, ∀ i, x i ∈ Ioo l r := by
    rw [configurationMeasure_eq_restrict]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi (fun _ ↦ measurableSet_Ioo))]
      with x hx
    exact fun i ↦ hx i (mem_univ i)
  filter_upwards [configurationDensity_ae l r N f hf u, hbox] with x hx hbox
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (densitySymbol_norm_le f l r C hC x hbox)
    (norm_nonneg _)

/-- Multiplication preserves the actual closed bosonic fixed space, using a.e. pullbacks. -/
theorem configurationDensity_mem_bosonicSubspace (l r : ℝ) (N : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (u : ConfigurationHilbert l r N)
    (hu : u ∈ bosonicSubspace l r N) :
    configurationDensity l r N f hf u ∈ bosonicSubspace l r N := by
  apply (mem_bosonicSubspace_iff_ae l r _).mpr
  intro σ
  have hp := ((reindex_measurePreserving l r σ).symm (reindex σ)).quasiMeasurePreserving.ae
    (configurationDensity_ae l r N f hf u)
  have huσ := (mem_bosonicSubspace_iff_ae l r u).mp hu σ
  filter_upwards [hp, configurationDensity_ae l r N f hf u, huσ] with x hx hy hz
  change configurationDensity l r N f hf u (fun i ↦ x (σ i)) =
    densitySymbol f (fun i ↦ x (σ i)) * u (fun i ↦ x (σ i)) at hx
  rw [hx, densitySymbol_permute, hz, hy]

/-- Restriction of the genuine configuration multiplier to the closed bosonic sector. -/
def sectorDensity (l r : ℝ) (N : ℕ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    BosonicHilbert l r N →L[ℂ] BosonicHilbert l r N :=
  (configurationDensity l r N f hf).restrict
    (fun u hu ↦ configurationDensity_mem_bosonicSubspace l r N f hf u hu)

theorem sectorDensity_coe (l r : ℝ) (N : ℕ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (u : BosonicHilbert l r N) :
    (sectorDensity l r N f hf u : ConfigurationHilbert l r N) =
      configurationDensity l r N f hf u := rfl

theorem sectorDensity_ae (l r : ℝ) (N : ℕ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (u : BosonicHilbert l r N) :
    ((sectorDensity l r N f hf u : ConfigurationHilbert l r N) : Configuration N → ℂ)
      =ᵐ[configurationMeasure l r N]
        fun x ↦ densitySymbol f x * (u : ConfigurationHilbert l r N) x :=
  configurationDensity_ae l r N f hf u

theorem sectorDensity_norm_le (l r : ℝ) (N : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (C : ℝ) (hC : ∀ t ∈ Icc l r, ‖f t‖ ≤ C)
    (u : BosonicHilbert l r N) :
    ‖sectorDensity l r N f hf u‖ ≤ ((N : ℝ) * C) * ‖u‖ :=
  configurationDensity_norm_le l r N f hf C hC u

/-- A fixed-sector operator norm bound, with no uniform-in-N assertion. -/
theorem sectorDensity_opNorm_le (l r : ℝ) (N : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t ∈ Icc l r, ‖f t‖ ≤ C) :
    ‖sectorDensity l r N f hf‖ ≤ (N : ℝ) * C :=
  (sectorDensity l r N f hf).opNorm_le_bound (mul_nonneg (Nat.cast_nonneg N) hC0)
    (sectorDensity_norm_le l r N f hf C hC)

/-- No particles means the zero observable on the entire vacuum sector. -/
theorem configurationDensity_zero (l r : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (u : ConfigurationHilbert l r 0) : configurationDensity l r 0 f hf u = 0 := by
  apply Lp.ext
  filter_upwards [configurationDensity_ae l r 0 f hf u,
    Lp.coeFn_zero ℂ 2 (configurationMeasure l r 0)] with x hx hz
  rw [densitySymbol_zero, zero_mul] at hx
  exact hx.trans hz.symm

theorem sectorDensity_zero (l r : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (u : BosonicHilbert l r 0) : sectorDensity l r 0 f hf u = 0 := by
  apply Subtype.ext
  exact configurationDensity_zero l r f hf u

/-- At fixed particle number, a constant profile gives exactly `b N` times identity. -/
theorem configurationDensity_const (l r : ℝ) (N : ℕ) (b : ℂ)
    (u : ConfigurationHilbert l r N) :
    configurationDensity l r N (fun _ ↦ b) contDiff_const u = (b * (N : ℂ)) • u := by
  apply Lp.ext
  filter_upwards [configurationDensity_ae l r N (fun _ ↦ b) contDiff_const u,
    Lp.coeFn_smul (b * (N : ℂ)) u] with x hx hs
  rw [densitySymbol_const] at hx
  exact hx.trans hs.symm

theorem sectorDensity_const (l r : ℝ) (N : ℕ) (b : ℂ) (u : BosonicHilbert l r N) :
    sectorDensity l r N (fun _ ↦ b) contDiff_const u = (b * (N : ℂ)) • u := by
  apply Subtype.ext
  exact configurationDensity_const l r N b u

/-- Actual N=1 agreement, proved by pulling interval representative identities through
the measure-preserving evaluation map. No density operator is defined by conjugation. -/
theorem sectorDensity_one_intervalUnitary (T : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (u : BECInteriorCommutator.IntervalHilbert 0 (T / 2)) :
    sectorDensity 0 (T / 2) 1 f hf (intervalBosonicUnitary 0 (T / 2) u) =
      intervalBosonicUnitary 0 (T / 2) (BECWallParity.intervalMultiplier T f hf u) := by
  apply Subtype.ext
  apply Lp.ext
  have hw := (oneParticleEvaluation_measurePreserving 0 (T / 2)).quasiMeasurePreserving.ae
    (BECWallParity.intervalMultiplier_ae T f hf u)
  filter_upwards [sectorDensity_ae 0 (T / 2) 1 f hf (intervalBosonicUnitary 0 (T / 2) u),
    intervalBosonicUnitary_ae 0 (T / 2) u,
    intervalBosonicUnitary_ae 0 (T / 2) (BECWallParity.intervalMultiplier T f hf u), hw]
    with x hm hu hv hw
  change BECWallParity.intervalMultiplier T f hf u (x 0) = f (x 0) * u (x 0) at hw
  rw [hm, densitySymbol_one, hu, hv, hw]

/-- The equivalent conjugated-operator statement on every physical interval vector. -/
theorem sectorDensity_one_conjugate (T : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (u : BECInteriorCommutator.IntervalHilbert 0 (T / 2)) :
    (intervalBosonicUnitary 0 (T / 2)).symm
      (sectorDensity 0 (T / 2) 1 f hf (intervalBosonicUnitary 0 (T / 2) u)) =
        BECWallParity.intervalMultiplier T f hf u := by
  rw [sectorDensity_one_intervalUnitary, LinearIsometryEquiv.symm_apply_apply]

/-- The inverse intertwining identity holds for every vector of the actual N=1 sector. -/
theorem sectorDensity_one_symm (T : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (u : BosonicHilbert 0 (T / 2) 1) :
    (intervalBosonicUnitary 0 (T / 2)).symm (sectorDensity 0 (T / 2) 1 f hf u) =
      BECWallParity.intervalMultiplier T f hf ((intervalBosonicUnitary 0 (T / 2)).symm u) := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    sectorDensity_one_conjugate T f hf ((intervalBosonicUnitary 0 (T / 2)).symm u)

end SKEFTHawking.DKMBootstrap.BECMicroscopicDensity
