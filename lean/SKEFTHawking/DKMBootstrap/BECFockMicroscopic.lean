import SKEFTHawking.DKMBootstrap.BECFockOperators
import SKEFTHawking.DKMBootstrap.BECMicroscopicPotential

/-!
# Microscopic observables and interactions on the actual Fock graph

Density is the actual configuration multiplier in every sector, given full sector domain;
its Fock domain still requires square-summable actual outputs. The interacting family adds
the actual real one-body and even pair potential to a supplied kinetic family. Its N=1 wall
identification is conditional only on the free N=1 kinetic identification. No concrete
higher wall kinetic or self-adjointness of the full direct sum is asserted.

Constant density is particle number times the constant, commutes on the actual four-membership
common domain, and is globally unbounded when the constant and physical interval are nonzero.
The supported unit tests use the accepted nonzero constant configuration sectors.
-/

noncomputable section

namespace SKEFTHawking.DKMBootstrap.BECFockMicroscopic

open BECBosonicSectors BECFockOperators BECMicroscopicDensity BECMicroscopicPotential
open scoped ContDiff

variable {l r : ℝ}

/-- Actual microscopic multiplication, with full domain in each individual sector. -/
def densityFamily (l r : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) : SectorFamily l r :=
  fun n ↦ (sectorDensity l r n f hf).toLinearMap.toPMap ⊤

@[simp] theorem densityFamily_domain (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    (densityFamily l r f hf n).domain = ⊤ := rfl

theorem densityFamily_apply (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (u : (densityFamily l r f hf n).domain) :
    densityFamily l r f hf n u = sectorDensity l r n f hf u := rfl

/-- The genuine diagonal observable; its graph uses the actual density output sequence. -/
def fockDensity (l r : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    FockHilbert l r →ₗ.[ℂ] FockHilbert l r :=
  diagonal (densityFamily l r f hf)

theorem mem_fockDensity_domain (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (ψ : FockHilbert l r) :
    ψ ∈ (fockDensity l r f hf).domain ↔
      Memℓp (fun n ↦ sectorDensity l r n f hf (ψ n)) 2 :=
  mem_diagonalDomain_iff _ ψ (fun _ ↦ Submodule.mem_top)

theorem fockDensity_apply (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (ψ : (fockDensity l r f hf).domain) (n : ℕ) :
    fockDensity l r f hf ψ n = sectorDensity l r n f hf ((ψ : FockHilbert l r) n) := rfl

/-- Full-domain equality includes the transferred domain, using the independently proved
intertwining of actual multiplication and the onto one-particle unitary. -/
theorem densityFamily_one (T : ℝ) [Fact (0 < T)] (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) :
    densityFamily 0 (T / 2) f hf 1 = densitySector T f hf := by
  apply LinearPMap.ext
  · simp [densityFamily, densitySector, BECWallParity.potentialPMap,
      LinearPMap.unitaryConj]
  · intro x hx hy
    change sectorDensity 0 (T / 2) 1 f hf x =
      intervalBosonicUnitary 0 (T / 2)
        (BECWallParity.intervalMultiplier T f hf ((intervalBosonicUnitary 0 (T / 2)).symm x))
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      sectorDensity_one_intervalUnitary T f hf ((intervalBosonicUnitary 0 (T / 2)).symm x)

/-- The actual bounded microscopic potential as a full-domain sector partial map. -/
def potentialFamily (l r : ℝ) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) : SectorFamily l r :=
  fun n ↦ (sectorPotential l r n V U hV hU).toLinearMap.toPMap ⊤

/-- Supplied free kinetics plus actual microscopic multiplication in every sector.
Evenness fixes the unordered-pair interpretation of this same potential. -/
def interactingFamily (K : SectorFamily l r) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (_hEven : Function.Even U) :
    SectorFamily l r := fun n ↦ K n + potentialFamily l r V U hV hU n

theorem interactingFamily_domain (K : SectorFamily l r) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U) (n : ℕ) :
    (interactingFamily K V U hV hU hEven n).domain = (K n).domain := by
  simp [interactingFamily, potentialFamily, LinearPMap.add_domain]

theorem potentialFamily_one (T : ℝ) [Fact (0 < T)] (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) :
    potentialFamily 0 (T / 2) V U hV hU 1 =
      densitySector T (realProfile V) (realProfile_smooth V hV) := by
  rw [← densityFamily_one]
  apply LinearPMap.ext
  · rfl
  intro x hx hy
  exact sectorPotential_one_density 0 (T / 2) V U hV hU x

/-- Bounded real sector multiplication is symmetric as a partial map. -/
theorem potentialFamily_symmetric (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (n : ℕ) :
    DFT.IsSymmetricPMap (potentialFamily l r V U hV hU n) := by
  intro u v
  exact sectorPotential_symmetric l r n V U hV hU u v

theorem potentialFamily_relBounded (K : SectorFamily l r) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (n : ℕ) :
    DFT.IsRelBounded (K n) (potentialFamily l r V U hV hU n) 0
      ‖sectorPotential l r n V U hV hU‖ := by
  refine ⟨le_top, fun u ↦ ?_⟩
  simpa [potentialFamily] using (sectorPotential l r n V U hV hU).le_opNorm u

/-- Kato–Rellich at each finite sector, conditional on the supplied free self-adjointness.
This proves no assertion about a self-adjoint direct sum. -/
theorem interactingFamily_selfAdjoint (K : SectorFamily l r) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U)
    (n : ℕ) (hK : IsSelfAdjoint (K n)) :
    IsSelfAdjoint (interactingFamily K V U hV hU hEven n) :=
  DFT.katoRellich (a := 0) (b := ‖sectorPotential l r n V U hV hU‖) hK
    (potentialFamily_symmetric V U hV hU n) (by norm_num) (by norm_num)
    (norm_nonneg (sectorPotential l r n V U hV hU)) (potentialFamily_relBounded K V U hV hU n)

/-- Constant profiles are precisely b times the particle number on each full sector. -/
theorem densityFamily_const (b : ℂ) (n : ℕ)
    (u : (densityFamily l r (fun _ ↦ b) contDiff_const n).domain) :
    densityFamily l r (fun _ ↦ b) contDiff_const n u = (b * (n : ℂ)) • (u : Sector l r n) :=
  sectorDensity_const l r n b u

/-- Coordinatewise particle-number action on the actual square-summable graph domain. -/
theorem fockDensity_const_apply (b : ℂ)
    (ψ : (fockDensity l r (fun _ ↦ b) contDiff_const).domain) (n : ℕ) :
    fockDensity l r (fun _ ↦ b) contDiff_const ψ n =
      (b * (n : ℂ)) • (ψ : FockHilbert l r) n :=
  sectorDensity_const l r n b _

/-- Conservation on the genuine common domain. No assertion that all of D(K) belongs
to this common domain is made: number-weighted outputs must themselves lie in ℓ². -/
theorem constant_bracket_zero (K : SectorFamily l r) (b : ℂ) (ψ : FockHilbert l r)
    (h : CommonDomain (diagonal K) (fockDensity l r (fun _ ↦ b) contDiff_const) ψ) :
    bracketValue (diagonal K) (fockDensity l r (fun _ ↦ b) contDiff_const) ψ h = 0 := by
  apply lp.ext
  funext n
  have hi := coordinate_mem K ⟨ψ, h.in_A⟩ n
  have ho := coordinate_mem K
    ⟨fockDensity l r (fun _ ↦ b) contDiff_const ⟨ψ, h.in_B⟩, h.after_B⟩ n
  have he : (⟨fockDensity l r (fun _ ↦ b) contDiff_const ⟨ψ, h.in_B⟩ n, ho⟩ :
      (K n).domain) = (b * (n : ℂ)) • (⟨ψ n, hi⟩ : (K n).domain) :=
    Subtype.ext (fockDensity_const_apply b ⟨ψ, h.in_B⟩ n)
  change K n ⟨_, ho⟩ -
    fockDensity l r (fun _ ↦ b) contDiff_const ⟨diagonal K ⟨ψ, h.in_A⟩, h.after_A⟩ n = 0
  rw [he, (K n).map_smul, fockDensity_const_apply]
  exact sub_self _

/-- Normalize the actual nonzero constant sector furnished by positive product volume. -/
theorem exists_unit_sector (hlr : l < r) (n : ℕ) :
    ∃ u : Sector l r n, ‖u‖ = 1 := by
  obtain ⟨u, hu⟩ := exists_nonzero_sector l r hlr n
  refine ⟨(‖u‖⁻¹ : ℂ) • u, ?_⟩
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg u), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]

/-- Actual supported unit tests have response norm |b| N, including the vacuum. -/
theorem exists_supported_unit_density (hlr : l < r) (b : ℂ) (n : ℕ) :
    ∃ u : Sector l r n, ‖u‖ = 1 ∧
      ∃ h : sectorInjection n u ∈ (fockDensity l r (fun _ ↦ b) contDiff_const).domain,
        ‖sectorInjection n u‖ = 1 ∧
        ‖fockDensity l r (fun _ ↦ b) contDiff_const ⟨sectorInjection n u, h⟩‖ =
          ‖b‖ * (n : ℝ) := by
  obtain ⟨u, hu⟩ := exists_unit_sector hlr n
  have hm := injection_mem_diagonal (densityFamily l r (fun _ ↦ b) contDiff_const)
    n ⟨u, Submodule.mem_top⟩
  refine ⟨u, hu, hm, (sectorInjection_norm n u).trans hu, ?_⟩
  change ‖diagonal (densityFamily l r (fun _ ↦ b) contDiff_const)
    ⟨sectorInjection n u, hm⟩‖ = _
  rw [diagonal_injection _ n ⟨u, Submodule.mem_top⟩ hm, sectorInjection_norm,
    densityFamily_const, norm_smul, norm_mul, Complex.norm_natCast, hu, mul_one]

/-- Nonzero constant density has no global bounded extension on a positive physical interval.
The witnesses are actual normalized single-sector vectors in the density graph domain. -/
theorem constant_density_unbounded (hlr : l < r) (b : ℂ) (hb : b ≠ 0) :
    ¬ ∃ A : FockHilbert l r →L[ℂ] FockHilbert l r,
      ∀ ψ : (fockDensity l r (fun _ ↦ b) contDiff_const).domain,
        A (ψ : FockHilbert l r) = fockDensity l r (fun _ ↦ b) contDiff_const ψ := by
  rintro ⟨A, hA⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (‖A‖ / ‖b‖)
  obtain ⟨u, _, hm, hu, hout⟩ := exists_supported_unit_density hlr b n
  have hbound := A.le_opNorm (sectorInjection n u)
  rw [hA ⟨_, hm⟩, hout, hu, mul_one] at hbound
  have hpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hlt : ‖A‖ < ‖b‖ * (n : ℝ) := by
    have hh := (div_lt_iff₀ hpos).mp hn
    simpa only [mul_comm] using hh
  exact (not_lt_of_ge hbound) hlt

section Wall

open BECWallParity BECInteriorCommutator

variable (T : ℝ) [Fact (0 < T)]

/-- Only the free one-particle wall identification is assumed. The pair potential vanishes
by the actual N=1 multiplier theorem, rather than by replacing other sectors. -/
theorem interactingFamily_one (K : SectorFamily 0 (T / 2))
    (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U)
    (hK : K 1 = LinearPMap.unitaryConj (intervalBosonicUnitary 0 (T / 2))
      (halfKinetic T (BECPeriodicCommutator.scale T a) σ hσ)) :
    interactingFamily K V U hV hU hEven 1 =
      wallSector T a σ hσ (realProfile V) (realProfile_smooth V hV) := by
  unfold interactingFamily
  rw [hK, potentialFamily_one]
  apply LinearPMap.ext
  · simp [wallSector, wallHamiltonian, densitySector, LinearPMap.unitaryConj,
      LinearPMap.add_domain, potentialPMap]
  · intro x hx hy
    simp only [wallSector, wallHamiltonian, densitySector, LinearPMap.unitaryConj_apply,
      LinearPMap.add_apply, map_add]

/-- Actual compact tests have all four memberships for the interacting microscopic graph,
conditional only on the supplied free N=1 wall identification. -/
theorem compact_interacting_commonDomain (K : SectorFamily 0 (T / 2))
    (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U)
    (hK : K 1 = LinearPMap.unitaryConj (intervalBosonicUnitary 0 (T / 2))
      (halfKinetic T (BECPeriodicCommutator.scale T a) σ hσ))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (ψ : Domain 0 (T / 2)) :
    CommonDomain (diagonal (interactingFamily K V U hV hU hEven))
      (fockDensity 0 (T / 2) f hf)
      (sectorInjection 1 (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ))) :=
  compact_fock_commonDomain T a σ hσ (realProfile V) f (realProfile_smooth V hV) hf
    _ _ (interactingFamily_one T K a σ hσ V U hV hU hEven hK) (densityFamily_one T f hf) ψ

/-- Exact differential bracket on the same genuine microscopic common-domain tests. -/
theorem compact_interacting_bracket (K : SectorFamily 0 (T / 2))
    (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U)
    (hK : K 1 = LinearPMap.unitaryConj (intervalBosonicUnitary 0 (T / 2))
      (halfKinetic T (BECPeriodicCommutator.scale T a) σ hσ))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (ψ : Domain 0 (T / 2))
    (h : CommonDomain (diagonal (interactingFamily K V U hV hU hEven))
      (fockDensity 0 (T / 2) f hf)
      (sectorInjection 1 (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ)))) :
    bracketValue (diagonal (interactingFamily K V U hV hU hEven))
      (fockDensity 0 (T / 2) f hf)
      (sectorInjection 1 (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ))) h =
        sectorInjection 1 (intervalBosonicUnitary 0 (T / 2)
          (toIntervalL2 (BECInteriorCommutator.commutator a (realProfile V) f
            (realProfile_smooth V hV) hf ψ))) :=
  compact_fock_bracket T a σ hσ (realProfile V) f (realProfile_smooth V hV) hf
    _ _ (interactingFamily_one T K a σ hσ V U hV hU hEven hK) (densityFamily_one T f hf) ψ h

/-- Conditional microscopic obstruction: actual sector potentials and summed density,
with only the free one-particle kinetic identification left as a premise. -/
theorem no_bounded_interacting_bracket (K : SectorFamily 0 (T / 2))
    {a : ℝ} (ha : 0 < a) (σ : ℂ) (hσ : σ ^ 2 = 1) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U)
    (hK : K 1 = LinearPMap.unitaryConj (intervalBosonicUnitary 0 (T / 2))
      (halfKinetic T (BECPeriodicCommutator.scale T a) σ hσ))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hn : ∃ x ∈ Set.Ioo 0 (T / 2), ∃ y ∈ Set.Ioo 0 (T / 2), f x ≠ f y) :
    ¬ ∃ A : FockHilbert 0 (T / 2) →L[ℂ] FockHilbert 0 (T / 2),
      ∀ ψ (h : CommonDomain (diagonal (interactingFamily K V U hV hU hEven))
        (fockDensity 0 (T / 2) f hf) ψ),
        A ψ = bracketValue (diagonal (interactingFamily K V U hV hU hEven))
          (fockDensity 0 (T / 2) f hf) ψ h :=
  no_bounded_fock_wall_extension T ha σ hσ (realProfile V) f
    (realProfile_smooth V hV) hf hn _ _
    (interactingFamily_one T K a σ hσ V U hV hU hEven hK) (densityFamily_one T f hf)

/-- Nonzero response is witnessed on actual compact common-domain vectors under the same
free kinetic premise; the obstruction is not a consequence of an empty domain. -/
theorem exists_interacting_nonzero_bracket (K : SectorFamily 0 (T / 2))
    {a : ℝ} (ha : 0 < a) (σ : ℂ) (hσ : σ ^ 2 = 1) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U)
    (hK : K 1 = LinearPMap.unitaryConj (intervalBosonicUnitary 0 (T / 2))
      (halfKinetic T (BECPeriodicCommutator.scale T a) σ hσ))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hn : ∃ x ∈ Set.Ioo 0 (T / 2), ∃ y ∈ Set.Ioo 0 (T / 2), f x ≠ f y) :
    ∃ ψ : Domain 0 (T / 2),
      ∃ h : CommonDomain (diagonal (interactingFamily K V U hV hU hEven))
        (fockDensity 0 (T / 2) f hf)
        (sectorInjection 1 (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ))),
        bracketValue (diagonal (interactingFamily K V U hV hU hEven))
          (fockDensity 0 (T / 2) f hf)
          (sectorInjection 1 (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ))) h ≠ 0 :=
  exists_compact_fock_nonzero_bracket T ha σ hσ (realProfile V) f
    (realProfile_smooth V hV) hf hn _ _
    (interactingFamily_one T K a σ hσ V U hV hU hEven hK) (densityFamily_one T f hf)

/-- An actual smooth real compact profile supplies nonconstant density and the obstruction
for both wall parities, for every free family satisfying its N=1 identification. -/
theorem exists_real_compact_interacting_obstruction {a : ℝ} (ha : 0 < a)
    (V U : ℝ → ℝ) (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U)
    (hEven : Function.Even U) :
    ∃ f : ℝ → ℝ, ∃ hf : ContDiff ℝ ∞ f,
      HasCompactSupport f ∧ tsupport f ⊆ Set.Ioo 0 (T / 2) ∧
      (∃ x ∈ Set.Ioo 0 (T / 2), ∃ y ∈ Set.Ioo 0 (T / 2),
        realProfile f x ≠ realProfile f y) ∧
      ∀ (σ : ℂ) (hσ : σ ^ 2 = 1) (K : SectorFamily 0 (T / 2)),
        K 1 = LinearPMap.unitaryConj (intervalBosonicUnitary 0 (T / 2))
          (halfKinetic T (BECPeriodicCommutator.scale T a) σ hσ) →
        ¬ ∃ A : FockHilbert 0 (T / 2) →L[ℂ] FockHilbert 0 (T / 2),
          ∀ ψ (h : CommonDomain (diagonal (interactingFamily K V U hV hU hEven))
            (fockDensity 0 (T / 2) (realProfile f) (realProfile_smooth f hf)) ψ),
            A ψ = bracketValue (diagonal (interactingFamily K V U hV hU hEven))
              (fockDensity 0 (T / 2) (realProfile f) (realProfile_smooth f hf)) ψ h := by
  obtain ⟨f, hf, hc, hs, x, hx, hd⟩ :=
    exists_compact_real_profile (show 0 < T / 2 by linarith [(Fact.out : 0 < T)])
  have hn : ∃ z ∈ Set.Ioo 0 (T / 2), ∃ y ∈ Set.Ioo 0 (T / 2),
      realProfile f z ≠ realProfile f y := by
    by_contra hn
    push Not at hn
    have he : Set.EqOn (realProfile f) (fun _ ↦ realProfile f x) (Set.Ioo 0 (T / 2)) :=
      fun y hy ↦ hn y hy x hx
    have hz := he.deriv isOpen_Ioo hx
    simp only [deriv_const] at hz
    change deriv (fun y ↦ (f y : ℂ)) x = 0 at hz
    rw [hd] at hz
    exact one_ne_zero hz
  exact ⟨f, hf, hc, hs, hn, fun σ hσ K hK ↦
    no_bounded_interacting_bracket T K ha σ hσ V U hV hU hEven hK
      (realProfile f) (realProfile_smooth f hf) hn⟩

end Wall

end SKEFTHawking.DKMBootstrap.BECFockMicroscopic
