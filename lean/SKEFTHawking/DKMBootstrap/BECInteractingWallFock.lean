import SKEFTHawking.DKMBootstrap.BECFockMicroscopic
import SKEFTHawking.DKMBootstrap.BECProductWallKinetic

/-!
# Interacting physical wall Hamiltonian on bosonic Fock space

The direct sum is the existing square-summable graph, with no uniform sector bound.
The vacuum kinetic is zero, the one-particle kinetic is the accepted transported
half-interval operator, and higher sectors use the closure of the actual symmetric
finite product-mode operator. The real smooth microscopic potential is added on
each unchanged kinetic domain. Compact common-domain tests below are supported
in sector one. No maximal Sobolev characterization, higher compact graph membership,
state moment hierarchy or physical device identification is asserted.
-/

noncomputable section

namespace SKEFTHawking.DKMBootstrap.BECFockOperators

variable {l r : ℝ} (K : SectorFamily l r)

/-- Finite linear combinations of actual supported sector-domain tests. -/
def supportedDomain : Submodule ℂ (FockHilbert l r) :=
  Submodule.span ℂ {ψ | ∃ n, ∃ v : (K n).domain,
    ψ = sectorInjection n (v : Sector l r n)}

theorem supportedDomain_le : supportedDomain K ≤ (diagonal K).domain := by
  apply Submodule.span_le.mpr
  rintro ψ ⟨n, v, rfl⟩
  exact injection_mem_diagonal K n v

/-- Supported domain tests are dense whenever the individual domains are dense. -/
theorem supportedDomain_dense (hK : ∀ n, Dense ((K n).domain : Set (Sector l r n))) :
    Dense (supportedDomain K : Set (FockHilbert l r)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro ψ hψ
  apply lp.ext
  funext n
  apply (hK n).eq_zero_of_inner_right ℂ
  intro v hv
  have hi := (Submodule.mem_orthogonal _ _).mp hψ (sectorInjection n v)
    (Submodule.subset_span ⟨n, ⟨v, hv⟩, rfl⟩)
  exact (sector_inner n v ψ).symm.trans hi

theorem diagonal_dense (hK : ∀ n, Dense ((K n).domain : Set (Sector l r n))) :
    Dense ((diagonal K).domain : Set (FockHilbert l r)) :=
  (supportedDomain_dense K hK).mono (supportedDomain_le K)

/-- Exact graph equivalence: the reverse direction uses the actual output vector's ℓ²
membership, rather than an assumed bound on the sector operators. -/
theorem mem_diagonal_graph_iff (ψ φ : FockHilbert l r) :
    (ψ, φ) ∈ (diagonal K).graph ↔ ∀ n, (ψ n, φ n) ∈ (K n).graph := by
  constructor
  · rintro h n
    obtain ⟨v, hv, ho⟩ := (LinearPMap.mem_graph_iff _).mp h
    dsimp only at hv ho
    subst ψ
    exact (LinearPMap.mem_graph_iff _).mpr
      ⟨⟨(v : FockHilbert l r) n, coordinate_mem K v n⟩, rfl,
        (diagonal_apply K v n _).symm.trans (congrArg (fun w ↦ w n) ho)⟩
  · intro h
    have hm : ∀ n, ψ n ∈ (K n).domain := fun n ↦ by
      obtain ⟨v, hv, _⟩ := (LinearPMap.mem_graph_iff _).mp (h n)
      change (v : Sector l r n) = ψ n at hv
      rw [← hv]
      exact v.property
    have he : ∀ n, K n ⟨ψ n, hm n⟩ = φ n := fun n ↦ by
      obtain ⟨v, hv, ho⟩ := (LinearPMap.mem_graph_iff _).mp (h n)
      have hv' : (⟨ψ n, hm n⟩ : (K n).domain) = v := Subtype.ext hv.symm
      rw [hv']
      exact ho
    have hs : ψ ∈ (diagonal K).domain := by
      refine ⟨hm, ?_⟩
      convert lp.memℓp φ using 1
      exact funext he
    refine (LinearPMap.mem_graph_iff _).mpr ⟨⟨ψ, hs⟩, rfl, ?_⟩
    apply lp.ext
    exact funext he

/-- The actual graph adjoint is precisely the coordinatewise graph adjoint. Supported
tests give the forward implication; the reverse implication uses the ℓ² inner-product sum. -/
theorem mem_diagonal_graph_adjoint_iff (ψ φ : FockHilbert l r) :
    (ψ, φ) ∈ (diagonal K).graph.adjoint ↔ ∀ n, (ψ n, φ n) ∈ (K n).graph.adjoint := by
  constructor
  · intro h n
    apply (Submodule.mem_adjoint_iff _ _).mpr
    intro a b hab
    obtain ⟨v, hv, ho⟩ := (LinearPMap.mem_graph_iff _).mp hab
    dsimp only at hv ho
    subst a
    subst b
    have hi := (Submodule.mem_adjoint_iff _ _).mp h
      (sectorInjection n (v : Sector l r n)) (sectorInjection n (K n v))
      ((LinearPMap.mem_graph_iff _).mpr
        ⟨⟨_, injection_mem_diagonal K n v⟩, rfl, diagonal_injection K n v _⟩)
    simp only [sector_inner] at hi
    exact hi
  · intro h
    apply (Submodule.mem_adjoint_iff _ _).mpr
    intro a b hab
    have hc := (mem_diagonal_graph_iff K a b).mp hab
    have he : ∀ n, inner ℂ (b n) (ψ n) = inner ℂ (a n) (φ n) := fun n ↦
      sub_eq_zero.mp ((Submodule.mem_adjoint_iff _ _).mp (h n) _ _ (hc n))
    rw [sub_eq_zero, lp.inner_eq_tsum, lp.inner_eq_tsum]
    exact tsum_congr he

/-- A self-adjoint family gives a self-adjoint operator on the actual diagonal graph. -/
theorem diagonal_selfAdjoint (hK : ∀ n, IsSelfAdjoint (K n)) :
    IsSelfAdjoint (diagonal K) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (diagonal_dense K
    (fun n ↦ (hK n).dense_domain))]
  ext ⟨ψ, φ⟩
  rw [mem_diagonal_graph_adjoint_iff, mem_diagonal_graph_iff]
  apply forall_congr'
  intro n
  rw [← LinearPMap.adjoint_graph_eq_graph_adjoint (hK n).dense_domain,
    (LinearPMap.isSelfAdjoint_def.mp (hK n))]

end SKEFTHawking.DKMBootstrap.BECFockOperators

namespace SKEFTHawking.DKMBootstrap.BECInteractingWallFock

open BECBosonicSectors BECFockOperators BECFockMicroscopic BECWallParity
  BECPhysicalWallModes BECMicroscopicPotential BECInteriorCommutator
open scoped ContDiff

variable (T : ℝ) [Fact (0 < T)]

/-- Actual physical kinetic family: vacuum zero, exact half-wall conjugate at one,
and the symmetric finite-product kinetic closure in every higher sector. -/
def kineticFamily (a : ℝ) (odd : Bool) : SectorFamily 0 (T / 2)
  | 0 => 0
  | 1 => LinearPMap.unitaryConj (intervalBosonicUnitary 0 (T / 2))
      (halfKinetic T (BECPeriodicCommutator.scale T a) (sign odd) (sign_sq odd))
  | n + 2 => (BECProductWallKinetic.bosonicPMap T odd (n + 2) a).closure

@[simp] theorem kineticFamily_zero (a : ℝ) (odd : Bool) :
    kineticFamily T a odd 0 = 0 := rfl

@[simp] theorem kineticFamily_one (a : ℝ) (odd : Bool) :
    kineticFamily T a odd 1 =
      LinearPMap.unitaryConj (intervalBosonicUnitary 0 (T / 2))
        (halfKinetic T (BECPeriodicCommutator.scale T a) (sign odd) (sign_sq odd)) := rfl

/-- All higher sectors use the accepted physical product-mode closure. -/
theorem kineticFamily_higher (a : ℝ) (odd : Bool) (n : ℕ) (hn : 2 ≤ n) :
    kineticFamily T a odd n = (BECProductWallKinetic.bosonicPMap T odd n a).closure := by
  cases n with
  | zero => omega
  | succ n => cases n with
    | zero => omega
    | succ n => rfl

omit [Fact (0 < T)] in
/-- Self-adjointness of the full-domain zero vacuum operator. -/
theorem vacuum_selfAdjoint :
    IsSelfAdjoint (0 : Sector 0 (T / 2) 0 →ₗ.[ℂ] Sector 0 (T / 2) 0) := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hz : (0 : Sector 0 (T / 2) 0 →ₗ.[ℂ] Sector 0 (T / 2) 0) =
      (0 : Sector 0 (T / 2) 0 →L[ℂ] Sector 0 (T / 2) 0).toPMap ⊤ := rfl
  rw [hz]
  simpa using ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense
    (0 : Sector 0 (T / 2) 0 →L[ℂ] Sector 0 (T / 2) 0)
    (p := ⊤) (by simp)

theorem kineticFamily_selfAdjoint (a : ℝ) (odd : Bool) (n : ℕ) :
    IsSelfAdjoint (kineticFamily T a odd n) := by
  cases n with
  | zero => exact vacuum_selfAdjoint T
  | succ n => cases n with
    | zero =>
      exact LinearPMap.unitaryConj_isSelfAdjoint _
        (halfKinetic_selfAdjoint T _ _ _)
    | succ n => exact BECProductWallKinetic.bosonicPMap_closure_selfAdjoint T odd (n + 2) a

/-- Real smooth one-body and even pair interactions on the constructed kinetic domains. -/
def hamiltonianFamily (a : ℝ) (odd : Bool) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U) :
    SectorFamily 0 (T / 2) :=
  interactingFamily (kineticFamily T a odd) V U hV hU hEven

theorem hamiltonianFamily_selfAdjoint (a : ℝ) (odd : Bool) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U) (n : ℕ) :
    IsSelfAdjoint (hamiltonianFamily T a odd V U hV hU hEven n) :=
  interactingFamily_selfAdjoint _ V U hV hU hEven n (kineticFamily_selfAdjoint T a odd n)

/-- The real microscopic potential is zero in vacuum, so the entire vacuum operator is zero. -/
theorem hamiltonianFamily_zero (a : ℝ) (odd : Bool) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U) :
    hamiltonianFamily T a odd V U hV hU hEven 0 = 0 := by
  have hp : potentialFamily 0 (T / 2) V U hV hU 0 = 0 := by
    apply LinearPMap.ext
    · rfl
    · intro x hx hy
      exact sectorPotential_vacuum 0 (T / 2) V U hV hU x
  simp only [hamiltonianFamily, interactingFamily, kineticFamily_zero, zero_add, hp]

/-- Bounded sector interactions leave the actual kinetic domains unchanged. -/
theorem hamiltonianFamily_domain (a : ℝ) (odd : Bool) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U) (n : ℕ) :
    (hamiltonianFamily T a odd V U hV hU hEven n).domain =
      (kineticFamily T a odd n).domain :=
  interactingFamily_domain _ V U hV hU hEven n

/-- The actual interacting Fock Hamiltonian, including the exact ℓ² output condition. -/
def hamiltonian (a : ℝ) (odd : Bool) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U) :
    FockHilbert 0 (T / 2) →ₗ.[ℂ] FockHilbert 0 (T / 2) :=
  diagonal (hamiltonianFamily T a odd V U hV hU hEven)

theorem hamiltonian_selfAdjoint (a : ℝ) (odd : Bool) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U) :
    IsSelfAdjoint (hamiltonian T a odd V U hV hU hEven) :=
  diagonal_selfAdjoint _ (hamiltonianFamily_selfAdjoint T a odd V U hV hU hEven)

/-- Exact interacting Fock graph domain, including square summability of the actual
interacting outputs. No number cutoff or uniform operator bound is inserted. -/
theorem mem_hamiltonian_domain (a : ℝ) (odd : Bool) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U)
    (ψ : FockHilbert 0 (T / 2)) :
    ψ ∈ (hamiltonian T a odd V U hV hU hEven).domain ↔
      ∃ h : ∀ n, ψ n ∈ (hamiltonianFamily T a odd V U hV hU hEven n).domain,
        Memℓp (fun n ↦ hamiltonianFamily T a odd V U hV hU hEven n ⟨ψ n, h n⟩) 2 :=
  Iff.rfl

/-- Supported physical interacting domain tests span a dense subspace of Fock space. -/
theorem hamiltonian_supported_dense (a : ℝ) (odd : Bool) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U) :
    Dense (supportedDomain (hamiltonianFamily T a odd V U hV hU hEven) :
      Set (FockHilbert 0 (T / 2))) :=
  supportedDomain_dense _ (fun n ↦
    (hamiltonianFamily_selfAdjoint T a odd V U hV hU hEven n).dense_domain)

/-- Exact first-sector wall identity; the pair term vanishes intrinsically at N=1. -/
theorem hamiltonianFamily_one (a : ℝ) (odd : Bool) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U) :
    hamiltonianFamily T a odd V U hV hU hEven 1 =
      wallSector T a (sign odd) (sign_sq odd) (realProfile V) (realProfile_smooth V hV) :=
  interactingFamily_one T _ a _ _ V U hV hU hEven (kineticFamily_one T a odd)

/-- Every compact interior one-particle test has all four genuine common-domain
memberships for this constructed Hamiltonian and the actual microscopic density. -/
theorem compact_commonDomain (a : ℝ) (odd : Bool) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (ψ : Domain 0 (T / 2)) :
    CommonDomain (hamiltonian T a odd V U hV hU hEven)
      (fockDensity 0 (T / 2) f hf)
      (sectorInjection 1 (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ))) :=
  compact_interacting_commonDomain T _ a _ _ V U hV hU hEven
    (kineticFamily_one T a odd) f hf ψ

/-- The exact differential wall bracket on the supported compact tests of the fully
constructed interacting Hamiltonian. The pair term is absent only because N=1. -/
theorem compact_bracket (a : ℝ) (odd : Bool) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (ψ : Domain 0 (T / 2))
    (h : CommonDomain (hamiltonian T a odd V U hV hU hEven)
      (fockDensity 0 (T / 2) f hf)
      (sectorInjection 1 (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ)))) :
    bracketValue (hamiltonian T a odd V U hV hU hEven) (fockDensity 0 (T / 2) f hf)
      (sectorInjection 1 (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ))) h =
        sectorInjection 1 (intervalBosonicUnitary 0 (T / 2)
          (toIntervalL2 (BECInteriorCommutator.commutator a (realProfile V) f
            (realProfile_smooth V hV) hf ψ))) :=
  compact_interacting_bracket T _ a _ _ V U hV hU hEven
    (kineticFamily_one T a odd) f hf ψ h

/-- A nonconstant density admits no bounded bracket extension for either physical wall
choice, with no remaining supplied kinetic-family premise. -/
theorem no_bounded_density_bracket {a : ℝ} (ha : 0 < a) (odd : Bool) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hn : ∃ x ∈ Set.Ioo 0 (T / 2), ∃ y ∈ Set.Ioo 0 (T / 2), f x ≠ f y) :
    ¬ ∃ A : FockHilbert 0 (T / 2) →L[ℂ] FockHilbert 0 (T / 2),
      ∀ ψ (h : CommonDomain (hamiltonian T a odd V U hV hU hEven)
        (fockDensity 0 (T / 2) f hf) ψ),
        A ψ = bracketValue (hamiltonian T a odd V U hV hU hEven)
          (fockDensity 0 (T / 2) f hf) ψ h :=
  no_bounded_interacting_bracket T _ ha _ _ V U hV hU hEven
    (kineticFamily_one T a odd) f hf hn

/-- The common domain has a compact supported witness with genuinely nonzero response. -/
theorem exists_nonzero_density_bracket {a : ℝ} (ha : 0 < a) (odd : Bool) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hn : ∃ x ∈ Set.Ioo 0 (T / 2), ∃ y ∈ Set.Ioo 0 (T / 2), f x ≠ f y) :
    ∃ ψ : Domain 0 (T / 2),
      ∃ h : CommonDomain (hamiltonian T a odd V U hV hU hEven)
        (fockDensity 0 (T / 2) f hf)
        (sectorInjection 1 (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ))),
        bracketValue (hamiltonian T a odd V U hV hU hEven)
          (fockDensity 0 (T / 2) f hf)
          (sectorInjection 1 (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ))) h ≠ 0 :=
  exists_interacting_nonzero_bracket T _ ha _ _ V U hV hU hEven
    (kineticFamily_one T a odd) f hf hn

/-- One actual real compact nonconstant density profile obstructs bounded extension for
both the Neumann (`false`) and Dirichlet (`true`) constructed Hamiltonians. -/
theorem exists_real_compact_obstruction {a : ℝ} (ha : 0 < a) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U) :
    ∃ f : ℝ → ℝ, ∃ hf : ContDiff ℝ ∞ f,
      HasCompactSupport f ∧ tsupport f ⊆ Set.Ioo 0 (T / 2) ∧
      (∃ x ∈ Set.Ioo 0 (T / 2), ∃ y ∈ Set.Ioo 0 (T / 2),
        realProfile f x ≠ realProfile f y) ∧
      ∀ odd : Bool,
        ¬ ∃ A : FockHilbert 0 (T / 2) →L[ℂ] FockHilbert 0 (T / 2),
          ∀ ψ (h : CommonDomain (hamiltonian T a odd V U hV hU hEven)
            (fockDensity 0 (T / 2) (realProfile f) (realProfile_smooth f hf)) ψ),
            A ψ = bracketValue (hamiltonian T a odd V U hV hU hEven)
              (fockDensity 0 (T / 2) (realProfile f) (realProfile_smooth f hf)) ψ h := by
  obtain ⟨f, hf, hc, hs, hn, h⟩ :=
    exists_real_compact_interacting_obstruction T ha V U hV hU hEven
  exact ⟨f, hf, hc, hs, hn, fun odd ↦ h (sign odd) (sign_sq odd)
    (kineticFamily T a odd) (kineticFamily_one T a odd)⟩

/-- Constant density is conserved on the actual common domain of this Hamiltonian. -/
theorem constant_density_bracket_zero (a : ℝ) (odd : Bool) (V U : ℝ → ℝ)
    (hV : ContDiff ℝ ∞ V) (hU : ContDiff ℝ ∞ U) (hEven : Function.Even U)
    (b : ℂ) (ψ : FockHilbert 0 (T / 2))
    (h : CommonDomain (hamiltonian T a odd V U hV hU hEven)
      (fockDensity 0 (T / 2) (fun _ ↦ b) contDiff_const) ψ) :
    bracketValue (hamiltonian T a odd V U hV hU hEven)
      (fockDensity 0 (T / 2) (fun _ ↦ b) contDiff_const) ψ h = 0 :=
  constant_bracket_zero _ b ψ h

/-- The conserved nonzero constant observable itself remains globally unbounded:
its actual action is bN, as opposed to its vanishing first bracket. -/
theorem constant_density_no_bounded_extension (b : ℂ) (hb : b ≠ 0) :
    ¬ ∃ A : FockHilbert 0 (T / 2) →L[ℂ] FockHilbert 0 (T / 2),
      ∀ ψ : (fockDensity 0 (T / 2) (fun _ ↦ b) contDiff_const).domain,
        A (ψ : FockHilbert 0 (T / 2)) =
          fockDensity 0 (T / 2) (fun _ ↦ b) contDiff_const ψ :=
  constant_density_unbounded (show 0 < T / 2 by linarith [(Fact.out : 0 < T)]) b hb

end SKEFTHawking.DKMBootstrap.BECInteractingWallFock
