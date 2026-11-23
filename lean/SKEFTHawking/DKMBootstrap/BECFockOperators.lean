import SKEFTHawking.DKMBootstrap.BECBosonicSectors
import SKEFTHawking.DKMBootstrap.BECWallParity
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.LinearPMap

/-!
# Bosonic Hilbert direct sum and diagonal graph operators

The carrier is the genuine dependent ℓ² sum of the product-volume bosonic sectors.
The diagonal domain requires every coordinate to lie in its sector operator domain
and the actual outputs to be square summable. No uniform sector bound is assumed.
The one-particle specialization uses the actual interval-to-bosonic unitary and
the existing wall-plus-potential operator. Its compact tests have all four genuine
common-domain memberships and the differential bracket action after injection.
Higher-particle physical Hamiltonians and Fock classifications remain separate.
-/

noncomputable section

namespace SKEFTHawking.DKMBootstrap.BECFockOperators

open BECBosonicSectors

/-- Physical bosonic sectors, with the unnormalized product Lebesgue measure. -/
abbrev Sector (l r : ℝ) (n : ℕ) : Type := ↥(BosonicHilbert l r n)

/-- The uncapped Hilbert direct sum, including the vacuum sector. -/
abbrev FockHilbert (l r : ℝ) : Type := ↥(lp (Sector l r) 2)

example (l r : ℝ) : CompleteSpace (FockHilbert l r) := inferInstance
example (l r : ℝ) : InnerProductSpace ℂ (FockHilbert l r) := inferInstance

variable {l r : ℝ}

/-- The actual supported sector injection. -/
def sectorInjection (n : ℕ) : Sector l r n →L[ℂ] FockHilbert l r :=
  lp.singleContinuousLinearMap ℂ (Sector l r) 2 n

/-- Coordinate projection on the actual ℓ² carrier. -/
def sectorProjection (n : ℕ) : FockHilbert l r →L[ℂ] Sector l r n :=
  lp.evalCLM ℂ (Sector l r) 2 n

@[simp] theorem sectorInjection_apply_self (n : ℕ) (v : Sector l r n) :
    sectorInjection n v n = v := lp.single_apply_self 2 n v

@[simp] theorem sectorInjection_apply_ne (n : ℕ) (v : Sector l r n)
    {m : ℕ} (h : m ≠ n) : sectorInjection n v m = 0 :=
  lp.single_apply_ne 2 n v h

@[simp] theorem sectorProjection_injection (n : ℕ) (v : Sector l r n) :
    sectorProjection n (sectorInjection n v) = v := sectorInjection_apply_self n v

theorem sectorInjection_norm (n : ℕ) (v : Sector l r n) :
    ‖sectorInjection n v‖ = ‖v‖ := lp.norm_single (by norm_num) n v

/-- The injection is a complex linear isometry, not just an algebraic inclusion. -/
def sectorIsometry (n : ℕ) : Sector l r n →ₗᵢ[ℂ] FockHilbert l r where
  toLinearMap := (sectorInjection n).toLinearMap
  norm_map' := sectorInjection_norm n

theorem sectorProjection_norm_le (n : ℕ) (ψ : FockHilbert l r) :
    ‖sectorProjection n ψ‖ ≤ ‖ψ‖ := lp.norm_apply_le_norm (by norm_num) ψ n

theorem sector_inner (n : ℕ) (v : Sector l r n) (ψ : FockHilbert l r) :
    inner ℂ (sectorInjection n v) ψ = inner ℂ v (sectorProjection n ψ) :=
  lp.inner_single_left n v ψ

/-- A family of genuine, possibly unbounded, sector partial linear operators. -/
abbrev SectorFamily (l r : ℝ) := ∀ n, Sector l r n →ₗ.[ℂ] Sector l r n

variable (K : SectorFamily l r)

/-- An algebraic completion witnesses that prescribing the first sector is consistent.
The other operators are zero; this is not a higher-particle physical Hamiltonian. -/
def firstSectorCompletion (A : Sector l r 1 →ₗ.[ℂ] Sector l r 1) : SectorFamily l r :=
  fun n ↦ if h : n = 1 then h.symm ▸ A else 0

@[simp] theorem firstSectorCompletion_one (A : Sector l r 1 →ₗ.[ℂ] Sector l r 1) :
    firstSectorCompletion A 1 = A := by simp [firstSectorCompletion]

/-- Exact graph domain: coordinate membership and square summability of actual outputs. -/
def diagonalDomain : Submodule ℂ (FockHilbert l r) where
  carrier := {ψ | ∃ h : ∀ n, ψ n ∈ (K n).domain,
    Memℓp (fun n ↦ K n ⟨ψ n, h n⟩) 2}
  zero_mem' := by
    refine ⟨fun n ↦ (K n).domain.zero_mem, ?_⟩
    convert (zero_memℓp : Memℓp (0 : ∀ n, Sector l r n) 2) using 1
    funext n
    exact (K n).map_zero
  add_mem' := by
    rintro ψ φ ⟨hψ, oψ⟩ ⟨hφ, oφ⟩
    refine ⟨fun n ↦ (K n).domain.add_mem (hψ n) (hφ n), ?_⟩
    convert oψ.add oφ using 1
    funext n
    exact (K n).map_add ⟨ψ n, hψ n⟩ ⟨φ n, hφ n⟩
  smul_mem' := by
    rintro c ψ ⟨hψ, oψ⟩
    refine ⟨fun n ↦ (K n).domain.smul_mem c (hψ n), ?_⟩
    convert oψ.const_smul c using 1
    funext n
    exact (K n).map_smul c ⟨ψ n, hψ n⟩

/-- Explicit coordinate-domain evidence extracted from graph membership. -/
theorem coordinate_mem (ψ : (diagonalDomain K)) (n : ℕ) :
    (ψ : FockHilbert l r) n ∈ (K n).domain := ψ.property.choose n

/-- Genuine diagonal partial operator, with its value packaged in ℓ². -/
def diagonal : FockHilbert l r →ₗ.[ℂ] FockHilbert l r where
  domain := diagonalDomain K
  toFun :=
    { toFun := fun ψ ↦ ⟨fun n ↦ K n ⟨(ψ : FockHilbert l r) n,
        coordinate_mem K ψ n⟩, ψ.property.choose_spec⟩
      map_add' := by
        intro ψ φ
        apply lp.ext
        funext n
        exact (K n).map_add ⟨(ψ : FockHilbert l r) n, coordinate_mem K ψ n⟩
          ⟨(φ : FockHilbert l r) n, coordinate_mem K φ n⟩
      map_smul' := by
        intro c ψ
        apply lp.ext
        funext n
        exact (K n).map_smul c ⟨(ψ : FockHilbert l r) n, coordinate_mem K ψ n⟩ }

/-- Coordinate action on any legitimate graph-domain vector. -/
theorem diagonal_apply (ψ : (diagonal K).domain) (n : ℕ)
    (h : (ψ : FockHilbert l r) n ∈ (K n).domain) :
    diagonal K ψ n = K n ⟨(ψ : FockHilbert l r) n, h⟩ := rfl

/-- Any explicit coordinate witnesses give the same exact graph membership test. -/
theorem mem_diagonalDomain_iff (ψ : FockHilbert l r)
    (h : ∀ n, ψ n ∈ (K n).domain) :
    ψ ∈ diagonalDomain K ↔ Memℓp (fun n ↦ K n ⟨ψ n, h n⟩) 2 :=
  ⟨fun hψ ↦ hψ.choose_spec, fun ho ↦ ⟨h, ho⟩⟩

/-- Every supported domain vector has legitimate coordinate memberships. -/
theorem injection_coordinate_mem (n : ℕ) (v : (K n).domain) (m : ℕ) :
    sectorInjection n (v : Sector l r n) m ∈ (K m).domain := by
  by_cases h : m = n
  · subst m
    simpa only [sectorInjection_apply_self] using v.property
  · rw [sectorInjection_apply_ne n _ h]
    exact (K m).domain.zero_mem

/-- The actual output vector on a supported input is supported at the same sector. -/
theorem injection_output (n : ℕ) (v : (K n).domain)
    (h : ∀ m, sectorInjection n (v : Sector l r n) m ∈ (K m).domain) :
    (fun m ↦ K m ⟨sectorInjection n (v : Sector l r n) m, h m⟩) =
      (sectorInjection n (K n v) : FockHilbert l r) := by
  funext m
  by_cases hmn : m = n
  · subst m
    simp only [sectorInjection_apply_self]
  · have hz : (⟨sectorInjection n (v : Sector l r n) m, h m⟩ : (K m).domain) = 0 :=
      Subtype.ext (sectorInjection_apply_ne n _ hmn)
    calc
      _ = 0 := by rw [hz]; exact (K m).map_zero
      _ = _ := (sectorInjection_apply_ne n _ hmn).symm

/-- No output bound is needed: a single actual output is automatically in ℓ². -/
theorem injection_mem_diagonal (n : ℕ) (v : (K n).domain) :
    sectorInjection n (v : Sector l r n) ∈ (diagonal K).domain := by
  refine ⟨injection_coordinate_mem K n v, ?_⟩
  rw [injection_output K n v]
  exact lp.memℓp _

/-- The diagonal acts by the supplied sector partial operator on supported inputs. -/
theorem diagonal_injection (n : ℕ) (v : (K n).domain)
    (h : sectorInjection n (v : Sector l r n) ∈ (diagonal K).domain) :
    diagonal K ⟨sectorInjection n (v : Sector l r n), h⟩ =
      sectorInjection n (K n v) := by
  apply lp.ext
  exact injection_output K n v _

/-- Sector injection neither loses nor invents sector domain membership. -/
theorem injection_mem_diagonal_iff (n : ℕ) (v : Sector l r n) :
    sectorInjection n v ∈ (diagonal K).domain ↔ v ∈ (K n).domain := by
  constructor
  · intro h
    simpa only [sectorInjection_apply_self] using coordinate_mem K ⟨_, h⟩ n
  · intro h
    exact injection_mem_diagonal K n ⟨v, h⟩

section Bracket

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- The natural common composition domain. Each image membership is individual;
there is no assumption that either operator preserves the other's entire domain. -/
structure CommonDomain (A B : E →ₗ.[ℂ] E) (v : E) : Prop where
  in_A : v ∈ A.domain
  in_B : v ∈ B.domain
  after_B : B ⟨v, in_B⟩ ∈ A.domain
  after_A : A ⟨v, in_A⟩ ∈ B.domain

/-- The bracket on its genuine common domain, without `LinearPMap.comp`. -/
def bracketValue (A B : E →ₗ.[ℂ] E) (v : E) (h : CommonDomain A B v) : E :=
  A ⟨B ⟨v, h.in_B⟩, h.after_B⟩ - B ⟨A ⟨v, h.in_A⟩, h.after_A⟩

end Bracket

section UnitaryBracket

variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

/-- Forward unitary transport supplies the individual common-domain witnesses. -/
theorem unitary_commonDomain (U : H ≃ₗᵢ[ℂ] H') (A B : H →ₗ.[ℂ] H)
    (v : H) (h : CommonDomain A B v) :
    CommonDomain (LinearPMap.unitaryConj U A) (LinearPMap.unitaryConj U B) (U v) where
  in_A := LinearPMap.map_mem_unitaryConj_domain U A ⟨v, h.in_A⟩
  in_B := LinearPMap.map_mem_unitaryConj_domain U B ⟨v, h.in_B⟩
  after_B := by
    rw [LinearPMap.unitaryConj_apply_map U B ⟨v, h.in_B⟩]
    exact LinearPMap.map_mem_unitaryConj_domain U A ⟨_, h.after_B⟩
  after_A := by
    rw [LinearPMap.unitaryConj_apply_map U A ⟨v, h.in_A⟩]
    exact LinearPMap.map_mem_unitaryConj_domain U B ⟨_, h.after_A⟩

/-- Actual unitary transport of the bracket, retaining explicit legitimate memberships. -/
theorem unitary_bracket (U : H ≃ₗᵢ[ℂ] H') (A B : H →ₗ.[ℂ] H)
    (v : H) (h : CommonDomain A B v)
    (hU : CommonDomain (LinearPMap.unitaryConj U A) (LinearPMap.unitaryConj U B) (U v)) :
    bracketValue (LinearPMap.unitaryConj U A) (LinearPMap.unitaryConj U B) (U v) hU =
      U (bracketValue A B v h) := by
  have hB : LinearPMap.unitaryConj U B ⟨U v, hU.in_B⟩ = U (B ⟨v, h.in_B⟩) :=
    LinearPMap.unitaryConj_apply_map U B ⟨v, h.in_B⟩
  have hA : LinearPMap.unitaryConj U A ⟨U v, hU.in_A⟩ = U (A ⟨v, h.in_A⟩) :=
    LinearPMap.unitaryConj_apply_map U A ⟨v, h.in_A⟩
  have hAB : LinearPMap.unitaryConj U A
      ⟨LinearPMap.unitaryConj U B ⟨U v, hU.in_B⟩, hU.after_B⟩ =
      U (A ⟨B ⟨v, h.in_B⟩, h.after_B⟩) := by
    have he : (⟨LinearPMap.unitaryConj U B ⟨U v, hU.in_B⟩, hU.after_B⟩ :
        (LinearPMap.unitaryConj U A).domain) =
        ⟨U (B ⟨v, h.in_B⟩),
          LinearPMap.map_mem_unitaryConj_domain U A ⟨_, h.after_B⟩⟩ := Subtype.ext hB
    rw [he]
    exact LinearPMap.unitaryConj_apply_map U A ⟨_, h.after_B⟩
  have hBA : LinearPMap.unitaryConj U B
      ⟨LinearPMap.unitaryConj U A ⟨U v, hU.in_A⟩, hU.after_A⟩ =
      U (B ⟨A ⟨v, h.in_A⟩, h.after_A⟩) := by
    have he : (⟨LinearPMap.unitaryConj U A ⟨U v, hU.in_A⟩, hU.after_A⟩ :
        (LinearPMap.unitaryConj U B).domain) =
        ⟨U (A ⟨v, h.in_A⟩),
          LinearPMap.map_mem_unitaryConj_domain U B ⟨_, h.after_A⟩⟩ := Subtype.ext hA
    rw [he]
    exact LinearPMap.unitaryConj_apply_map U B ⟨_, h.after_A⟩
  unfold bracketValue
  rw [hAB, hBA, map_sub]

end UnitaryBracket

variable (M : SectorFamily l r)

/-- Every legitimate sector common-domain vector supplies all four ambient memberships. -/
theorem injection_commonDomain (n : ℕ) (v : Sector l r n)
    (h : CommonDomain (K n) (M n) v) :
    CommonDomain (diagonal K) (diagonal M) (sectorInjection n v) where
  in_A := injection_mem_diagonal K n ⟨v, h.in_A⟩
  in_B := injection_mem_diagonal M n ⟨v, h.in_B⟩
  after_B := by
    rw [diagonal_injection M n ⟨v, h.in_B⟩]
    exact injection_mem_diagonal K n ⟨_, h.after_B⟩
  after_A := by
    rw [diagonal_injection K n ⟨v, h.in_A⟩]
    exact injection_mem_diagonal M n ⟨_, h.after_A⟩

/-- Actual common-domain bracket action on an embedded sector vector. -/
theorem injection_bracket (n : ℕ) (v : Sector l r n)
    (h : CommonDomain (K n) (M n) v)
    (hF : CommonDomain (diagonal K) (diagonal M) (sectorInjection n v)) :
    bracketValue (diagonal K) (diagonal M) (sectorInjection n v) hF =
      sectorInjection n (bracketValue (K n) (M n) v h) := by
  have hAB : diagonal K ⟨diagonal M ⟨sectorInjection n v, hF.in_B⟩, hF.after_B⟩ =
      sectorInjection n (K n ⟨M n ⟨v, h.in_B⟩, h.after_B⟩) := by
    have he : (⟨diagonal M ⟨sectorInjection n v, hF.in_B⟩, hF.after_B⟩ :
        (diagonal K).domain) =
        ⟨sectorInjection n (M n ⟨v, h.in_B⟩),
          injection_mem_diagonal K n ⟨_, h.after_B⟩⟩ :=
      Subtype.ext (diagonal_injection M n ⟨v, h.in_B⟩ hF.in_B)
    rw [he]
    exact diagonal_injection K n ⟨_, h.after_B⟩ _
  have hBA : diagonal M ⟨diagonal K ⟨sectorInjection n v, hF.in_A⟩, hF.after_A⟩ =
      sectorInjection n (M n ⟨K n ⟨v, h.in_A⟩, h.after_A⟩) := by
    have he : (⟨diagonal K ⟨sectorInjection n v, hF.in_A⟩, hF.after_A⟩ :
        (diagonal M).domain) =
        ⟨sectorInjection n (K n ⟨v, h.in_A⟩),
          injection_mem_diagonal M n ⟨_, h.after_A⟩⟩ :=
      Subtype.ext (diagonal_injection K n ⟨v, h.in_A⟩ hF.in_A)
    rw [he]
    exact diagonal_injection M n ⟨_, h.after_A⟩ _
  unfold bracketValue
  rw [hAB, hBA, map_sub]

/-- Compression is an actual bounded sector operator. -/
def sectorCompression (n : ℕ) (A : FockHilbert l r →L[ℂ] FockHilbert l r) :
    Sector l r n →L[ℂ] Sector l r n :=
  (sectorProjection n).comp (A.comp (sectorInjection n))

/-- Ambient bounded agreement forces bounded agreement on every sector common-domain vector. -/
theorem bracket_compression (n : ℕ) (A : FockHilbert l r →L[ℂ] FockHilbert l r)
    (hA : ∀ ψ (h : CommonDomain (diagonal K) (diagonal M) ψ),
      A ψ = bracketValue (diagonal K) (diagonal M) ψ h)
    (v : Sector l r n) (h : CommonDomain (K n) (M n) v) :
    sectorCompression n A v = bracketValue (K n) (M n) v h := by
  have he := hA (sectorInjection n v) (injection_commonDomain K M n v h)
  rw [injection_bracket K M n v h] at he
  have hp := congrArg (sectorProjection n) he
  simpa only [sectorCompression, ContinuousLinearMap.comp_apply,
    sectorProjection_injection] using hp

/-- A sector obstruction on the genuine common domain rules out ambient bounded agreement. -/
theorem no_bounded_bracket_extension (n : ℕ)
    (hsector : ¬ ∃ B : Sector l r n →L[ℂ] Sector l r n,
      ∀ v (h : CommonDomain (K n) (M n) v), B v = bracketValue (K n) (M n) v h) :
    ¬ ∃ A : FockHilbert l r →L[ℂ] FockHilbert l r,
      ∀ ψ (h : CommonDomain (diagonal K) (diagonal M) ψ),
        A ψ = bracketValue (diagonal K) (diagonal M) ψ h := by
  rintro ⟨A, hA⟩
  exact hsector ⟨sectorCompression n A, bracket_compression K M n A hA⟩

section WallSector

open BECInteriorCommutator BECWallParity
open scoped ContDiff

variable (T : ℝ) [Fact (0 < T)]

/-- The actual wall Hamiltonian, transported to the physical N=1 bosonic sector. -/
def wallSector (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    Sector 0 (T / 2) 1 →ₗ.[ℂ] Sector 0 (T / 2) 1 :=
  LinearPMap.unitaryConj (intervalBosonicUnitary 0 (T / 2))
    (wallHamiltonian T a σ hσ V hV)

/-- The actual N=1 density multiplier under the same physical unitary. -/
def densitySector (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    Sector 0 (T / 2) 1 →ₗ.[ℂ] Sector 0 (T / 2) 1 :=
  LinearPMap.unitaryConj (intervalBosonicUnitary 0 (T / 2)) (potentialPMap T f hf)

/-- All four actual wall common-domain memberships hold for every compact interior test. -/
theorem compact_wall_commonDomain (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (ψ : Domain 0 (T / 2)) :
    CommonDomain (wallHamiltonian T a σ hσ V hV) (potentialPMap T f hf)
      (toIntervalL2 ψ) where
  in_A := compact_mem_wallHamiltonian T a σ hσ V hV ψ
  in_B := Submodule.mem_top
  after_B := multiplier_compact_mem_wallHamiltonian T a σ hσ V f hV hf ψ
  after_A := Submodule.mem_top

/-- Compact tests enter the actual transported common domain, not a hypothetical branch. -/
theorem compact_sector_commonDomain (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (ψ : Domain 0 (T / 2)) :
    CommonDomain (wallSector T a σ hσ V hV) (densitySector T f hf)
      (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ)) :=
  unitary_commonDomain _ _ _ _ (compact_wall_commonDomain T a σ hσ V f hV hf ψ)

/-- The transported common-domain bracket is the original differential bracket. -/
theorem compact_sector_bracket (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (ψ : Domain 0 (T / 2))
    (h : CommonDomain (wallSector T a σ hσ V hV) (densitySector T f hf)
      (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ))) :
    bracketValue (wallSector T a σ hσ V hV) (densitySector T f hf)
        (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ)) h =
      intervalBosonicUnitary 0 (T / 2)
        (toIntervalL2 (BECInteriorCommutator.commutator a V f hV hf ψ)) := by
  exact (unitary_bracket (intervalBosonicUnitary 0 (T / 2)) _ _ _
    (compact_wall_commonDomain T a σ hσ V f hV hf ψ) h).trans
      (congrArg (intervalBosonicUnitary 0 (T / 2))
        (wallHamiltonian_bracket_compact T a σ hσ V f hV hf ψ))

/-- The physical wall obstruction survives actual N=1 unitary transport. -/
theorem no_bounded_wall_sector_extension {a : ℝ} (ha : 0 < a)
    (σ : ℂ) (hσ : σ ^ 2 = 1) (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hf : ContDiff ℝ ∞ f)
    (hn : ∃ x ∈ Set.Ioo 0 (T / 2), ∃ y ∈ Set.Ioo 0 (T / 2), f x ≠ f y) :
    ¬ ∃ B : Sector 0 (T / 2) 1 →L[ℂ] Sector 0 (T / 2) 1,
      ∀ v (h : CommonDomain (wallSector T a σ hσ V hV) (densitySector T f hf) v),
        B v = bracketValue (wallSector T a σ hσ V hV) (densitySector T f hf) v h := by
  rintro ⟨B, hB⟩
  apply no_bounded_interval_extension_of_nonconstant ha V f hV hf hn
  let U := intervalBosonicUnitary 0 (T / 2)
  let A : HalfSpace T →L[ℂ] HalfSpace T :=
    U.symm.toLinearIsometry.toContinuousLinearMap.comp
      (B.comp U.toLinearIsometry.toContinuousLinearMap)
  refine ⟨A, fun ψ ↦ ?_⟩
  have he := hB (U (toIntervalL2 ψ)) (compact_sector_commonDomain T a σ hσ V f hV hf ψ)
  rw [compact_sector_bracket T a σ hσ V f hV hf ψ] at he
  change U.symm (B (U (toIntervalL2 ψ))) = _
  rw [he]
  exact U.symm_apply_apply _

/-- The N=1 tests enter the actual Fock common domain for any family with these two
identified first sectors. No higher-sector physical realization is assumed. -/
theorem compact_fock_commonDomain (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (KF MF : SectorFamily 0 (T / 2))
    (hK : KF 1 = wallSector T a σ hσ V hV) (hM : MF 1 = densitySector T f hf)
    (ψ : Domain 0 (T / 2)) :
    CommonDomain (diagonal KF) (diagonal MF)
      (sectorInjection 1 (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ))) := by
  apply injection_commonDomain
  rw [hK, hM]
  exact compact_sector_commonDomain T a σ hσ V f hV hf ψ

/-- Actual compact wall tests have the actual differential bracket after Fock injection. -/
theorem compact_fock_bracket (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (KF MF : SectorFamily 0 (T / 2))
    (hK : KF 1 = wallSector T a σ hσ V hV) (hM : MF 1 = densitySector T f hf)
    (ψ : Domain 0 (T / 2))
    (hF : CommonDomain (diagonal KF) (diagonal MF)
      (sectorInjection 1 (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ)))) :
    bracketValue (diagonal KF) (diagonal MF)
        (sectorInjection 1 (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ))) hF =
      sectorInjection 1 (intervalBosonicUnitary 0 (T / 2)
        (toIntervalL2 (BECInteriorCommutator.commutator a V f hV hf ψ))) := by
  have hs : CommonDomain (KF 1) (MF 1)
      (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ)) := by
    rw [hK, hM]
    exact compact_sector_commonDomain T a σ hσ V f hV hf ψ
  rw [injection_bracket KF MF 1 _ hs hF]
  congr 1
  simpa only [hK, hM] using compact_sector_bracket T a σ hσ V f hV hf ψ
    (compact_sector_commonDomain T a σ hσ V f hV hf ψ)

/-- A nonconstant smooth density rules out any ambient bounded bracket extension
whenever the first sectors are the actual transported wall and density operators. -/
theorem no_bounded_fock_wall_extension {a : ℝ} (ha : 0 < a)
    (σ : ℂ) (hσ : σ ^ 2 = 1) (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hf : ContDiff ℝ ∞ f)
    (hn : ∃ x ∈ Set.Ioo 0 (T / 2), ∃ y ∈ Set.Ioo 0 (T / 2), f x ≠ f y)
    (KF MF : SectorFamily 0 (T / 2))
    (hK : KF 1 = wallSector T a σ hσ V hV) (hM : MF 1 = densitySector T f hf) :
    ¬ ∃ A : FockHilbert 0 (T / 2) →L[ℂ] FockHilbert 0 (T / 2),
      ∀ ψ (h : CommonDomain (diagonal KF) (diagonal MF) ψ),
        A ψ = bracketValue (diagonal KF) (diagonal MF) ψ h := by
  apply no_bounded_bracket_extension KF MF 1
  rw [hK, hM]
  exact no_bounded_wall_sector_extension T ha σ hσ V f hV hf hn

/-- The obstruction has nonzero actual compact common-domain witnesses in Fock space. -/
theorem exists_compact_fock_nonzero_bracket {a : ℝ} (ha : 0 < a)
    (σ : ℂ) (hσ : σ ^ 2 = 1) (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hf : ContDiff ℝ ∞ f)
    (hn : ∃ x ∈ Set.Ioo 0 (T / 2), ∃ y ∈ Set.Ioo 0 (T / 2), f x ≠ f y)
    (KF MF : SectorFamily 0 (T / 2))
    (hK : KF 1 = wallSector T a σ hσ V hV) (hM : MF 1 = densitySector T f hf) :
    ∃ ψ : Domain 0 (T / 2),
      ∃ h : CommonDomain (diagonal KF) (diagonal MF)
        (sectorInjection 1 (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ))),
      bracketValue (diagonal KF) (diagonal MF)
        (sectorInjection 1 (intervalBosonicUnitary 0 (T / 2) (toIntervalL2 ψ))) h ≠ 0 := by
  have hex : ∃ ψ : Domain 0 (T / 2),
      toIntervalL2 (BECInteriorCommutator.commutator a V f hV hf ψ) ≠ 0 := by
    by_contra hnz
    push Not at hnz
    exact no_bounded_interval_extension_of_nonconstant ha V f hV hf hn
      ⟨0, fun ψ ↦ (hnz ψ).symm⟩
  obtain ⟨ψ, hψ⟩ := hex
  refine ⟨ψ, compact_fock_commonDomain T a σ hσ V f hV hf KF MF hK hM ψ, ?_⟩
  rw [compact_fock_bracket T a σ hσ V f hV hf KF MF hK hM ψ]
  intro hz
  have hi := congrArg (sectorProjection 1) hz
  simp only [sectorProjection_injection, map_zero] at hi
  exact hψ ((intervalBosonicUnitary 0 (T / 2)).injective
    (hi.trans (map_zero _).symm))

/-- A completely constructed algebraic family realizes the obstruction, so the first-sector
matching hypotheses above are inhabited. The zero higher operators have no physical claim. -/
theorem no_bounded_completed_wall_extension {a : ℝ} (ha : 0 < a)
    (σ : ℂ) (hσ : σ ^ 2 = 1) (V f : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hf : ContDiff ℝ ∞ f)
    (hn : ∃ x ∈ Set.Ioo 0 (T / 2), ∃ y ∈ Set.Ioo 0 (T / 2), f x ≠ f y) :
    ¬ ∃ A : FockHilbert 0 (T / 2) →L[ℂ] FockHilbert 0 (T / 2),
      ∀ ψ (h : CommonDomain
        (diagonal (firstSectorCompletion (wallSector T a σ hσ V hV)))
        (diagonal (firstSectorCompletion (densitySector T f hf))) ψ),
        A ψ = bracketValue
          (diagonal (firstSectorCompletion (wallSector T a σ hσ V hV)))
          (diagonal (firstSectorCompletion (densitySector T f hf))) ψ h :=
  no_bounded_fock_wall_extension T ha σ hσ V f hV hf hn _ _
    (firstSectorCompletion_one _) (firstSectorCompletion_one _)

end WallSector

end SKEFTHawking.DKMBootstrap.BECFockOperators
