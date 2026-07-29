import Mathlib
import SKEFTHawking.SingularRelativeUCInt

/-!
# Phase 5q.H (E1/N4) — the ABSOLUTE integral universal-coefficient theorem + the leg's Kronecker flip

The absolute (closed-space) port of the integral relative UCT engine `SingularRelativeUCInt`
(2aa2f5f0 harvest). Over ℤ the absolute universal-coefficient short exact sequence

  `0 → Ext(Hₙ₋₁(X), ℤ) → Hⁿ(X; ℤ) --κ--> Hom(Hₙ(X; ℤ), ℤ) → 0`

makes the absolute Kronecker map `κ = kroneckerHInt n` an iso exactly when `Hₙ₋₁(X; ℤ)` is free.
This module builds, mirroring the relative engine §3–§6 with the quotient layer stripped:

* §1 — the cycle-summand retraction from projective boundaries (`exists_boundary_section` /
  `exists_cycles_retraction`): the ℤ replacement for the field complement;
* §2 — surjectivity of `κ` (`kroneckerHInt_surjective_of_projective`, the Hom-side — needs only
  projective boundaries);
* §3 — injectivity of `κ` when `Hₙ₋₁` is free (`kroneckerHInt_injective_of_free`, the `Ext = 0` half);
* §4 — the bijectivity headline + packaged iso `ucIntEquivOfFree : Hⁿ(X;ℤ) ≃ₗ (Hₙ(X;ℤ))*`;
* §5 — **the leg's Kronecker FLIP** `kronFlipOfFree : Hₙ(X;ℤ) ≃ₗ (Hⁿ(X;ℤ))*` — the σ÷16 leg's
  `kron` binder direction — from `ucIntEquivOfFree` dualized through the reflexivity of `Hₙ`
  (`Module.IsReflexive.of_finite_of_free`), with the leg's exact computation rule
  `kronFlipOfFree h b = kroneckerHInt n b h` (`hkron`);
* §6 — the degree-2 packaging `kronH2OfFree`/`kronH2OfFree_apply` in the σ÷16 leg's literal binder
  shape (`Homology X 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology X 2)`).

**The honest hypothesis set** (all carried as instances, never derived — the ℤ-analog of the mod-2
Erdős–Kaplansky forcing is PROVABLY BLOCKED, settled fork `5qH-fg-ek-over-Z-blocked`):
* `Module.Projective ℤ (boundaries X n)` at the two relevant degrees — universally true over the PID ℤ
  (submodules of free modules are free), Mathlib-gapped at infinite rank — exactly the instances the
  relative engine carries;
* `Module.Free ℤ (Homology X (n-1))` — the genuine `Ext = 0` topological input (`H₁` torsion-free for
  the deg-2 case);
* `Module.Free ℤ (Homology X n)` + `Module.Finite ℤ (Homology X n)` — the genuine finiteness input
  for the flip's reflexivity (N5-adjacent: the finiteness tower that discharges `intH2_basis_datum`
  produces exactly these).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt

namespace SKEFTHawking.SingularAbsoluteUCInt

variable {X : TopCat}

/-! ## §1. The cycle-summand retraction from projective boundaries (absolute) -/

/-- **The boundary map splits when the boundaries are projective** (absolute mirror of
`SingularRelativeUCInt.exists_boundary_section`): a section `s : boundaries X N → C_{N+1}` of
`∂ : C_{N+1} ↠ B_N`, from `Module.Projective`'s lifting property. -/
theorem exists_boundary_section {N : ℕ} [Module.Projective ℤ (boundaries X N)] :
    ∃ s : boundaries X N →ₗ[ℤ] SingularChainInt X (N + 1),
      ∀ b : boundaries X N, chainBoundary X N (s b) = (b : SingularChainInt X N) := by
  let bdryR : SingularChainInt X (N + 1) →ₗ[ℤ] boundaries X N :=
    (chainBoundary X N).codRestrict (boundaries X N) (fun c => ⟨c, rfl⟩)
  have hsurj : Function.Surjective (bdryR : SingularChainInt X (N + 1) → boundaries X N) := by
    rintro ⟨b, hb⟩
    obtain ⟨c, rfl⟩ := hb
    exact ⟨c, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property bdryR LinearMap.id hsurj
  refine ⟨s, fun b => ?_⟩
  have hcf := LinearMap.congr_fun hs b
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hcf
  have h2 : ((bdryR (s b) : boundaries X N) : SingularChainInt X N)
      = ((b : boundaries X N) : SingularChainInt X N) := congrArg Subtype.val hcf
  rwa [show (bdryR (s b) : boundaries X N).1 = chainBoundary X N (s b) from rfl] at h2

/-- **The retraction onto the cycles** `r : C_{N+1} → Z_{N+1}` (`r ∘ incl = id`), from a boundary
section `s`: `r = id - s ∘ ∂` lands in `ker ∂ = Z_{N+1}` and fixes cycles. The ℤ replacement for the
field complement (absolute mirror of `SingularRelativeUCInt.exists_cycles_retraction`). -/
theorem exists_cycles_retraction {N : ℕ} [Module.Projective ℤ (boundaries X N)] :
    ∃ r : SingularChainInt X (N + 1) →ₗ[ℤ] cycles X (N + 1),
      ∀ z : cycles X (N + 1), r (z : SingularChainInt X (N + 1)) = z := by
  obtain ⟨s, hs⟩ := exists_boundary_section (X := X) (N := N)
  have hmem : ∀ c : SingularChainInt X (N + 1),
      chainBoundary X N c ∈ boundaries X N := fun c => ⟨c, rfl⟩
  refine ⟨{
    toFun := fun c => ⟨c - s ⟨chainBoundary X N c, hmem c⟩, ?_⟩
    map_add' := ?_
    map_smul' := ?_ }, ?_⟩
  · -- membership in cycles (N+1) = ker ∂
    show c - s ⟨chainBoundary X N c, hmem c⟩ ∈ LinearMap.ker (chainBoundary X N)
    rw [LinearMap.mem_ker, map_sub, hs ⟨chainBoundary X N c, hmem c⟩, sub_self]
  · intro c d
    apply Subtype.ext
    show (c + d) - s ⟨chainBoundary X N (c + d), _⟩
      = (c - s ⟨chainBoundary X N c, _⟩) + (d - s ⟨chainBoundary X N d, _⟩)
    rw [show (⟨chainBoundary X N (c + d), hmem (c + d)⟩ : boundaries X N)
        = ⟨chainBoundary X N c, hmem c⟩ + ⟨chainBoundary X N d, hmem d⟩ from by
          apply Subtype.ext; simp [map_add], map_add]
    abel
  · intro t c
    apply Subtype.ext
    show (t • c) - s ⟨chainBoundary X N (t • c), _⟩
      = t • (c - s ⟨chainBoundary X N c, _⟩)
    rw [show (⟨chainBoundary X N (t • c), hmem (t • c)⟩ : boundaries X N)
        = t • ⟨chainBoundary X N c, hmem c⟩ from by
          apply Subtype.ext; simp [map_smul], map_smul, smul_sub]
  · intro z
    apply Subtype.ext
    show (z : SingularChainInt X (N + 1)) - s ⟨chainBoundary X N z, _⟩ = z
    have hz0 : chainBoundary X N (z : SingularChainInt X (N + 1)) = 0 := by
      have hzmem : (z : SingularChainInt X (N + 1)) ∈ LinearMap.ker (chainBoundary X N) := z.2
      rwa [LinearMap.mem_ker] at hzmem
    rw [show (⟨chainBoundary X N (z : SingularChainInt X (N + 1)), hmem _⟩ : boundaries X N)
        = 0 from by apply Subtype.ext; exact hz0, map_zero, sub_zero]

/-! ## §2. Surjectivity of `κ` (the Hom-side; needs only projective boundaries) -/

/-- **`κ = kroneckerHInt (N+1)` is surjective**: every functional on `Hₙ₊₁(X; ℤ)` is the Kronecker
pairing of an integral cohomology class — provided the boundaries `boundaries X N` are projective
(so a functional on the cycles extends to all chains via the §1 retraction). The integral Hom-side
of the absolute UCT; the `Ext` obstruction lives only in injectivity. Absolute mirror of
`SingularRelativeUCInt.relKroneckerHInt_surjective` (and integral mirror of the mod-2
`SingularUCFinite.kroneckerH_surjective_field`, with the retraction replacing
`LinearMap.exists_extend`). -/
theorem kroneckerHInt_surjective_of_projective {N : ℕ}
    [Module.Projective ℤ (boundaries X N)] :
    Function.Surjective (kroneckerHInt (X := X) (N + 1)) := by
  intro φ
  -- Pull `φ` back along the homology quotient to a functional `ψ` on the cycles.
  set ψ : cycles X (N + 1) →ₗ[ℤ] ℤ :=
    φ.comp ((boundaries X (N + 1)).submoduleOf (cycles X (N + 1))).mkQ with hψ
  -- Extend `ψ` to all chains via the retraction `r : C_{N+1} → Z_{N+1}`.
  obtain ⟨r, hr⟩ := exists_cycles_retraction (X := X) (N := N)
  set F : SingularChainInt X (N + 1) →ₗ[ℤ] ℤ := ψ.comp r with hF
  -- `F` agrees with `ψ` on cycles.
  have hFcyc : ∀ z : cycles X (N + 1), F (z : SingularChainInt X (N + 1)) = ψ z := by
    intro z; rw [hF, LinearMap.comp_apply, hr z]
  -- Realize `F` as `kronecker a` for a cochain `a` (the chains are free).
  obtain ⟨a, ha⟩ := SKEFTHawking.SingularRelativeUCInt.exists_cochainInt_of_functional F
  -- `F` kills boundaries (they are `0` in homology).
  have hFbd : ∀ w : SingularChainInt X (N + 2), F (chainBoundary X (N + 1) w) = 0 := by
    intro w
    have hmem : chainBoundary X (N + 1) w ∈ boundaries X (N + 1) := ⟨w, rfl⟩
    have hcyc : chainBoundary X (N + 1) w ∈ cycles X (N + 1) :=
      boundaries_le_cycles X (N + 1) hmem
    have hzero : ((boundaries X (N + 1)).submoduleOf (cycles X (N + 1))).mkQ
        ⟨chainBoundary X (N + 1) w, hcyc⟩ = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_comap.mpr hmem
    have h1 : F (chainBoundary X (N + 1) w) = ψ ⟨chainBoundary X (N + 1) w, hcyc⟩ :=
      hFcyc ⟨chainBoundary X (N + 1) w, hcyc⟩
    exact h1.trans ((congrArg φ hzero).trans (map_zero φ))
  -- Hence `a` is a cocycle: `⟨δa, σ⟩ = F (∂σ) = 0` on every basis simplex.
  have hcocycle : a ∈ LinearMap.ker (coboundaryₗ X (N + 1)) := by
    rw [LinearMap.mem_ker]
    funext σ
    have hkz : kronecker (coboundary X (N + 1) a) (Finsupp.single σ 1) = 0 := by
      rw [kronecker_coboundary_chainBoundary, ha, hFbd]
    rw [kronecker_single, one_mul] at hkz
    exact hkz
  -- `[a]` pairs to `φ`.
  refine ⟨Submodule.Quotient.mk ⟨a, hcocycle⟩, ?_⟩
  ext z'
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z'
  rw [kroneckerHInt_mk_mk, ha, hFcyc z, hψ, LinearMap.comp_apply]
  rfl

/-! ## §3. Injectivity of `κ` — the Ext obstruction, killed by `Hₙ` free (absolute) -/

/-- **The boundaries retract inside the cycles when `Hₙ` is free** (absolute mirror of
`SingularRelativeUCInt.exists_boundaries_in_cycles_retraction`): a projection `Zₙ ↠ Bₙ` fixing
`Bₙ`, from splitting the quotient `Zₙ ↠ Hₙ = Zₙ/Bₙ` (`Hₙ` free ⟹ projective ⟹ the quotient map
splits). -/
theorem exists_boundaries_in_cycles_retraction {N : ℕ} [Module.Free ℤ (Homology X N)] :
    ∃ ρ : cycles X N →ₗ[ℤ] (boundaries X N).submoduleOf (cycles X N),
      ∀ b : (boundaries X N).submoduleOf (cycles X N), ρ (b : cycles X N) = b := by
  set Bsub := (boundaries X N).submoduleOf (cycles X N) with hBsub
  -- `Hₙ = Zₙ / Bsub` is free ⟹ projective ⟹ the surjection `Bsub.mkQ : Zₙ ↠ Hₙ` splits.
  have e : Homology X N ≃ₗ[ℤ] (↥(cycles X N) ⧸ Bsub) := LinearEquiv.refl ℤ _
  haveI hproj : Module.Projective ℤ (↥(cycles X N) ⧸ Bsub) := Module.Projective.of_equiv e
  obtain ⟨sec, hsec⟩ := Module.projective_lifting_property Bsub.mkQ
    (LinearMap.id (R := ℤ) (M := ↥(cycles X N) ⧸ Bsub)) Bsub.mkQ_surjective
  -- `z - sec (mkQ z) ∈ Bsub = ker (mkQ)`.
  have hmem : ∀ z : cycles X N, z - sec (Bsub.mkQ z) ∈ Bsub := by
    intro z
    have hid : Bsub.mkQ (sec (Bsub.mkQ z)) = Bsub.mkQ z := by
      have h := LinearMap.congr_fun hsec (Bsub.mkQ z)
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at h
      exact h
    have hk : z - sec (Bsub.mkQ z) ∈ LinearMap.ker Bsub.mkQ := by
      rw [LinearMap.mem_ker, map_sub, hid, sub_self]
    rwa [Submodule.ker_mkQ] at hk
  refine ⟨{
    toFun := fun z => ⟨z - sec (Bsub.mkQ z), hmem z⟩
    map_add' := ?_
    map_smul' := ?_ }, ?_⟩
  · intro a b; apply Subtype.ext
    show (a + b) - sec (Bsub.mkQ (a + b)) = (a - sec (Bsub.mkQ a)) + (b - sec (Bsub.mkQ b))
    rw [map_add, map_add]; abel
  · intro t a; apply Subtype.ext
    show (t • a) - sec (Bsub.mkQ (t • a)) = t • (a - sec (Bsub.mkQ a))
    rw [map_smul, map_smul, smul_sub]
  · intro b; apply Subtype.ext
    show ((b : cycles X N)) - sec (Bsub.mkQ (b : cycles X N)) = (b : cycles X N)
    have hb0 : Bsub.mkQ (b : cycles X N) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact b.2
    rw [hb0, map_zero, sub_zero]

/-- **A functional on the boundaries extends to all chains** (the `Ext = 0` engine, absolute):
given `Hₙ = H_{M+1}` free and the previous boundaries `B_M` projective, `B_{M+1}` is a direct
summand of `C_{M+1}` (via the composite retraction `C_{M+1} ↠ Z_{M+1} ↠ B_{M+1}`), so any
`ḡ : B_{M+1} → ℤ` extends to `F : C_{M+1} → ℤ` with `F|B = ḡ`. Absolute mirror of
`SingularRelativeUCInt.exists_functional_extension_boundaries`. -/
theorem exists_functional_extension_boundaries {M : ℕ}
    [Module.Free ℤ (Homology X (M + 1))] [Module.Projective ℤ (boundaries X M)]
    (g : boundaries X (M + 1) →ₗ[ℤ] ℤ) :
    ∃ F : SingularChainInt X (M + 1) →ₗ[ℤ] ℤ,
      ∀ b : boundaries X (M + 1), F (b : SingularChainInt X (M + 1)) = g b := by
  -- Retraction `C_{M+1} ↠ Z_{M+1}` (§1, needs `B_M` projective).
  obtain ⟨r, hr⟩ := exists_cycles_retraction (X := X) (N := M)
  -- Retraction `Z_{M+1} ↠ B_{M+1}` inside the cycles (§3a, needs `H_{M+1}` free).
  obtain ⟨ρ, hρ⟩ := exists_boundaries_in_cycles_retraction (X := X) (N := M + 1)
  have hcoe : ∀ w : (boundaries X (M + 1)).submoduleOf (cycles X (M + 1)),
      ((w : cycles X (M + 1)) : SingularChainInt X (M + 1)) ∈ boundaries X (M + 1) := by
    intro w
    exact Submodule.mem_comap.mp w.2
  refine ⟨g.comp
    ({ toFun := fun c => ⟨((ρ (r c) : cycles X (M + 1)) : SingularChainInt X (M + 1)),
          hcoe (ρ (r c))⟩
       map_add' := fun a b => by apply Subtype.ext; simp [map_add]
       map_smul' := fun t a => by apply Subtype.ext; simp [map_smul] } :
      SingularChainInt X (M + 1) →ₗ[ℤ] boundaries X (M + 1)), ?_⟩
  intro b
  rw [LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  show ((ρ (r (b : SingularChainInt X (M + 1))) : cycles X (M + 1)) : SingularChainInt X (M + 1))
    = (b : SingularChainInt X (M + 1))
  -- `b : B_{M+1} ⊆ Z_{M+1}`; `r` fixes it (it is a cycle), `ρ` fixes it (it is a boundary).
  have hbcyc : (b : SingularChainInt X (M + 1)) ∈ cycles X (M + 1) :=
    boundaries_le_cycles X (M + 1) b.2
  have hrb : r (b : SingularChainInt X (M + 1)) = ⟨(b : SingularChainInt X (M + 1)), hbcyc⟩ :=
    hr ⟨(b : SingularChainInt X (M + 1)), hbcyc⟩
  rw [hrb]
  have hbsubmem : (⟨(b : SingularChainInt X (M + 1)), hbcyc⟩ : cycles X (M + 1))
      ∈ (boundaries X (M + 1)).submoduleOf (cycles X (M + 1)) :=
    Submodule.mem_comap.mpr b.2
  rw [hρ ⟨_, hbsubmem⟩]

/-- **`κ` is injective when `Hₙ` is free** (the `Ext(Hₙ) = 0` half, absolute): a cohomology class
`ω = [a]` of degree `M+2` pairing to `0` with every homology class is `0`. `φ = ⟨a, ·⟩` vanishes on
the cycles `Z_{M+2} = ker ∂`, so factors as `ḡ ∘ ∂` through `im ∂ = B_{M+1}`; extend `ḡ` to
`g : C_{M+1} → ℤ` (`exists_functional_extension_boundaries`); realize `g = ⟨b, ·⟩`; the adjunction
gives `a = δb`, so `ω = 0`. Absolute mirror of
`SingularRelativeUCInt.relKroneckerHInt_injective_of_free`. -/
theorem kroneckerHInt_injective_of_free {M : ℕ}
    [Module.Free ℤ (Homology X (M + 1))] [Module.Projective ℤ (boundaries X M)]
    (ω : Cohomology X (M + 2))
    (h : ∀ β : Homology X (M + 2), kroneckerHInt (M + 2) ω β = 0) : ω = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ ω
  set φ : SingularChainInt X (M + 2) →ₗ[ℤ] ℤ := kroneckerₗ (M + 2) a.1 with hφ
  -- `φ` vanishes on the cycles `Z_{M+2} = ker ∂_{M+1}`.
  have hvanish : LinearMap.ker (chainBoundary X (M + 1)) ≤ LinearMap.ker φ := by
    intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    have hzcyc : z ∈ cycles X (M + 2) := hz
    have hh := h (Homology.mk X (M + 2) ⟨z, hzcyc⟩)
    rwa [show Homology.mk X (M + 2) ⟨z, hzcyc⟩
        = (Submodule.Quotient.mk ⟨z, hzcyc⟩ : Homology X (M + 2)) from rfl,
      kroneckerHInt_mk_mk] at hh
  -- Factor `φ` through `im ∂_{M+1} = B_{M+1}` as `ḡ` with `φ = ḡ ∘ ∂`.
  set dlm := chainBoundary X (M + 1) with hdlm
  set gbar : dlm.range →ₗ[ℤ] ℤ :=
    (Submodule.liftQ (LinearMap.ker dlm) φ hvanish).comp
      (LinearMap.quotKerEquivRange dlm).symm.toLinearMap with hgbar
  -- `gbar (∂ c) = φ c`.
  have hgbar_apply : ∀ c : SingularChainInt X (M + 2),
      gbar ⟨chainBoundary X (M + 1) c, ⟨c, rfl⟩⟩ = φ c := by
    intro c
    have hrr : (LinearMap.quotKerEquivRange dlm).symm ⟨chainBoundary X (M + 1) c, ⟨c, rfl⟩⟩
        = Submodule.Quotient.mk c := by
      apply (LinearMap.quotKerEquivRange dlm).injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      rfl
    rw [hgbar, LinearMap.comp_apply, LinearEquiv.coe_coe, hrr, Submodule.liftQ_apply]
  -- Extend `gbar` to `g : C_{M+1} → ℤ`.
  obtain ⟨g, hg⟩ := exists_functional_extension_boundaries (X := X) gbar
  -- Realize `g` as `kronecker b`.
  obtain ⟨b, hb⟩ := SKEFTHawking.SingularRelativeUCInt.exists_cochainInt_of_functional g
  -- `a = δb` (coboundary): check on each basis simplex via the adjunction.
  have hcobound : (a : SingularCochainInt X (M + 2)) = coboundary X (M + 1) b := by
    funext σ
    have e1 : kronecker (a : SingularCochainInt X (M + 2)) (Finsupp.single σ 1)
        = (a : SingularCochainInt X (M + 2)) σ := by rw [kronecker_single, one_mul]
    have e2 : kronecker (coboundary X (M + 1) b) (Finsupp.single σ 1)
        = coboundary X (M + 1) b σ := by rw [kronecker_single, one_mul]
    rw [← e1, ← e2]
    have hlhs : kronecker (a : SingularCochainInt X (M + 2)) (Finsupp.single σ 1)
        = φ (Finsupp.single σ 1) := rfl
    have hrhs : kronecker (coboundary X (M + 1) b) (Finsupp.single σ 1)
        = φ (Finsupp.single σ 1) := by
      rw [kronecker_coboundary_chainBoundary, hb,
        hg ⟨chainBoundary X (M + 1) (Finsupp.single σ 1), ⟨Finsupp.single σ 1, rfl⟩⟩]
      exact hgbar_apply (Finsupp.single σ 1)
    rw [hlhs, hrhs]
  -- `[a] = 0`: `a` is a coboundary.
  have hamem : a ∈ (coboundaryRange X (M + 2)).submoduleOf (LinearMap.ker (coboundaryₗ X (M + 2))) := by
    refine Submodule.mem_comap.mpr ?_
    show (a : SingularCochainInt X (M + 2)) ∈ LinearMap.range (coboundaryₗ X (M + 1))
    exact ⟨b, hcobound.symm⟩
  exact (Submodule.Quotient.mk_eq_zero _).mpr hamem

/-! ## §4. The bijectivity headline and the packaged UCT iso -/

/-- **The absolute integral universal-coefficient theorem, free case** — `κ` is BIJECTIVE:
`Hⁿ(X; ℤ) ≅ Hom(Hₙ(X; ℤ), ℤ)` (`n = M+2`) when the previous homology `H_{M+1}` is free
(⟹ `Ext(H_{M+1}, ℤ) = 0`) and the relevant boundaries are projective. Combines §2 surjectivity with
§3 injectivity. Absolute mirror of `SingularRelativeUCInt.relKroneckerHInt_bijective_of_free`. -/
theorem kroneckerHInt_bijective_of_free {M : ℕ}
    [Module.Free ℤ (Homology X (M + 1))]
    [Module.Projective ℤ (boundaries X M)]
    [Module.Projective ℤ (boundaries X (M + 1))] :
    Function.Bijective (kroneckerHInt (X := X) (M + 2)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro ω hω
    exact kroneckerHInt_injective_of_free ω (fun β => LinearMap.congr_fun hω β)
  · exact kroneckerHInt_surjective_of_projective (X := X) (N := M + 1)

/-- **The absolute integral UCT free-case iso** `Hⁿ(X; ℤ) ≃ₗ Module.Dual ℤ (Hₙ(X; ℤ))` (`n = M+2`)
as a `LinearEquiv`, from `kroneckerHInt_bijective_of_free`. -/
noncomputable def ucIntEquivOfFree (X : TopCat) (M : ℕ)
    [Module.Free ℤ (Homology X (M + 1))]
    [Module.Projective ℤ (boundaries X M)]
    [Module.Projective ℤ (boundaries X (M + 1))] :
    Cohomology X (M + 2) ≃ₗ[ℤ] Module.Dual ℤ (Homology X (M + 2)) :=
  LinearEquiv.ofBijective (kroneckerHInt (M + 2)) kroneckerHInt_bijective_of_free

@[simp] theorem ucIntEquivOfFree_apply {M : ℕ}
    [Module.Free ℤ (Homology X (M + 1))]
    [Module.Projective ℤ (boundaries X M)]
    [Module.Projective ℤ (boundaries X (M + 1))]
    (ω : Cohomology X (M + 2)) :
    ucIntEquivOfFree X M ω = kroneckerHInt (M + 2) ω := rfl

/-! ## §5. The leg's Kronecker FLIP — `Hₙ ≃ₗ (Hⁿ)*` through reflexivity -/

/-- **The σ÷16 leg's Kronecker duality, honest-hypotheses form** — the FLIP
`Hₙ(X; ℤ) ≃ₗ Module.Dual ℤ (Hⁿ(X; ℤ))` (`n = M+2`): the double-dual reflexivity of `Hₙ`
(`Module.evalEquiv`, from `Hₙ` finite free) composed with the dual of the §4 UCT iso. This is the
exact direction of the leg's `kron` binder (`Homology M 2 ≃ₗ Module.Dual ℤ (Cohomology M 2)`); the
computation rule `kronFlipOfFree_apply` is the leg's `hkron`. -/
noncomputable def kronFlipOfFree (X : TopCat) (M : ℕ)
    [Module.Free ℤ (Homology X (M + 1))]
    [Module.Projective ℤ (boundaries X M)]
    [Module.Projective ℤ (boundaries X (M + 1))]
    [Module.Free ℤ (Homology X (M + 2))]
    [Module.Finite ℤ (Homology X (M + 2))] :
    Homology X (M + 2) ≃ₗ[ℤ] Module.Dual ℤ (Cohomology X (M + 2)) :=
  haveI : Module.IsReflexive ℤ (Homology X (M + 2)) :=
    Module.IsReflexive.of_finite_of_free ℤ (Homology X (M + 2))
  (Module.evalEquiv ℤ (Homology X (M + 2))).trans (ucIntEquivOfFree X M).dualMap

/-- **The flip computes as the Kronecker pairing** (the leg's `hkron`):
`kronFlipOfFree h b = ⟨b, h⟩ = kroneckerHInt (M+2) b h`. -/
theorem kronFlipOfFree_apply {M : ℕ}
    [Module.Free ℤ (Homology X (M + 1))]
    [Module.Projective ℤ (boundaries X M)]
    [Module.Projective ℤ (boundaries X (M + 1))]
    [Module.Free ℤ (Homology X (M + 2))]
    [Module.Finite ℤ (Homology X (M + 2))]
    (h : Homology X (M + 2)) (b : Cohomology X (M + 2)) :
    kronFlipOfFree X M h b = kroneckerHInt (M + 2) b h := rfl

/-! ## §6. The degree-2 packaging — the σ÷16 leg's literal binder shape -/

/-- **The leg's `kron` binder, discharged**: `H₂(X; ℤ) ≃ₗ Module.Dual ℤ (H²(X; ℤ))` at the literal
degree-2 spelling the σ÷16 leg consumes, under the honest hypothesis set — `H₁` free (the `Ext = 0`
input), the two boundary projectivities (universally true over the PID ℤ, Mathlib-gapped at
infinite rank), and `H₂` finite free (the reflexivity input; N5-adjacent). -/
noncomputable def kronH2OfFree (X : TopCat)
    [Module.Free ℤ (Homology X 1)]
    [Module.Projective ℤ (boundaries X 0)]
    [Module.Projective ℤ (boundaries X 1)]
    [Module.Free ℤ (Homology X 2)]
    [Module.Finite ℤ (Homology X 2)] :
    Homology X 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology X 2) :=
  haveI : Module.Free ℤ (Homology X (0 + 1)) := inferInstanceAs (Module.Free ℤ (Homology X 1))
  haveI : Module.Projective ℤ (boundaries X (0 + 1)) :=
    inferInstanceAs (Module.Projective ℤ (boundaries X 1))
  haveI : Module.Free ℤ (Homology X (0 + 2)) := inferInstanceAs (Module.Free ℤ (Homology X 2))
  haveI : Module.Finite ℤ (Homology X (0 + 2)) := inferInstanceAs (Module.Finite ℤ (Homology X 2))
  kronFlipOfFree X 0

/-- **The leg's `hkron` binder, discharged**: `kronH2OfFree X h b = kroneckerHInt 2 b h` — the
exact computation rule `sixteen_dvd_latticeSigInt` and its orientation/cert forms demand. -/
theorem kronH2OfFree_apply (X : TopCat)
    [Module.Free ℤ (Homology X 1)]
    [Module.Projective ℤ (boundaries X 0)]
    [Module.Projective ℤ (boundaries X 1)]
    [Module.Free ℤ (Homology X 2)]
    [Module.Finite ℤ (Homology X 2)]
    (h : Homology X 2) (b : Cohomology X 2) :
    kronH2OfFree X h b = kroneckerHInt 2 b h := rfl

end SKEFTHawking.SingularAbsoluteUCInt
