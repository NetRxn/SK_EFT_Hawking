/-
# Phase 5q.H (E1 CSC-PD tower) — Kaplansky: a submodule of a free ℤ-module is free

`Module.Free ℤ ↥N` for any submodule `N` of a free ℤ-module (arbitrary, possibly infinite, rank).
Mathlib has only the `[Finite ι]` PID theory (`Submodule.basisOfPid` / `smithNormalForm`); the
infinite-rank case (Kaplansky, `infer_instance` FAILS for `Submodule ℤ (ℕ →₀ ℤ)`) is absent, yet it is
exactly what the integral UCT needs to discharge `hproj` (`relBoundariesInt` projective) and `hfree`
(top relative homology free) — both are submodules/subquotients of the free `RelativeChainInt`
(`free_relChainInt`).

**Method** (classical well-ordered leading-term descent): well-order the basis index `ι`; every
`f ≠ 0 : ι →₀ ℤ` has a max-support index `leadIdx f` with a nonzero leading coefficient and zero above
it. The leading coefficients at each index form an ideal `dᵢℤ`; choosing generators gives a basis of
`N` (linear independence from distinct leading indices; spanning by well-founded descent on `leadIdx`).

This file: the leading-term infrastructure (green foundation). Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib

namespace SKEFTHawking.FreeSubmoduleInt

variable {ι : Type*} [LinearOrder ι]

/-- **The leading index** of a nonzero finitely-supported function: the maximum element of its
support (w.r.t. the linear order on `ι`). -/
noncomputable def leadIdx (f : ι →₀ ℤ) (hf : f ≠ 0) : ι :=
  f.support.max' (Finsupp.support_nonempty_iff.mpr hf)

/-- The leading coefficient `f (leadIdx f)` is nonzero. -/
theorem lead_coeff_ne_zero (f : ι →₀ ℤ) (hf : f ≠ 0) : f (leadIdx f hf) ≠ 0 := by
  have hmem : leadIdx f hf ∈ f.support := f.support.max'_mem _
  exact Finsupp.mem_support_iff.mp hmem

/-- `f` vanishes strictly above its leading index. -/
theorem eq_zero_of_gt_leadIdx (f : ι →₀ ℤ) (hf : f ≠ 0) {j : ι} (hj : leadIdx f hf < j) :
    f j = 0 := by
  by_contra hfj
  have hmem : j ∈ f.support := Finsupp.mem_support_iff.mpr hfj
  exact absurd (f.support.le_max' j hmem) (not_le.mpr hj)

/-- The leading index is `≤` any index at which `f` is nonzero (it is the max of the support). -/
theorem leadIdx_le_of_ne_zero (f : ι →₀ ℤ) (hf : f ≠ 0) {j : ι} (hj : f j ≠ 0) :
    j ≤ leadIdx f hf :=
  f.support.le_max' j (Finsupp.mem_support_iff.mpr hj)

/-- A function `f` is **`i`-truncated** if it vanishes strictly above `i`. -/
def IsTrunc (i : ι) (f : ι →₀ ℤ) : Prop := ∀ j, i < j → f j = 0

/-- **The leading-coefficient ideal at `i`**: the coefficients `f i` for `i`-truncated `f ∈ N`.
A submodule of `ℤ` (hence, `ℤ` a PID, a principal ideal `(dᵢ)`); `dᵢ` is the leading coefficient
that generates the `i`-th step of the basis. -/
def leadIdeal (N : Submodule ℤ (ι →₀ ℤ)) (i : ι) : Submodule ℤ ℤ where
  carrier := {c | ∃ f ∈ N, IsTrunc i f ∧ f i = c}
  add_mem' := by
    rintro _ _ ⟨f, hfN, hf, rfl⟩ ⟨g, hgN, hg, rfl⟩
    exact ⟨f + g, N.add_mem hfN hgN,
      fun j hj => by rw [Finsupp.add_apply, hf j hj, hg j hj, add_zero], Finsupp.add_apply _ _ _⟩
  zero_mem' := ⟨0, N.zero_mem, fun _ _ => rfl, rfl⟩
  smul_mem' := by
    rintro a _ ⟨f, hfN, hf, rfl⟩
    exact ⟨a • f, N.smul_mem a hfN,
      fun j hj => by rw [Finsupp.smul_apply, hf j hj, smul_zero], Finsupp.smul_apply _ _ _⟩

/-- Membership in `leadIdeal`: `c` is a leading coefficient at `i` iff some `i`-truncated `f ∈ N` has
`f i = c`. -/
theorem mem_leadIdeal {N : Submodule ℤ (ι →₀ ℤ)} {i : ι} {c : ℤ} :
    c ∈ leadIdeal N i ↔ ∃ f ∈ N, IsTrunc i f ∧ f i = c := Iff.rfl

variable (N : Submodule ℤ (ι →₀ ℤ))

/-- **The principal generator** of the leading-coefficient ideal at `i` (`ℤ` a PID). The `i`-th step
of the basis exists exactly when `genCoeff N i ≠ 0`. -/
noncomputable def genCoeff (i : ι) : ℤ :=
  Submodule.IsPrincipal.generator (leadIdeal N i)

theorem genCoeff_mem (i : ι) : genCoeff N i ∈ leadIdeal N i :=
  Submodule.IsPrincipal.generator_mem _

/-- `genCoeff` generates the leading ideal: every leading coefficient at `i` is a `ℤ`-multiple of it. -/
theorem genCoeff_dvd {i : ι} {c : ℤ} (hc : c ∈ leadIdeal N i) : genCoeff N i ∣ c :=
  (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp hc

/-- **A chosen `i`-truncated witness** in `N` realizing the leading coefficient `genCoeff N i`. -/
noncomputable def gVec (i : ι) : ι →₀ ℤ := (mem_leadIdeal.mp (genCoeff_mem N i)).choose

theorem gVec_mem (i : ι) : gVec N i ∈ N := (mem_leadIdeal.mp (genCoeff_mem N i)).choose_spec.1

theorem gVec_trunc (i : ι) : IsTrunc i (gVec N i) :=
  (mem_leadIdeal.mp (genCoeff_mem N i)).choose_spec.2.1

theorem gVec_apply (i : ι) : (gVec N i) i = genCoeff N i :=
  (mem_leadIdeal.mp (genCoeff_mem N i)).choose_spec.2.2

/-- Above `i`, `gVec N i` vanishes (it is `i`-truncated). -/
theorem gVec_eq_zero_of_gt {i j : ι} (hj : i < j) : (gVec N i) j = 0 := gVec_trunc N i j hj

/-- **Evaluation of a `gVec`-combination at its top index reads off the leading coefficient.** For a
finite index set `s` with maximum `k`, `(∑ i ∈ s, g i • gVec N i) k = g k • genCoeff N k` — every lower
`gVec` is `i`-truncated hence vanishes at `k`. The triangular structure driving linear independence. -/
theorem sum_gVec_apply_max {s : Finset ι} (g : ι → ℤ) {k : ι} (hk : k ∈ s)
    (hmax : ∀ j ∈ s, j ≤ k) :
    (∑ i ∈ s, g i • gVec N i) k = g k • genCoeff N k := by
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single_of_mem k hk]
  · rw [Finsupp.smul_apply, gVec_apply]
  · intro i hi hik
    rw [Finsupp.smul_apply, gVec_eq_zero_of_gt N (lt_of_le_of_ne (hmax i hi) hik), smul_zero]

/-- **Triangular linear independence (finite-support core).** Any `ℤ`-combination of `gVec`s over a
finite set of indices with nonzero leading coefficients that sums to `0` has all coefficients `0` —
evaluate at the top nonzero index (`sum_gVec_apply_max`); its coefficient is `g k • genCoeff N k`, a
product of two nonzeros in the domain `ℤ`. -/
theorem gVec_indep_core {s : Finset ι} (g : ι → ℤ) (hs : ∀ i ∈ s, genCoeff N i ≠ 0)
    (hsum : ∑ i ∈ s, g i • gVec N i = 0) : ∀ i ∈ s, g i = 0 := by
  intro i₀ hi₀s
  by_contra hi₀
  set t := s.filter (fun i => g i ≠ 0) with ht
  have htne : t.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨hi₀s, hi₀⟩⟩
  set k := t.max' htne with hkdef
  have hkt : k ∈ t := t.max'_mem htne
  have hks : k ∈ s := (Finset.mem_filter.mp hkt).1
  have hkg : g k ≠ 0 := (Finset.mem_filter.mp hkt).2
  have hsum_t : ∑ i ∈ t, g i • gVec N i = 0 := by
    rw [← hsum]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro i his hit
    have hgi : g i = 0 := by by_contra hgi; exact hit (Finset.mem_filter.mpr ⟨his, hgi⟩)
    rw [hgi, zero_smul]
  have hmax : ∀ j ∈ t, j ≤ k := fun j hj => t.le_max' j hj
  have hzero : g k • genCoeff N k = 0 := by
    rw [← sum_gVec_apply_max N g hkt hmax, hsum_t, Finsupp.coe_zero, Pi.zero_apply]
  rw [smul_eq_mul] at hzero
  exact mul_ne_zero hkg (hs k hks) hzero

/-- **Spanning by well-founded descent.** Every `f ∈ N` lies in the span of the `gVec`s: subtract the
appropriate multiple `a • gVec N (leadIdx f)` (with `genCoeff N (leadIdx f) ∣ f (leadIdx f)` since `ℤ`
is a PID) to kill the leading term, strictly lowering the leading index; `WellFoundedLT` on `ι`
terminates the descent. -/
theorem mem_span_gVec [WellFoundedLT ι] (f : ι →₀ ℤ) (hf : f ∈ N) :
    f ∈ Submodule.span ℤ (Set.range (fun i : {i : ι // genCoeff N i ≠ 0} => gVec N (i : ι))) := by
  set W := Submodule.span ℤ (Set.range (fun i : {i : ι // genCoeff N i ≠ 0} => gVec N (i : ι))) with hW
  suffices H : ∀ i : ι, ∀ g ∈ N, (∀ j, g j ≠ 0 → j ≤ i) → g ∈ W by
    by_cases hf0 : f = 0
    · rw [hf0]; exact Submodule.zero_mem _
    · exact H (leadIdx f hf0) f hf (fun j hj => leadIdx_le_of_ne_zero f hf0 hj)
  intro i
  induction i using WellFoundedLT.induction with
  | _ i IH =>
    intro g hgN hsupp
    by_cases hg0 : g = 0
    · rw [hg0]; exact Submodule.zero_mem _
    · set m := leadIdx g hg0 with hmdef
      have hmi : m ≤ i := hsupp m (lead_coeff_ne_zero g hg0)
      have hc_mem : g m ∈ leadIdeal N m :=
        ⟨g, hgN, fun j hj => eq_zero_of_gt_leadIdx g hg0 hj, rfl⟩
      obtain ⟨a, ha⟩ := genCoeff_dvd N hc_mem
      -- the leading index has nonzero generator (its ideal contains the nonzero leading coeff `g m`)
      have hm_ne : genCoeff N m ≠ 0 := fun h0 =>
        lead_coeff_ne_zero g hg0 (zero_dvd_iff.mp (h0 ▸ genCoeff_dvd N hc_mem))
      have hmem_span : gVec N m ∈ W := Submodule.subset_span ⟨⟨m, hm_ne⟩, rfl⟩
      set g' := g - a • gVec N m with hg'def
      have hg'N : g' ∈ N := N.sub_mem hgN (N.smul_mem a (gVec_mem N m))
      have hg'm : g' m = 0 := by
        rw [hg'def, Finsupp.sub_apply, Finsupp.smul_apply, gVec_apply, smul_eq_mul, ha]; ring
      have hg'supp : ∀ j, g' j ≠ 0 → j < m := by
        intro j hj
        have hle : j ≤ m := by
          by_contra hgt
          apply hj
          rw [hg'def, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
            eq_zero_of_gt_leadIdx g hg0 (not_le.mp hgt), gVec_eq_zero_of_gt N (not_le.mp hgt)]
          ring
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exact absurd (h ▸ hg'm) hj
      by_cases hg'0 : g' = 0
      · have hfeq : g = a • gVec N m := sub_eq_zero.mp hg'0
        rw [hfeq]; exact Submodule.smul_mem _ _ hmem_span
      · have hlt_i : leadIdx g' hg'0 < i :=
          lt_of_lt_of_le (hg'supp _ (lead_coeff_ne_zero g' hg'0)) hmi
        have hspan' : g' ∈ W :=
          IH (leadIdx g' hg'0) hlt_i g' hg'N (fun j hj => leadIdx_le_of_ne_zero g' hg'0 hj)
        have hfeq : g = g' + a • gVec N m := by rw [hg'def]; abel
        rw [hfeq]; exact Submodule.add_mem _ hspan' (Submodule.smul_mem _ _ hmem_span)

/-- **The `gVec` family (over nonzero-generator indices) is linearly independent** — the ambient
(`ι →₀ ℤ`) form of the triangular independence `gVec_indep_core`, reindexed to the subtype. -/
theorem gVec_linearIndependent :
    LinearIndependent ℤ (fun i : {i : ι // genCoeff N i ≠ 0} => gVec N (i : ι)) := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hval_inj : Function.Injective
      (Subtype.val : {i : ι // genCoeff N i ≠ 0} → ι) := Subtype.val_injective
  set g' : ι → ℤ := Function.extend Subtype.val g 0 with hg'
  have hg'val : ∀ j : {i : ι // genCoeff N i ≠ 0}, g' (↑j) = g j :=
    fun j => hval_inj.extend_apply g 0 j
  have hsum' : ∑ j ∈ s.image Subtype.val, g' j • gVec N j = 0 := by
    rw [Finset.sum_image (fun x _ y _ h => hval_inj h)]
    refine Eq.trans ?_ hsum
    exact Finset.sum_congr rfl (fun j _ => by rw [hg'val j])
  have himg_ne : ∀ j ∈ s.image Subtype.val, genCoeff N j ≠ 0 := by
    intro j hj; obtain ⟨j', _, rfl⟩ := Finset.mem_image.mp hj; exact j'.2
  have hcore := gVec_indep_core N g' himg_ne hsum' (↑i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  rwa [hg'val i] at hcore

/-- **Kaplansky, `Finsupp` core**: a submodule of the free ℤ-module `ι →₀ ℤ` (well-ordered `ι`, any
rank) is free. The `gVec`s over nonzero-generator indices are a basis (`gVec_linearIndependent` +
`mem_span_gVec`). -/
theorem free_submodule_finsupp [WellFoundedLT ι] : Module.Free ℤ ↥N := by
  set v : {i : ι // genCoeff N i ≠ 0} → ↥N := fun i => ⟨gVec N (i : ι), gVec_mem N (i : ι)⟩ with hv
  have hli : LinearIndependent ℤ v :=
    (LinearMap.linearIndependent_iff N.subtype (Submodule.ker_subtype N)).mp
      (gVec_linearIndependent N)
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    rintro x -
    have hy : (x : ι →₀ ℤ) ∈ Submodule.map N.subtype (Submodule.span ℤ (Set.range v)) := by
      rw [Submodule.map_span]
      have himg : N.subtype '' Set.range v
          = Set.range (fun i : {i : ι // genCoeff N i ≠ 0} => gVec N (i : ι)) := by
        rw [← Set.range_comp]; rfl
      rw [himg]
      exact mem_span_gVec N x.1 x.2
    obtain ⟨z, hz, hzeq⟩ := Submodule.mem_map.mp hy
    have hzx : z = x := Subtype.ext hzeq
    rwa [hzx] at hz
  exact Module.Free.of_basis (Module.Basis.mk hli hsp)

/-- **Kaplansky (general free ℤ-module)**: a submodule of ANY free ℤ-module is free (arbitrary rank).
Transfers the `Finsupp` core `free_submodule_finsupp` along a chosen basis; the well-order on the basis
index is supplied internally by `exists_wellOrder`, so the statement carries no order hypothesis. This is
the Mathlib-absent lemma the integral UCT needs (`infer_instance` fails on `Submodule ℤ (ℕ →₀ ℤ)`). -/
theorem free_submodule_of_free {F : Type*} [AddCommGroup F] [Module ℤ F] [Module.Free ℤ F]
    (P : Submodule ℤ F) : Module.Free ℤ ↥P := by
  letI b := Module.Free.chooseBasis ℤ F
  obtain ⟨lo, wf⟩ := exists_wellOrder (Module.Free.ChooseBasisIndex ℤ F)
  letI := lo
  haveI := wf
  have hinj : Function.Injective b.repr.toLinearMap := b.repr.injective
  haveI : Module.Free ℤ ↥(Submodule.map b.repr.toLinearMap P) := free_submodule_finsupp _
  -- transfer along the equiv `↥(P.map b.repr) ≃ₗ ↥P`; bridge the ℤ-module diamond on `↥P`
  -- (`Submodule.module` vs `AddCommGroup.toIntModule`) via `Subsingleton (Module ℤ ↥P)`.
  exact (Subsingleton.elim P.module (AddCommGroup.toIntModule ↥P)) ▸
    (@Module.Free.of_equiv ℤ ℤ (↥(Submodule.map b.repr.toLinearMap P)) (↥P) _ _ _ _ _ P.module
      _ _ _ _ (Submodule.equivMapOfInjective b.repr.toLinearMap hinj P).symm this)

/-- **Projectivity form** (ℤ a PID, projective ⟺ free): a submodule of a free ℤ-module is projective. -/
theorem projective_submodule_of_free {F : Type*} [AddCommGroup F] [Module ℤ F] [Module.Free ℤ F]
    (P : Submodule ℤ F) : Module.Projective ℤ ↥P :=
  haveI := free_submodule_of_free P
  Module.Projective.of_free

end SKEFTHawking.FreeSubmoduleInt
