import SKEFTHawking.FiniteGibbsResetScheduleExchange

/-! A linear projection that agrees on every reset target is insensitive
to permutations of the fixed list of slices. -/

noncomputable section

set_option autoImplicit false

namespace SKEFTHawking.FinitePositiveKernel.GibbsReset

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- If all targets agree after a complex-linear projection, the projected
final state agrees for all orders of the same slices on any common input. -/
theorem evolveResetSchedule_map_eq_of_perm (project : Matrix n n ℂ →ₗ[ℂ] W)
    (target : W) {left right : List (ResetSlice n)} (hPerm : left.Perm right) :
    (∀ s ∈ left, project s.target = target) →
    ∀ X : Matrix n n ℂ,
      project (evolveResetSchedule left X) = project (evolveResetSchedule right X) := by
  induction hPerm with
  | nil => intro _ X; rfl
  | cons s _ ih =>
      intro h X
      exact ih (fun t ht => h t (List.mem_cons_of_mem s ht)) (s.evolve X)
  | swap s t post =>
      intro h X
      have ht : project t.target = target := h t List.mem_cons_self
      have hs : project s.target = target := h s (List.mem_cons_of_mem t List.mem_cons_self)
      have exchange := evolveResetSchedule_adjacent_exchange [] post t s X
      simp only [List.nil_append] at exchange
      apply sub_eq_zero.mp
      rw [← map_sub, exchange, map_smul, map_sub, hs, ht, sub_self, smul_zero]
  | trans hleft _ ihLeft ihRight =>
      intro h X
      exact (ihLeft h X).trans (ihRight (fun s hs => h s (hleft.mem_iff.mpr hs)) X)

end SKEFTHawking.FinitePositiveKernel.GibbsReset
