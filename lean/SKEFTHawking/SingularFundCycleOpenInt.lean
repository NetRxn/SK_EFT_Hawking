/-
# Phase 5q.H (E1 integral topology) — the fundamental cycle of a compact in an open (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularFundCycleOpen`'s `exists_fundCycle_in_open`: a relative cycle
`z` for `(M, Kᶜ)` (a `hasFundClassInt` representative `μ_K ∈ Hₙ(M|K;ℤ)`) has, after subdivision, a
representative **supported in any open `W ⊇ K`** — `z_W ∈ subspaceChainsInt W`, still a relative cycle,
and rel-homologous to `z`. This is the geometric input making `relativeDualityKInt` instantiable in the
open-cover PD induction (Hatcher 3.36): the fund cycle of `K` lives in `C(W;ℤ)`, so the cap lands in
`H_{n-k}(sub W;ℤ)`.

The `{W, Kᶜ}` excisiveness (`interiors_cover_of_compact_subset_open`) is coefficient-free — reused from
the mod-2 module. The one genuine ℤ-difference is the same `+`→`−` seen in `KCycleInt`: the mod-2
`mk z + mk(Sdᵐz) ∈ relBoundaries` is the honest DIFFERENCE `mk z − mk(Sdᵐz)` over ℤ (the signed
subdivision homotopy `∂Dₘ = 1 − Sdᵐ − Dₘ∂`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularFundCycleOpen

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularExcisionInt
open SKEFTHawking.SingularSubdivisionInt
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.SingularFundCycleOpen (interiors_cover_of_compact_subset_open)

namespace SKEFTHawking.SingularFundCycleOpenInt

variable {X : TopCat}

/-- **Subdivision rel-homologousness** (integral, `−` form): the relative class of `c` minus that of its
`m`-fold subdivision `Sdᵐ c` is a relative boundary. Witness `Dₘ c` (`iterHomotopyInt`), via the signed
homotopy `∂(Dₘc) = c − Sdᵐc − Dₘ(∂c)` with `Dₘ(∂c) ∈ C(A)` (so its relative class vanishes). Integral
mirror of `SingularExcision.relative_add_singularSd_iterate_mem_relBoundaries` (mod-2 `+` → ℤ `−`). -/
theorem relative_sub_singularSd_iterate_mem_relBoundariesInt {A : Set ↑X} {n : ℕ}
    {c : SingularChainInt X (n + 1)} (hc : chainBoundary X n c ∈ subspaceChainsInt A n) (m : ℕ) :
    RelativeChainInt.mk A (n + 1) c
        - RelativeChainInt.mk A (n + 1) ((⇑(singularSdInt X (n + 1)))^[m] c)
      ∈ relBoundariesInt A (n + 1) := by
  refine ⟨RelativeChainInt.mk A (n + 2) (iterHomotopyInt X (n + 1) m c), ?_⟩
  rw [relBoundaryInt_mk]
  have hsd : chainBoundary X (n + 1) (iterHomotopyInt X (n + 1) m c)
      = (c - (⇑(singularSdInt X (n + 1)))^[m] c) - iterHomotopyInt X n m (chainBoundary X n c) := by
    rw [eq_sub_iff_add_eq]; exact iterHomotopyInt_chainHomotopy X m n c
  have hzero : RelativeChainInt.mk A (n + 1) (iterHomotopyInt X n m (chainBoundary X n c)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (iterHomotopyInt_mem_subspaceChainsInt hc m)
  rw [hsd, show RelativeChainInt.mk A (n + 1)
        ((c - (⇑(singularSdInt X (n + 1)))^[m] c) - iterHomotopyInt X n m (chainBoundary X n c))
      = (RelativeChainInt.mk A (n + 1) c
          - RelativeChainInt.mk A (n + 1) ((⇑(singularSdInt X (n + 1)))^[m] c))
        - RelativeChainInt.mk A (n + 1) (iterHomotopyInt X n m (chainBoundary X n c)) from rfl,
    hzero, sub_zero]

/-- **The fundamental cycle of a compact in an open** (integral): a relative cycle `z` for `(M, Kᶜ)`
has, after subdivision, a representative supported in any open `W ⊇ K`, still a relative cycle and
rel-homologous to `z`. Integral mirror of `SingularFundCycleOpen.exists_fundCycle_in_open`. -/
theorem exists_fundCycle_in_openInt [T2Space ↑X] {K W : Set ↑X} (hK : IsCompact K) (hW : IsOpen W)
    (hKW : K ⊆ W) {n : ℕ} {z : SingularChainInt X (n + 1)}
    (hz : chainBoundary X n z ∈ subspaceChainsInt Kᶜ n) :
    ∃ zW : SingularChainInt X (n + 1), zW ∈ subspaceChainsInt W (n + 1) ∧
      chainBoundary X n zW ∈ subspaceChainsInt Kᶜ n ∧
      RelativeChainInt.mk Kᶜ (n + 1) z - RelativeChainInt.mk Kᶜ (n + 1) zW
        ∈ relBoundariesInt Kᶜ (n + 1) := by
  obtain ⟨m, hm⟩ :=
    exists_iterate_smallChainsInt (interiors_cover_of_compact_subset_open hK hW hKW) z
  obtain ⟨zW, hzW, zKc, hzKc, hsplit⟩ := Submodule.mem_sup.mp (smallChainsInt_two_le W Kᶜ (n + 1) hm)
  refine ⟨zW, hzW, ?_, ?_⟩
  · have hbd_sd : chainBoundary X n ((⇑(singularSdInt X (n + 1)))^[m] z) ∈ subspaceChainsInt Kᶜ n := by
      rw [singularSdInt_iterate_chainBoundary]
      exact singularSdInt_iterate_mem_subspaceChainsInt hz m
    have heq : chainBoundary X n zW
        = chainBoundary X n ((⇑(singularSdInt X (n + 1)))^[m] z) - chainBoundary X n zKc :=
      eq_sub_of_add_eq (by rw [← map_add, hsplit])
    rw [heq]
    exact Submodule.sub_mem _ hbd_sd (chainBoundary_mem_subspaceChainsInt Kᶜ n zKc hzKc)
  · have hrel := relative_sub_singularSd_iterate_mem_relBoundariesInt (A := Kᶜ) hz m
    have hmk : RelativeChainInt.mk Kᶜ (n + 1) ((⇑(singularSdInt X (n + 1)))^[m] z)
        = RelativeChainInt.mk Kᶜ (n + 1) zW := by
      rw [← hsplit]
      refine (Submodule.Quotient.eq _).mpr ?_
      rw [add_sub_cancel_left]
      exact hzKc
    rwa [hmk] at hrel

end SKEFTHawking.SingularFundCycleOpenInt
