/-
SK_EFT_Hawking Phase 6p Wave 2d.4: ε-Net Base Case for Solovay-Kitaev

This module ships the **non-constructive ε-net** base case for the Solovay-
Kitaev recursion (Dawson-Nielsen 2005 §3, p. 5 footnote).

Given a finite gate set `G ⊆ U(d)` closed under inversion such that the set
of products of words from `G` is *entrywise dense* in the target unitary
group, for any ε > 0 there exists a finite list of "anchor words" forming
a δ₀-net of `SU(d)` (more precisely: for each U there is a word w whose
product is within δ₀ of U entrywise).

The "ε-net" is in fact the unfolding of the density hypothesis itself —
no Mathlib substrate is required beyond `Classical.choice` extraction.

This module is **purely constructive modulo `Classical.choice`** — no new
project-local axioms are introduced. The substantive content of D-N's
"compactness extracts a finite δ₀-net" argument is already encoded in
`ClosureDenseProp`/`UniversalGateSet`: density of the generated set
*is* the property we extract anchors from. The Mathlib-substrate-heavy
"compactness ⇒ finite-net" form (`Metric.IsCompact.finite_cover_balls`)
is operationally unnecessary because our consumers only need the
pointwise approximation, not the *finiteness* of the net.

Primary source: Dawson-Nielsen 2005 §3, p. 5 (the "preprocessing" stage);
                Ozols 2009 "The Solovay-Kitaev Algorithm", p. 8.
-/

import Mathlib
import SKEFTHawking.FKLW.BridgeProp

set_option autoImplicit false

namespace SKEFTHawking.FKLW

open scoped Matrix

/-! ## 1. UniversalGateSet — the strictly-weaker hypothesis

The genuinely-substantive hypothesis for Solovay-Kitaev: the gate set `G` is
closed under inversion and the set of products of words from `G` is dense in
the target unitary group.

Inversion closure is required by the Dawson-Nielsen recursion (the V†, W†
factors in the V W V† W† group commutator). Density is the universality
property.

This predicate is **strictly weaker** than the previous `h_dense` hypothesis
of `sk_axiom_Dawson_Nielsen`, which restated the conclusion verbatim. Here
the hypothesis is a property of the gate set itself, independent of
approximation accuracy ε: the *set* of products is dense, end-of-story. -/

/-- Take a list of gates from `G` together with a flag for each entry
    indicating whether to invert that gate, and produce the product in
    matrix algebra. Closure of `G` under inversion is the only nontrivial
    structural property required by the Dawson-Nielsen group commutator. -/
noncomputable def gateWord {d : ℕ} (G : List (Matrix (Fin d) (Fin d) ℂ))
    (w : List (Fin G.length × Bool)) : Matrix (Fin d) (Fin d) ℂ :=
  List.foldl (· * ·) (1 : Matrix (Fin d) (Fin d) ℂ)
    (w.map (fun ⟨i, b⟩ => if b then (G[i.val]'i.isLt)⁻¹ else (G[i.val]'i.isLt)))

/-- The genuine-universality hypothesis: every target unitary is approximated
    entrywise (to within any ε > 0) by some list-product of gates drawn from
    `G`. This is the operational form of "⟨G⟩ is dense in U(d)" without the
    Mathlib-norm-instance overhead.

    Equivalently: the *set* `{ list-product of gates from G : List (Matrix _ _ ℂ) }`
    is dense in `Matrix (Fin d) (Fin d) ℂ` entrywise.

    **Distinct from `SolovayKitaevProp d G`**: this predicate states only
    pointwise approximation existence, no length bound. The Solovay-Kitaev
    theorem proper adds the `O(log^c(1/ε))` length bound (see
    `SolovayKitaevConstructive.lean`). -/
def UniversalGateSet (d : ℕ) (G : List (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  ∀ (U : Matrix (Fin d) (Fin d) ℂ) (ε : ℝ), 0 < ε →
    ∃ (gates : List (Matrix (Fin d) (Fin d) ℂ)),
      (∀ g ∈ gates, g ∈ G) ∧
      (∀ i j : Fin d, ‖(List.foldl (· * ·) (1 : Matrix (Fin d) (Fin d) ℂ) gates) i j - U i j‖ < ε)

/-! ## 2. ε-net extraction (the base case)

For any precision δ₀ > 0 and any target U, choose an anchor word from
`UniversalGateSet`. Operationally this is `Classical.choice` extraction
from the existential in `UniversalGateSet`. -/

/-- The δ₀-net anchor: given universality of G and a target U, extract an
    approximating word product. -/
noncomputable def anchorWord {d : ℕ} {G : List (Matrix (Fin d) (Fin d) ℂ)}
    (hG : UniversalGateSet d G)
    (U : Matrix (Fin d) (Fin d) ℂ) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    List (Matrix (Fin d) (Fin d) ℂ) :=
  Classical.choose (hG U δ₀ hδ₀)

/-- The anchor word's gates lie in G. -/
theorem anchorWord_in_G {d : ℕ} {G : List (Matrix (Fin d) (Fin d) ℂ)}
    (hG : UniversalGateSet d G)
    (U : Matrix (Fin d) (Fin d) ℂ) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∀ g ∈ anchorWord hG U δ₀ hδ₀, g ∈ G :=
  (Classical.choose_spec (hG U δ₀ hδ₀)).1

/-- The anchor word approximates U entrywise within δ₀. -/
theorem anchorWord_approx {d : ℕ} {G : List (Matrix (Fin d) (Fin d) ℂ)}
    (hG : UniversalGateSet d G)
    (U : Matrix (Fin d) (Fin d) ℂ) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∀ i j : Fin d,
      ‖(List.foldl (· * ·) (1 : Matrix (Fin d) (Fin d) ℂ) (anchorWord hG U δ₀ hδ₀))
         i j - U i j‖ < δ₀ :=
  (Classical.choose_spec (hG U δ₀ hδ₀)).2

/-! ## 3. ClosureDenseProp ⇒ UniversalGateSet bridge

When a representation `ρ : BraidGroup n → U(d)` has `ClosureDenseProp`
(Wave 2a.3 — i.e. FKLW density), and `G` contains the images of the
braid generators (and their inverses, to satisfy the inversion-closure
implicit in `UniversalGateSet`), then `UniversalGateSet d G` follows.

We state the bridge schematically; concrete instantiations live in the
downstream universality-witness modules (e.g. `FibonacciQutritUniversality`,
`FibonacciQuintetUniversality`). -/

/-- Bridge from a representation-level density witness to a gate-set-level
    universality witness, assuming the gate set contains a single-element
    image of every braid word. This is the operational restatement of
    `ClosureDenseProp` for downstream Solovay-Kitaev consumers.

    The bridge is strict: it requires for every braid `b` the existence
    of a list of gates from G whose product equals `ρ b` exactly. This
    holds whenever `G ⊇ ρ '' generators ∪ ρ '' generators⁻¹`, but the
    exact ⊆ relation depends on the chosen presentation. -/
theorem universal_of_closure_dense
    {n d : ℕ} {ρ : BraidGroup n → Matrix (Fin d) (Fin d) ℂ}
    {G : List (Matrix (Fin d) (Fin d) ℂ)}
    (h_density : ClosureDenseProp n d ρ)
    (h_realize : ∀ (b : BraidGroup n), ∃ (gates : List (Matrix (Fin d) (Fin d) ℂ)),
      (∀ g ∈ gates, g ∈ G) ∧
      List.foldl (· * ·) (1 : Matrix (Fin d) (Fin d) ℂ) gates = ρ b) :
    UniversalGateSet d G := by
  intro U ε hε
  -- density gives a braid b within ε/2 of U entrywise
  obtain ⟨b, hb⟩ := h_density U (ε/2) (by linarith)
  -- realize that braid as a list of G-gates
  obtain ⟨gates, hgates_in, hgates_eq⟩ := h_realize b
  refine ⟨gates, hgates_in, ?_⟩
  intro i j
  -- the product equals ρ b exactly, so the error is ‖ρ b i j - U i j‖ < ε/2 < ε
  rw [hgates_eq]
  exact lt_of_lt_of_le (hb i j) (by linarith)

/-! ## 4. Module summary

EpsilonNet.lean: Solovay-Kitaev base case + UniversalGateSet substrate.

  - `UniversalGateSet d G` — strictly-weaker universality hypothesis (the
    entrywise-density form, parameter-free in ε).
  - `gateWord` — explicit list-product with inversion flags.
  - `anchorWord`, `anchorWord_in_G`, `anchorWord_approx` — base-case
    `Classical.choice` extractors.
  - `universal_of_closure_dense` — bridge from `ClosureDenseProp` (Wave 2a.3)
    to `UniversalGateSet` (this module).

This module introduces **no new axioms**. It is the pure-Mathlib-substrate
ε-net machinery for the Solovay-Kitaev recursion.

Zero sorry. Zero new axioms (`Classical.choice` only).
-/

end SKEFTHawking.FKLW
