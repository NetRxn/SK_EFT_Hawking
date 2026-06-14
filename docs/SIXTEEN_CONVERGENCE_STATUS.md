# The "16 Convergence" — proved / hypothesis / enumerated / refuted

**Canonical framing doc (created 2026-06-13).** Purpose: a single quotable source separating what the project
has *proved* about the recurring number 16 from what it *carries as a hypothesis*, what it merely *enumerates*,
and what it has *proved is not true*. Companion to `RokhlinBridge.lean` (whose own docstring already enforces
"enumeration, not unification") and `RokhlinArfNoGo.lean` (the machine-checked lattice-Arf no-go). The
formalization plan for a *genuine* common-origin proof is `docs/roadmaps/Phase5qE_SixteenConvergence_Roadmap.md`.

> **One-line rule for all papers/talks:** the load-bearing physics result is **three generations**, and it does
> **not** depend on the "16 convergence." Describe the convergence as a **formal enumeration** connected in the
> literature by spin-bordism — never as a "formally verified unification." (`RokhlinBridge.lean:108`.)

---

## 1. The load-bearing result (does NOT use the convergence)

Three generations follows from a short, self-standing chain — exactly one "16" enters, via the fermion count:

1. **SM fermion content** ⟹ `c₋ = 8·N_f` (16 Weyl/generation × ½ = 8). — `c_minus_eight_N_f` (WangBridge), kernel-pure.
2. **Modular invariance** of the Dedekind-η framing anomaly ⟹ `24 ∣ c₋`. — physics premise (consistency requirement).
3. Arithmetic: `24 ∣ 8·N_f ⟺ 3 ∣ N_f`. — `generation_constraint_iff`, proved by `omega`.

Rokhlin's 16, the ℤ₁₆ anomaly, and Kitaev's 16 appear **nowhere** in this proof (verified: `generation_constraint_iff`'s
import closure never touches the Rokhlin / lattice / Arf machinery; blast radius of the whole Rokhlin leg = narrative-only).

## 2. What `sixteen_convergence_full` literally is — an ENUMERATION

Unfolded, the theorem is the conjunction: `(SM count = 16) ∧ (16 ≡ 0 mod 16, a tautology) ∧ (the Rokhlin
hypothesis you fed in) ∧ (SM count = 16 again, retyped)`. Its own docstring (`RokhlinBridge.lean:100`):

> *"The theorem records, in the proof assistant, that the numeral '16' appears in these four contexts. It does
> NOT demonstrate a common origin… Papers citing this theorem MUST describe it as a formal enumeration, not a
> formal unification… never 'formally verified convergence'."*

## 3. The four 16s — by status

| Facet | What the 16 actually is | Status |
|---|---|---|
| **SM Weyl count = 16** | the **16 of Spin(10)** (irreducible real spinor; 10⊕5̄⊕1, the 1 = ν_R) | ✅ **proved** (`total_components_with_nu_R`); the only 16 that feeds the physics. **Branching realized** (Phase 5q.E W2, `Spin10Sixteen.lean`): the SU(5) decomposition `16 → 10 ⊕ 5̄ ⊕ 1` is machine-checked at the dimension/assignment level — multiplets are even exterior powers Λ⁰,Λ²,Λ⁴ (`C(5,0)+C(5,2)+C(5,4)=2⁴`), Georgi–Glashow assignment is a verified partition. (Constructing the spinor *module* is still Mathlib-absent.) |
| **ℤ₁₆ global anomaly** | SM Dai–Freed anomaly for the spin/ℤ₄ structure is ℤ₁₆-valued; 16 fermions cancel it (GEM 2018) | ⚠️ **cited input** — bordism `= ℤ₁₆` not formalized; the arithmetic consequence (16-fermion cancellation with ν_R) IS proved (`z16_anomaly_always_cancels_with_nu_R`, `z16_anomaly_without_nu_R`) |
| **Rokhlin `16∣σ`** | Ω₄^Spin ≅ ℤ (K3, σ=−16); Dirac index even | ⚠️ **8∣σ proved** (van der Blij) **+ tracked hypothesis** `topo : 2∣σ/8` (geometric Â-genus/Guillou–Marin factor) |
| **Kitaev 16-fold way** | 16 (2+1)D topological-SC phases by chiral central charge mod 16 | ✅ **central-charge ℤ₁₆ formalized as a faithful character** (Phase 5q.E W1, `KitaevSixteenFold.lean`): `c₋(ν)=ν/2`, the 16 charges pairwise-distinct mod 8 (`kitaevCentralCharge_faithful` — *the* 16-fold statement), bosonic index-8 sub-sector, SM lands on the trivial class. (The *categorical* 16-fold-way / super-modular ℤ₁₆-torsor structure is still cited, not formalized.) |

## 3.5 The explicit-maps upgrade (Phase 5q.E, 2026-06-13) — enumeration with explicit maps

Phase 5q.E replaces the bare enumeration (`sixteen_convergence_full`, whose one conjunct is the
tautology `(16:ZMod 16)=0`) with **explicit faithful maps** for the buildable facets, and proves
the convergence **constrains, it does not derive** — the rigorous answer to "is 'all the same 16'
just coincidence-spotting?":

- **Faithful Kitaev character** (`KitaevSixteenFold.lean`): the 16 phases carry 16 *genuinely
  distinct* central charges mod 8 (`kitaevCentralCharge_faithful`). So the shared ℤ₁₆ has 16
  physically-distinct realizations.
- **SM is one of sixteen** (`SixteenConvergenceExplicit.sm_trivial_among_sixteen_distinct`): the SM
  realizes the *trivial* element (class 0), but `ν=1` is provably a different phase — so the ℤ₁₆
  **does not single out the SM**. It constrains; it does not derive.
- **Explicit facet-1 → facet-4 composition** (`sm_count_trivializes_z16`): the Spin(10) branching
  sum `dim(10)+dim(5̄)+dim(1)=16` is *the* integer whose Kitaev class is `0` — a genuine
  composition of explicit maps, not a numerical coincidence of two 16s.

**Still NOT proved (the wall):** the genuine *identification* of the facets' ℤ₁₆s as one bordism
invariant under the Smith homomorphism (computed `Ω₄^{Pin⁺}/Ω₅^{Spin-ℤ₄} ≅ ℤ₁₆` + the Dai–Freed
functor) is Mathlib-absent (Phase 5q.E roadmap §"Walls"). The explicit maps are algebraic shadows,
not the bordism identification. None of this touches the independent 3-generation headline.

## 4. Proved NOT true (the no-gos — what the discipline caught)

- **Lattice Arf bridge** `σ/8 ≡ Arf(redQuad) mod 2` — **FALSE** (`RokhlinArfNoGo.lean`; E₈: Arf=0, σ/8=1; Arf(redQuad)≡0 on every even-unimodular lattice). The genuine σ/8↔Arf is the *geometric* Guillou–Marin Arf on a characteristic surface, not a lattice invariant.
- **`σ ≡ 0 mod 16` for general even-unimodular lattices** — **FALSE** (E₈, σ=8; `rokhlin_strictly_stronger`, `algebraic_bound_is_8_not_16`). This is *why* Rokhlin needs a smooth-topological input.
- **Cautionary precedent:** a claimed `dim Ext⁴_{A(1)} = 16` was, on computation, actually **3** (`RokhlinBridge.lean:280`). A fifth "16" that evaporated — same pattern as the Arf bridge.

## 5. What a genuine convergence would mean (physics)

Underneath, all four 16s are the **mod-16 structure of real K-theory / spin bordism near dim 4** — Bott
periodicity 8 doubled by the quaternionic/reality structure of spinors ("8×2"). At that level a convergence is
not a discovery; it's "it's all KO-theory."

The *meaningful* level is **anomaly theory** (anomaly in d = invertible term in d+1 = bordism invariant). "The
same 16" would mean: **SM anomaly cancellation, which 4-manifolds are smooth-spin (Rokhlin), and (2+1)D
topological-matter classification (Kitaev) are governed by one ℤ₁₆ bordism invariant**, and 16 fermions/generation
are exactly what trivializes it. For the emergent-substrate thesis, the prize version: **the SM matter content
is a topological invariant of the emergent vacuum, not a tunable input** — anomaly inflow from a ℤ₁₆-SPT
substrate *forces* the boundary fermion content (the SymTFT picture, Phase 6r `SMMatterAsSymTFTBoundary`).

**Caveats (load-bearing):** a shared bordism invariant **constrains, it does not derive** (many theories share
ℤ₁₆; it says nothing about couplings/masses/mixings); "all the same 16" is physics **only with the explicit maps**
(Smith homomorphism + the bordism isomorphisms) — the map is the content, the numeral is not; and even proved,
it is a classification statement, not a dynamical mechanism.

## 6. How to say it (one breath)

> *"Three generations follows from the Standard Model's 16 Weyl fermions per generation plus modular invariance —
> that part is machine-verified. Separately, the number 16 recurs in Rokhlin's theorem, the ℤ₁₆ global anomaly,
> and Kitaev's classification; the literature ties those together through spin-bordism, and we've formally
> recorded each occurrence — but we have not formally proved they share a single origin, and we don't claim to."*
