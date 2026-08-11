# L2 apex retrofit (backfill) — the only Letter with a deep closure, and every disclosure verifies

**Date:** 2026-08-07 · Backfill: L2 declared its apexes before this retrofit began, so it had no
FINDINGS doc. Written now so **DONE item 2 holds for all 21 bundles**, not just the seventeen.

**Read IN FULL before anything was written,** per ADR-010 C4: `papers/L2/paper_draft.tex`
(489 lines, every line), `bundle_metadata.json`, and — applying the bundle-name probe from the L3
correction — `papers/D2/paper_draft.tex` searched for **"L2"**.

---

## 1. What is declared

**8 apexes → 430 declarations across 40 modules, depth 14, 3 private truncations.**

⚠️ **The only Letter in the portfolio with a deep closure.** L1 is depth 1, E2 depth 1, L3 and E1
depth 2 — **L2 is depth 14 over 40 modules**, from a four-page PRL.

**The reason is visible in the draft and is not a defect.** Seven of the eight apexes are shallow
(fermion counting, the eta shift, the Ext ranks); the eighth, `SmoothSpinManifold4.rokhlin`, pulls
in the entire number-theoretic tower L2 built to discharge `8 ∣ σ` without assuming it —
`HasseMinkowski*` (4 modules), `HilbertSymbol*` (4), `Theta*` (4), `LatticeSig*`/`Lattice*` (7),
`MultivarPoisson*` (2), `VanDerBlijReduction`, `RokhlinFromHM`, `RokhlinHMDischarge`. **A single
apex carries ~90% of the closure**, and the draft says so: the `8 ∣ σ` half is *"machine-checked
… by van der Blij classification — Hasse–Minkowski and theta-modularity, both discharged."*

---

## 1b. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

| field | statement |
|---|---|
| **Audience** | Particle theorists who care about the family puzzle, and the anomaly/bordism community around Wang and García-Etxebarria–Montero. Secondarily formalization readers, since the claim is *machine-checked*. |
| **Venue** | PRL, per the metadata. Right register: one arithmetic identity, `24 = 8 × 3`, and one conclusion. |
| **The claim only this container can make** | **That the three-generation count follows from two independently machine-checked ingredients, and that the same chain yields a formal argument for right-handed neutrinos.** `c₋ = 8N_f` from a Lean-verified Weyl count, `24 ∣ c₋` from the Dedekind-eta shift through Mathlib's `Complex.exp_add`, hence `3 ∣ N_f`; and without `ν_R` the charge `c₋ = 15/2` is fractional, which L2 discharges by *constructing a contradiction from `15/2 ∈ ℕ`*. Its deep companion D2 develops the algebraic core; only L2 puts the four-page arithmetic on the table. |
| **Substrate** | 40 modules, 430 declarations, depth 14: `WangBridge`, `SMFermionData`, `GenerationConstraint`, `A1{Ring,Resolution,Ext,ExtSubstantive}`, `SpinRokhlinInterface`, and the Hasse–Minkowski / theta-modularity / lattice-signature tower beneath `rokhlin`. |
| **Honest size vs charter** | 489 lines against a PRL. Third bundle at or near charter, after L1 and L3 — **all three are Letters**, which is the pattern. |
| **Boundary failure?** | **No, but it is the closest call in the portfolio.** `L2 ∩ D2 = 391` — **91% of L2's closure lies inside D2's.** That is a *declared* splash/deep relationship (§2), not a boundary failure: L2's purpose is statable on its own substrate, and it is D2 that says L2 compresses the material. |

---

## 2. ✅ Fourth declared splash/deep pair — D2 says it in its own words

Running the bundle-name probe on D2:

> *"The **PRL splash companion** [L2] **compresses this material to four pages**; here we expose the
> algebraic core."*
>
> and, on a hypothesis L2 lists as open: *"the dimension-equality identity substantively discharges
> the H2 hypothesis **listed as open in the L2 splash** at the dimensional level."*
>
> and in D2's header: *"L2 PRL splash already extracted from paper10 §2 content."*

**Fourth pair after L1/D3, L3/D3, E1+E2/D1.** The 391-declaration overlap and the 4 shared apexes
are the design. **Nothing reassigned.**

⚠️ **And D2 records a one-way improvement**: a hypothesis L2 still carries as open, D2 has since
discharged at the dimensional level. **A splash and its deep companion can drift apart in
*hypothesis status*, not just in length** — the deep paper moved and the Letter has not been
updated. Recorded here because it is the same class as TODO-D20 (E2 corrected, E1 not): **shared
content diverging because only one member of a declared pair was revised.**

---

## 3. ✅ Every disclosure verifies — including the `native_decide` one, at exact membership

L2 is the only bundle whose closure carries `native_decide` **and** whose draft says which theorems
use it. Measured with the validated `axiom_deps_project` instrument:

| L2's abstract says | measured |
|---|---|
| *"chain-complex property `dₙ·dₙ₊₁ = 0` for `n=1,…,4` via `native_decide` on explicit `𝔽₂` matrices"* | **exactly 6 carriers**: `d1_d2_zero`, `d2_d3_zero`, `d3_d4_zero`, `d4_d5_zero`, `chain_complex_property`, `ext_computation_summary` ✓ |
| *"`\axiomcount` axioms"* (= 0) | **zero declarations of kind `axiom`** project-wide ✓ |
| *"the formerly asserted `gapped_interface_axiom` is now a tracked Prop `TPFConjecture`"* | `gapped_interface_axiom` **absent**; `TPFConjecture` present as a **`def`** ✓ |
| closure axiom set | exactly `{propext, Classical.choice, Quot.sound}` ✓ |

⚠️ **L2 declares a `native_decide`-carrying theorem (`ext_computation_summary`) as an apex and
discloses the fact in the abstract.** That is the correct handling, and it is the direct opposite
of the error V26 corrected — where *I* claimed no load-bearing `native_decide` existed anywhere.

---

## 4. What L2 gets right — the strongest conditional-claim discipline in the corpus

- **It states why its own headline cannot be unconditional, with a counterexample**: `16 ∣ σ` is
  *"not claimed unconditional — necessarily so, since `16 ∣ σ` is false for general even-unimodular
  forms (Freedman's `E₈`, `σ = 8`)."* **Said three times** — abstract, §3, §4 — each time with the
  counterexample attached.
- **The conditional's single input is isolated and named**: the machine-checked half `8 ∣ σ`, plus
  *"the single topological factor-of-two input `2 ∣ σ/8` … carried as a disclosed tracked
  hypothesis."*
- **Textbook inputs are classified as a library gap, not an open problem**: ko cohomology, ASS
  convergence and ABP splitting are *"established results … tracked pending Mathlib formalization
  of the requisite infrastructure (spectra, the Adams spectral sequence, Thom spectra) — a library
  gap, not an open problem."*
- **The division of labour with the citation is stated explicitly**: the change-of-rings adjunction
  *"enters as a standard Cartan–Eilenberg homological-algebra theorem (textbook content; the
  algebraic Ext-over-`A(1)` kernel above is what this Letter contributes at the machine-checked
  level)."*
- **An unformalized suggestion is labelled as one**: *"The Kitaev relationship to (iv) is
  suggestive but not formalized."*
- **The `24` is given both origins** — analytic (`η`'s `q`-expansion) and physical (Casimir
  `E₀ = −c/24`, `ζ(−1) = −1/12`) — and the arithmetic split is stated as separating mathematical
  from physical input: *"their ratio is the generation constraint."*
- **A no-project-lemma claim about a Mathlib reduction**: the eta shift reduces to
  `Complex.exp_add`, *"no project-originated lemma is required."*
- **An upgrade is described as an upgrade**: `sixteen_convergence_unconditional`'s `16 ∣ σ`
  conjunct *"is now this interface theorem rather than a bare assumed input."*

---

## 5. Also observed

- **Three pin-drift sites** (`v4.29.1`, `\mathlibcommit = 5e932f97`) — the registered
  `paper_toolchain_pin_drift` check already names **L2:12, 387, 396**. Existing coverage; nothing
  filed, nothing built.
- **The count macros are used for a *library-state* claim** — *"library state: `\totaltheorems`
  theorems across `\leanmodules` modules, `\axiomcount` axioms"* — which is project-scoped and
  therefore **correct usage**, like E1's and unlike D1's and D5's. Fourth data point for the
  restated TODO-D9.
- **A build-time claim not verified here**: *"builds in ∼30 s on commodity hardware."* Not measured;
  measuring it is not a closure question. Stated per C4 rather than glossed.

---

## 6. Ledger

| artifact | change |
|---|---|
| `docs/audits/2026-08-07-l2-retrofit/FINDINGS.md` | **created** — DONE item 2 backfilled for L2 |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V40 |

No metadata changed: L2's 8 apexes were already declared and all resolve. Gate unchanged —
`UNDECLARED_APEX_CEILING` is already 0.
