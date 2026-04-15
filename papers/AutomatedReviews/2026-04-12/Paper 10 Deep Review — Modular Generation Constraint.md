# Paper 10 Deep Review: *From Modular Forms to Generation Counting*
**File:** `papers/paper10_modular_generation/paper_draft.tex` — Target journal: PRD (Letter format)
**Review date:** April 11, 2026. All source files read live from the repository.

***

## Executive Summary

Paper 10 has a genuinely sound mathematical core: the conditional derivation `24 | 8N_f ⟹ 3 | N_f` is tight arithmetic, correctly formalized, and the Lean proofs for that specific chain are clean. The Ext computation over A(1) is the paper's most impressive independent contribution. However, the paper contains four categories of problems that require addressing before submission: (1) a fundamental logical gap in the main claim's justification chain, (2) citation errors and missing key references, (3) an overstated "16 convergence" section, and (4) presentation issues specific to the PRD Letters format. Several physics claims either exceed what the cited sources support or rest on hidden physical assumptions not disclosed to the reader.

***

## Section 1 — The Core Claim: Is It Actually Derived?

### The Main Theorem Is Correct But Conditional

The central result — `N_f ≡ 0 (mod 3)` — follows cleanly from two inputs: (A) `c_- = 8N_f` and (B) `24 | c_-`. The arithmetic is unimpeachable. What requires scrutiny is whether each input is "derived" as the abstract claims, or whether they each rest on non-trivial physical assumptions treated as axioms.

**Input A: `c_- = 8N_f` — partially derived, but with a hidden assumption.**

The paper correctly derives `c_- = 8` from the SM fermion table (16 components × 1/2) via the Alvarez-Gaumé–Witten formula for the chiral central charge upon dimensional reduction to 2D. **The gap:** the dimensional reduction itself — collapsing a 4D QFT to a 2D theory on a circle — is not derived; it is Wang (2024)'s proposed mechanism. Wang's abstract states "we propose a novel solution" and explicitly notes that "the dimensional reduction process, although not necessary, is sufficiently supported by the ℤ₁₆ class Smith homomorphism." Paper 10 presents this as a derivation without disclosing that it is a proposal contingent on a specific dimensional reduction scheme. The paper's abstract says `c_- = 8N_f` is "derived ... not axiomatized" — but the derivation rests on Wang's proposed framework. This is an epistemic overstatement that a PRD referee will catch.

**Input B: `24 | c_-` — sound in the modular forms sector, but the physics bridge is implicit.**

The Lean proof that `e^{2πic/24} = 1 ↔ 24 | c` is correct Mathlib-verified mathematics. The physical claim that the SM's 2D reduced partition function must be modular invariant — specifically that it satisfies `Z(τ+1) = Z(τ)` rather than `Z(τ+1) = e^{2πic_-/24} Z(τ)` with a non-trivial phase — requires placing the theory on a spin 3-manifold with a specific framing (p₁-structure). This framing assumption is Wang's string bordism ℤ₂₄ class. The paper states the constraint follows from "the Dedekind eta function's modular transformation law" — technically true, but the reader is not told why the SM must satisfy modular invariance in this particular form. The physical assumption (spin manifold + framing) is buried in a single sentence: "fermion components per generation (not axiomatized). The framing anomaly..."

**Required fix:** Add one paragraph — ideally at the opening of Section 3 — stating explicitly:

> "The constraint `24 | c_-` applies to theories placed on spin 3-manifolds equipped with a framing (p₁-structure). The physical justification that the 3+1D Standard Model, upon dimensional reduction, satisfies this geometric condition follows Wang's argument via the string bordism ℤ₂₄ class [Wang2024]. This is a proposal, not a theorem proved from SM first principles; the present work formalizes the mathematical consequences of this proposal."

Without this, the paper claims to derive a constraint on the SM while concealing the physical assumption doing the real work.

***

## Section 2 — Citation Audit (Line by Line)

### `[Wang2024]` — ✅ Verified correct
- Cited as: *Phys. Rev. D* **110**, 125028 (2024), arXiv:2312.14928
- Title confirmed: *"Family Puzzle, Framing Topology, c₋=24 and 3(E₈)₁ Conformal Field Theories: 48/16 = 45/15 = 24/8 = 3"*
- Author confirmed: Juven Wang
- **Issue:** The paper cites Wang as evidence that `N_f = 3` is derived. Wang's own abstract says "we **propose** a novel solution." The word "derive" in Paper 10's abstract and Section 4 upgrades Wang's epistemic status. Fix: replace "derived" with "established" or "argued on topological grounds" in the introduction's framing of Wang 2024.

### `[AlvarezGaumeWitten1984]` — ✅ Verified correct
- Cited as: *Nucl. Phys. B* **234**, 269 (1984)
- INSPIRE confirms: volume 234, first page 269, year 1984, title "Gravitational Anomalies"
- The specific claim (each Weyl fermion contributes `c = 1/2` upon 2D reduction) is correctly sourced.

### `[GarciaEtxebarria2019]` — ✅ Verified correct
- Cited as: *JHEP* **08**, 003 (2019), arXiv:1808.00009
- Confirmed title: "Dai-Freed anomalies in particle physics"
- **Issue:** Paper 10 uses GE2019 to support the ℤ₁₆ anomaly and the "16 fermions requires ν_R" claim. GE2019's abstract confirms this. However, Paper 10 does not cite GE2019 for the specific statement "the ℤ₁₆ anomaly automatically vanishes for any N_f with ν_R" (`z16_anomaly_always_cancels_with_nu_R`). That theorem needs GE2019 as the physics source in the text (not just the Lean attribution), since a referee will ask where this result comes from.

### `[GrossJackiw1972]` — ✅ Verified correct
- *Phys. Rev. D* **6**, 477 (1972) — standard reference for perturbative anomaly cancellation generation-by-generation.

### `[Rademacher1973]` — ⚠️ Misattributed claim
- Rademacher, *Topics in Analytic Number Theory*, Springer, 1973 — this is a legitimate reference for the Dedekind eta function and its modular properties.
- **Problem:** Paper 10 cites Rademacher for the claim that the 24 in `η(τ+1) = e^{2πi/24}η(τ)` "traces to the zeta-function regularization `ζ(-1) = -1/12`." The connection between the eta function's q-expansion exponent 1/24, the Casimir energy `E_0 = -c/24`, and `ζ(-1) = -1/12` is a physics argument from CFT operator formalism (normally attributed to the conformal Ward identity on the torus), not to Rademacher's number theory text. Rademacher treats the eta function analytically; the "24 = 1/ζ(-1) from Casimir energy" physical interpretation appears in CFT textbooks, most cleanly in di Francesco et al. (*Conformal Field Theory*, Springer, 1997, §5.4). The current citation gives Rademacher credit for a physical insight he did not make.
- **Fix:** Replace `\cite{Rademacher1973}` with the CFT textbook or cite both: Rademacher for the number-theoretic identity and di Francesco et al. (or Ginsparg's *Applied Conformal Field Theory*, Les Houches 1988) for the physical interpretation.

### `[Rokhlin1952]` — ✅ Verified correct
- *Dokl. Akad. Nauk SSSR* **84**, 221 (1952) — standard citation for Rokhlin's theorem.
- **Note:** Rokhlin enters Paper 10 as a *hypothesis* in the Lean theorems (correctly disclosed in Section 4). The text correctly says "Rokhlin's theorem enters as a hypothesis (not an axiom) in the key theorems." This is intellectually honest.

### `[Kitaev2009]` — ✅ Verified correct but scope overstated
- Cited as: *AIP Conf. Proc.* **1134**, 22 (2009), DOI: 10.1063/1.3149495
- Full page range is pp. 22–30 (bibitem omits the end page — minor fix).
- **Scope problem:** Kitaev (2009) presents the tenfold periodic table using Bott periodicity. The ℤ₁₆ classification appears in its title as the 2D class-D entry in the table. However, Kitaev (2009) does not discuss the *interacting* ℤ₁₆ classification — that result (where interactions reduce ℤ to ℤ₁₆ in 2D class D) comes from Fidkowski-Kitaev (2010), *Phys. Rev. B* **81**, 134509. Paper 10's item 4 ("Kitaev 16-fold way: topological superconductors with time-reversal symmetry have a ℤ₁₆ classification") conflates two different results:
  - *Free-fermion* 2D class D: classified by ℤ (from Kitaev 2009)
  - *Interacting* 2D class D: classified by ℤ₁₆ (from Fidkowski-Kitaev 2010 for 1D, extended to 2D in subsequent works)
  The ℤ₁₆ that connects to Wang's argument is the *interacting* case. Kitaev 2009 alone does not establish ℤ₁₆. This needs `[FidkowskiKitaev2010]` added.

### `[Stolz1993]` — 🔴 Wrong paper
- Cited as: *Math. Ann.* **296**, 685 (1993)
- The Annals of Mathematics (Princeton) *Ann. Math.* **136**, 511 (1992) is Stolz's major paper "Simply connected manifolds of positive scalar curvature."
- *Mathematische Annalen* **296** (1993) exists as a journal volume, but a search finds no Stolz paper at page 685 in that volume. The Invent. Math. paper by Stolz is *Invent. Math.* **96**, 155 (1989) "Simply connected manifolds with positive scalar curvature"; there is no Math. Ann. 296, 685 Stolz paper in standard databases.
- **More critically:** Stolz 1993 is cited in the context of the machine-checked Ext computation over A(1) and the "algebraic content of the Rokhlin bound." The relevant work connecting spin cobordism, A(1), and the Rokhlin bound is *not* Stolz's positive scalar curvature work. The algebraically correct reference for the Adams spectral sequence computation detecting the Rokhlin bound via Ext over A(1) is Anderson-Brown-Peterson (1967) and the Beaudry-Campbell guide — both already in the bibliography. Stolz appears to be misplaced here. The paper should cite what is actually used: ABP 1967 for the spin cobordism ring structure and Beaudry-Campbell for the Adams spectral sequence methodology. Replace or remove `[Stolz1993]`.

### `[Adams1974]` — ✅ Verified correct
- Adams, *Stable Homotopy and Generalised Homology*, University of Chicago Press, 1974 — standard reference for ko cohomology and Adams spectral sequence.

### `[ABP1967]` — ⚠️ Page number wrong
- Cited as: *Ann. Math.* **86**, 256 (1967)
- Correct: Anderson, Brown, Peterson, "The structure of the spin cobordism ring," *Ann. Math.* **86**, pages **271–298** (1967), Issue 2.
- The bibitem has page 256 — that page belongs to a different article in the same issue (Goldschmidt, pp. 246–270). The ABP paper starts at **page 271**.
- **Fix:** Change `256` → `271` in `\bibitem{ABP1967}`. This is a verifiable error that any specialist will catch immediately.

### `[BeaudryCampbell]` — ✅ Verified correct
- *Contemp. Math.* **718**, 1 (2018) — confirmed: Beaudry and Campbell, "A guide for computing stable homotopy groups," appears at page 89 of Contemporary Mathematics vol. 718 (AMS, 2018).
- **Minor fix:** Bibitem lists page 1 but the actual start page in the volume is 89. Update: `\textbf{718}, 89 (2018)`.

***

## Section 3 — Physics Claims Against Published Literature

### 3.1 — The "16 Convergence" Section: Four Claims, Two Wrong

**Claim 1 — "SM fermion content: 16 Weyl components per generation"** — ✅ Correct *with ν_R*. But the paper's own table shows the ν_R row — so the paper is internally consistent. It correctly discloses the ν_R dependence in the `with/without ν_R` subsection. This is the best-handled part of the 16 narrative.

**Claim 2 — "ℤ₁₆ classification: the bordism group Ω₅^{Spin^{Z₄}} ≅ ℤ₁₆"** — ⚠️ Mathematically plausible but Lean proof is a tautology. The Lean theorem `dai_freed_spin_z4` is discharged as `Equiv.refl` (identity equivalence on ZMod 16), which proves nothing about the actual bordism group. The text says this is "formalized in RokhlinBridge.lean (14 theorems)" — but the formalization is a placeholder. The paper should say: "The cobordism group Ω₅^{Spin^{Z₄}} ≅ ℤ₁₆, established by Dai-Freed [GarciaEtxebarria2019], enters as a hypothesis in the Lean formalization."

**Claim 3 — "Rokhlin's theorem: σ(M) ≡ 0 (mod 16) for spin 4-manifolds"** — ✅ Correct, and correctly identified as a hypothesis in the Lean proofs. The K3 surface example (σ = -16) and E8 manifold example (σ = 8, not spin) are both correct.

**Claim 4 — "Kitaev 16-fold way: topological superconductors with time-reversal symmetry have a ℤ₁₆ classification"** — 🔴 Wrong symmetry class. Kitaev's AIP 2009 paper, which is what is cited, presents the tenfold table. The symmetry class with *time-reversal* symmetry T² = -1 and no charge conservation is class **DIII**, which has **ℤ** classification in 3D and **ℤ₂** in 2D (non-interacting). The ℤ₁₆ associated with Kitaev-type arguments appears in class **D** (no time-reversal, no charge conservation) in 2D, which is Kitaev's *p+ip* superconductor sixteenfold way. The description "with time-reversal symmetry" is therefore incorrect for the ℤ₁₆ entry. This will trigger an immediate correction from any condensed matter referee.
- **Fix:** Change "topological superconductors with time-reversal symmetry" → "2D topological superconductors in class D (no time-reversal symmetry), where anyonic excitations form a ℤ₁₆ classification (Kitaev's sixteenfold way)."

### 3.2 — "16 = 8 × 2, where 8 is the Bott period... and 2 is the Pfaffian factor"

This unification claim appears at the end of the "16 Convergence" section: *"ultimately tracing to Bott periodicity: 16 = 8 × 2, where 8 is the Bott period of π_n(O) and 2 is the Pfaffian factor (square root of the determinant for real structures)."*

This statement is physically motivated but is not a theorem — it is an interpretive heuristic. The Bott period is indeed 8 for `π_n(O)`. The factor of 2 from the Pfaffian is physically intuitive, but the precise statement that `16 = 8 × 2` "connects" all four appearances of 16 is not established in any cited reference. Wang (2024) connects them through cobordism morphisms (Smith homomorphism), not through "8 × 2 = 16." Kitaev's ℤ₁₆ in 2D class D comes from the anyonic structure of Ising-type phases, not from Bott period × Pfaffian.

**This is the most intellectually problematic sentence in the paper.** It presents as physical insight something that is numerological. A PRD referee in algebraic topology or condensed matter will flag it.

**Fix:** Replace with: "The appearance of 16 in all four contexts is non-accidental: Wang (2024) establishes the connection between the Rokhlin bound, the ℤ₁₆ anomaly, and the SM fermion count via the string bordism ℤ₂₄ class and Smith homomorphism. The relationship to the Kitaev classification is suggestive but has not been formalized here."

### 3.3 — The Fractional Central Charge Argument (`c_- = 15/2` without ν_R)

The Lean proof `central_charge_fractional_without_nu_R` proves that 15/2 ∉ ℕ — which is trivially true. The physics claim being made is that a *fractional* chiral central charge signals an anomaly (gravitational inconsistency). This is correct — a chiral central charge c_- ∉ ℤ for a 1+1D CFT indicates a gravitational anomaly. However, the argument requires that c_- must be an integer for consistency, which follows from modular invariance on spin surfaces — the same assumption used in the main argument. The paper presents this as an "independent argument for ν_R" — but it is not independent; it rests on the same framing assumption. The word "independent" should be removed or qualified.

### 3.4 — "Without ν_R, N_f = lcm(16,3) = 48 provides formal evidence for ν_R"

The logical structure here is: "If we observe N_f = 3 and the theory requires N_f = 48 without ν_R, then ν_R must exist." This is a valid argument by contradiction — *assuming* both constraints hold simultaneously. But the two constraints come from different physics: the ℤ₁₆ constraint comes from GE2019's Dai-Freed argument (which independently requires ν_R), and the mod-3 constraint comes from modular invariance. The lcm argument is elegant, but calling it "formal evidence for ν_R" in the conclusions risks overstating it as a proof-by-contradiction from observations, when it is really a conditional: "IF both anomaly constraints apply AND N_f = 3 THEN ν_R must exist." This conditional form is not what the conclusions say. The Lean theorem `constraints_without_nu_R` correctly formalizes the conditional; the paper's prose in the conclusions upgrades it to unconditional.

***

## Section 4 — Lean Proof Issues Specific to Paper 10

### 4.1 — Module count discrepancy

The abstract says "130 Lean 4 modules." The conclusions section says "130 Lean 4 modules." The README says 131 modules. Minor — update to current count.

### 4.2 — Aristotle run IDs cited in conclusions

The conclusions cite Aristotle run IDs `a1dfcbde` (GenerationConstraint) and `b54f9611` (ModularInvariance). This is an unusual practice for a physics journal paper — the reader cannot verify an Aristotle run ID without access to the Harmonic system. For PRD, this should be moved to a footnote or supplemental material, or replaced with: "machine-verified by Lean 4's kernel (v4.28.0, Mathlib commit 8f9d9cff)." The actual verification is done by Lean's kernel, not by the prover; the prover finds the proof term, the kernel checks it.

### 4.3 — `sixteen_convergence_full` — tautological structure not disclosed

As established in the Lean source audit, the theorem's third conjunct is literally the hypothesis `h_rokhlin` echoed in the conclusion, and the fourth conjunct repeats the first. The paper says "formally verified as `sixteen_convergence_full` in RokhlinBridge.lean (14 theorems; Rokhlin's theorem enters as a hypothesis, not an axiom)." The parenthetical is honest about Rokhlin being a hypothesis, but does not disclose that the proof does not demonstrate any mathematical connection between the four 16s — only that the number 16 appears in four contexts. A referee who reads the Lean source will immediately see this. The paper should not describe this theorem as establishing a "convergence" — it should describe it as a "record" or "enumeration."

### 4.4 — The Ext computation claim

The claim "first machine-checked Ext computation over any Steenrod subalgebra in any proof assistant" requires a provenance check. The ext computation is over A(1) = ⟨Sq¹, Sq²⟩ through degree 5. Before making the "first in any proof assistant" claim, verify that no such computation exists in:
- Lean/Mathlib (check `Mathlib4/AlgebraicTopology`)
- Agda standard library or Cubical Agda
- Coq/Rocq HoTT library
This is not a retraction — it is likely correct — but the word "first" requires due diligence that is not documented in the paper.

***

## Section 5 — Format and Presentation (PRD Letters)

PRD Physical Review Letters format imposes specific constraints that Paper 10 currently violates:

### 5.1 — Length
The paper as written is approximately 3,500 words of body text plus two tables, two figures, and extensive conclusions. PRL Letters are limited to **3,500 words total** including abstract, references, and figure captions. PRD Letters (if submitted as a Letter) have the same constraint. The paper will need significant compression if targeting the Letters format stated in the README. The Ext computation discussion alone (~250 words in the conclusions) may need to become a separate technical companion paper or supplemental material.

### 5.2 — Two figures are appropriate; verify they render from the repo
- `fig75_modular_invariance_phase.png` and `fig73_sm_generation_constraint.png` are referenced but confirmed to exist in the repository. ✅
- Figure captions are informative and within scope.

### 5.3 — The fermion table formatting
The tabular environment in the body (`\begin{center}\begin{tabular}...`) is inside a `\begin{center}` block rather than a `\begin{table}` float. For PRD, this should be a proper `\begin{table}[t]` with a `\caption{}` and `\label{}` to allow cross-referencing. The current format will produce unformatted output in the two-column RevTeX layout.

### 5.4 — The ν_R table (`With vs. without ν_R`)
Same issue — currently in `\begin{center}` rather than a `\begin{table}` float. In PRD two-column format, unboxed center-aligned tables frequently break across columns.

### 5.5 — Missing journal for `[BeaudryCampbell]`
The bibitem for BeaudryCampbell has no journal field — only the year. Should read:
```
\bibitem{BeaudryCampbell}
A.~Beaudry and J.~A.~Campbell,
\emph{A guide for computing stable homotopy groups},
Contemp.\ Math.\ \textbf{718}, 89 (2018) [arXiv:1801.07530].
```

***

## Section 6 — Missing Citations

These references are directly relevant to Paper 10's claims and their absence will draw referee queries:

### 6.1 — Fidkowski-Kitaev 2010 (required for ℤ₁₆ in class D)
```
\bibitem{FidkowskiKitaev2010}
L.~Fidkowski and A.~Kitaev,
Phys.\ Rev.\ B \textbf{81}, 134509 (2010) [arXiv:0904.2197].
```
Cite at item 4 of the "16 Convergence" list (replaces the incorrect "time-reversal symmetry" framing).

### 6.2 — di Francesco et al. (CFT textbook) for Casimir energy / `c/24` connection
```
\bibitem{diFrancesco1997}
P.~di Francesco, P.~Mathieu, and D.~S\'en\'echal,
\emph{Conformal Field Theory} (Springer, 1997).
```
Cite in Section 3.2 alongside or instead of Rademacher for the physical origin of the 24.

### 6.3 — Freed-Hopkins (for framing anomaly and spin manifold context)
Wang 2024 cites Freed-Hopkins extensively for the physical framework. For completeness and because multiple claims in Paper 10 rest on this machinery:
```
\bibitem{FreedHopkins2021}
D.~S.~Freed and M.~J.~Hopkins,
Reflect.\ Ann.\ Math.\ Studies \textbf{219}, 169 (2021) [arXiv:2103.01190].
```

### 6.4 — Wang 2024 is cited once but drives almost everything
Wang 2024 should be cited at every major physics claim it supports: the dimensional reduction scheme (Section 2), the framing anomaly condition (Section 3), the ℤ₂₄ bordism class, and the generation constraint derivation. Currently it appears as a single end-of-introduction citation. Add it to each section where it is the actual source.

***

## Section 7 — Consolidated Issue Table

| # | Location | Severity | Issue | Fix |
|---|---|---|---|---|
| 1 | Abstract | 🔴 | "derived" overstates Wang's proposal | Replace "derived" with "argued on topological grounds (Wang 2024)" |
| 2 | Section 2.1 | 🟡 | Dimensional reduction not derived — Wang's proposal | Add framing paragraph disclosing Wang 2024 is a proposal |
| 3 | Section 3.2 | 🟡 | Rademacher cited for physics result he didn't make | Add di Francesco et al. 1997 for Casimir energy interpretation |
| 4 | Section 4, item 4 | 🔴 | "time-reversal symmetry" wrong for ℤ₁₆ in class D | Fix to "class D, no time-reversal" + add Fidkowski-Kitaev 2010 |
| 5 | Section 4 paragraph | 🔴 | "16 = 8 × 2" is numerological, not a theorem | Replace with Wang 2024 Smith homomorphism language |
| 6 | Section 4 | 🟡 | `sixteen_convergence_full` is tautological but described as proving connection | Change "formally verified convergence" → "formally recorded" |
| 7 | Section 4 | 🟡 | ℤ₁₆ bordism Lean proof is placeholder (`Equiv.refl`) | Disclose as hypothesis, not proved |
| 8 | Section 2.2 | 🔵 | "independent argument for ν_R" — not independent of framing assumption | Remove "independent" |
| 9 | Conclusions | 🟡 | "formal evidence for ν_R" from lcm=48 is conditional, not unconditional | Restate as conditional: "IF both constraints hold AND N_f=3, THEN ν_R" |
| 10 | Conclusions | 🔵 | Aristotle run IDs in body text — unusual for PRD | Move to footnote or supplemental |
| 11 | Bibliography | 🔴 | ABP1967 page 256 wrong — should be 271 | Fix page number |
| 12 | Bibliography | 🟡 | Stolz1993 Math.Ann. 296, 685 — not found; possibly misidentified | Replace with correct Stolz citation or remove |
| 13 | Bibliography | 🔵 | BeaudryCampbell start page is 89, not 1 | Fix page number |
| 14 | Bibliography | 🔵 | Kitaev2009 page range missing end page (should be 22–30) | Add end page |
| 15 | All sections | 🟡 | Wang 2024 cited once but drives most claims | Add to each section where used |
| 16 | Missing | 🟡 | Fidkowski-Kitaev 2010 absent | Add for ℤ₁₆ in class D |
| 17 | Missing | 🟡 | di Francesco et al. 1997 absent | Add for c/24 Casimir energy physics |
| 18 | Missing | 🔵 | Freed-Hopkins 2021 absent | Add for framing anomaly context |
| 19 | Formatting | 🟡 | Fermion table not in `\begin{table}` float | Reformat for PRD two-column layout |
| 20 | Formatting | 🟡 | ν_R comparison table not in `\begin{table}` float | Reformat for PRD two-column layout |
| 21 | Length | 🟡 | Likely exceeds PRD Letters limit (~3500 words) | Compress or split Ext discussion |
| 22 | "First" claim | 🔵 | "First Ext computation in any proof assistant" needs provenance check | Verify no prior Agda/Coq/Lean formalization |
| 23 | Module count | 🔵 | Abstract/Conclusions say 130 modules; README says 131 | Update to 131 |

***

## Section 8 — What Is Genuinely Strong

These elements should be preserved and highlighted more prominently:

- **The Ext computation over A(1)** (through degree 5, `dim Ext^n = 1,2,2,2,3,4`) is the paper's most original formalization contribution and is likely correct as the first such computation in a proof assistant. This deserves its own paragraph in the introduction, not just the conclusions.
- **The `c_- = 15/2` fractional charge result** (without ν_R) is a clean, well-formalized argument that is accessible to a broad PRD readership. Formalize it more prominently.
- **The conditional chain** `[24 | 8N_f] ∧ [c_- = 8N_f] ⟹ [3 | N_f]` is tight, correct, and completely machine-verified. Zero sorries. This should be the centerpiece.
- **The `with/without ν_R` comparison table** is pedagogically excellent and should be kept.
- **The disclosure that Rokhlin enters as a hypothesis** is intellectually honest and rare in AI-generated physics papers. Keep and expand it as a model for how to handle other conditional results.