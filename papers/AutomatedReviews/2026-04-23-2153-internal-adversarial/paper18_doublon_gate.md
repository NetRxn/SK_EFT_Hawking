---
paper: paper18_doublon_gate
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-23T21:53:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper18_doublon_gate

## Summary

Five findings: 0 BLOCKER, 2 REQUIRED, 3 RECOMMENDED. Paper is substantively
sound — all 8 bibkeys resolve and live in `CITATION_REGISTRY`, all 17
numerical/structural claims in the prose trace to named Lean theorems
with substantive proofs (no `rfl`/`trivial` placeholders on non-trivial
statements), no cross-paper contradictions, no uncited numerical
simulation evidence, and the scope boundary (no adiabatic theorem, no
Berry connection, no fiber bundles) is disclosed repeatedly. Two gates
remain draft-OK but open for submission: NarrativeGrounding (the W8e
"purely geometric and equals −1" framing overstates what the Lean
theorem encodes) and NumericalFreshness (two raw count literals
remain inline instead of flowing through the counts macro chain).
Submission-readiness: YELLOW — not blocked, but two REQUIRED items
must be resolved before the paper can pass all 11 readiness gates.

## Findings

### 5.1 — 🟡 REQUIRED — W8e statement does not prove "Berry phase equals −1"

- **Gate:** NarrativeGrounding (Gate 7)
- **Location:** `papers/paper18_doublon_gate/paper_draft.tex:380-408`; backing theorem `lean/SKEFTHawking/FermiHubbardDimer.lean:2522` (`geometric_phase_minus_one_on_pi_loop`)
- **Observed:** Paper prose at §5 (Minimal Berry Phase Theorem) and the theorem's docstring describe W8e as "the **bundled geometric-phase theorem**" whose conclusion is "the accumulated phase on any π-sweep satisfying the kernel-angle condition is purely geometric and equal to −1" (L406-408). The abstract (L42-48) uses the same framing: "the minimum Berry-phase statement required to interpret the gate action as geometric rather than dynamical — namely that the dark state acquires a −1 sign on a π-sweep of the mixing angle while remaining at zero energy throughout." The Lean theorem's actual conclusion is the conjunction `darkStateθ(θ+π) = −darkStateθ(θ) ∧ dotProduct(dark, H·dark) = 0`. No "Berry phase" object is defined in Lean; no equality `BerryPhase = −1` is proved; the integrated dynamical phase `∫ ⟨ψ|H|ψ⟩ ds` is not constructed, only the pointwise vanishing of the integrand is.
- **Evidence:** Theorem body at L2522-2526 is `exact ⟨darkStateθ_add_pi_sign_flip θ, dark_state_dynamical_phase_vanishes t Δ θ hθ⟩`. No integral, no phase construction, no continuity assumption, no path functional. The paper at §5 "What this theorem does and does not say" (L418-429) already discloses this limitation accurately — but the earlier W8e framing in the same section, the abstract, and the theorem name itself (`geometric_phase_minus_one_on_pi_loop`) all imply more than the bundled conjunction delivers.
- **Expected:** Either (a) soften the prose framing and the Lean theorem name/docstring to match what is proved — e.g., "the two finite-dimensional facts required for a Berry-phase interpretation: sign flip on π-sweep, and pointwise zero-energy along the path," or (b) actually construct the dynamical-phase integral (even over the discrete θ-grid) and prove its vanishing as a single equality, then the "=−1" claim would have a single theorem to point at.
- **Fix:** Rewrite the W8e framing in the abstract (L42-48), §5 intro paragraph (L381-384), and the W8e bullet (L406-408) to describe W8e as a conjunction of two necessary facts, not a conclusion about an integrated phase. Example: replace "the accumulated phase on any π-sweep... is purely geometric and equal to −1" with "the two independent finite-dimensional facts (sign flip + pointwise zero-energy) required to interpret the accumulated phase as purely geometric; the integral-of-phase construction itself is Target B."
- **Cache:** N/A (semantic check, not a citation fetch)

### 9.1 — 🟡 REQUIRED — Two raw count literals outside the macro chain

- **Gate:** NumericalFreshness (Gate 9)
- **Location:** `papers/paper18_doublon_gate/paper_draft.tex:50` ("141 theorems") and `paper_draft.tex:223` ("W5 core + round-2, 21 theorems")
- **Observed:** `validate.py --check count_literals` flags paper18 with two inline count literals. The abstract uses `141 theorems` as a hardcoded integer rather than a `\totaltheorems`-style macro; §3 (BDI Symmetry Protection) hard-codes "21 theorems" for W5. The table at L447-458 also hard-codes the per-section integers 13, 6, 22, 22, 38, 15, 19, 6 and the total 141. All count macros (`\totaltheorems`, `\substantivetheorems`, `\placeholdertheorems`, `\totaltests`) flow in correctly, but per-module and per-section counts do not.
- **Evidence:** `uv run python scripts/validate.py --check count_literals` output: `⚠ paper18_doublon_gate — USES MACROS but 2 count-literal matches: L50 "141 theorems" (theorems); L223 "21 theorems" (theorems)`. Source-of-truth module count (ripgrep `^theorem |^lemma ` in FermiHubbardDimer.lean) = 141, matching the paper's hardcode *today*; however if the module gains or loses theorems the paper will silently drift.
- **Expected:** Per-module and per-section theorem counts emitted from a canonical per-module counts file (e.g., `docs/counts_fermi_hubbard_dimer.tex` with macros `\fhdTheoremTotal{}`, `\fhdW2Total{}`, ..., regenerated by `update_counts.py --modules`) and `\input{}` into the paper.
- **Fix:** Extend `scripts/update_counts.py` to emit per-module count macros for every module that a paper references by per-section breakdown. Replace L50 with `\fhdTheoremTotal{}`, L223 with the corresponding W5 macro, and regenerate the Table 1 rows from a tables.py-generated `\input{tables/paper18_wave_counts.tex}`. This is the same retrofit the Gate 9 spec requires for every paper at submission; paper18 does it halfway (project-wide counts via `\input{../../docs/counts.tex}`, per-module counts hardcoded).
- **Cache:** N/A

### 5.2 — 🔵 RECOMMENDED — W8e theorem name is stronger than its statement

- **Gate:** LeanProofSubstance (Gate 5)
- **Location:** `lean/SKEFTHawking/FermiHubbardDimer.lean:2522` (`theorem geometric_phase_minus_one_on_pi_loop`)
- **Observed:** The theorem name `geometric_phase_minus_one_on_pi_loop` syntactically implies "the geometric phase equals −1 on the π-loop." The statement is a conjunction of two lemmas (W8a: the dark-state vector itself flips sign; W8d: the Hamiltonian expectation vanishes). Neither conjunct is a statement about a Berry-phase functional. A reader searching the project for "Berry phase" will find this name and reasonably infer a Berry-phase-equals-scalar theorem is available to downstream consumers — it is not.
- **Evidence:** Body = `exact ⟨darkStateθ_add_pi_sign_flip θ, dark_state_dynamical_phase_vanishes t Δ θ hθ⟩` (2 lines). No quantitative scalar "−1" appears in the conclusion except indirectly, as the coefficient of the RHS vector in W8a. This is not a Gate-5 BLOCKER — the proof is not tautological, the conjuncts are both load-bearing, the body legitimately combines them. But the name is a Gate-5 "semantic tautology adjacent" pattern: the conclusion reproduces a hypothesis-shaped token ("−1" in the name, encoded as vector negation in the statement).
- **Fix:** Rename to `geometric_phase_necessary_conditions_on_pi_loop` or `dark_state_pi_sweep_sign_and_dynamical_vanishing`, aligning the name with the actual conjunction it proves.

### 2.1 — 🔵 RECOMMENDED — Paper is parameter-provenance N/A (intentional, documented)

- **Gate:** ParameterProvenance (Gate 3)
- **Location:** paper-wide
- **Observed:** The paper uses only symbolic model parameters (`t`, `Δ`, `U` as abstract reals). No BEC, optical-lattice, or graphene experimental numbers appear. The Kiefer2026 "99.9% fidelity" and "4× robustness" numbers are quoted in prose as experimental results from the cited paper, not used as parameters in any computation or figure.
- **Evidence:** No `PARAMETER_PROVENANCE` lookups apply. The claims_review.json entry for parameter_provenance says "N/A" and I confirm this independently — no numerical experimental parameters are asserted.
- **Fix:** None. Documented here so the readiness gate dashboard can mark Gate 3 as `passed-by-N/A` rather than `open`.

### 4.1 — 🔵 RECOMMENDED — Shared Kitaev2009 bibitem uses different format across papers

- **Gate:** CrossPaperConsistency (Gate 2)
- **Location:** `papers/paper18_doublon_gate/paper_draft.tex:609-611` and `papers/paper10_modular_generation/paper_draft.tex:353` (shared `Kitaev2009` bibkey)
- **Observed:** Paper 10 bibitem reads "A. Kitaev, AIP Conf. Proc. 1134, 22–30 (2009)." — no title, page range 22-30. Paper 18 bibitem reads "A. Kitaev, *Periodic table for topological insulators and superconductors*, AIP Conf. Proc. 1134, 22 (2009), arXiv:0901.2686." — with title, single-page citation style, with arXiv ID. Both resolve to the same physical paper. Not a Gate-2 BLOCKER (no CONTRADICTS edge, no different arXiv IDs), but the bibliographic format should be canonicalized through `CITATION_REGISTRY` so every paper renders the same bibitem.
- **Evidence:** `grep -A 3 "bibitem{Kitaev2009}"` on both files. `CITATION_REGISTRY["Kitaev2009"]` is present (confirmed by claims_review.json) but the two papers are not rendering bibitems from the registry — each paper hand-writes its own bibitem block.
- **Fix:** Migrate both papers to `\input{}`-based bibitem rendering driven by a per-paper bibitem-selection that pulls from the registry. This is a project-wide retrofit, not a paper18-specific fix; listed here as RECOMMENDED so the QI candidate section picks it up.

## QI Candidate

**Theme:** Per-module theorem counts are hand-coded in paper tables; project-wide counts flow through macros but per-module counts do not. This is how paper18 originally shipped the wrong "139" figure that claims-reviewer caught; the retrofit to "141" was done by hand and will silently drift the next time FermiHubbardDimer.lean is edited. A `scripts/update_counts.py --per-module` extension that writes `docs/counts_<module>.tex` plus a `tables.py` spec for per-wave theorem tables would close this drift class for every paper at once.

**Secondary theme:** Bibitem formatting drift across papers that share a `CITATION_REGISTRY` key. Paper 10 and Paper 18 both cite `Kitaev2009` but render it differently. A `scripts/render_bibitem.py <bibkey>` helper that emits a canonical bibitem block from the registry, paired with a `\input{../../docs/bibitems/<key>.tex}` pattern in each paper, would eliminate this class entirely. Listed as QI because the benefit is project-wide, not paper18-specific.
