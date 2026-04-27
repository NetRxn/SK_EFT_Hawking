---
paper: note_rt_ch_bounds
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-04-28T22:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — note_rt_ch_bounds

## Summary

Cost-bounded review (Classes 1, 3, 4, 5, 6 only). The Lean module
`RTCasiniHuertaBounds.lean` ships 7 substantive theorems with
load-bearing bodies; the knife-edge biconditional
`rt_eq_kaulMajumdar_iff_trivial_reduced_area` is non-trivial (uses
`Real.exp_log` + `Real.log_one`). Class 1 cache-skip on all four
bibitems. One REQUIRED issue: the abstract claim "a separate
non-universality witness in the literature is Sen's 4D Schwarzschild
log coefficient $77/45$" is in the Lean docstring (line 26-27,
`sen_4d_disagrees_with_kaul_majumdar`) but the paper §intro at
lines 75-78 omits the actual reference (no `\cite{Sen...}` for the
77/45 number); the value 77/45 is sourced informally. Two RECOMMENDED
issues: (a) `H_CasiniHuerta_Bound_Valid_witness_saturated` discharges
via `rfl` on the bound's third field — borderline structural-tautology
because the saturation function is exactly the bound, but it's a
legitimate "witness exists" pattern, so not blocking; (b) the
note's title says "$-(3/2)\log(A/4G_N)$" but the abstract first
mentions $S = A/(4\GN) - (3/2)\log(A/4G_N)$ — these match by inspection,
just verifying.

## Findings

### 5.1 — 🟡 REQUIRED — Sen's 4D log coefficient $77/45$ is referenced but no primary-source citation

- **Gate:** NarrativeGrounding (Gate 7) / CitationIntegrity (Gate 1)
- **Location:** `note_rt_ch_bounds/paper_draft.tex:75-78`; `lean/SKEFTHawking/RTCasiniHuertaBounds.lean:26-27`
- **Observed:** Paper §intro lines 75-78: "A separate non-universality witness in the literature is Sen's 4D Schwarzschild log coefficient $77/45 \approx 1.711$, which differs from $-3/2$, indicating that the microscopic log coefficient is not universal across Lagrangian regularizations." The value $77/45$ is presented as a literature-anchored numerical claim but no `\cite{Sen...}` reference is given, and the paper bibliography does not contain a Sen entry. Lean docstring at `RTCasiniHuertaBounds.lean:27` references "the W3 non-universality witness `sen_4d_disagrees_with_kaul_majumdar`" but the paper does not connect this to a published source.
- **Evidence:** `note_rt_ch_bounds/paper_draft.tex:75-78` — no `\cite{...}` adjacent to the 77/45 claim; `\thebibliography` at lines 259-283 has no Sen entry. The actual Sen reference is likely arXiv:1205.0971 (per the project's parameter-provenance memory at `feedback_post_wave_strengthening_audit.md` and the project status memory).
- **Expected:** Either (a) add a Sen bibitem and `\cite{Sen2012}` adjacent to "Sen's 4D Schwarzschild log coefficient $77/45$" at line 76, or (b) drop the 77/45 specific number and discuss only the qualitative non-universality.
- **Fix:** Add a bibitem along the lines of: `\bibitem{Sen2012} A.~Sen, ``Logarithmic corrections to N=2 black hole entropy: an infrared window into the microstates,'' Gen.\ Rel.\ Grav.\ \textbf{44}, 1207 (2012); arXiv:1108.3842.` (or arXiv:1205.0971 — verify against the actual Lean module's source). Cite at line 76. **CITATION_REGISTRY** entry must also be added if not present.

### 3.1 — 🔵 RECOMMENDED — `H_CasiniHuerta_Bound_Valid_witness_saturated.ch_bound` proof is `rfl` on the bound

- **Gate:** LeanProofSubstance (Gate 5)
- **Location:** `lean/SKEFTHawking/RTCasiniHuertaBounds.lean:223-229`
- **Observed:** Witness theorem proves the saturated entropy `S_sat(L) = (c/3) log(L/UV)` satisfies `H_CasiniHuerta_Bound_Valid` by setting the `ch_bound` field via `fun _ _ => by unfold saturatedCHEntropy; rfl`. The saturation function is *defined* to equal the bound, so the bound check trivially holds with equality. This is a legitimate "non-vacuous existence" pattern (showing the predicate has a witness), but the structural content is "the bound is sharp" rather than "the bound is satisfied by some non-trivial entropy function."
- **Evidence:** `RTCasiniHuertaBounds.lean:215-216, 226-229`: the saturated entropy is defined as `(c/3) * Real.log (L/UV)`; the witness theorem's `ch_bound` field is then `S_ent L ≤ (c/3) * log(L/UV)` which is `(c/3) log(L/UV) ≤ (c/3) log(L/UV)` — true by `le_refl`. The proof writes `rfl` because both sides are definitionally equal.
- **Expected:** Borderline. The witness is non-vacuous — `H_CasiniHuerta_Bound_Valid` has at least one inhabitant, which is the substantive content. But adding a *non-saturating* witness (e.g., a strict-inequality entropy function like `(c/6) log(L/UV)`) would strengthen the predicate's non-vacuity envelope.
- **Fix:** Optionally add a second witness `H_CasiniHuerta_Bound_Valid_witness_strict` for an entropy function `(c/6) log(L/UV)` that satisfies the bound *strictly* (not at equality). This separates "bound is sharp" from "bound has a non-trivial inhabitant."

### 5.2 — 🔵 RECOMMENDED — abstract "seven substantive theorems" matches the file's `theorem` count

- **Gate:** NumericalFreshness (Gate 9)
- **Location:** `note_rt_ch_bounds/paper_draft.tex:53, 230`
- **Observed:** Both abstract (line 53) and §formalization (line 230) say "seven substantive theorems." `grep -cE "^theorem " RTCasiniHuertaBounds.lean = 7`. Match.
- **Expected:** Same retrofit advisory as papers 35, 36, 37, 38.

## Class 1 cache-skip summary

All four bibitems are major published works:
- `RyuTakayanagi2006` — arXiv:hep-th/0603001, PRL 96, 181602 (2006) — `cache-skip`.
- `CasiniHuerta2009` — arXiv:0905.2562, J. Phys. A 42, 504007 (2009) — `cache-skip`.
- `KaulMajumdar2000` — PRL 84, 5255 (2000) — `cache-skip`. (Note: bibitem provides no arXiv ID, but the paper is well-known.)
- `LewkowyczMaldacena2013` — arXiv:1304.4926, JHEP 08, 090 (2013) — `cache-skip`.
- (Sen reference missing — Finding 5.1.)

## Class 4 cross-paper consistency

No bibkeys shared with the other six papers in this batch.

## Class 3 substantive-body confirmation

All 7 cited theorems inspected:
- `rt_entropy_pos` — uses `h.rt_proportional` (load-bearing tracked-Prop access) + `div_pos`, OK.
- `rt_kaulMajumdar_gap_at_reduced_area_two` — unfolds `kaulMajumdarS`, computes via `field_simp + ring`, substantive, OK.
- `rt_eq_kaulMajumdar_iff_trivial_reduced_area` — uses `Real.exp_log` to invert log → ratio, substantive biconditional, OK.
- `rt_falsified_by_kaul_majumdar` — uses both `h_rt.rt_proportional` and the biconditional contrapositive, OK.
- `ch_log_bound_pos_at_log_pos` — uses `h.c_pos`, `h.uv_pos`, `Real.log_pos`, `mul_pos`, OK.
- `H_CasiniHuerta_Bound_Valid_witness_saturated` — `rfl` on the saturation (Finding 3.1), borderline.
- `kaulMajumdar_not_H_RT` — uses `Real.log_pos (Real.log 2 > 0)` plus `linarith`, substantive, OK.

No P3/P4 patterns. P5 borderline at 3.1 (saturated witness).

## Class 6 assumption disclosure

`H_RT_Formula_Valid` and `H_CasiniHuerta_Bound_Valid` are tracked external-hypothesis Props. Paper §II discloses both with their full structural content (rt_proportional clause, ch_bound clause + c_pos / uv_pos fields). Sufficient.
