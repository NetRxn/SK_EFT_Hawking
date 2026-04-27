---
paper: paper35_qec_holography
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-04-29T00:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper35_qec_holography

## Summary

Re-scan after strengthening pass. **Prior REQUIRED 5.1** (`codeDistance` substrate-vs-encoding conflation) is **resolved**: §III prose at lines 87-93 now explicitly identifies `\dC` as a "code-distance proxy" and "substrate-level quantity" with the upper-bound qualifier "upper-bounding any per-encoding code distance one would obtain from an explicit Yoshida-Kitaev decoder" — the prior conflation between the substrate-level `log d_max` and the per-encoding QEC code distance is now disambiguated. **Prior RECOMMENDED 5.2** (literal "ten" → counts macro retrofit) is **resolved**: abstract line 46 and §formalization line 266 now use `\qecHolographyThms{}` macro (verified — counts.tex resolves to 10, matches `grep -cE "^theorem " QECHolographyBridge.lean = 10`). **Prior RECOMMENDED 6.1** (cross-bridge `S_horizon` parameter not disclosed) is **resolved**: §VII at lines 248-254 now reads "The assumption bundle is parametrized by an abstract horizon-entropy function `S_horizon` (instantiated downstream by the project's `S_horizon` candidates such as Kaul-Majumdar or Verlinde); the proof here uses only the bundle's `areaLeading` field, so the bridge does not depend on any specific entropy-function choice." Counts macro `\qecHolographyTests` resolves to 30. No new BLOCKER/REQUIRED/RECOMMENDED findings. Submission-ready.

## Findings

(none — re-scan finds no new issues; all three prior findings resolved)

## Verification of strengthening-pass changes

### Class 5 — `codeDistance` substrate-vs-encoding disambiguation

- **File:** `papers/paper35_qec_holography/paper_draft.tex:87-93`
- New prose: "A *code-distance proxy* $\dC := \log \dmax$ measuring the fusion-channel entropy that shields an encoded logical qubit from boundary errors. We use ``proxy'' deliberately: $\dC$ is a *substrate-level* quantity --- it depends only on the MTC spectrum, not on the specific encoding-anyon choice --- upper-bounding any per-encoding code distance one would obtain from an explicit Yoshida--Kitaev decoder."
- Body §III at lines 130-138 retains the topological-shielding-scale framing but now consistent with proxy language. Abstract at line 33-34 also reads "code-distance proxy $\dC := \log\dmax$ identifying the topological-shielding scale." ✓ proxy framing propagated.

### Class 6 — cross-bridge `S_horizon` disclosure

- **File:** `papers/paper35_qec_holography/paper_draft.tex:240-256`
- §VII now reads: "The assumption bundle is parametrized by an abstract horizon-entropy function `S_horizon` (instantiated downstream by the project's `S_horizon` candidates such as Kaul-Majumdar or Verlinde); the proof here uses only the bundle's `areaLeading` field, so the bridge does not depend on any specific entropy-function choice." (lines 248-254)
- The proof body's reliance on only the `areaLeading` field is correctly disclosed; downstream `S_horizon` instantiations (Kaul-Majumdar, Verlinde) are named. ✓

### Class 7 — counts macros

- `\qecHolographyThms{}` → 10 — matches `grep -cE "^theorem " QECHolographyBridge.lean = 10` ✓
- `\qecHolographyTests{}` → 30 — matches `tests/test_qec_holography.py` test count ✓
- No "Undefined control sequence" in `paper_draft.log`. ✓
- Abstract line 46 ("ships \qecHolographyThms{} substantive theorems") and §formalization line 266 ("ships \qecHolographyThms{} substantive theorems") use the macro consistently ✓.

## Class 1 cache-skip summary (unchanged)

All seven bibitems are major published works with no smell:
- `HaydenPreskill2007` — arXiv:0708.4025, JHEP 09, 120 (2007) — `cache-skip`
- `AlmheiriDongHarlow2015` — arXiv:1411.7041, JHEP 04, 163 (2015) — `cache-skip`
- `PYHP2015` — arXiv:1503.06237, JHEP 06, 149 (2015) — `cache-skip`
- `YoshidaKitaev2017` — arXiv:1710.03363 — `cache-skip`
- `KitaevAnyons2003` — arXiv:quant-ph/9707021 — `cache-skip` (also cited identically in paper 36)
- `NayakAnyons2008` — RMP 80, 1083 (2008) — `cache-skip`
- `KitaevPreskill2006` — arXiv:hep-th/0510092, PRL 96, 110404 (2006) — `cache-skip`

## Class 4 cross-paper consistency

`KitaevAnyons2003` shared with paper 36; both bibitems identical (Annals Phys. 303, 2 (2003); arXiv:quant-ph/9707021). Consistent.

## Class 3 substantive-body confirmation (unchanged)

All ten cited theorems re-inspected; bodies unchanged from prior pass. No P3/P4/P5 patterns detected. The `codeDistance := H.horizon.areaLawKappa` definition is unchanged but the prose now correctly identifies it as a substrate-level proxy.
