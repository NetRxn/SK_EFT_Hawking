---
paper: paper36_center_symmetry
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-04-29T00:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper36_center_symmetry

## Summary

Re-scan after strengthening pass. **Prior REQUIRED 5.1** (3D 3-state Potts ν=0.5 misrepresented as measured exponent) is **resolved**: §III prose at lines 156-163 now explicitly states "$\nuPotts \approx 1/2$ is a mean-field placeholder: the 3D 3-state Potts transition is weakly first order, so $\nuPotts$ is not a measured exponent and the literal value is illustrative only. What is load-bearing is the *ordering* $\nuPotts < \nuIsing$, which separates the two universality classes regardless of the precise Potts value." **Prior RECOMMENDED 3.1** (`ising_nu_above_0_6` and `potts_nu_below_0_6` redundant with `ising_nu_gt_potts_nu`) is **resolved**: both threshold theorems removed (verified `grep -n "ising_nu_above_0_6\|potts_nu_below_0_6" CenterSymmetryConfinement.lean → no matches`). **Prior RECOMMENDED 6.1** (Walker-Wang witness not surfaced in §V) is **resolved**: §V at lines 217-219 now mentions "A boundary witness theorem `walker_wang_witness_at_kss_lower` confirms that the predicate is non-vacuous: $\eta/s = \mathrm{KSS}$ saturates the lower bound." **Prior RECOMMENDED 5.2** (counts macro retrofit) is **resolved**: abstract line 48 and §VI line 272 now use `\centerSymmThms{}` (resolves to 18). **Newly cited**: `Polyakov1978` (Phys. Lett. B 72, 477) at line 30 abstract introducing the Polyakov-loop name. **One new RECOMMENDED finding (7.1 below): `\centerSymmThms` resolves to 18, but the prior review's count was 20** — the strengthening pass that removed `ising_nu_above_0_6` and `potts_nu_below_0_6` correctly reduced the count, and the macro update propagated. No drift, no BLOCKER/REQUIRED.

## Findings

(none — re-scan finds no new issues; all three prior findings resolved)

## Verification of strengthening-pass changes

### Class 5 — Potts ν=0.5 placeholder caveat added

- **File:** `papers/paper36_center_symmetry/paper_draft.tex:156-163`
- New prose: "$\nuIsing$ tracks the Pelissetto-Vicari and Kos-Poland-Simmons-Duffin precision values [refs] and $\nuPotts \approx 1/2$ is a mean-field placeholder: the 3D 3-state Potts transition is weakly first order, so $\nuPotts$ is not a measured exponent and the literal value is illustrative only. What is load-bearing is the *ordering* $\nuPotts < \nuIsing$, which separates the two universality classes regardless of the precise Potts value." ✓ explicit caveat.
- Lean docstring at `CenterSymmetryConfinement.lean:201` now reads: "3D 3-state Potts universality (Z_3 spin model; first-order in 3D)." ✓ also caveat-aware.

### Class 3 — `ising_nu_above_0_6` + `potts_nu_below_0_6` removed

- `grep -n "ising_nu_above_0_6\|potts_nu_below_0_6" CenterSymmetryConfinement.lean` → no matches ✓
- Only `ising_nu_gt_potts_nu` (line 233) remains as the substantive comparison theorem. Theorem count: 18 (was 20 before this removal).

### Class 5 — Walker-Wang witness mentioned in §V

- **File:** `papers/paper36_center_symmetry/paper_draft.tex:216-219`
- New prose: "A boundary witness theorem `walker_wang_witness_at_kss_lower` confirms that the predicate is non-vacuous: $\eta/s = \mathrm{KSS}$ saturates the lower bound. Two concrete numerical falsifiers complete the bracket: ..."
- Reader now sees both witness and falsifier; the bracket has both an existence proof and rejection proofs. ✓

### Class 1 — Polyakov1978 cited in abstract

- **File:** `papers/paper36_center_symmetry/paper_draft.tex:30`
- Abstract: "We formalize confinement as $\mathbb{Z}_N$ 1-form center-symmetry unbreaking in Lean~4, treating the **Polyakov loop**~\cite{Polyakov1978} $P$ as the complex order parameter."
- Bibitem at line 321: "A.~M.~Polyakov, ``Thermal properties of gauge fields and quark liberation,'' Phys.\ Lett.\ B \textbf{72}, 477 (1978)." ✓ correct historical attribution; also cited in paper 38 cross-paper.

### Class 7 — counts macros

- `\centerSymmThms{}` → 18 — matches `grep -cE "^theorem " CenterSymmetryConfinement.lean = 18` ✓ (correctly reflects the strengthening-pass removal of 2 redundant theorems from 20 → 18)
- `\centerSymmTests{}` → 28 — matches `tests/test_center_symmetry.py` ✓
- Abstract line 48 ("ships \centerSymmThms{}") and §VI line 272 ("ships \centerSymmThms{}") use the macro consistently ✓
- No "Undefined control sequence" in `paper_draft.log`. ✓

## Class 1 cache-skip summary (updated)

All seven bibitems re-inspected; new entry `Polyakov1978` is well-known historical reference, no smell:
- `SvetitskyYaffe1982` — Nucl. Phys. B 210, 423 (1982) — `cache-skip`
- `KovtunSonStarinets2005` — arXiv:hep-th/0405231, PRL 94, 111601 (2005) — `cache-skip`
- `HofmanIqbal2018` — arXiv:1707.08577, SciPost Phys. 4, 005 (2018) — `cache-skip`
- `PelissettoVicari2002` — arXiv:cond-mat/0012164, Phys. Rep. 368, 549 (2002) — `cache-skip`
- `KosPolandSimmonsDuffin2016` — arXiv:1603.04436, JHEP 03, 086 (2016) — `cache-skip`
- `Polyakov1978` — Phys. Lett. B 72, 477 (1978) — `cache-skip` (also in paper 38; foundational paper introducing the Polyakov-loop name)
- `KitaevAnyons2003` — arXiv:quant-ph/9707021 — `cache-skip` (also in paper 35)

## Class 4 cross-paper consistency

`Polyakov1978` shared with paper 38 (CFL); both bibitems identical (Phys. Lett. B 72, 477 (1978)). Consistent.
`KitaevAnyons2003` shared with paper 35 (QEC); both bibitems identical. Consistent.

## Class 3 substantive-body confirmation

All 18 cited theorems re-inspected; no new P3/P4/P5 patterns introduced. The KSS bracket [0.07, 0.08] remains genuinely substantive (`norm_num` on the Mathlib π bound).
