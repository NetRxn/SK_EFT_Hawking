# Phase 5w Wave 10 — Pickup Document

**Written:** 2026-04-16 (end of Phase 5w session)
**Status:** Waves 2-9 COMPLETE, Wave 10 partially complete (10b + 10d done, 10a blocks on deep research, 10c deferred)
**Next action:** Integrate deep research result when returned, then execute Wave 10a

## What's done

### Waves 2-8 (all 12-stage pipeline, committed)
- `DiracFluidMetric.lean` (9 thms): 3×3 acoustic metric, block-diag, horizon
- `GrapheneHawking.lean` (6 thms): T_eff positivity, EFT bound, dispersive correction
- `DiracFluidSK.lean` (9 thms): transport counting, WF, KSS, EFT perturbativity
- `src/graphene/` (6 modules): hawking_predictions, wkb_spectrum, transport_counting, platform_comparison, bilayer_eos, __init__
- `src/core/formulas.py`: 7 graphene formulas added
- `src/core/constants.py`: GRAPHENE_PLATFORMS (4 platforms), E_CHARGE, V_FERMI_GRAPHENE, etc.
- `src/core/visualizations.py`: 4 figures (102-105)
- 5 test files, 95 tests (all pass)
- Paper 16 draft (6 pages, 4 figures, reviewed by 3 Opus agents)

### Wave 10 (partially done)
- **10b DONE** (`691c17a`): bilayer EOS — ζ/η ≈ 0.02, negligible impact
- **10d DONE** (`3e2a451`): bandwidth-cumulative SNR — 1 min (not 27)
- **10a BLOCKED**: noise formula derivation — deep research filed at `Lit-Search/Tasks/Phase5w_landauer_buttiker_noise_electronic_analog_horizon.md`
- **10c DEFERRED**: quasi-1D Lean bound — low priority

## What blocks

The ONE remaining blocker is the noise formula derivation (Wave 10a). Currently the paper's S_I(ω) formula is:
```
S_Hawking(ω) = (2e²/π) σ_Q ω n_Hawking(ω)
```
This is a leading-order estimate, not a first-principles derivation. The paper acknowledges this caveat. The deep research task asks for:
1. Scattering matrix for the sonic horizon
2. Landauer-Büttiker noise → Hawking mapping
3. Keldysh propagator → S_I derivation
4. Correct prefactor with geometry dependence

## When deep research returns

1. Read `Lit-Search/Phase-5w/` for the new result
2. Check: is our formula correct to within a factor of 2? 10? Or completely wrong?
3. If correct: update Paper 16 §IV.A with derivation, remove "leading-order estimate" caveat
4. If wrong: recompute all noise spectrum predictions, update figures, rerun tests
5. Create `GrapheneNoiseFormula.lean` with the Keldysh → noise PSD theorem
6. Update `wkb_spectrum.py` with the corrected formula
7. Rerun all 3 review agents on the updated paper

## Key physics findings (don't lose these)

1. **δ_diss negligible by 11 orders**: The SK-EFT's main value for graphene is the framework (systematic organization + verification), not the dissipative T_H correction
2. **Bandwidth-cumulative SNR**: 1 min for SNR=1, 25 min for 5σ — much better than single-bin 27 min
3. **Bilayer conformality**: ζ/η ≈ 0.02, negligible impact on T_H and δ_disp
4. **First-order count coincidence**: 2 coefficients in both 1+1D BEC and 2+1D conformal — different physics, same count
5. **Dissipation window marginal**: ω_H/Γ_mr ≈ 1.6 for Dean (improves to ~5 with cleaner samples)

## Collaboration outreach readiness

The detection protocol is concrete enough for Lucas/Dean outreach:
- T_H ≈ 2.4 K, D = 0.23, EFT valid
- Detection band: 0.5-85 GHz
- Bandwidth-cumulative: SNR=1 in ~1 min, 5σ in ~25 min
- Formal verification: 24 Lean theorems, 0 sorry

**Do NOT send the noise formula to experimentalists until Wave 10a is resolved.** The order-of-magnitude prediction is right but the prefactor may be wrong.

## Why the noise formula can't be shortcutted (explore agent finding, 2026-04-16)

Checked all existing BEC/polariton infrastructure for a template:
- **BEC** (`wkb/spectrum.py`, `wkb/bogoliubov.py`): maps n(ω) → density correlations with NO explicit prefactor formula. SNR uses Poissonian shot counting: signal = |deviation| × n, noise = √n. No current noise, no e² factors.
- **Polariton** (Paper 12): maps n(ω) → stimulated gain G(ω) via probe photon counting. Still no universal formula — uses device-specific greybody Γ(ω).
- **Graphene**: ONLY platform that needs n(ω) → S_I(ω) in A²/Hz. This requires a scattering matrix for the horizon, which doesn't exist anywhere in the codebase.

The `(2e²/π) σ_Q ω n_Hawking` formula is a dimensional analysis ansatz, not a derivation. The deep research task is the correct path — no shortcut exists.

## File locations

| Item | Path |
|---|---|
| Roadmap | `docs/roadmaps/Phase5w_Roadmap.md` |
| Deep research (main) | `Lit-Search/Phase-5w/5w-SK-EFT Hawking framework meets...md` |
| Deep research (noise, pending) | `Lit-Search/Tasks/Phase5w_landauer_buttiker_noise...md` |
| Paper 16 | `papers/paper16_graphene_sk_eft/paper_draft.tex` |
| Lean modules | `lean/SKEFTHawking/DiracFluidMetric.lean`, `GrapheneHawking.lean`, `DiracFluidSK.lean` |
| Python modules | `src/graphene/*.py` |
| Tests | `tests/test_graphene_*.py`, `tests/test_platform_comparison.py` |
| Figures | `figures/phase5w/fig102-105_*.png` |
| Constants | `src/core/constants.py` (GRAPHENE_PLATFORMS section) |
