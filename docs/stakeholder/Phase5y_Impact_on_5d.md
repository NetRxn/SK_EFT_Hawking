# Phase 5y Impact on Phase 5d (RHMC ADW Fermion Bootstrap)

**Date:** 2026-04-23

---

## Headline: ZERO impact, 5d orthogonal

**Phase 5d (RHMC ADW fermion-bootstrap) is structurally orthogonal to
Phase 5y. ADW condensation as a mechanism for generating tetrad physics
is independent of the dark-energy application.** 5d continues on its
own timeline.

---

## Why 5y's closure doesn't propagate

Phase 5d is concerned with:
- **Rational Hybrid Monte Carlo** (RHMC) simulation of the ADW
  gap equation at `L = 4` and `L = 8`
- **Fermion-bootstrap construction** of the emergent tetrad VEV
- **Non-perturbative validation** of the gap equation's phase
  structure

The 5y closure concerns the late-time dark-energy **application** of
tetrad condensation (via vestigial gravity). The **mechanism**
(ADW → emergent tetrad → emergent gravity) is unaffected by 5y's
dark-sector NO-GO. ADW remains the most viable Layer-3 construction
for emergent GR in the SM+GR-sector predictive scope (per
`ARCHITECTURE_SCOPE.md`).

---

## Relationship to vestigial gravity

Phase 5y Wave 6 extends `TetradGapEquation.lean` with:
- BCS-like `T_{c,vest} = Λ_UV · exp(−1/g̃_*)` (EQ.108)
- Natural-scale obstruction: no mechanism ties `T_{c,vest}` to `H(t)`

These extensions are:
1. **Compatible with 5d's RHMC program** — they add algebraic content,
   not constraints on simulation parameters
2. **Useful for 5d's gap-equation analysis** — the natural-scale
   obstruction frames why certain coupling regimes give BCS-like
   condensates versus symmetry-restored phases
3. **Independent of 5y's DESI-incompatibility** — the `T_c` value
   matters for lab physics / ADW phenomenology, not for cosmological
   dark energy

---

## Forward motion on 5d

**Unchanged.** 5d continues with:

1. **L=8 RHMC production runs** (per `project_rhmc_eo_optimization`)
2. **Even-odd decomposition optimization** for 2× speedup
3. **Data reorganization** to `data/rhmc/L{L}/`
4. **Gap-equation phase diagram** extraction

---

## Action items for Phase 5d

**None driven by Phase 5y closure.** Optional: reference Wave 6
TetradGapEquation extensions (`T_c_vest`, `uv_tied_Tc_not_hubble_tied`)
in future 5d memos for algebraic context on why `T_c` is a UV-controlled
scale.

---

## References

- `docs/stakeholder/Phase5y_Closure_Summary.md`
- `docs/ARCHITECTURE_SCOPE.md`
- `lean/SKEFTHawking/TetradGapEquation.lean` — Wave 6 extensions
- `project_rhmc_eo_optimization` memory entry

---

*Phase 5y cross-phase impact memo. One of five Wave 9 deliverables.*
