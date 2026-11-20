# Independent Task1 original-physics/source review R1

**REVISE_TASK1_IMPLEMENTATION_SOURCE_AND_BOUNDED_TESTS.** One required P2 correction: the local-degree certificate falsely certifies vanishing at its inclusive maximum degree. The remainder of the reviewed Task1 scientific construction is consistent with its bounded specification; this report grants no acceptance pending repair and independent reassessment.

Reviewer: different original-physics/spec/source reviewer, parent publication-remediation, ROOT sole notebook writer and intake owner. Owned outputs are only this report and its JSON companion. PRIMARY source is 056ccb9f08454238934977de4bb6548d18c6275e plus the three frozen assigned paths. Other reviewers share read-only PRIMARY; ROOT's broader profile runs in a different worktree. No source/Git/Lean/MCP/build/cache/controller/registry/notebook edit, full pytest, heavy coefficient evaluation or campaign occurred.

## Required correction: SCIENCE-1 (P2)

`src/vestigial/original_coefficients.py:532-533` implements `vanishes_above(degree)` as `degree >= self.degree_bound`. But `degree_bound` is the maximum potentially surviving coframe degree: 8 for N16 centered support, 4 for a self-neighbor one-site coframe. The accepted R2 section2 explicitly kills degrees **greater than**8 and retains degree8 in the compensation construction. The comparison drops the limiting layer. `tests/test_original_coefficients.py:195` explicitly entrenches the error by asserting `cert.vanishes_above(8)`.

This is an actual false certificate, not an inferred future risk or proof-absence claim. Independently evaluated a tiny original, valid-group fixture: V=1, periodic four-torus, all four links `U_L=U_R=i sigma_3` (quaternions (0,0,0,1)), and `T_(origin,mu=0,A=3)` assembled from all four original blocks. Its matrix is `-i gamma_3 diag(sigma_3,sigma_3)`, determinant1. The code returns a local certificate with bound4 and `vanishes_above(4)=True`; its exact exterior fourth power is **24 Theta**, mask255 with scalar coefficient24, hence nonzero. This is a supplied-unit-link coframe calculation, not an integrated coefficient or full one-site W calculation. The four successive products consumed only64 scalar products under a1000-product scope.

Reproduction (existing PRIMARY .venv):

```python
from src.core.formulas import original_spin4_link, original_coframe_blocks
from src.vestigial.original_coefficients import (
    OriginalRegulator, assemble_coframe, local_degree_certificate,
    ExteriorPolynomial, Polynomial, ScalarCost,
)
r = OriginalRegulator((1,1,1,1)); x = (0,0,0,0)
u = original_spin4_link((0,0,0,1), (0,0,0,1))
links = {anchor: u for anchor in r.link_order}
f = assemble_coframe(r, original_coframe_blocks(r, (x,0,3), links)).to_exterior(r)
c = local_degree_certificate(r, x, [f])
p = ExteriorPolynomial(((0, Polynomial.scalar(1)),))
with ScalarCost(1000):
    for _ in range(4):
        p = p * f
# c.degree_bound == 4; c.vanishes_above(4) == True
# p.terms == ((255, Polynomial.scalar(24)),)
```

Required repair: use the strict upper comparison (or an equally explicit API with correct inclusive-bound semantics); assert the helper is false at8 and true at9 for N16, false at4 and true at5 for the actual one-site boundary, and retain a nonzero limiting-power fixture. Keep `production_authorized=False` and default global4V. The inactive production status bounds current impact but does not make a false certificate acceptable for the Task1 API or its Task2 consumer.

## Entire Task1 scientific assessment

Read all657 lines of the new domain, all382 test lines, and the entire appended formula section. The unchanged formulas body was not independently re-reviewed: ROOT's exact original-prefix conservation is retained as supplied intake evidence; the fresh packet and frozen whole-file hash were independently checked. Read complete ROOT review notebook, accepted R2 narrative, both independent prospective reviews, actual author report/structured evidence and raw final/red test logs. Relevant original inputs directly inspected include original composite/auxiliary notes, actual Grassmann Eq7 design and implemented-source review, and current actual coframe/source Lean definitions and theorem bodies/signatures. The roadmap's current original B3/transport BUILD boundary was checked. Broad combined displays that truncated were followed by narrower source/plan reads; no conclusion relies on hidden output.

1. **Geometry and coframe:** positive extents and paired real boundary signs are frozen as tuples, four independent psi/bar indices per site, 64 distinct anchored Spin4 links on N16. `step` applies the same real sign on the reversed crossing. The four matrices are respectively `gamma U_f†`, `U_f gamma`, `gamma U_b`, `U_b† gamma`, with +/−/−/+ quarters. `assemble_coframe` adds every slot; L2 coincident neighbor positions retain both independent anchors. L1 self-neighbor addition produces the required anticommutator. No bare mass/kinetic, Majorana, Pfaffian or absolute determinant is introduced.

2. **Quaternion and gamma:** plus-i entries are `[[q0+iq3,q2+iq1],[-q2+iq1,q0-iq3]]`; these are unitary/determinant1 on each real sphere sum(q_a²)=1. Polynomial code intentionally works in the ambient real-coordinate polynomial ring before Haar; it does not quotient by sphere identities or treat coordinates as independent Gaussian measures. Separate L/R anchor labels retain the 128 SU2 sphere domains. Numeric unit-quaternion fixtures satisfy the constraint. The constructor is a polynomial extension, not a numeric sphere validator. Canonical C gamma upper blocks are (-i sigma_x,-i sigma_y,-i sigma_z,I); lower blocks are adjoints. Gamma5 is diag(I,-I). This matches actual current Lean definitions, and the C ordered product is +gamma5.

3. **Ordered source:** printed `A B C† D†` and closed `D† C† B A` use the four actual forward anchors and retain factor order. Complete raw S4 has24 internal epsilon terms/site with fixed world directions and no extra factorial. Raw S2 has24 ordered world tuples times16 internal pairs/site, g2/4 stripped only for coupling bookkeeping. Ordered trace retains scalar/diagonal pieces until actual antisymmetrization; no prefilter silently removes them. Factors mark T-degree4/2 without hardcoding numerical coefficients or integration outcomes. Source exp(+S) and arbitrary supplied couplings remain the accepted convention.

4. **Complete Euclidean dictionary:** M in this API is Euclidean M_N, pi=(3,0,1,2), with fixed gamma5 and ordered gamma product -gamma5. World and internal axes, sites/extents/paired signs, every independent anchor, J/h labels, unchanged spinors/chiral blocks, metric unordered pairs, frame ordered pairs, phase/current site labels, variance and Berezin order are mapped explicitly. Two odd epsilon transports cancel for S4; only the world sign contributes to S2, so g1 is unchanged and unsquared g2 changes sign. Tests use nonzero raw g1/S2, both words, noncommuting unit links and a real source-C compact-link coefficient -2 rather than relying on even-g2 agreement. Metric/current/frame labels here are the pre-Haar dictionary foundation; full derivative/contact implementation is Task2, not accepted as already executed.

5. **Independent cut:** temporal_axis is independently selectable, validated and transported as a world index. Unreflected coframe/action do not depend on it. Reflection metadata uses gamma at the chosen cut and reverses the temporal anchor endpoint. The C3↔N0 dictionary does not identify physical WORLDcut P0 or Lorentz L_P; equality of one displayed gamma matrix cannot establish full field/source/cut/antilinear-kernel correspondence. No test or producer in this Task1 scope consumes the Task3 physical metric certificate. The additional actual physical-P0↔C3/N0 certificate identification remains Executor BUILD. No Lorentz reconstruction, physical positive domain or reflection positivity is adopted here.

6. **Berezin and support:** output local top barL1 barL2 psiL1 psiL2 barR1 barR2 psiR1 psiR2 differs from local all-bars/all-psis by four crossings; permutation of degree8 site blocks has positive sign. Actual supplied permutation-matrix top test discriminates determinant orientation. N16 structural counts256 components/1024 increments/8192 scalar writes/4096 coframe slots/16384 coordinate terms/512 Dirac entries are construction metadata, not integrated coefficient populations. S2 has eight distinct anchored links, the whole site action twenty. Fermion/support records are conservative envelopes before cancellations and do not factor shared Haar variables. Four directed16x16 determinant blocks follow parity flip and chirality flip; explicit row/column permutation signs are retained. Reachability53137 masks/200076 transitions per block is unsigned Boolean metadata, with no nonzero or factorized-integral claim.

7. **Local support lemma:** the min-center-generator argument and min(4V,floor(8/minimum)) bound are valid support upper bounds for supplied centered bilinears; the ninth N16 product envelope is empty. Centered frame combinations preserve that support; noncentered inputs are refused. The mandatory finding is the helper's inclusive comparison, not a rejection of the degree8 construction. Production global4V stays unchanged.

8. **Grounding:** actual current Lean `FiniteGrassmannCoframe.{q,gamma,gamma5,dirac,coframe,hopping,hopping_reconstructs_coframe}` and `FiniteGrassmannSourceAuxiliary.{plaquettePrinted,plaquetteClosed,cosmological,einsteinCartan_ordered,coframe_source_evaluation}` ground their stated definitions. Current C3 is not inferred absent from a stale dependency catalog. These real declarations do not kernel-prove this executable quaternion parametrization, entire M/C transport, new local8 certificate or the full Eq9 matrix-bilinear/Eq10 Berezin-determinant bridge. Those remain explicitly scoped Stage2/3 work. I did not repeat ROOT's actual LSP checks, invoke Lean or claim fresh kernel evidence.

## Test and conservation evidence

The author raw final log says29 passed in8.52s (24 Task1+5 dependency tests), with largest reported fixture70016 scalar products and actual symbolic Dirac object graph9131398 bytes. These are observed author receipts, not my independent rerun or scientific proof; the different algebra/error reviewer owns the bounded rerun. My independently executed64-product counterexample disproves the certificate despite that green suite. Object-graph bytes are not RSS or a250M/70M scientific execution fit.

Before source inspection, I read the assigned packet first and independently compared every authority/reference and owned-file SHA256; all matched. The first official `codex_continuity.py check` occurred later during review and returned exit0,fresh=true,changed=[]; it was not literally my first tool action. Final SAME-packet official check also returned exit0,fresh=true,changed=[]. All three source hashes were independently conserved:

- formulas.py: 0293e17b4b0c73aa2e39d8741bb631acea1f30a45bf87ede9cde6375cdcd696d
- original_coefficients.py: dbda2b494204116771f44ffca72757b14f79a44ddb0dc22faf7ab1ce020323dd
- test_original_coefficients.py: d50977905e85a9143d60a09291b766186f3b4282d3aba1e34be0a8f2c348794f

No snapshot refresh or hidden source repair occurred. Hash/freshness check proves conservation, not correctness or acceptance. No direct primary-PDF re-review or web research was needed for this bounded implementation/spec review. A lightweight memory registry query supplied no original-coefficient-specific evidence and no memory-derived assertion was used.

## Preserved original debt

Task2 remains owed in full: family-graded raw jets, singular-safe complementary minors, Hermite W/Gaussian/Haar kernels, all first/repeated/mixed source/frame/current/measure/denominator contacts and refusal APIs; then separately admitted complete original V1 direct versus W4 control, all3876 source quartics/740 center-compatible slots, full4029 W entries/23504 queries, both words and variances2/3, full interacting denominator and literal-T/ten-H/frame jets. The limiting-degree repair must not delete this target.

Task3 remains owed: complete original N16 invariant36-entry tables by independent direct/minor routes, full24-minor roster/projectors, all F60/G52 temporal/spatial contacts, both chiral loops, anchors and exclusions under separately admitted70M allocation and source/error review. No physical certificate cross-consumption before actual P0↔C3/N0 identification. Expected45/4,12 and other values remain regression outputs.

Task4 remains owed: exact split-factor complete denominator/source frontier and viable reviewed full allocation, actual full coefficient calculation and nonzero normalization certificate. Full source calibration/projector/state/domain/product/adjoint, B2 correspondence, physical susceptibility/B3 normalization and derived interval, stable modes/matter/transport, controlled thermodynamic/source/continuum limits and publication gates remain OPEN BUILD. This review closes no canonical finding, full B3, main/full-tree/native or publication gate.
