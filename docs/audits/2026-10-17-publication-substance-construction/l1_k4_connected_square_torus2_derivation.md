# Connected square and torus sharing a jointly fixed source

Status: design only. The next42 continuity packet checked fresh. All work below used Python standard-library graph, AST, JSON and hash operations. No scientific module, Haar moment, gamma preparation, fixed control or coefficient was executed. ROOT owns candidate and notebook writes.

## Remainder and complete next class

The canonical 272-word manifest is pinned by SHA256 `ada6e3a7bd8b32b238a85f1a8e7070dde1d2846f5fe6bc5184068a0fc9596d5b`. Its original five disjoint accepted populations contain 90+86+6+30+8=220 words. Actual `EXPECTED_WORDS` constants were read by AST from the canonical additional modules for 106/142, 191/202/238/239 and 243/245/257/270. Their disjoint union has 230 scientifically accepted words. Public portable scope at assignment remains 226 until ROOT completes the last archive acceptance.

The exact remainder has 42 indices: 28 same-axis and 14 mixed-axis. The complete roster, eight accepted populations and source hashes are in `l1-next42-author-geometry.json`. All 42 residual core graphs were independently repeeled from their existing manifest rows using standard-library graph operations, and the original degree-eight condition was checked at every site. No new index was generated.

The smallest complete coherent next class is **78/80**, both with sources `((0,2),(1,2))`. Each residual core has five faces and is connected before gauge fixing: a fully protected square shares exactly one directed source link with a four-face `(2,3)` torus.

| Word | Square; live link | Three fixed square links | Shared source; torus bases |
|---|---|---|---|
| 78 | `(0,0,2)`; `(0,0)` | `(0,2),(1,2),(4,0)` | `(1,2)`; `1,5,9,13` |
| 80 | `(1,0,2)`; `(1,0)` | `(0,2),(1,2),(5,0)` | `(0,2)`; `0,4,8,12` |

Both sources are fixed on the square's three-edge tree, spanning sites 0,1,4,5. The shared source is the torus's only protected directed boundary link. The square and torus boundaries intersect exactly in that link. Neither source's geometric edge carries an action frame: J=0. There are 20 action geometric edges, 15 paired action vertices and ten peeled curvature pairs.

## Conditional Haar factorization

Let F be the three fixed square links, r the shared source, ell the square live link and T the torus boundary. The verified set relations are:

- F contains both source links.
- Square boundary intersect T is exactly `{r}`.
- T intersect the protected links is exactly `{r}`.
- F intersect T is exactly `{r}`; ell does not belong to T.

Fix all F links jointly to identity using the previously accepted normalized Haar forest gauge. The three links are acyclic, so its volume is one, with the same Spin/Grassmann change-of-variable convention as the accepted both-source square construction.

After that joint fixing, the conditional five-face curvature polynomial is

`square_pair(ell; F=I) * torus_four_pairs(T minus {r}; r=I)`.

The remaining Haar variables are disjoint: ell versus seven torus links. The formerly shared variable r is now deterministic identity in both curvature blocks and in its explicit source polynomial. Conditional Haar integration therefore factors exactly. This does **not** average the unfixed shared variable independently, and it does **not** factor the final Grassmann/source coefficient.

The square live holonomy stays joined to its action frame through the existing `square_factor` and `probed_action_edge`. The seven remaining torus links carry no action or source factors, so their conditional integral is precisely the existing fifteen-term `protected_branches(linked,other)` tensor. The source polynomial on r is not contained in that curvature tensor: it remains once in the explicit source loop. Both original source insertions remain exactly once.

## Curvature centers versus action centers

This distinction is essential because accepted `prepare` uses square-component weights at `at_center` and `core.get(q)` elsewhere.

| Word | Square curvature center | Torus curvature centers | Live-edge action center | Fixed-edge action centers |
|---|---|---|---|---|
| 78 | 0 | 1,5,9,13 | 1, using `core.get(1)` | 4 peeled; 5 using `core.get(5)` |
| 80 | 1 | 0,4,8,12 | 0, using `core.get(0)` | 4 using `core.get(4)`; 5 peeled |

The square curvature center is disjoint from the four torus curvature centers in both words. Thus the square `(comp,)` selector never overwrites a torus domain. But the square's live action center is a torus center. Its gamma label remains attached to that torus-weighted center factor, and the same label enters the live probed edge. The torus gamma restriction and square probe are therefore coupled through the unchanged factor graph.

The other square geometric edge is 4–5 and carries **two** action labels, `(4,0)` and `(5,0)`. Both are retained. For word78 the fixed directed anchor is `(4,0)`; for word80 it is `(5,0)`. Accepted `fixed_action_edge` receives both labels, both endpoint-center flags and the actual fixed-anchor orientation. One directed anchor is fixed; the opposite directed anchor remains Haar integrated. The early written description mistakenly used a singular fixed action center; the failed metadata assertion is preserved in `l1-next42-author-incidence-attempt1.json`. The proposed scientific source already retained both labels and was unchanged.

A symbolic factor-graph audit, without numerical gamma or Haar evaluation, gives 38 factors, 32 labels each occurring twice, and Grassmann degree eight at all sixteen sites. The graph retains all 20 action edges and both source polynomials. This audit and the per-center domain selector are recorded in the geometry JSON.

## Normalization, signs and covariance

E=20 and J=0 in both words. Each action geometric edge supplies two raw directed moments, giving `192^40`. Both fixed source identity moments still carry one factor of 192 each, giving `192^42`. Sixty action coframes plus four source coframes give `4^64`; ten peeled curvature pairs give `48^10`; fifteen paired factorials give `2^15`. The exact divisor is

`192^42 * 4^64 * 48^10 * 2^15`.

The explicit square and fifteen-term conditional torus tensor retain all five unpeeled curvature pairs. Their exact rational branch weights remain external. There is no extra `48^4`, duplicated shared-source moment, source-order factor, shear factor or axis multiplicity.

All endpoint coframe signs, exterior products, Gaussian integers and remaps use existing accepted kernels. The square live physical anchor is opposite its action center in both words. The two-label fixed action edge retains the actual directed anchor. Both source Gamma sums are evaluated at identity and remapped to their own endpoints. Row and pair caps remain 120000 and 3000000.

Actual XOR1 translation maps word78 to80, including omitted site 2 to3, every changed frame, both sources, the shared source and fixed-anchor direction. Both sources have axis2; their interchange has positive parity because each source factor has Grassmann degree four. The single protected-torus branch order maps directly; there is no two-torus branch transpose. This is a geometry prediction only: no coefficient equality has yet been computed.

## Proposed source and necessary next controls

`l1-next42-author-source-r1.py` has SHA256 `d5244fb68dbb9f10fd098a1b0e7f94679bfed53c43e0eb2271aed0031b64f68f`. Its `prepare`, `contraction` and fifteen-branch `solve` ASTs are identical to accepted source `5f3252854e81ef1c569cf99da7d12aae1e13d40dcdb0409b0a06ac95b6220289`. Only geometry/data selection changes. Sixteen principal source hashes were rechecked unchanged. The proposal is **AST-only and unrun**.

Before any complete pilot:

1. Independently verify the exact 42-word remainder and the two geometries, including both source links, F3 forest, singleton shared boundary, all action labels, and the curvature/action-center distinction above.
2. Validate the joint conditioned five-face Haar polynomial against explicit square coefficients times the fifteen-term torus formula. Include same/opposite chirality, mixed components and exact multi-coordinate SU(2) quaternions to activate off-diagonal probe monomials, as well as basis samples.
3. The actual canonical `mixed_curvature_core.integrate` assumes each integrated edge is shared by two factors and one scalar factor remains. After r is fixed, the square may be an external or constant disconnected factor. Do not call this API blindly on all five faces and interpret its final single-factor assertion as missing physics. Use torus `conditional` plus direct square `face_vector`, or an independent scratch polynomial reference that multiplies disconnected scalar factors at closure. No production kernel change is required by this construction.
4. Check both fixed source identity polynomials and endpoint remaps, each inserted once. Check the opposite-center live probe and the two-action-center fixed edge for both physical anchor orientations.
5. Prepare all fifteen branches for both words. Inspect actual gamma weights at live and fixed action centers against their torus or peeled selectors, rather than only counting labels. Verify degree eight, two occurrences per label, exact weights, bindings and unchanged caps. Then run bounded fixed-Gamma controls and XOR1 raw/weight/divisor covariance.
6. Only after independent design/direct/fixed review and ROOT authorization, propose one complete word78 pilot with 600-second cold preparation, 60 seconds for the whole fifteen-branch warm solve, and a 665-second parent bound.

All 42 coefficients remain owed. No full k4, common partition, complete source/action ensemble, physical B3, modes or transport result follows from this design.
