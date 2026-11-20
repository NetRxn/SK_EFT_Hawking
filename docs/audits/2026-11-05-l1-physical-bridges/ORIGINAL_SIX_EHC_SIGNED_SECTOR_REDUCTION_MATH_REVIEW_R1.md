# Actual mathematical review of the original twelve–six signed reduction

**ACCEPT** the exact coefficient reduction, including the 32-row cancellation and the aggregate for the 12 distinct-class rows. No required mathematical correction. This review concerns candidate `/private/tmp/l1-sixehc-signed-sector-reduction-r1.md`, 19,802 bytes, SHA-256 `84e5a541aba0a138d7e59ce938119e38b4e55a19b64540da0712ed01b229d8e6`, at source `8efe7d579f993b18b807aea75cd600f494b67cc1`. Parent is publicationROOT01a13f67/L1-physical-observable-boundary. Executor01a1ac65 owns the primary notebook and writes it. The R2 handoff packet returned fresh on entry. This is independent actual mathematics review.

## Complete coefficient and fixed record check

Source construction equations (1)–(3) give the reduced original interslice source cases with weights 8 eta times the polarization sign, the complete signed curvature classes, and exactly one occupation/class factorial denominator. The retained class epsilon diagnostic does not multiply these complete classes. The accepted necessary-support argument allows all excluded terms to be set to zero. A retained term can still vanish.

I decoded all 44 little-endian records directly from the accepted archive in binary order, checking the class IDs and their actual descriptors, case IDs, source vertices and axes, times [0,1], weight, epsilon diagnostic, root, divisor, occupations, curvature parity, version and padding against the manifest and corresponding TSV row. The archive, binary and TSV digests respectively are:

- `0c75e293a7c352adc3147caffecdf8c30526d4fc0681ac9b53c5e037fd0c65a1`
- `5d4954553ce10c37da75e6ff1cbfc1bcb84d21be58904cbd5956a9ae41bfaa26`
- `4d7456c8f95ca49347c34c275aa8e08cc5ec689effed039534bd5b8f37e7a14b`

The partition is exactly 16 rows each of weights -8 and +8 at divisor 512, and 4 rows of weight -8 and 8 of +8 at divisor 1. The row-22 original raw weight -1/2 has the same divisor, so its reduced weight is larger by a factor of 16. The first source is always centered at 0 in the stored rows. Actual second source locations and axes agree with the candidate, including choices centered opposite the curvature-carrying anchor.

## Both endpoint Fourier proofs

For anchors U at x and V at y, the x coframe is [F_x(U)−F_x(V†)]/4, with the gamma positions in ORIGINAL_SHEAR14_ONE_CANDIDATE equations (16)–(17). The y coframe is [F_y(U)−F_y(V†)]/4 with F_y(U)=bar_x U† gamma_A psi_y−bar_y gamma_A U psi_x. In a chosen chiral block of U the latter repeats the same algebra with the barred and unbarred doublets now chosen for the actual endpoint gamma position, and B_A=q_A U or q_A† U in place of U q_A or U q_A†. Four unit quaternion basis matrices still have determinant one, and their completeness relation under real orthogonal right multiplication is the same. Each b p and p b term therefore has coefficient -8 in the four-square sum. The cross regrouping swaps an odd number of odd generators, converting -2 to +2 before quaternion completeness gives +4 n n. This gives 4K in the sum of the chiral terms, matching the original K even when the active chirality tracks the opposite end's fields. No gamma commutation is needed.

Independent V averaging kills the cross-anchor terms and leaves its constant 4K contribution with quarter-squared normalization. The mixed chiral term in F(U)^2 has zero average over the chiral group external to a single D1 insertion. The constants multiply a mean-zero adjoint matrix entry. Changing the active anchor is a Haar-preserving exchange with inversion, under which the sign of a single coframe cancels in the square. An inverse in the actual holonomy gives the transpose of D1 and does not change coefficientwise vanishing. Unweighted both-group averaging yields K/2 for the full Q. This argument requires all outside factors to be independent of both source anchors except the single displayed D1 insertion. It preserves the common exterior algebra, so shared fields in the outside polynomial do not invalidate it. The accepted exact ordered-monomial component values (-1,-1,+1,+1)/48 verify that the FULL-Q trace is essential. This is an inherited analytic control.

## Doubled rows and normalization

I verified the hole/class data, non-saturated edges, carrying anchor and its dagger flag, and the absence of the source edge in either other face for every row in the 32-row sector. In the following table, the two source anchors are the carrying ones in holonomy order convention, by vertex and axis. They need not be the source Q centers.

| Rows | Holes x,z and bridge b | Carry at x | Carry at z | Free hole order |
|---|---|---|---|---|
| 0,1 | 4,1,5 | (4,2)† | (1,3)† | x first |
| 10,11 | 4,13,5 | (4,2)† | (13,2) | either |
| 12,13 | 0,9,1 | (0,2)† | (9,2) | either |
| 16,17 | 0,5,1 | (0,2)† | (5,3)† | x first |
| 18,19 | 4,7,5 | (4,2)† | (7,2)† | either |
| 20,21 | 4,7,5 | (4,2)† | (7,3)† | either |
| 22,23 | 0,3,1 | (0,2)† | (3,2)† | either |
| 24,25 | 0,3,1 | (0,2)† | (3,3)† | either |
| 26,27 | 4,7,6 | (4,2)† | (7,2)† | either |
| 28,29 | 4,7,6 | (4,2)† | (7,3)† | either |
| 30,31 | 0,3,2 | (0,2)† | (3,2)† | either |
| 32,33 | 0,3,2 | (0,2)† | (3,3)† | either |
| 34,35 | 4,13,12 | (4,2) | (13,2)† | either |
| 36,37 | 4,13,12 | (4,2) | (13,3)† | z first |
| 40,41 | 0,9,8 | (0,2) | (9,2)† | either |
| 42,43 | 0,9,8 | (0,2) | (9,3)† | z first |

Every undirected edge is represented once in the paired allocation, each with two coframes at one endpoint. The bridge face omits the hole vertices, hence their frame edges. If the first hole's frames are blocked, the other face has reached its vertex through the equality S_z=I. The symmetric obstruction requires S_x=J. Both together put both source edges through the other shared neighbor x+J=z+I, contrary to their distinct time slices. For each free hole the full same-endpoint frame-pair identity gives R(H) after extracting the edge factors. Its world epsilon is squared. Its sole active source anchor occurs once inside each adjoint character, and the independent partner is absent from all curvatures. Thus the full-Q lemma eliminates both correlated characters termwise, yielding 24 and K/2. The remaining hole then has free frame edges and the same argument applies.

The core retains only the bridge face. Exactly four occupied D² centers are free on every leg, yielding 24 per center from the identical two internal epsilons. The two surviving core corners have two free directions. The two-index epsilon contraction is twice the antisymmetrizer difference of delta pairings. Applied to the two remaining coframe directions it yields 2G at each corner, with the subtractive mixed square and G(t,t)=0. Four hole-frame pairs plus two bridge-frame pairs plus sixteen full D² pairs plus four partial-D² pairs is 26 factors K/8. With the two remaining K/2 source factors the 28 noncore edges are each represented exactly once. The two source halves cancel the factors 2 from the pair of partial epsilons. Together with the two removed R constants and four fully contracted D² constants this gives the common prefactor 8^-26 times 24^6, with literal quarters retained in the core.

The candidate's permutation and XOR map sends every core to {1,5,9,13}, with b at 1, partial epsilons at 5 and 9, and the remaining 28 edges bijectively outside this core. The site relabeling carries eight odd generators at a time, so each exchanged block gives positive top sign. Anchors permute as independent normalized Haar variables. Internal field order and gamma placements are preserved. The squared world epsilons leave no parity factor, and the curvature character is invariant under inversion. Slice translation enters only after both actual sources are integrated. Therefore all 32 unweighted amplitudes agree with the same U and their actual signed weights cancel. This proof does not evaluate U or kill its remaining bridge adjoints.

## Distinct classes and original aggregate

I checked the fixed maps row by row: (2,14), (3,15), (6,38), (7,39) under axis swap 1↔3, and (4,8), (5,9) under translations xor1 and xor5 respectively. The maps take the actual full six-class, occupation and source rosters to their partners. Axis permutations act on the world slots while preserving internal labels. Sorting an inverted plaquette gives H† and F(H†)=−F(H), as follows from the chiral quaternion expressions linear in its vector parts. Swapping the complementary frame order adds its antisymmetric sign. With the world epsilon these give one det(pi) per class, and the four world slots in D give one per D. The total exponent 12+6 is even. Source axis 2 and actual time assignments survive the axis swap. Translation may exchange the two sources in the other two pairs, and commuting their even quartics has positive sign. The original coefficient weights, checked directly, cancel the first four pairs and add the final two pairs. Hence the result is 16(A4+A5).

For rows 4 and 5 the exact common background is the product of the 12 distinct D factors off {0,1,4,5} and the six complete classes (0,02),(4,02),(1,12),(5,12),(1,23),(5,23). Translation xor4 preserves this background and exchanges Q0/Q4 and Q1/Q5 inside their own time slices. This proves 16(A4+A5)=8 L[(Q0+Q4)(Q1+Q5)] and leaves the original two endpoint choices present on each source edge. The aggregate and even-site top argument never require A4=A5.

## Residual cost and scope

The six explicit plaquettes have the proposed ten-edge union. The central edge 1–5 carries three occurrences per anchor, plus two source coframes in any summand, so individual center parity forces a split of one coframe onto each anchor. All other curvature-carrying pairs have 2+0 or 1+1 curvature occurrences and two coframes. Independent chiral center parity in surviving terms gives even degrees at most four. The 64 chirality assignments are a logical count using the two chiral trace blocks of each fundamental curvature factor. They do not enumerate exterior masks or qualify a contraction plan. The 22 noncurve pairs are mixed endpoint. The eight sites outside the curvature-vertex set have ten internal edges and twelve outside legs. Four colors on twelve legs give 16,777,216 dense boundary cells, so a dense table of that type would exceed a 120,000-row cap. A compressed boundary representation or exact bounded slicing and signed reconstruction still need qualification. I did not independently recost the cited optional, already-cancelled four-core control. Its proposed operation and payload figures are not aggregate bounds or runtime observations.

The accepted identity preserves the original 128 odd generators, 64 independent Spin(4) anchors, coframe quarters, product Haar and oriented top. The aggregate, its sign, zero or nonzero value, the full normalized response and the stated physical gates remain unresolved. No execution admission follows.

## Actual review commands

The first and final repository/freshness check is `python3 scripts/codex_continuity.py check /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-sixehc-signed-sector-review-r2.json`. Routine text reads used `cat`, `nl -ba`, `sed -n`, `rg -n`, `rg --files`, `head`, and `tail` on the governing docs, handoff, candidate, notebook/roadmap references, support/one-candidate original definitions, record spec and static encoding source. `wc -c` and `shasum -a 256` checked the candidate; `unzip -l`, `unzip -p`, `jq` and `shasum -a 256` inspected and pinned the accepted existing archive, binary, manifest and TSV. A read-only `python3 -` standard-library snippet using ast, collections, csv, json, struct, zipfile and pathlib decoded the fixed records and checked their exact TSV alignment, their fixed-row edge and anchor incidence, their canonical-core coordinate maps, and the six explicit distinct-class maps. It generated no support and evaluated no field polynomial. `cat` wrote this sole review artifact. No scientific source was run or imported and no support replay, moment, tensor, Gram, CAS, test, Lean, build, slot, or process action was performed.
