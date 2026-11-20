# ACTUAL original-source review — page0 compiler design R2

**ACCEPT** the exact design-stage R2 package at clean source
6830c734218ed094f632092bd372ad9a263a2711. Wrapper 28,132 bytes,
SHA256 04fc0b7cac98d819ea9abd33cab17f7a1b5ff3516c91d4605a7594d7cb0424fb.
Mathematical design 43,922 bytes, SHA256
8cd0d6e177b5633074ee48be49afb1be24555ed9235c6a322366942f116a7b60.
Reviewed full R2 wrapper and math plus the full 30,754-byte diff
(SHA256 355d397242b0a1866800c909b83c41ac0046c1a68da7f167aed3e69b81eac9b0).
No required source correction remains. The immutable R1 REVISE report
retains its exact 11,446 bytes, SHA256
06f0592dcd1034e996f4a8e6968eba6fddbbfba4a4b69ca8c876fab0816bdc82.
The prior source/test, optional ordering, oracle audit, and prior
oracle section keep their original pins and scope. No current peer
R2 verdict was consulted.

## Actual group law and completeness

R2 §2 correctly starts with the two actual central MATRIX factors
U_(r5,c1), V_(r1,c5), and derives the inverse action on their
coefficients. Hub1 raw coefficient types in face order are (g_chi0,
g_chi4^-T); hub5 types are (g_chi0^-T,g_chi4). The E adapters
on c1 and c5 turn each remaining fundamental coefficient into a
dual one, by E g=g^-T E. The adapters are real signed permutations.
The inverse must apply E^T=-E with the contracted indices reversed.
Two original open side vector components at each hub still transform
by the actual orthogonal internal Lambda. No lattice axis has changed.

The held source L is a dual column of components and held R is
fundamental. R2's hatL=E L is fundamental by E g^-T=g E; hatR=R.
The new map occurs only in the HUB numerical basis. Each L flavour's
spin pair changes by determinant-one E, and the full wedge top and
auxiliary original-coordinate norm are preserved. The signed slots
(old1,−old0,old3,−old2) are correct. The original coframes, outside
V and curvature words are untouched. If implementing coefficient
extraction in original Phi, insert E_ij per hatL_i and retain the
odd-product order. These one-nonzero-per-row maps do not change
the spin branch cardinality or introduce a denominator.

There is an independent way to check all paths in (8)–(10). From
g_L^-1 q_A g_R=Lambda_AB q_B and Lambda^T Lambda=1, form an actual
world-component dummy w' = Lambda w. Then Q(w')=g_L Q(w)g_R^-1,
so S(w')=g_L S(w)g_R^T. This gives a fundamental slot in each
chirality. Introduce two such world dummies and the two commuting
fundamental central dummies. Their polynomial paired with a proposed
I(F) must be invariant; each contraction path satisfies this by
g^T E g=E:

- The six same-chi scalar paths pair the two field spinors, the two
  central spinors, and the world δ. The own-triplet path pairs the
  two symmetric field spin entries with the corresponding central
  dummies through E.
- The opposite triplet pairs its field legs into the opposite
  chirality of two S tensors, and each central dummy into the other
  S leg. Summing both ordered world assignments gives exactly m7.
  For equal R the S transpose simply puts the correct chirality
  first.
- In the unequal scalar paths each field pairs with the matching
  central dummy. The unequal (1,1) paths have two E pairings per
  chiral factor, which are symmetrized as in (10). Reversing LR to
  RL exchanges commuting central dummies and leaves the original
  odd field order alone.

Extracting dummy coefficients gives precisely (7c), because the
world action is orthogonal and the two central coefficient actions
are dual. This works for arbitrary independent compact hub actions.
It does not infer covariance from orthogonality of the numerical
basis. The independently accepted invariant type count is eight
per case, so eight independent covariant basis vectors suffice.

The earlier LL adverse example was nonzero at dummy22 with weight
t^-2 instead of t² (equivalently at dummy11 with the reciprocal
failure). Repaired m6 is δ_AB Stilde_L,uv in literal held L fields;
in particular the t^-2 Stilde_L,11 term now sits at dummy11. The
old LR scalar placed L opposite its required index and similarly had
the wrong t exponent; after the new map it is δ_AB L_pu R_qα E_αv
with both correct dual torus exponents. Quaternion multiplication
checks the three listed nondiagonal world maps: −q1 on the left,
−q0 on the left, and q1 on the right give respectively
(−w2,−w3,w0,w1), (−w3,w2,−w1,w0), (−w2,w3,w0,−w1).
These canaries agree with the full arbitrary-group proof. The six
infinitesimal conformance checks have up to six tensor-slot action
terms per cell. The <2^28 subtotal uses one shared 57,344-cell
converted basis, with separate verified raw adapters at each hub.
If the implementation repeats the shared checks twice, <2^29 is
safe and remains inside the 2^33 setup allowance. Neither cost nor
a conformance run is measured here.

## Exact norms, source grammar and serialized shape

The repaired hub transformation is a bijective signed coordinate
map, so it preserves the full Gram, the magnitude ≤4 of pointwise
basis entries, and all norm divisibilities. Independently, the
flavour singlets have squared norms 4,2,4, orthogonal by field
support. The symmetric spin map has norm 12. The δ_AB and E norm
factors are 4 and 2. Orthogonality of scalar and spin-one field
coordinates and the scalar-side trace cancellation split the paths.
This gives (32,16,32,32,16,32,48,576) for equal chirality and four
16 plus four 576 for unequal, with all stated off-diagonal zeros.
The double vector/symmetrizer norm is 4·12·12=576. Full ordered
1792-coordinate norms apply to 1120 packed coordinates only if
the off-diagonal side multiplicity is 2. R2 correctly uses the
dual from those exact norms and inverts the signed adapters on
reconstruction.

The original six T, both Q alternatives, H0=c†b†Ua, H4=d†a†Vb,
two EHC world minus signs, full ordered gamma commutators with
lower gamma5 sign, and their six quarter factors agree with the
accepted original word. Central U,V are undaggered here. Source
edge c,d are different. No additional normalizer belongs inside
page0. The canonical copy representatives 01,02,03 require no
half. Unnormalized Hodge sums would be twice the representatives
and carry complement signs with possible kappa xor1111; no
original kappa or source term is deleted.

Proof of complete branch coverage continues to distinguish
side-first direction bits from the commuting source-first compact
gather. No odd factor moves under that gather. Parity and the
original 2L2R outside tops give the same 5120 labelled rank-channel
and 8192 matching rosters, equally split over both sources. The
hub E maps do not change field categories. At most four two-site
representative/support pairs, four endpoint basis-label pairs,
sixteen paired basis diagrams and four commutator choices give
2^23 graph attempts. Pair-completeness eliminates all internal
vector sums with at most nine factors of two. A graph vertex is
an identity-wire equivalence class of two factor ports. Traversal
uses the ordered monomial factors with the correct original row
even when traversing backward. The repaired count includes at most
four additional E edges, 96 before simplification and ≤128 at
the guard. Two-seed cycles keep the prior 2^128 bound.

With actual moments joint per anchor and at most one surviving page0
P4, the conservative Haar denominator divides 576. The six T
quarters, two curvature halves and basis-dual divisor give D =
4^6·4·576·576² = 2^32·3^6. Haar scale ≤16, dual scale ≤1296
and the graph/width bounds give total absolute prefix <2^175,
inside signed256. Full source arrays have exactly 2304 coordinates
each. Equal-face source sectors contribute the 864/864/576
structural zero obligations for Q0/Q4/sum, irrespective of any
additional zeros. All three arrays, including every zero, occupy
442,368 numeric bytes. The codec, checksums, version, completion
and counter assertions are specified design checks, with execution
and resource qualification still separate.

## Independent oracle and source controls

The unchanged independent oracle is a literal original expression
with 24-cell quadrature on all 12 chiral noncentral anchors,
formal central entry probes and the tagged Pfaffian on twenty
ordered odd generators. It does not reuse the graph parity
grammar. It must compare the original full magnetic expression and
inverse-adapter reconstruction, alongside the three numerically
projected arrays. Agreement in a shared erroneous subspace would
not qualify. R2's exact Gaussian basis/dual and divisibility verify
the conditional signed512 arithmetic envelope. The literal
astronomical full oracle remains unexecuted and ineligible.
Preserve the existing nonzero control values for the central dagger,
distinct Q endpoints, ordered-Z factor, Hodge scale, joint P4,
mixed physical kernel and original tops, separately from the new
covariance tests. No mutation is assumed to change an unknown
complete-page amplitude.

The optional 85,320,272,257-product G ordering is conditional on
correct page/endpoint-closure inputs. It uses the same signed row
across both boundary triples and all 64 assignments. Page1/page3
and local closure compiler costs remain outside that ceiling.
No core or aggregate value/sign/nonzero, complete fit or physical
acceptance follows. No scientific program or test was run and
no repository, notebook, candidate or historical report was edited.

## Readback

First the old review-r1 packet and then the deliberate review-r2
packet returned SAME. Read commands were continuity check, jq,
sed/rg, shasum/wc and git status/rev-parse. All candidate and
supporting design hashes were checked. Final review-r2 packet
returned SAME at clean pinned source. This is design acceptance only.

Implementation accounting clarification: build_integral_basis(face_pair,
endpoint) may return the common four-case converted basis together with
the requested endpoint-specific raw adapter. The 57,344 basis cells and
114,688 typed bytes count that common table once. Check each raw adapter
separately; do not duplicate endpoint basis tables under this byte bound.
The cost allowance discussed above for optionally repeating the shared
covariance checks at both hubs is below 2^29 and the total setup stays
below 2^33. Static review must verify the actual loops and storage.
