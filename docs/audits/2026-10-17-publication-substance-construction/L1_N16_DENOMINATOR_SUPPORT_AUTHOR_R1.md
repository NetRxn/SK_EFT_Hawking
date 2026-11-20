# Original closed N16 denominator support preflight

This author checkpoint uses clean primary `a72e9c41fd91c51a0e15dd1e5648203aaf3228c0`
and the original periodic `source_C` regulator. It carries the exact zero-source
closed-word construction and all nine allowed powers at each site. The accepted
finite nonvanishing certificate at `(g1,g2)=(2^1717,1)` remains a separate
analytic result. This work builds a bounded candidate support route for
additional coefficients of the complete original denominator. It computes
no denominator coefficient, nodal P0 contraction, full partition value, or
normalized observable.

## Exact original source census

The existing `original_spin4_link`, `original_coframe_blocks`,
`assemble_coframe`, and `original_action_factors` constructors were used.
All 16 sites were independently constructed. At each center the census has
384 raw ordered S2 orientations and 24 raw S4 permutations, 6,528 source
branches in total. Each coframe uses the actual 128-generator order. Every
quaternion bit denotes one original site/direction/chirality/coordinate among
the 512 distinct coordinates. No two-cycle anchors are identified.

Coframe variables are even, so the source trace polynomials can be added
for identical sorted component monomials before taking Boolean support.
This actual signed grouping gives 72 nonzero S2 monomials and 24 S4 terms
per center, retaining the complete original source. The raw and grouped
branches, component and anchor identities and nonzero trace support counts
are in `support-census.json`. Branch scopes union each trace scope with
the scopes of its actual coframes before joint exterior multiplication.
The union can include collisions or subsequent cancellations.

The resulting complete site-factor scope is 40 generator and 160 quaternion
coordinate bits at each site. A deterministic greedy site contraction
minimizes the next structural processed/future intersection, with ties in
site order. It measures a peak of 520 bits (104 exterior and 416 quaternion
parity), compared with 640 in lexical site order. Each bit is weighted by
its Boolean domain; this describes this contraction order's structural
frontier. It is a different measurement from the earlier group-level
variable elimination and gives no actual state-count or optimality claim.

## Measured Boolean growth and last use

The two-center pair is x=(0,0,0,0), y=x+e0. Each Boolean record retains the
projected exterior mask and full parity at each selected exact quaternion
coordinate, and carries the ordered local S2/S4 powers in the surrounding
map. Products reject overlap on retained exterior bits and XOR parity on
the original anchored chiral coordinates. Projected-out exterior bits may
hide a collision. Distinct full exponents with the same parity are
identified for this support query. Coefficient cancellations after source
grouping are not applied. These are conservative support envelopes, with
the full logical source weights unchanged.

Each lane reserves previous and next maps and transient Boolean rows under
8,192 logical records and caps attempted join pairs at 20,000,000. Immutable
actual source rows, Python object bytes, and RSS are outside the support-row
measure. Cap controls reproduce prospective refusal for both limits.

| Exact retained coordinates | Last completed local work | Prospective refusal |
| --- | --- | --- |
| All exterior and quaternion parity | Partial first S2 | S2 component 1 after 7,041 pair visits |
| Both endpoint masks and all 16 reciprocal directed-anchor parity bits | Partial S4 | S4 component 4 after 244,655 visits |
| Both endpoint masks and two distinct chiral parity coordinates | S2 264, S4 880, S2 squared 4,860 states | S2 times S4 after 213,693 visits |
| Central eight-bit mask and all eight parity bits at one outgoing anchor, over all five source owners | Earlier local powers | S2 to the fourth after 1,696,573 visits |
| Same central mask and two parity coordinates on that anchor | All nine first-center powers with 809 states | Second star layer after 323,455 visits |

All refusal bounds are 8,193 prospective records under cap 8,192. No
selected coordinate is private to the initial adjacent pair. The actual
five-owner star was extracted from source scopes for the central site
and outgoing anchor. The last-use code enforces exactly eight generators
and even parity at the selected coordinates only when no remaining source
factor owns them. The larger star attempts refuse before this event. A narrower actual-source
control retains central bar0/psi0 and coordinate 0 of both chiralities
at one original outgoing anchor. It completes the five-site owner star.
Boundary records are 121, 377, 761, 1,273, and 120. Only the last step
enforces coverage of both retained generators and evenness at both
retained chiral coordinates, leaving zero live coordinate labels.
This checks the real last-use mechanism with all nine powers. The 120
remaining projected coupling grades are support controls for this
subproblem, not complete original Z grades. Peak 2,114 records and
244,038 charged visits.

Projecting further to site-level directional occupancy alone gives
`1,6,1,19,6,44,1,19,85` profiles in the frozen nine-power order. The all-grade
frontier reaches 182 then 7,483 records and refuses at the third site.
Bounding g1/g2 powers to c14 or c0 with this same frontier still refuses
at site three. The pure g1 control completes all 16 sites with peak 53 and
339 charged visits. A direct occupation DFS also independently reproduces
all-linear and both checkerboards, exactly the three analytic c16
occupation classes in 138 attempted choices. Neither Boolean result
substitutes for the existing analytic sign and positive lower bound.

## Complete directional occupancy split for the mixed c14 coefficient

Target `c14=[g1^14 g2^4]Z`. Every S2 monomial uses two distinct coframe
directions. Every S4 uses each direction once. Given the multiset of four
S2 center/plane labels, form the 16-vector `b` from each label's contribution
of two at its center and one at each selected neighbor. S4 powers `q`
must then obey `(4I+A)q=8-b`, where A is 4-cube adjacency. The possible
directions are extracted from the actual nonzero grouped source terms.

The eigenvalues `8-2 wt(m)` follow by applying the matrix to each Walsh
character. The only kernel is the checkerboard character. Every S2
plane contribution annihilates this character by its endpoint signs.
For each of the 96 actual center/plane labels precompute a rational
particular correction to the all-ones solution, with common denominator
384. Verify the full original 16-row matrix equation for every correction.
Remove its q0 entry by the kernel. A four-label multiset has an integral
completion exactly when the modular sum of the four corrected vectors is
zero. Use the canonical nondecreasing split into the first and last
unordered pairs, with a one-coordinate residue partition and an exact
match on all remaining residues. Then try q0 from 0 to its local bound,
checking all 16 local nine-power caps and the unprojected directional
occupation equations.

The complete 3,764,376 unordered four-label multisets reduce to 1,320
integral multisets and 1,968 admissible pairs of plane multiset and S4
occupation. These exact counts concern site-direction occupancy, before
component labels, actual exterior chirality, full anchored Haar and
signed cancellation. The measured pair search uses 202,461 charged
visits and peak 1,365 logical pair-index records. The output is a distinct
streamed metadata roster with cap 2,048. Each record includes its
exponential divisor from factorials of the repeated S2 plane counts and
site S4 counts. All sixteen sites and both reciprocal directed anchors
remain present for subsequent coefficient assembly.

An independent algorithm in the author controls inverts the rational
15-by-15 principal minor with q0 fixed, verifies all source equations,
visits all 3,764,376 multisets directly and matches every one of the
1,968 streamed roster entries and its factorial divisor. No scientific
coefficient or original-mode job ran. This complete projected roster
removes the need to expand an unconditioned occupancy frontier for c14.

## Next substantive check

Use the complete c14 roster as an exact directional conditioning stage,
then construct separate chirality/exterior and shared-link parity bounds
for its 96 all-distinct-S2, 1,776 paired-S2 and 96 single-center-S2
occupation rows. Stream each row into signed factorization only after the
actual component and Haar separator envelopes are measured. Test signed
transport before identifying any symmetry-related cases. This advances one
mixed coefficient route. The other coupling grades, pure EHC c0, original
complete Z value, executable and physical Eq11 acceptance all remain open.
