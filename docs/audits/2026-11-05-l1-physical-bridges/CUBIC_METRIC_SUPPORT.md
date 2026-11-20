# Four-site full metric: exact support truncation

Manual result, revision 2 for independent mathematical and physics review.
Revision 1 and its completed reviews remain preserved unchanged.
Use the original closed, uncoupled gravity action and literal local metric
Q_mu,nu(0), J=0, on the 2x2x1x1 periodic regulator, with normalized Spin(4)
product Haar, eight Grassmann generators/site and the recorded orientation.
All original source/field units and couplings remain fixed. No matter, external
source, thermodynamic phase or Lorentzian continuation is introduced.

## Actual support definitions

The source helpers l1_interacting_support.py and l1_mixed_g1_support.py define
forward(x,d)=x xor 2^d for d=0,1 and forward(x,d)=x for d=2,3. A frame T_d(x)
has degree one at each end (degree two at x for a collapsed direction) and
one occurrence of its link coordinate. Extended directions have two possible
link anchors; collapsed directions have the unique anchor x. Link centre
parity is recorded by XOR, so an odd coordinate occurrence on any link kills
its Haar integral under U_link -> -U_link, including joint repeated occurrences.

A determinant S4 term at x has Grassmann degree six at x and one at each of
x xor 1 and x xor 2. It has one collapsed selflink (x,2) and one (x,3).
Its four anchor choices do not change these two collapsed-link parities.
Two determinant centres coinciding would put degree at least twelve at that
site. Such a Grassmann term is identically zero, regardless of other factors.

## Full cubic metric coefficient

Accepted degree/reflection selection allows only Q S4 S2^5 and Q S4^3 S2
for the four-site one-point numerator. In the latter, nonzero Grassmann support
requires three distinct determinant centres, hence six distinct odd collapsed
selflinks. Any literal Q has two frame factors and can toggle at most two
collapsed selflinks (equal collapsed directions toggle the same link twice).

An S2 term has a plaquette in directions k<l plus the two complementary frames.
Its number of odd collapsed links is at most three, in every actual label:

- Plane01: plaquette has no collapsed links; its complementary frames give two.
- One extended and one collapsed direction: the plaquette gives two distinct
  collapsed links at neighboring sites; the other collapsed frame gives one.
- Plane23: each collapsed plaquette link occurs twice and cancels in parity;
  the two complementary frames are extended, giving none.

Q and the one S2 together can therefore toggle at most five collapsed links.
They cannot cancel the six odd collapsed links from the three determinants.
The Haar integral vanishes termwise for every anchor, all ten symmetric metric
coordinates and every determinant label. No coefficient sign or gamma trace
evaluation is used. Thus I[Q_mu,nu S4^3 S2]=0 for the full literal metric,
extending the historical tagged mixed-action cubic diagnostic.

## Quartic partition coefficient

The only degree-compatible quartic term is S4^4. Four distinct centres give
eight odd collapsed selflinks, with no S2 or Q factors available to cancel them.
A repeated centre is already Grassmann zero. Thus I[S4^4]=0.

## Exact finite polynomial and interpretation

For g2 != 0, x=g1/g2^2, accepted reflection/degree selection plus the two
identities above give

    Z = g2^8 (z0 + z2 x^2),
    N_mu,nu = g2^7 c_mu,nu x,
    G_mu,nu = c_mu,nu x / (g2 (z0 + z2 x^2))

where z0=1252309350145403/2123366400 and
c_mu,nu=I[Q_mu,nu S4 S2^5]/5!. Neither z2 nor the nonempty c components have
been evaluated here. In particular no nonzero denominator away from x=0 is
assumed; a neighborhood exists by finite polynomial continuity and z0>0.

The complete independently accepted leading support roster has no entries for
00,02,03,11,12,13, and has480 entries total for01,22,23,33. Empty necessary
support forces those c entries to zero without amplitude contraction. Therefore
N00=N11=0 identically at all finite couplings on this specific regulator;
where Z != 0 their normalized components vanish too. In particular a real
Euclidean G cannot be strictly positive definite: its quadratic form on the
nonzero coordinate vector e0 is zero. This holds for any overall finite scalar
unit conversion as well. It is an obstruction to this enabling regulator
supplying the requested SPD collective body, not an evaluation of the unknown
full tensor, z2, determinant or inertia.

Zero diagonal entries alone do not imply degeneracy for an indefinite metric.
There is no conclusion for a Lorentzian continuation, the sixteen-site regulator,
matter backreaction, a source-selected thermodynamic phase or another action.
No new physical assumption, deferral or reduction in publication acceptance is
authorized. This manual finite-support argument is not a Lean kernel theorem
or a canonical settled global no-go. The full leading tensor assignment remains
open unless publication explicitly dispositions its next scientific milestone.

## Zero-coupling boundary and source correspondence

Without division by g2 the exact raw polynomial statements are

    Z = z0 g2^8 + z2 g1^2 g2^4,
    N_mu,nu = c_mu,nu g1 g2^5.

They hold at g2=0 too: both Z and every N vanish there, so no normalized
expectation is defined at g2=0, even when g1 is nonzero. For g2!=0, any zero
of z0+z2 x^2 is also excluded from normalized statements. This is not a
positive-measure argument and supplies neither a sign for z2 nor a physical
parameter interval away from the nonzero neighborhood of x=0.

G here is exactly the expectation of the literal tetrad pair Q. It is not
M=B0+lambda Q, a background-added configuration metric in the earlier scalar
matter interface. In particular an externally supplied positive B0 cannot
be counted as gravity demonstrating a positive literal G. The action, Haar
normalization, Grassmann algebra, source J=0 and dimensionless lattice units
are the original fixed ones; physical metric conversion by a finite overall
scalar factor does not remove the zero quadratic form. No physical scale or
new coupling is fitted by this argument.

## Construction breakdown and remaining ownership

The physical purpose of the full c tensor calculation was to test whether
leaving g1=0 could provide the missing strict Euclidean collective body on
this SAME four-site uncoupled regulator. The exact all-coupling zero00 result
settles that necessary property without needing the nonempty c contractions:
none can restore its zero e0 quadratic form. It therefore replaces further
c contractions ONLY for deciding that particular SPD-body route here. It
neither evaluates the full tensor nor makes those open coefficient tasks
complete. The unknown c01 could still produce an indefinite nondegenerate
block; no full determinant, susceptibility or physical state was determined.

Executor retains the explicitly open enabling full-tensor assignment and
hands this source-linked construction breakdown to Publication Remediation
for scientific prioritization; no deferral/reduction is silently recorded.
The sixteen-site full denominator, original source/body/state and matter
matching, susceptibility, B3 normalization and range, tensor dynamics,
luminality/gain and transport obligations remain unresolved by this result.
It does not establish that an original publication claim is false. Any
actual scope or deferral decision still requires explicit operator disposition.
The separately reviewed Dirac-loop factorization remains a prospective
mathematical design, with no implementation/control/feasibility acceptance.
