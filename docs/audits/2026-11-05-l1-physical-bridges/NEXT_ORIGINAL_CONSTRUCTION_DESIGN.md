# Next original-model construction: viability decision and precise breakdown

Status: PROPOSED DESIGN FOR INDEPENDENT REVIEW. No physical implementation.
Result proposed to ROOT: no implementation-ready positive-state construction
brief can currently be specified from the accepted inputs below. This is a
bounded design breakdown, not a new impossibility theorem or an exhaustive
search for all quantizations. Review must either identify a concrete viable
construction missed here or accept/revise this breakdown. Approval of the
breakdown must NOT be recorded as approval to construct a physical state.

## 1. Fixed target and available objects

Keep Diakonov1109.0091v1 V(20)-(28): independent compact Spin(4) directed
links, eight independent barred/unbarred Grassmann generators per site,
symmetric alpha=1/2 coframe, closed g1*S4+g2*S2, oriented site top and
normalized compact Haar. The enabling regulator remains the periodic 2^4
lattice, finite real g1 and real g2!=0. No higher action term from the source's
ellipsis, bilinear kinetic term, matter determinant, tetrad body or boundary
wavefunction is added. The full literal metric J and prescribed C2 world-frame
j sources and their first/mixed-second contacts remain those already accepted.

Use, without rederivation:

- Original transfer source975ad00d, checkpointd421925e: exact pair transfers
  T_t from the complete three-slice weight w_t and finite-rank K=T1*T0;
  spatial metric wedge multipliers and crossing-source integral vertices.
- Boundary/gauge source452ed859, checkpointc4c848d: exact unused-coordinate
  reduction E, H=L2(Spin(4)^56) tensor Lambda(C^128), endpoint gauge Pi,
  L_t=E* T_t E and K_g=(L1 L0)|PiH. After the derived center identity the
  ENTIRE original functional is Z(J,j)=Tr_(PiH) K_g(J,j), including contacts.
  This norm remains auxiliary. No new Pi or positivity projection is chosen.
- Qualification448daa53, checkpoint26bf5596: actual Vergeles II/III/IV/VI
  data and precise unmatched original-model domain/evolution/source map.
- Premise correspondence33462331 and kinetic/dictionary63d98c23: scoped
  accepted failures used below; do not rerun or broaden them.

The source-level quartet Q is not an ordinary c-number metric. W1 requires
an actual physical algebra/state/source map, and W2-W4 must consume that SAME
map. B3's O(Lambda^2/(16*pi^2)) normalization and [0.1,10] must be derived;
no value, source normalization or coupling is selected to hit the interval.

## 2. Concrete direct construction considered and where it stops

The most immediate construction would reuse the exact sewn boundary amplitude
as the physical state. Its unproved identification would be

    H_phys = Pi H with a source-derived positive scalar product,
    rho = K_g/Z, physical dagger = that scalar product's adjoint,
    original metric/source vertices -> physical insertions with the SAME jets.

This is a proposed identification to assess, NOT a definition adopted here.
To be implementation-ready it must specify the scalar product/domain and the
operator map, and justify positivity and source compatibility. It presently
stops at the following exact alternatives, with different evidentiary status.

| Proposed way to supply the identification | Earliest blocked inference | Accepted evidence and precise scope |
| --- | --- | --- |
| Reconstruct from the entire original even gauge-invariant half-symbol pairing | The form to be completed is not PSD; a zero diagonal has a nonzero mixed entry | 33462331 sections2-5: F62/G58 and full g2^2*a>0; all specified algebra anti-involutions, unitary Nt2 twists and full-pairing-preserving linear quotients fail. No full Z value is needed for that raw obstruction |
| Make the existing coefficient/Haar norm physical and name the ordinary trace a density | Trace and kinematic gauge support do not establish Hermiticity/PSD or the physical adjoint/product | 975ad00d section5 and452ed859 sections3-6 construct the trace exactly but do not prove K_g/Z PSD. The two invariant witnesses survive the existing coordinate/Gauss reduction; the center removes the supertrace sign, not the physical-state debt |
| Derive fixed CAR by inverting the bare kinetic form | The particular unconstrained inverse does not exist over the same finite Grassmann coefficient algebra | 63d98c23 section2: continuum time-split alpha has a two-form with zero body. This does NOT settle a discrete constrained reduction or certify the continuum limit of the symmetric lattice |
| Import the cited composite-unitarity construction | Its completed original-model positive domain and kernel/spectral correspondence have not been supplied | 448daa53: explicit VI6.1 composite extension retained; ONB/normalizability/spectral premises remain assumptions; original compact-hypercubic action/measure/source transport unmatched |
| Supply ordinary metric powers or a finite affine Gibbs state from the literal source polynomial | These optional dictionaries are already failed tests, not required physics | 63d98c23 sections3-6: high-jet moment and finite-dimensional affine-Gibbs results have stated hypotheses. C2 correspondence does not impose either dictionary; neither is a valid new default construction |

The first row is an actual obstruction to its specified reconstruction. The
other rows must not be inflated into further no-go theorems. In particular,
this report does NOT infer that K_g is non-PSD merely from a negative symbol
pairing; that implication itself would need the missing operator/source map.
It does not test any spectrum or invent a new inner product to make K_g PSD.

This isolates the dependency cut: exact sewing and exact trace/source data
exist, but sewing alone supplies neither a positive resolution of identity
nor the physical multiplication/adjoint that would connect those data to
CGL's operator density/evolution. No additional normalization arithmetic,
Gauss averaging, generic positive-matrix lemma, or another optional symbol
norm test closes that inference. Full Z/c0 and N4 remain independently owed.

## 3. Concrete constrained route examined as a prospective next package

A genuinely original-model route would derive further boundary constraints
and the physical insertion algebra from the lattice action, rather than
choose a favorable subspace or import CAR. The precise input is the SAME
three-slice local density s_t(q_(t-1),q_t,q_(t+1);J,j), w_t=exp(s_t), used in
the accepted transfer. A prospective action-induced boundary analysis would:

1. Cut an open slab out of that local action, retaining the endpoint dependence
   needed so that periodic sewing recovers the accepted original functional.
   Use actual compact-link differentials and ordered Grassmann variations;
   introduce no log of w, inverse transfer, independent tetrad or continuum
   Hamiltonian. The open-slab endpoints are analytical boundary data, not a
   replacement physical boundary condition.
2. Derive the boundary variational relation and its constraint ideal from the
   COMPLETE action, including link and Grassmann variations and local gauge
   identities; distinguish actual dynamical constraints from the already
   solved kinematic Pi. Check the consistency of any proposed reduction under
   original sewing and all first/mixed-second source variations.
3. Construct, rather than stipulate, the admissible boundary algebra/domain,
   nondegenerate physical product/adjoint and positive form, and demonstrate
   that its evolved insertion/source map reproduces the original required
   response. Any loss of full symbol information must have a derived physical
   constraint/source explanation; deleting F/G for positivity is forbidden.

This is a specified research ROUTE, not an implementation-ready brief:
steps1-2 describe a deterministic classical/discrete constraint analysis;
step3 has NO source-derived quantization/completion prescription among the
accepted inputs. A canonical cotangent relation, even if constructed, would
not by itself determine the quantum positive inner product or transported
metric product. The accepted zero-body result blocks only the shortcut of
claiming a regular bare inverse, not every nonregular constraint treatment.

Thus I cannot honestly assign step3 to an implementer with fixed objects and
a checkable construction, or label steps1-2 a positive-state candidate. Nor
can I substitute the already accepted continuum time split for a controlled
lattice constraint analysis. No such new constraint derivation has begun.
The next substantive implementation milestone, IF this route is developed
into a viable reviewed brief, must be an actual source-derived admissible
boundary algebra/product and norm prescription whose sewing/source identities
are specified. A variational formula alone does not meet that milestone.

## 4. Other genuine frontier and exact decision needed

A controlled collective/critical/continuum reconstruction is a distinct
possibility, not an already excluded route. Diakonov V(28)/VI explicitly
leaves the infrared/long-loop analysis open; finiteness does not solve it.
The finite high-degree witnesses neither prove nor disprove positivity of
scaled local physical correlations. That route needs a prospectively fixed
larger-lattice family, couplings/regulator trajectory, physical metric-source
scaling, correlation domain, nonzero normalized functional, and convergence/
positivity statement. None is supplied by the single Nt2 transfer or the
qualified simplicial argument. I have no source-verified trajectory/state
candidate to insert into those slots; writing arbitrary functions there would
be choosing the missing physics. No limit candidate is started or proposed
as already viable by this report.

Recommendation to Publication ROOT/operator: keep all original BUILD criteria
and accepted finite results, and record this as a construction-design frontier.
Assess whether to commission a coherent original nonregular boundary-constraint/
quantization research package under the existing W1 roadmap, or obtain a
specific existing source-defined controlled scaling construction for review.
The former is the closer continuation of the exact original boundary work,
but it has not earned a claim of feasibility or a positive-state brief.
The disposition sought is research direction/ownership for the unresolved
quantization or scaling construction, NOT a convention, a chosen favorable
state, a new action/source, waived acceptance or a reduced publication target.
No operator is asked to invent a domain, polarization, CAR or source contact.

If a reviewer can supply a concrete source-defined missing prescription, it
must be frozen with its original-model correspondence and submitted as a NEW
brief. Do not silently insert it into the reviewed report or begin construction
under this design assignment. A competing accepted owner/artifact should be
reused; none is claimed absent globally by this bounded assessment.

## 5. Evidence, review contract and stop

This document only synthesizes source-pinned accepted constructions into a
construction-readiness decision and an explicit dependency/decision map. It
contains no new physical derivation, constraint calculation, norm test,
positive state, operator choice, spectral test or source-data implementation.

Require independent original-source and architecture/critical-path review of
(1) exact reuse/scopes, (2) whether the candidate disqualification is justified,
(3) whether the constrained proposal actually supplies an implementation-ready
state prescription, (4) an overlooked concrete viable route in the inspected
inputs, and (5) the exact research disposition without target reduction.
Verdicts must distinguish ACCEPT breakdown from APPROVE construction. A review
finding that supplies an actual viable route needs a separate frozen brief
and dual prospective approvals before work; result review remains separate.

STOP after returning the reviewed design/breakdown. No physical implementation,
scientific evaluator/CAS/Haar/exterior/matrix job, Lean/build/test/native/slot/
controller, infrastructure or Git integration authority follows. Any future
executable work also requires its exact independently reviewed producer,
inputs/command/controls/caps/output-evidence and fresh exact controller canary/
resource admission. None exists here. FullZ/c0, N4, positive state/source/limits,
B3, physical dynamics/matter/light and transport stay OPEN. ROOT retains the
entire ordinary/canonical L1 readiness package and operator/integration work.

Primary evidence (held bodies already read, exact reviewed source copies):
Diakonov1109.0091v1 I,V20-28,VI; Vergeles2506.00036v2 II/III/IV/VI;
CGL1511.03646v3 I1.7/I.F1.60. Original-state premise33462331,
kinetic/dictionary63d98c23, transfer975ad00d, boundary452ed859,
qualification448daa53. No paper-wide or literature-wide absence assertion.
