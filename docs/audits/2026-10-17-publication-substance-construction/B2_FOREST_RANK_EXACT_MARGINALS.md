# B2: forest rank certificates and source-correct exact BP marginals

18 October 2026 UTC. Independently accepted manual construction; [full original nonauthor graph/algebra/source review](reviews/B2_FOREST_RANK_EXACT_MARGINALS.md). Native/physical/complexity/Chern B2 remain OPEN BUILD. This advances B2/D7-08/09/10 without claiming a native certificate, efficient quantum simulation, a genuine Chern class or complete B2 closure. No project, mathematical software or prover was executed.

## 1. Actual source and necessary distinctions

The read current BeliefPropagation source defines a bipartite incidence graph on variable vertices V and factor vertices A. Its message coordinates are ALL pairs (V x A) disjoint-union (A x V), including NONINCIDENT pairs. The two BPRankCert inequalities also quantify every outgoing pair. They require the rank of x->y to exceed every incoming z->x with an actual edge zx and z!=y. They do not require the outgoing edge xy to exist.

The actual factor update sums over complete assignments y:V->X with y(v)=x, not just the variables in that factor's incidence scope. factorWeight is an arbitrary function on these complete assignments, without an encoded locality condition. The variable update is the unnormalized product of incident incoming factors other than its recipient. The existing finite-rank iteration theorem is genuine: any certificate produces stabilization and a fixed point after max(rank)+1, from every initial message array. Its proof does not need positive/local factor weights. It does not prove that this horizon is graph diameter or that its fixed point yields exact marginals without the missing hypotheses.

We first construct the actual all-pairs certificate for every finite forest. We then prove exact normalized marginal semantics for the actual update under explicitly necessary factor locality and a nonzero partition function, including its redundant-assignment multiplicities.

## 2. Forest-to-certificate construction on ALL coordinates

Let G be a finite simple bipartite forest with vertex set U=V disjoint-union A and n=|U|. The standard finite path facts used here follow directly from acyclicity: two different simple paths between a pair give a cycle by taking their first divergence and next reunion; every connected pair has a simple path by erasing repeated vertices. Thus connected vertices have unique simple paths. Removing an existing edge xy separates its connected component: an alternate connection between x,y would make a cycle.

For an oriented incident edge x->y let T_(x|y) be the vertex component containing x after deleting xy. For a nonincident coordinate x->y let C_x be the original connected component of x. Define

    r(x->y)=|T_(x|y)|-1  if xy is an edge,
    r(x->y)=|C_x|-1      otherwise.                       (1)

Every component used contains x, so subtraction is a natural-number subtraction from a positive size. No rank is stipulated as an input.

Consider a dependency z->x feeding x->y: zx is an edge and z!=y. If xy is an edge, T_(z|x) is a PROPER subset of T_(x|y). Indeed a path from z avoiding zx cannot reach x, since that would supply an alternate zx path. Joining any of its vertices to z, then zx, gives a path to x avoiding xy: otherwise the forest would have a second route around one of these edges. Equivalently the unique path to x reaches x from the z branch, not the distinct y branch. Thus the inclusion holds and x is absent from T_(z|x). If xy is not an edge, T_(z|x) is a proper subset of C_x by the same separation and because x is in C_x. In both cases positive finite cardinalities give

    r(z->x)<r(x->y).                                    (2)

These are precisely var_gt and fac_gt after replacing x,z,y with their variable/factor tags, including all nonincident outgoing coordinates. Therefore every finite acyclic incidence graph has a concrete BPRankCert at the manual level. This pays the missing construction instead of assuming it. Isolated sources have rank0 and no incoming dependency. Empty endpoint sets need no rank obligation.

For n>=1 every rank is at most n-1. Consequently the source-defined horizon is at most n when the endpoint set is nonempty; when it is empty, Finset.sup of the empty set is0 and the defined horizon is1. Uniformly,

    convergenceHorizon(r)<=max(1,n).                    (3)

To derive the source iteration result directly, a rank0 coordinate has no incoming dependency and its update is independent of the initial state after one sweep. By induction on rank k, all inputs of a rank-k update stabilize by sweep k; that coordinate stabilizes by sweep k+1. Every later complete array equals the horizon array, so one further update fixes it. This holds for arbitrary real weights and starting messages because it uses dependence alone, not positivity or normalization.

Conversely an incidence cycle forces a strict cyclic chain of ranks by following its oriented edges without immediate reversal. Each incoming dependency qualifies, so eventually a rank is strictly smaller than itself. No certificate exists in that case. For finite graphs the actual certificate existence is thus equivalent to acyclicity, not merely to absence of four-cycles.

## 3. A substantive path witness and the diameter pitfall

Use the five-vertex path v0-a0-v1-a1-v2, with V={v0,v1,v2}, A={a0,a1}. On its eight oriented actual edges, (1) gives ranks0,1,2,3 in each direction from an endpoint toward the opposite endpoint. Both certificate fields fire: at v1 there are two distinct factors, and at either factor there are two distinct variables. The four nonincident oriented coordinates have rank4 because their source components contain all five vertices. Thus the full source horizon is5, whereas graph diameter is4.

This is not merely an inefficient choice of certificate concealing a four-round universal theorem for the full source state. Let X be a singleton, every factor weight be1, and EVERY initial message value be2. Follow

    v0->a0, a0->v1, v1->a1, a1->v2, v2->a0.

The first update is the empty product1. Every subsequent update in this list reads precisely its predecessor (the singleton assignment sum contributes no multiplicity and the other-factor/product set is a singleton). Therefore the last, nonincident coordinate stays2 through sweep4 and becomes1 on sweep5. Its later value is1. The complete array has NOT stabilized in diameter4 rounds. This uses actual source formulas, no numerical run.

The current D7-09 audit correctly refuses arbitrary certificate ranks as diameter. Additionally the actual all-pairs carrier itself can require diameter+1, as this witness proves. A future native correction must retain that distinction. Restricting the represented state to actual arcs can support a different, sharper theorem; it is a separate carrier change, not a proof of the false full-array diameter assertion. The safe bound (3) already suffices for forest convergence and both nonvacuity fields.

## 4. Actual probability model and branch partition functions

Now assume a nonempty finite alphabet X of size q>=1. For each factor a let S_a be its incident variable set. Require SCOPE LOCALITY:

    if y,z agree on S_a then factorWeight(a,y)=factorWeight(a,z). (4)

Choosing any alphabet value for extension defines a well-defined table phi_a on X^(S_a), independent of that extension by (4). Suppose these tables are nonnegative and the actual finite partition function is positive:

    W(y)=product_a phi_a(y restricted to S_a),
    Z=sum_(y in X^V) W(y)>0.                              (5)

Unary priors can be factors. We do not assume the unnormalized messages sum to one. Arbitrary signed weights still have the convergence theorem but not the probability interpretation supplied by (5).

For an actual edge v-a remove it. Define M_(v->a)(x) as the sum over all variables in the component containing v other than v, with v fixed to x, of the product of all factors in that component. Define M_(a->v)(x) analogously over all variables in the component containing a; v is an external fixed boundary argument to factor a. Scope locality and the single removed edge ensure no other factor there refers to an external variable. Empty products and sums over the single empty assignment are1.

Removing a source node separates the branches, since an overlap or an interbranch connection would create a cycle. Their assignment sets are disjoint. Distributing finite sums over these disjoint products therefore proves

    M_(v->a)(x)=product_(b in N(v)\{a}) M_(b->v)(x),
    M_(a->v)(x)=sum_(z in X^(S_a\{v})) phi_a(x,z)
                         product_(u in S_a\{v}) M_(u->a)(z_u). (6)

The second formula sums exactly the incident variables other than v; branches below them are already summed by their messages. These formulas are justified directly by finite partition-function factorization, not by identifying a fixed point with a distribution by name.

At a variable v, splitting its whole component into these branches proves

    B_v(x):=product_(a in N(v)) M_(a->v)(x)
          =sum_(assignments to its component except v)
                     product_(factors in that component) phi_a. (7)

Different connected components factor the global partition sum. Isolated factors are constant by (4); isolated variables have B_v=1 and component partition q. Positivity of global Z and nonnegativity imply every component partition is positive, so normalizing (7) gives exactly the marginal of W/Z at v. Zero factor entries or branch messages are allowed; no individual message is divided by zero.

## 5. The source's full-assignment sum and its exact multiplicities

For an incident a-v and fixed v=x, the source factor update also sums over variables OUTSIDE S_a. Locality (4) and the fact that incoming products use only S_a\{v} make the summand independent of those variables. Each local assignment has exactly

    c_a=q^(|V|-|S_a|)>0                                 (8)

extensions. Thus the actual source factor update is c_a times the second standard expression in (6), not the literal usual local update.

For an incident oriented edge e, let C_e be the product of c_b over all factor vertices in its source-side component after deleting that edge. Set actual incident fixed messages to tilde M_e=C_e M_e. At a variable update the source-side factor components are disjoint and partition the relevant factors, so the product of incoming C factors is C_out. At a factor update they partition all source-side factors except a; the extra c_a from (8) supplies exactly C_out. Therefore these tilde M values satisfy the ACTUAL update on every incident coordinate.

Alternatively start the actual sweep from any messages and induct from leaves over the directed source subtrees. Once its incoming branches have stabilized, its next update is precisely the displayed tilde M. Hence the finite-rank limit constructed in sections2–3 has these exact incident values. This argument does not assume an initial normalization or silently omit the source's redundant powers of q. Nonincident coordinates stabilize too by (1)–(3), but they have no claimed cavity-marginal semantics and are not used by variableBelief.

For the component containing v, every factor is in exactly one incident branch. Consequently the ACTUAL source belief is

    tilde B_v(x)=(product_(a in component(v)) c_a) B_v(x),
    tilde B_v(x)/sum_t tilde B_v(t)=P_W/Z(y_v=x).          (9)

Its normalizer is positive: the first factor is positive and sum B_v is the positive component partition. This is an exact normalized-marginal theorem for every finite forest with local nonnegative factors and Z>0. Normalizing the full factor update in advance is unnecessary here; changing it would be an actual implementation/carrier decision requiring separate review.

These are finite-algebraic equalities, not a bit-complexity or floating-point algorithm guarantee. The current literal source loops over q^|V| complete assignments even on a tree; its name and finite sweep bound do not make that implementation polynomial time in the graph size. A local-table implementation can use (6) with costs in the input table sizes; arbitrary real-valued factors still require an explicitly chosen computable representation and arithmetic/precision contract before a complexity claim. No quantum-advantage demarcation is derived.

## 6. Exact countercontrols and remaining original B2 work

Locality is essential for source marginal correctness, not a cosmetic extra premise. Consider the connected path u-a-v-b, binary X={0,1}, scopes S_a={u,v}, S_b={v}, but actual full-assignment weights f_a=1 and f_b(y)=1 if y(u)=0, otherwise0. This violates only b's locality. The true Z is2 and u has probability1 at0. In the actual source updates, b->v sums over u and is constantly1; then v->a is1 and a->u sums over v and is constantly2. Thus variableBelief at u is uniform after normalization, disagreeing with the true marginal. Forest convergence still occurs: rank-locality never asserted exactness for nonlocal weights. Supplying actual tensor factors must establish (4); acyclicity alone cannot manufacture it.

Likewise if every factor value is zero in a graph with a factor, Z=0 and no normalized probability law exists. A formal real division convention at zero is not a probability theorem. The positivity assumption in (5) is checked at the true finite partition function, not smuggled into a normalization field. Finite positive factors give a sufficient special case when assignment space is nonempty, but zeros are admitted whenever Z>0.

The component-cardinality rank covers disconnected forests, isolated vertices, empty coordinate sets and nonincident coordinates, while the five-node path tests both strict certificate fields and the full-state diameter failure. Full-assignment multiplicities are retained and cancel only in the final normalized belief. None of these controls is an executed example or a native census.

The publication lead retains B2. Independent complete graph/finite-algebra/source verification is complete in the linked original review. Next: native construction of forest component/path/cardinality lemmas and BPRankCert for the actual carrier, actual path witness, safe horizon and local-factor/partition/marginal statements, then ordinary integration and manuscript/consumer propagation under ROOT authority. The actual tensor-network/analog-Hawking factor assignment, physical encoding/readout/simulation claims and computable precision/complexity contract remain separate substantive work. The genuine Chern-class branch is independently owed; a finite polynomial c0+c1*x does not supply it. Original B2 is not reduced, deemed infeasible, closed by honest disclosure, or replaced by a promise to add a theorem name.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

The current all-pairs message carrier includes nonincident coordinates and can require more than graph diameter rounds. The current factor function has no locality field, and its update over all assignments repeats unused variables. This construction addresses those exact semantics, deriving a forest certificate and conditional exact marginals with all multiplicities. It does not claim an already installed/native forest theorem or a genuine Chern invariant. Full B2 scientific/native/publication obligations remain OPEN.
