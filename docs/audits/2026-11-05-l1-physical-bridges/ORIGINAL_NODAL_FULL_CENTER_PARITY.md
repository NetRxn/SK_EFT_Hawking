# Full original P0: uniform site parity and occupation-flow reduction

Lead Executor01a1ac65 continuation of l1-nodal-p0-structural-exploration-r1, parent publication ROOT01a13f67. Manual additional result on source HEAD5ad2c7e0ba6f9236dd27308c609739b3b563c727; this private note is separately frozen for actual mathematical and original-source review. Reuses the same task source/notebook/roadmap snapshot, checked fresh before writing; exploratory discussion preceded this freeze. No P0 evaluation or positivity claim.

At V1=I, the original nodal A8 vertex with curvature plane {0,i} contains exactly one moving slice1 spatial matrix at the based direction-i anchor, and one moving matrix in EACH of its two coframes in the other directions j,k. Both ordered holonomies are U1_i(x)† U0_i(x) and U0_i(x)† U1_i(x); the fixed retained matrix changes no moving degree. Each coframe uses one of the two original moving anchors on its undirected endpoint pair. Thus every expanded vertex at x contributes exactly ONE moving occurrence on each of its three incident undirected spatial endpoint pairs, irrespective of which direction is curvature. Gamma/chiral zero terms can be discarded; nonzero terms retain this count.

Let m_x count its vertices in A8^16. For an undirected pair e={x,y} in direction i, only vertices centered at x or y can use either anchor belonging to that pair. Their TOTAL moving degree on its two anchors is consequently

 N_e=m_x+m_y.                                                (1)

The independent Spin(4) center (-I,-I) at either moving anchor changes sign on each fundamental or adjoint appearance, so a nonzero Haar integral requires even degree at EACH anchor. Hence N_e is even. Q3 is connected, so every m_x has the SAME parity. This applies to ALL direction mixtures and fixed retained u0, not just a pure-direction subtotal. It is necessary only; the independent chiral-center and individual-anchor conditions are stronger.

With 0<=m_x<=4 and sum m_x=16, the only parity families are:

- even: m_x in {0,2,4}, with equal numbers k of zeros and fours, 0<=k<=4;
- odd: m_x in {1,3}, with exactly four ones and four threes.

Before endpoint equations and the stronger anchor/chiral rules, there are exactly

 sum_(k=0..4) 8!/[k! k! (8-2k)!] + binom(8,4)
   =1+56+420+560+70+70=1177                                 (2)

labelled site-multiplicity assignments. This is a loose finite roster, not the count of nonzero terms, distinct tensor contractions or computational cost.

A compact exact remaining occupation description uses c_(x,i), the number of vertices centered at x whose curvature plane is {0,i}. Then

 c_(x,i)>=0, sum_i c_(x,i)=m_x,
 n_(x,i)=m_x-c_(x,i),
 sum_i c_(x+ei,i)=2m_x+sum_i m_(x+ei)-8.                     (3)

The last equality is the previously accepted endpoint saturation equation after eliminating coframe incidences. Because the action projections A_(x,i) are even, the full original coefficient can be expanded as

 P0(u0)=sum_(c satisfying sum c=16, (3), uniform parity)
          16!/[product_(x,i) c_(x,i)!]
          integral dU1 I64 product_(x,i) A_(x,i)^c_(x,i).     (4)

Here A_(x,i) includes BOTH world orders, BOTH coframe orders, all internal indices and actual original quarters. Excluding terms violating (3) uses exact odd saturation; excluding nonuniform-parity terms uses the proved Haar-center rule. No other term is excluded or called positive. Remaining shared-anchor/chiral Haar contractions and signed Berezin cancellations still determine P0. Formula(4) supplies additional exact pruning beyond the earlier generic projector expression, not its evaluation or a resource budget.

Only static source reading, manual algebra and ordinary continuity/artifact bookkeeping. No scientific evaluator/CAS/exterior/Haar/Gram/matrix program, Lean/build/test/slots/controller/Git or repository/notebook edit. Full P0 and all physical positive reconstruction/source/dynamics/publication obligations remain open.
