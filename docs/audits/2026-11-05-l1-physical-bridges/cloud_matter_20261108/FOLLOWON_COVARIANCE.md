# L1 cloud continuation: local covariances and source response

Candidate follow-on to the frozen reviewed plan/report in ../CLOUD_MATTER_EXECUTION_2026-11-08.md and existing PR125/issue121. Scientific base remains864f4ec, roadmapc0a775c. Only new files in this audit subdirectory are owned here. Original publication coefficient/fullZ/c0 and local paused execution remain untouched. New result review is required before acceptance; this file does not change canonical gates or original physics objectives.

## Domain and conventions

Use the same bare candidate M=I+λG, fixed periodic forward2×2×1×1 geometry, unit spacing/cells and positive scalar body mass, closed action exp(+g2S2), original oriented Berezin and normalized product Haar measures. Realg2≠0. Expansion is atλ=0 within the common-source regular neighborhood with domination, nonzero gravity/joint denominator and inverses where used. These are finite signed-functional results. No physical body, λ/scale, source state, positive reconstruction, continuum or real-time match is derived. Raw pair coefficients multiplyg2^6 and normalized moments divide matching Z8*g2^8, Z8=1252309350145403/2123366400.

## Two newly evaluated local entries

Let D=G22−G33,H=G23,T=G22+G33 at one site. Original support enumeration applies: these source squares saturate eight generators at site0, with even center parity on both collapsed source links. Thus all185 action words, action degree6 with target(0,8,8,8) and parity0, are the same necessary support. They are not extrapolated from a two-site result.

The145 source-decoupled words reuse their original closed gravity contraction subtotal318843 for D². Their local source moments21,9,129 give D/H/T subtotals318843,136647,1958607. H's local moment9 and T's129=2(75/2+27) are checked against the existing exact single-link moment machinery. The40 coupled words reuse the archived closed gravity tensors with new exact source kernels, preserving all center frames and factorials.

For H² the kernel is the exact signed top product of weighted frame-pair tensors, summed over both ordered internal indices, divided by256 because the two raw metric pairs each contain4T frames. T² has the opposite cross sign to D². The new script checks all1296 source-kernel entries for interchange symmetry and each pair of chiral sphere marginal sums. Across-center offdiagonal source-link entries are retained, including Hkernel((1,2),(1,2))=1/24. They must not be confused with within-center source TYPES. The independent64-case conjugation control proves precisely four scalar TYPES and two rotational-vector classes survive within a center, so the existing branch aggregation is complete for the replacement kernels.

| Bare local pair |145-word subtotal|40-word subtotal|Full raw g2^6 coefficient|Normalized moment timesg2²|
|---|---:|---:|---:|---:|
|D² control|318843|−23063/32|10179913/32|675490163097600/1252309350145403|
|H² new|136647|−71673/128|17419143/128|288962679398400/1252309350145403|
|T² new|1958607|−87581/16|31250131/16|377019762278400/113846304558673|

The bounded240-second-cap computation exited0. Its D control reproduces the original accepted185-word result. The new kernels, complete18-orbit output and full40-word histograms are in transverse_covariances.py/txt. These results require no new original sixteen-site contraction. Algebra also fixes the raw local G22G33 coefficient to52320349/128 from(T²−D²)/4, without assuming equal diagonal entries.

## Insertion into an identifiable scalar block

For the collapsed scalar, D and H have V=0 and local W_DxDx=−Kx/8,W_HxHx=−Kx/2. They supply the common term

`g2² Sigma_DH = −228917610086400/1252309350145403 K0`.

For the transverse trace alone, rho=sqrt[(1+λT/2)^2]=1+λT/2 near0 and Factive=rho I. Hence W_TT=0 and V_Tx=Kx/2. At unit mass/spacing, write H0=K0^-1 and sumKx=K0. Translation invariance and four scalar sites give Tr(H0Kx)=1. The known coincident covariance A_T=<Tx²> yields

`Sigma_T,coincident = −A_T K0/8 −(A_T/4) sum_x Kx H0 Kx`.

These are respectively determinant reweighting and inverse fluctuation; the quadratic metric term is zero in this isolated T direction. Off-site TxTy terms remain omitted, as do all active mixed components. known_block_kernel.py explicitly builds all four local matrices, retains both terms and checks each Fourier eigenvector. For momenta(00),(01),(10),(11), K0=(1,5,5,9), the known block g2²Sigma has numerators

`(−1139001425141760,−6063648671047680,−6063648671047680,−11909899780300800)/1252309350145403`.

Its ratios to K0 differ across the three distinct body eigenvalues, so the larger known block is not a common rescaling. Equal single-axis entries retain the exchange symmetry of these two finite directions. Mass and higher-difference corrections can explain these finite-mode differences; they establish no relative temporal/spatial speed. This is a partial finite-momentum correction, not a full dispersion law: omitted off-site/mixed blocks can modify or cancel it. Four momenta do not establish a controlled continuum expansion, kinetic signature, positivity, time continuation or propagation cone. No tensor/B3/GW conclusion follows.

## Remaining bounded input boundary

The active(a,b,c,T) site-pair covariance still needs nonlocal entries and the other active/coincident mixed blocks. Extra local H² andD² are now evaluated, leaving |u|²,|v|²,u·v, with u=(G02,G03),v=(G12,G13). Necessary support preflights find nonzero candidates; they are not zeros. For G02G12, action degree target(2,7,7,8) has ordered support0,5760,5760,11520 by the four longitudinal-link choices. For G02², target(2,6,8,8) has43560,37800,37800,43560. These sources leave generators at remote sites, so the185-word saturated-site factorization does not cover them. A new source-resolved separator/Dirac-loop contraction design and bounded row/work preflight are needed before campaigning; preserve existing owner failures and caps.

## Completed fixed-basis source jets

The [source-jet method](SOURCE_JET_METHOD.md), source_jet_reweight.py and its complete receipt evaluate all72 charged words. For uniform A=exp(jE), E=(0,0,1,−1), each action word carries chargeq=sum(−E_k−E_l). The185-word census is q0:113,q−4:36,q+4:36. All40 coupled words haveq0. The six charged private-family populations16,24,8,12,4,8 have signed subtotals93555/4,168399/4,1323/2,62937/2,0,567, each freshly rerun with exit0 under a60-second family cap. The first unoptimized individual-word quartic replay timed out; it was replaced by six exact symmetry representatives with unchanged contraction formulas/caps, not recorded as zero.

Their total196371/2 timesq²=16 gives the rawD numerator secondjjet1570968. Wordwise local source-moment scaling gives H/T raw secondj jets673272 and9650232. This includes both action terms X²+Y: the squared total charge differentiates the product of all source-dependent action insertions. It does not drop the Sg,jj contact. The fixed bareD/H/T observables have no source derivative; a transported-basis calculation must reproduce this using explicit observable contacts.

Transverse exchange gives both numerator and denominator firstjets zero. The accepted full uniform closed-action logZ_jj=954400425849600/113846304558673, consumed from the spectral interface, then gives

`A_O,jj = N_O,jj/Z − (N_O/Z) logZ_jj`.

Use h=2sqrt(2)j for the interface unit-plus source, so A_O,hh=A_O,jj/8. With common denominatorR=142570791678327415714294730219, the exact local variance secondhjets timesg2² are

`D:−33115793931313683139185868800/R`,
`H:−14128883684038456702776115200/R`,
`T:−203160484115670306319840051200/R`.

These are responses to the specified finite coframe action source, not a derived physical-strain calibration. For its determinant-one transverse exponential congruence, the fixed scalar kernel and vertices are exactlyh-independent on this collapsed regulator. known_block_source_jets.py therefore inserts these covariance jets into the same partial block without omitting vertex contacts; it preserves exact four-mode outputs separately. The first derivative of this block vanishes. The isolated plus term has `g2² Sigma_D,hh/K0=4139474241414210392398233600/R`. The full source response still needs every omitted active/offsite/mixed covariance jet and physical matching. No full source tensor or all mixed source jets are claimed.
