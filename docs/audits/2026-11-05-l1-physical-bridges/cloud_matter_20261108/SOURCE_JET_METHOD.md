# Fixed-basis transverse source jets by exact word reweighting

Candidate: the same four-site periodic closed pure-g2 model at scientific pin `864f4ec25667e345b90e8a8570a00c10c17b198f`, real g2≠0, on a nonzero-normalization source neighborhood. This extends the bounded PR125 calculation; it does not supply the remaining active covariance or a physical state, calibrated source, continuum/real-time cone or B3 quantity. All new files are confined to this audit directory; no original evaluator was changed.

## Exact source and basis

Hold the original bare composite components fixed as observables while varying the gravity action with the common **uniform** coframe A(j)=exp(jE), E=diag(0,0,1,−1), fixed holonomies, measure, lattice and scalar difference maps. Write D=G22−G33,H=G23,T=G22+G33. The observable is D² (or H²,T²) in the original reference-coordinate basis, not the transported D(j)². Transported observables require their additional explicit derivative contacts; these results must not be relabeled as those derivatives.

The common-source interface's unit Frobenius metric strain h uses P=E/sqrt(2), A(h)=exp(hP/2). Consequently h=2sqrt(2)j and second h derivatives are 1/8 of second j derivatives. This fixed prospective source family is not a derivation of the physical source or matching scale.

Each original S2 vertex t=(x,k,l,u,v) has coframes in complementary directions m,n. Its exact coframe multiplier is exp[j(E_m+E_n)]=exp[−j(E_k+E_l)]. Thus a six-vertex word w contributing to the bare D² numerator has charge q(w)=sum_t[−E_k−E_l], and its existing signed Haar/Berezin coefficient C_w (including the original factorials) is multiplied by exp[jq(w)]. Source differentiation therefore retains the full action contact: q² includes both derivatives on one occurrence and derivatives on distinct occurrences. No isolated covariance replaces the contact-inclusive derivative.

## Census, disjoint contractions and reuse

The existing complete same-site support contains185 distinct words. Exact enumeration gives q=−4 on36, q=0 on113, q=+4 on36. All40 source-coupled words have q=0. Only72 source-decoupled words affect the second numerator jet. These split disjointly by their shared-frame-link occurrence tags:

| Family | Words | Signed raw subtotal |
|---|---:|---:|
| private quadratic |16|93555/4|
| one shared quartic |24|168399/4|
| double shared quartic |8|1323/2|
| two shared quadratics |12|62937/2|
| four shared quadratics |4|0|
| mixed quartic/quadratic |8|567|
| Total |72|196371/2|

The source-decoupled closed-order transfer already accepted in `L1_RETARDED_SPECTRAL_INTERFACE.md:1510–1534` integrates private curvature/conjugators before joining source and frame tensors. It preserves the original world labels and applies wordwise, so multiplying by the scalar charge weight does not invalidate it. The new script consumes those existing exact Haar/Berezin kernels; it does not rederive or replace their action ordering.

`source_jet_reweight.py --family NAME` reruns each relevant subset through the existing evaluator. It prints source hashes. Function-source wrappers change only the selected support, known axis-exchange orbit multiplicity and expected population assertion, then return the original outcome counter. They leave the Haar, wedge orientation, source moments, rational denominators and original exponential factorial formulas untouched. `replace_once` asserts every source adaptation is unique to catch drift. Orbits use the existing time/space and transverse exchanges from `l1_equal_time_mixed_factor.transform`; the script checks each orbit stays in its assigned subset and |q|=4. There is no inference from a family having half as many words: each signed subtotal is explicitly contracted.

The private16 subset reruns the top-level original private evaluator with only its support/population controls adjusted. The one-quartic24 subset uses six4-word symmetry orbits: two values5103 and four values5103/64 give the stated subtotal. Double-quartic8 have value1323/16 each. The shared-quadratic subset has eight values1701/16 and four values15309/2. Four-quadratic4 are zero; mixed8 have value567/8. An initial unoptimized24-individual-word quartic attempt hit a60-second cap without completing; it is not a zero. The orbit form completed under the same per-family cap.

Transverse exchange sends j to−j and preserves squared bare observables, so the first numerator derivative and first denominator derivative vanish. The charged subtotal gives

`N_D2,jj(0)/g2^6 = 16*(196371/2) = 1570968`.

Equivalently the exact bare numerator is `N_D2(j)/g2^6 = 7037977/32 + (196371/2)cosh(4j)`, using the already accepted total s=10179913/32 at zero source. This last expression does not determine the full denominator away from zero.

## Complete normalized jet, including denominator contacts

The existing closed normalization is Z8=1252309350145403/2123366400. The independently reviewed full uniform-coframe log-partition second derivative is

`Ljj = (log Z),jj(0) = 954400425849600/113846304558673`.

Source: `L1_RETARDED_SPECTRAL_INTERFACE.md:1328–1368`, including the full common source j0=ja=j, original spatial weighting, zero one-point symmetry, operator product and action contact. Its earlier source definition at407–439 sums the charge over all centers in each slice, so setting the two slice parameters equal is precisely the uniform source used here. Since Z_j=0, Z_jj/Z=Ljj. Omitting this term would give the wrong sign for the normalized second jet.

For A_D(j)=<D_x²>_j, fixed bare basis and one site x,

`g2² A_D,jj(0) = 1570968/Z8 − (s/Z8)*Ljj`
` = −264926351450509465113486950400/142570791678327415714294730219`.

Its first derivative is zero; second h derivative divides the displayed result by8. Under the same collapsed-axis exponential common deformation, the scalar kernel is exactly source independent at fixed G; therefore this isolated D-sector scalar correction has

`g2² Sigma_D,hh(p)/K0(p) = 4139474241414210392398233600/142570791678327415714294730219`.

This is a derivative of one additive finite-candidate contribution. It is not the full scalar-kernel source response and changes no relative momentum coefficients by itself.

## Additional H/T source jets

The parent's independently executed adjacent `transverse_covariances.py` supplies complete zero-source raw numerators H²=17419143/128 and T²=31250131/16. In each of the145 source-decoupled words the source integral is the scalar local moment; its exact H²:D²:T² ratio is9:21:129. All40 source-coupled words have zero charge. Hence the second raw numerator jets are673272 for H² and9650232 for T², without further coupled contractions. The assembly mode records each normalized second jet as `raw_second/Z8 − raw_at_zero*Ljj/Z8`, and divides by8 for h. These are fixed bare H/T jets; T is also an active linear scalar coordinate. They still do not determine its separated-site covariance, mixed active blocks or their independent source directions.

## Reproduction and remaining boundary

Run each family with a60-second cap, e.g. `PYTHONDONTWRITEBYTECODE=1 timeout 60s python source_jet_reweight.py --family quartic`; run the six names private,quartic,double,pair,four,mixed. `--assemble` performs census and exact arithmetic only, with regression targets from those explicit contractions and the accepted denominator/baselines. Its output alone is not a fresh family replay. The saved `source_jet_reweight.txt` records actual per-family commands and exit codes followed by assembly output. Each original module may print its imported baseline controls before the new subset result.

Only the common uniform exponential transverse source jets of these same-site squared observables are evaluated here. General site-resolved first/second source tensors, active(a,b,c,T) covariance blocks, other local combinations, their cross jets and affine-path contacts remain separate inputs. Full scalar propagation, physical matching and original L1 scientific acceptance remain open. Independent mathematical/code and physics/source review are required before preserving this increment as accepted research.
