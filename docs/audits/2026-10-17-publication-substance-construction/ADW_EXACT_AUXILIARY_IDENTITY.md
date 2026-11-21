# Exact regulated ADW auxiliary representation with an explicit signed polynomial weight

17 October 2026. Author: Physics Publication Remediation lead /root, accepting the original microscopic-correspondence BUILD. SCOPED MANUAL CONSTRUCTION ACCEPTED, independent review SHA256 75727aa9418997ab8dac30f5c66a789f5fad5c04ffb2d64a8344bbaf7e007103. This is an exact finite-lattice representation of the source multifermion action, not the assumed scalar ADW/NJL potential, a positive RHMC measure, a continuum limit or a graviton-spectrum computation.

## Source and original objective

The lead directly read all20 pages of the held Diakonov2011 primary, arXiv1109.0091v1, and visually inspected PDF page14 carrying the regulated action/measure. Its equations23-28 specify composite site tetrads, compact link variables, eight independent Grassmann generators per site and quadratic/fourth-degree tetrad interactions. Cosmological vertices contain eight fermionic fields. The following is an original explicit auxiliary construction for this regulated action. It does not attribute an unprovided scalar one-loop potential or Lorentzian selection to that source.

The existing research result `HS+RHMC for ADW tetrad condensation with 8×8 Majorana fermions on Spin(4) lattice.md` proposes a real Gaussian decoupling. It is research input to check, not canonical acceptance. The construction below preserves the true eight-fermion action instead of silently changing it to a sum of squares of bilinears. The existing manuscript correctly discloses the missing equivalence and must retain the original full physical objective while a valid construction is developed.

## 1. Explicit finite regulator and field content

Fix a finite four-dimensional hypercubic torus Lambda with V sites and lattice spacing a>0. Choose fixed consistent fermion boundary conditions. At each site there are four independent complex Dirac generators psi_(x,I) and four independent barred generators barpsi_(x,I), I=1..4. They generate a complex Grassmann algebra with8V generators. This is not an asserted Euclidean eight-real-Majorana identification. Put compact Spin(4)=SU(2)_L times SU(2)_R link matrices Omega_(x,mu)=diag(U_L,U_R) in the Dirac representation (2,1) direct-sum (1,2), with normalized Haar measure on each factor. No (2,2) spinor or automatic positive Pfaffian is assumed.

Use the source's symmetric lattice coframe and let T_(x,mu,A)=a ehat_(x,mu,A), dimensionless. For source link orientation, write explicitly

T_(x,mu,A)=1/4[barpsi_x gamma_A Omega_(x,mu) dagger psi_(x+mu)
 -barpsi_(x+mu) Omega_(x,mu) gamma_A psi_x
 -barpsi_x gamma_A Omega_(x-mu,mu) psi_(x-mu)
 +barpsi_(x-mu) Omega_(x-mu,mu) dagger gamma_A psi_x].                     (1)

Boundary signs, if any, are incorporated in the fixed hopping coefficients. Each T is homogeneous Grassmann degree2 and even, so every pair of T's commutes. A product of more than M=4V such bilinears vanishes, irrespective of shared sites. The site/direction placement and independent connection are retained; no inverse tetrad or assumed bosonic quadratic norm has entered.

For fixed links introduce ordinary commuting symbols X_(x,mu,A). Let

S_x(X,Omega)=g1 epsilon_ABCD X_(x,1,A)X_(x,2,B)X_(x,3,C)X_(x,4,D)
 + (g2/4) sum_(kappa,lambda,mu,nu,C,D) epsilon^(kappa lambda mu nu)
     Tr[Omega_(x,kappa lambda) gamma_C gamma_D gamma5] X_(x,mu,C)X_(x,nu,D). (2)

The plaquette Omega_(x,kappa lambda) is the source's oriented product of four links. The a^4 and a^2 factors cancel on inserting T=a ehat. In this normalization (2) is precisely its cosmological plus Einstein-Hilbert-Cartan exponent in Eq28. g1,g2 are finite dimensionless couplings and the source convention is exp(+sum S_x). Additional specified polynomial even interactions could be included but are not needed here. Set

Z=integral dHaar(Omega) integral dBerezin(barpsi,psi) exp[sum_x S_x(T,Omega)]. (3)

Every exponential is a finite nilpotent polynomial. At finite V the compact group integral is finite; positivity or nonzero Z is not implied. This is the actual regulated multifermion target, rather than a propagator guessed by HS nomenclature.

## 2. Constructive finite Hermite identity

Choose ANY auxiliary variance sigma^2>0 in the dimensionless T normalization. For the16 commuting symbols at one site, define total-degree truncation [ ]_(<=M) and

P_x(X,Omega)=[exp(S_x(X,Omega)) exp(-sigma^2 sum_i X_i^2/2)]_(<=M)
            =sum_(|alpha|<=M) p_(x,alpha)(Omega) X^alpha.                  (4)

This is a completely specified finite polynomial algorithm: expand the degree2 and degree4 polynomials in(2), multiply the two formal series and retain total degree at most M. For instance a coefficient requires only finitely many powers and multinomial products. No polynomial degree tail or unknown fitting function remains. M is a safe global bound, not a claim of optimal computational cost. More local Grassmann support can lower it, but is not needed for exactness.

Let He_j denote probabilists' Hermite polynomials with generating function exp(t z-t^2/2)=sum_j He_j(z)t^j/j!, and He_alpha the product over16 components. Define real auxiliary fields h_(x,i), Gaussian probability measure

dmu_sigma(h_x)=(2pi sigma^2)^(-8) exp[-sum_i h_(x,i)^2/(2sigma^2)] product_i dh_(x,i),
W_x(h_x,Omega)=sum_(|alpha|<=M) p_(x,alpha)(Omega) sigma^(-|alpha|) He_alpha(h_x/sigma). (5)

W_x may be signed or complex. It is a specified polynomial, not exp(-sum h^2/(4g)) with a hidden positive-density assumption.

For standard normal z, integration by parts or the generating function gives E[He_alpha(z) exp(t.z)]=t^alpha exp(t.t/2). Taking t=sigma X therefore proves, coefficient by coefficient,

integral dmu_sigma(h_x) W_x(h_x,Omega) exp(h_x.X)
        =exp(sigma^2 sum_i X_i^2/2) P_x(X,Omega).                          (6)

The identity holds as a formal series. Evaluate at the commuting nilpotent T's: every monomial of degree>M vanishes. By(4), multiplication by the compensating Gaussian series then gives EXACTLY

exp[S_x(T,Omega)]=integral dmu_sigma(h_x) W_x(h_x,Omega) exp(sum_i h_(x,i) T_(x,i)). (7)

No saddle approximation, limit of a singular delta functional, analytic continuation of an unbounded det(e) potential or chosen sign of g1 is needed. The real Gaussian controls every finite polynomial moment. The proof remains valid when the T's have extra algebraic relations: it is an identity before those additional relations are imposed. It also includes g1=0/g2=0 and arbitrary finite couplings; sigma is a representation parameter that cancels exactly, not a physical fit.

A simple check shows why the sign/degree distinction matters. For one commuting nilpotent even X and g>0,

integral dh exp[-h^2/(4g)+h X]/sqrt(4pi g)=exp(+g X^2),                    (8)

by completing the square or Gaussian moments. It is not exp(-g X^2). Real coupling hX has that plus sign; i hX would instead yield the minus sign. Also a Gaussian with a linear bilinear coupling generates an exponent quadratic in those bilinears, hence a quartic fermion interaction, not the general fourth-degree determinant in T (eight fermionic fields). Choosing the opposite sign alone does not repair that degree mismatch. Equation7 handles both issues without substituting a different microscopic action.

## 3. Exact fermion determinant and measure

Since all S_x(T) commute, multiply(7) over sites using independent h_x. The exponent sum_(x,i) h_(x,i)T_(x,i) is a fermion BILINEAR, so define its matrix uniquely by

sum_(x,i) h_(x,i)T_(x,i)=sum_(y,I,z,J) barpsi_(y,I) M_(yI,zJ)(h,Omega) psi_(z,J). (9)

Equation1 specifies every matrix element and its sign: for each (x,mu,A), add h/4 times gamma_A Omega_x dagger to block(x,x+mu), minus Omega_x gamma_A to block(x+mu,x), minus gamma_A Omega_(x-mu) to block(x,x-mu), plus Omega_(x-mu) dagger gamma_A to block(x-mu,x). These are a complete construction algorithm for the4V by4V complex matrix M. In particular no independent bare mass/kinetic term is inserted and M is linear in h. It need not be symmetric, Hermitian or real antisymmetric for the determinant identity to hold.

Choose Berezin orientation consistently with integral exp(barpsi M psi)=det M; the source's four-bar/four-psi site orientation agrees (the possible all-bars/all-psis reordering factor is even for4V components). Integrating the fermions yields

Z=integral dHaar(Omega) product_x dmu_sigma(h_x)
                 [product_x W_x(h_x,Omega)] det M(h,Omega).               (10)

All exchanges of integrals are coefficientwise finite: the Grassmann exponential is polynomial, W is finite polynomial and det M is polynomial; Gaussian moments converge absolutely, and their link-dependent coefficients are continuous/bounded on the finite product of compact groups. Thus(10) is an actual finite-regulator identity, not merely a formal source analogy with an unspecified measure. It extends to inserted Grassmann polynomials because(7) is an algebra identity before Berezin integration. Correlation functions normalized by Z additionally require Z!=0.

There is no proof of a positive RHMC sampling measure. Both W and the determinant must be retained, including any phase. Replacing them with |det M|, a Pfaffian absolute value or a positive scalar potential changes the theory unless its effect is independently controlled. No cost scaling, continuum limit, spontaneous order or physical universality follows from a finite exact identity.

## 4. Composite observables and the remaining physical build

The new h is conjugate to the composite T, not automatically the physical tetrad expectation. Gaussian integration by parts gives, coefficientwise,

integral dmu W h_i exp(h.T)=sigma^2 integral dmu [partial_i W+W T_i] exp(h.T). (11)

Thus using <h>/sigma^2 as <T> would omit the derivative-of-weight term. A division by W at its zeros is unnecessary: keep(11) in its undivided insertion form. Composite source derivatives can instead be carried through(7)-(10) exactly. To obtain an effective physical tetrad action one must introduce actual composite sources, compute their response/Legendre information and justify the selected state/domain. The simple scalar C potential is not derived by setting all h=C or forgetting W.

This construction supplies explicit field content, finite regulator, an exact auxiliary transform and exact fermion integration for the actual cosmological/EHC action. The next substantive steps remain: derive and independently check tractable coefficients/observables or an alternative controlled large-volume representation; establish physical order/background and its effective action with source normalization; derive full tetrad stationarity, constraints, fluctuations and propagating modes; match any scalar reduction and physical parameters/cutoff; calculate the independent vacuum scale and its uncertainties. A full determinant/channel/Legendre calculation, Lorentzian dynamics, gravity/spin-2 content, thermodynamic/continuum control, native formalization and actual simulation are NOT completed here.

The original ADW/Phase5d and separate magnitude/KV obligations remain OPEN BUILD. This is one exact constructive milestone and a repair route, not a demonstrated impossibility, operator deferral, publication claim, G4/G5/G11 pass, native admission or closure. The source's infrared-gravity expectations remain research hypotheses; a well-defined finite Berezin integral by itself does not prove them.

CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES: A generic real Gaussian bilinear HS channel produces +gX^2 and quartic fermions. It does not reproduce the actual determinant of four bilinear tetrads with an assumed quadratic auxiliary potential. Diakonov's Dirac field content and compact block-diagonal Spin(4) links must not be replaced by an unproved real Majorana/Pfaffian positivity claim. The finite signed polynomial representation above is exact and makes those missing weights explicit; its sign/complexity is a cost input, not route closure.
