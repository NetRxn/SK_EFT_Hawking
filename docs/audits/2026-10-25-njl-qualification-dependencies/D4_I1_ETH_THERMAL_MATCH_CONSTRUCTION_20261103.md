# ETH thermal matching construction for D4 and I1

Parent obligation is the Wave 3a thermal-compatibility row of the [lift readback](D4_I1_ETH_LIFT_READBACK_20261103.md). The target is the inference from the diagonal ansatz to the canonical average of a specified initial state. Inozemcev and Volovich's [§§4–6, equations (14)–(22)](https://arxiv.org/pdf/2002.01857) distinguish a canonical saddle energy for each temperature from identifying that energy with the initial mean. The current Lean witness uses two distinct diagonal observable values and demands that both equal one Gibbs average. A single initial-state comparison, including how its temperature is chosen, is required to test the physical inference.

## Finite countermodel with a specified initial state

Take a three-level system with Hamiltonian `diag(E₀−Δ,E₀,E₀+Δ)`, where `E₀ > Δ > 0`, and observable `diag(1,0,1)`. The observable has exact smooth diagonal interpolation `f(E)=((E−E₀)/Δ)²` and zero off-diagonal elements. Prepare the middle eigenstate. Its mean energy is `E₀`, its energy variance is zero, and its time-dependent expectation and Cesàro mean both vanish.

At real inverse temperature `β`, write `x=exp(βΔ)>0`. Cancelling the common factor `exp(−βE₀)`, the Gibbs observable average is `(x+x⁻¹)/(1+x+x⁻¹)`. Since `x+x⁻¹−2=(x−1)²/x≥0`, this expectation is at least `2/3` for every temperature. Thus even selecting the temperature freely cannot make the two observable means agree. Requiring energy matching gives only `β=0`, where the average is exactly `2/3`. This separates exact diagonal interpolation, vanishing off-diagonal entries and an exactly sharp energy from agreement with a canonical observable mean in finite dimension.

## Positive control with quantitative error

For a diagonal observable of the form `f(H)`, let `p` be the initial spectral weights and `q` the Gibbs weights. If both have mean energy `μ` and `|f″|≤M` over the spectral interval, Taylor expansion about `μ` bounds each expectation's distance from `f(μ)` by half of `M` times its energy variance. The constant terms agree and each linear term averages to zero. The difference of the two expectations is therefore at most `M(Var_p+Var_q)/2`. For affine `f` the agreement is exact. In the countermodel at `β=0`, `M=2/Δ²`, `Var_p=0`, and `Var_q=2Δ²/3`; the bound is attained. This gives a check on the sign, the coefficient and the role of canonical concentration.

## Remaining scientific acceptance

This candidate isolates the finite implication and provides an exact control for a route to the thermodynamic result. The original many-body question still requires the energy and entropy scaling, an admissible observable family, the smoothness and concentration estimates on the same energy variable, and any random-element premise of the selected ansatz. A decisive asymptotic counterexample must keep a nonvanishing expectation gap while meeting those premises. The positive route is to establish a vanishing bound with justified energy matching, both concentration estimates and a separate bound on time fluctuations when the observable has off-diagonal elements. See the independent source and derivation review below.

## Independent review

The independent reviewer accepted `25a3a3ac` for the finite countermodel and sharp conditional bound (report SHA-256 `7d3a3ffb0da9045b509ec5cedd5387e162fe1943a79a62f0a27446bb5c892dd3`). They checked the v1 source, Gibbs and initial-state means, uniqueness of matching at β=0, and saturation of the bound. The reviewed sequence implication needs matched means and curvature times summed variances tending to zero. The many-body family, off-diagonal control and manuscript lift remain open. This is acceptance of the bounded construction.
