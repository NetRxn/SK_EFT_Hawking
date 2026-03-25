"""Second-order SK-EFT transport coefficient counting in 1+1D.

Counts the independent transport coefficients at each order in the SK-EFT
derivative expansion for a BEC superfluid in 1+1D, extending the Phase 1
result (2 coefficients at first order) to second order and beyond.

Physical setup:
    Fields: ψ_r (retarded/classical), ψ_a (advanced/quantum)
    Coordinates: (t, x) in 1+1D
    Background: transonic BEC flow (breaks spatial parity)

Method (validated against Phase 1 Lean proofs):
    At EFT order N, the general quadratic SK action has:

    Real (dissipative) sector:
        Monomials: ψ_a · ∂_t^m ∂_x^n ψ_r with m+n ≤ N+1
        (after IBP: all derivatives on ψ_r, undifferentiated ψ_a)

    Imaginary (noise) sector:
        Monomials: (∂^α ψ_a) · (∂^β ψ_a) symmetric bilinear

    The three SK axioms impose constraints:

    (A) Derivative ordering: Only the TOP-LEVEL real monomials (m+n = N+1)
        are new at order N. Lower-level monomials belong to the ideal fluid
        or lower-order corrections and "have no KMS partner" → coefficients
        vanish.  (Phase 1: r4, r5, r6 killed)

    (B) Time-reversal (T-parity): The CGL dynamical KMS symmetry includes
        time reversal (t → -t). Under T, ∂_t^m → (-1)^m ∂_t^m. Combined
        with the ψ_a → -ψ_a sign flip, real monomials acquire factor (-1)^{m+1}.
        For the Re part (which satisfies L_re → -L_re under the Z₂), we need
        (-1)^{m+1} = -1, i.e., m must be EVEN.
        (Phase 1: r3 killed — m=1, odd)

    (C) Fluctuation-dissipation relation (FDR): The iβ∂_t shift in the KMS
        transformation couples Re and Im sectors. Each surviving real coefficient
        determines a corresponding noise coefficient via:
            Im coefficient ~ (Re coefficient) / β
        Imaginary monomials without a real partner vanish.
        (Phase 1: i1 = -r2/β, i2 = (r1+r2)/β, i3 = 0)

    Result: Free transport coefficients at order N =
        #{(m,n) : m+n = N+1, m even, m ≥ 0, n ≥ 0}

    With spatial parity: additionally require n even.
    Our BEC system breaks parity → no n constraint.

Formula (no parity):
    At derivative level L = N+1:
    Count of (m,n) with m+n=L, m even = floor(L/2) + 1

Validation:
    Order 1 (L=2): floor(2/2)+1 = 2 ✓ (γ₁, γ₂ — Phase 1 Lean verified)
    Order 2 (L=3): floor(3/2)+1 = 2 (NEW: two second-order coefficients)
    Order 3 (L=4): floor(4/2)+1 = 3

References:
    - Crossley-Glorioso-Liu, JHEP 2017 (arXiv:1511.03646)
    - Phase 1 Lean proofs: SKDoubling.lean, FirstOrderKMS structure
    - Glorioso-Liu, JHEP 2018 (arXiv:1612.07705)
    - Jain-Kovtun, JHEP 2024 (arXiv:2309.00511)
"""

from dataclasses import dataclass, field
from typing import NamedTuple


# ═══════════════════════════════════════════════════════════════════
# Derivative multi-index
# ═══════════════════════════════════════════════════════════════════

class DerivIndex(NamedTuple):
    """(n_t, n_x) = ∂_t^{n_t} ∂_x^{n_x}."""
    n_t: int
    n_x: int

    @property
    def order(self) -> int:
        return self.n_t + self.n_x

    @property
    def t_parity_even(self) -> bool:
        """True if the number of time derivatives is even."""
        return self.n_t % 2 == 0

    @property
    def x_parity_even(self) -> bool:
        """True if the number of spatial derivatives is even."""
        return self.n_x % 2 == 0

    def __repr__(self):
        parts = []
        if self.n_t == 1: parts.append("∂_t")
        elif self.n_t > 1: parts.append(f"∂_t^{self.n_t}")
        if self.n_x == 1: parts.append("∂_x")
        elif self.n_x > 1: parts.append(f"∂_x^{self.n_x}")
        return " ".join(parts) if parts else ""


# ═══════════════════════════════════════════════════════════════════
# Transport coefficient counting
# ═══════════════════════════════════════════════════════════════════

@dataclass
class OrderAnalysis:
    """Complete analysis of transport coefficients at a given EFT order."""
    order: int
    deriv_level: int  # = order + 1
    all_real_monomials: list[DerivIndex]  # all (m,n) with m+n = deriv_level
    t_reversal_surviving: list[DerivIndex]  # subset with even m
    parity_surviving: list[DerivIndex]  # subset with even m AND even n
    n_transport_no_parity: int  # free params without spatial parity
    n_transport_with_parity: int  # free params with spatial parity


def analyze_order(N: int, verbose: bool = True) -> OrderAnalysis:
    """Count transport coefficients at EFT order N.

    Args:
        N: EFT order (1 = first dissipative correction, 2 = second, ...)
        verbose: Print detailed output

    Returns:
        OrderAnalysis with complete results.
    """
    L = N + 1  # derivative level

    # All real monomials at this level: ψ_a · ∂_t^m ∂_x^n ψ_r with m+n = L
    all_monoms = [DerivIndex(m, L - m) for m in range(L + 1)]

    # Time-reversal constraint: m must be even
    t_surviving = [d for d in all_monoms if d.t_parity_even]

    # Additional spatial parity: n must also be even
    p_surviving = [d for d in t_surviving if d.x_parity_even]

    result = OrderAnalysis(
        order=N,
        deriv_level=L,
        all_real_monomials=all_monoms,
        t_reversal_surviving=t_surviving,
        parity_surviving=p_surviving,
        n_transport_no_parity=len(t_surviving),
        n_transport_with_parity=len(p_surviving),
    )

    if verbose:
        print(f"\n{'='*70}")
        print(f"EFT ORDER {N}  (derivative level L = {L})")
        print(f"{'='*70}")

        print(f"\nAll real monomials at level {L} (ψ_a · ∂^α ψ_r, |α|={L}):")
        for d in all_monoms:
            d_str = repr(d)
            t_ok = "✓" if d.t_parity_even else "✗"
            p_ok = "✓" if d.x_parity_even else "✗"
            print(f"  ψ_a · {d_str + ' ' if d_str else ''}ψ_r"
                  f"   [m={d.n_t} {t_ok}T-rev, n={d.n_x} {p_ok}parity]")

        print(f"\nAfter T-reversal (even m):")
        for d in t_surviving:
            d_str = repr(d)
            print(f"  ψ_a · {d_str + ' ' if d_str else ''}ψ_r")

        print(f"\nNew transport coefficients at order {N}:")
        print(f"  Without spatial parity: {result.n_transport_no_parity}")
        print(f"  With spatial parity:    {result.n_transport_with_parity}")

    return result


def fdr_relations(N: int) -> list[str]:
    """Describe the FDR relations at order N (how Im coefficients are fixed).

    At each order, the imaginary (noise) sector is fully determined by the
    real (dissipative) coefficients via the fluctuation-dissipation relation.

    The FDR works through the iβ∂_t shift in the KMS transformation:
    - Each real coefficient r_{m,n} at level L generates an imaginary
      contribution via the shift
    - The imaginary coefficients are then fixed as linear combinations
      of real coefficients divided by β

    Phase 1 example:
        i₁ = -r₂/β  (noise coefficient from ∂²_x dissipation)
        i₂ = (r₁+r₂)/β  (noise coefficient from ∂²_t + ∂²_x dissipation)
        i₃ = 0  (no partner)
    """
    L = N + 1
    surviving = [DerivIndex(m, L - m) for m in range(L + 1) if m % 2 == 0]

    relations = []
    for i, d in enumerate(surviving):
        coeff_name = f"γ_{{{N},{i+1}}}"
        deriv_str = repr(d)
        relations.append(
            f"{coeff_name}: coefficient of ψ_a · {deriv_str + ' ' if deriv_str else ''}ψ_r"
        )

    return relations


# ═══════════════════════════════════════════════════════════════════
# Imaginary sector enumeration
# ═══════════════════════════════════════════════════════════════════

def count_imaginary_monomials(N: int) -> dict:
    """Count imaginary (noise) monomials at order N.

    The imaginary sector has monomials (∂^α ψ_a)(∂^β ψ_a) with the constraint
    that each ψ_a factor has at most N derivatives, and the total is ≤ 2N.

    After IBP reduction and symmetry:
    - Symmetric bilinear: count unordered pairs {α, β}
    - IBP: relates some pairs (e.g., ψ_a · ∂_μ ψ_a = total derivative → vanishes)
    - T-reversal: total time derivatives must be even (since ψ_a → -ψ_a under Z₂,
      and Im must be invariant, the overall sign from (-1)^{total_m} must be +1)

    Returns dict with counts.
    """
    max_a_deriv = N

    # All derivative indices for ψ_a up to order N
    a_derivs = []
    for total in range(max_a_deriv + 1):
        for m in range(total + 1):
            a_derivs.append(DerivIndex(m, total - m))

    # Symmetric pairs (unordered)
    all_pairs = []
    for i, d1 in enumerate(a_derivs):
        for d2 in a_derivs[i:]:
            total_t = d1.n_t + d2.n_t
            total_x = d1.n_x + d2.n_x
            total_deriv = d1.order + d2.order

            # IBP: pairs where one factor is undifferentiated and the other
            # has exactly 1 derivative are total derivatives → vanish
            is_total_deriv = (d1.order == 0 and d2.order == 1) or \
                             (d1.order == 1 and d2.order == 0)

            # T-reversal: total time derivatives must be even
            t_rev_ok = total_t % 2 == 0

            all_pairs.append({
                'pair': (d1, d2),
                'total_derivs': total_deriv,
                'total_t': total_t,
                'total_x': total_x,
                'is_total_deriv': is_total_deriv,
                't_reversal_ok': t_rev_ok,
                'survives': t_rev_ok and not is_total_deriv,
            })

    surviving = [p for p in all_pairs if p['survives']]

    return {
        'all_pairs': all_pairs,
        'surviving': surviving,
        'n_total': len(all_pairs),
        'n_surviving': len(surviving),
    }


# ═══════════════════════════════════════════════════════════════════
# Parity alternation theorem
# ═══════════════════════════════════════════════════════════════════

def parity_alternation(N: int) -> dict:
    """Determine whether order-N corrections require broken spatial parity.

    Structural result: at EFT order N with derivative level L = N+1,
    the surviving monomials have (m, n) with m even and n = L - m.

    - If N is odd → L is even → n = L - m is even (since m even, L even)
      → ALL monomials are parity-preserving
      → count(N, parity) = count(N, no parity)

    - If N is even → L is odd → n = L - m is odd (since m even, L odd)
      → ALL monomials REQUIRE broken parity
      → count(N, parity) = 0

    Physical implication:
      - Odd-order corrections (N=1,3,5,...) exist universally, even in
        homogeneous systems with full spatial symmetry.
      - Even-order corrections (N=2,4,6,...) are pure background-flow effects
        that vanish without spatial parity breaking.

    This creates a systematic alternation in the EFT derivative expansion:
    universal → flow-only → universal → flow-only → ...

    Returns:
        Dict with keys: N, L, requires_parity_breaking, all_monomials_parity_type,
        count_no_parity, count_with_parity, physical_interpretation.
    """
    L = N + 1
    requires_breaking = N % 2 == 0  # even N → odd L → requires breaking

    r = analyze_order(N, verbose=False)

    if requires_breaking:
        interp = (f"Order {N} (even): ALL {r.n_transport_no_parity} monomials have "
                  f"odd spatial derivative count → require broken parity (background flow). "
                  f"These corrections vanish in homogeneous systems.")
    else:
        interp = (f"Order {N} (odd): ALL {r.n_transport_no_parity} monomials have "
                  f"even spatial derivative count → parity-preserving. "
                  f"These corrections exist universally.")

    return {
        'N': N,
        'L': L,
        'requires_parity_breaking': requires_breaking,
        'all_monomials_parity_type': 'odd_n' if requires_breaking else 'even_n',
        'count_no_parity': r.n_transport_no_parity,
        'count_with_parity': r.n_transport_with_parity,
        'monomials': r.t_reversal_surviving,
        'physical_interpretation': interp,
    }


def third_order_analysis(verbose: bool = True) -> OrderAnalysis:
    """Detailed analysis of the third-order EFT extension.

    At N=3, L=4, the three surviving monomials are:
      (m=0, n=4): ψ_a · ∂⁴_x ψ_r  — quartic spatial
      (m=2, n=2): ψ_a · ∂²_t ∂²_x ψ_r  — mixed temporal-spatial
      (m=4, n=0): ψ_a · ∂⁴_t ψ_r  — quartic temporal

    Key qualitative features:
      1. ALL THREE are parity-even (n even) → exist without background flow
      2. The ∂⁴_x term matches the Bogoliubov superluminal dispersion ℏ²k⁴/4m²
      3. Spectrum correction δ^(3)(ω) ∝ ω⁴ is even in frequency (unlike odd ω³ at N=2)
      4. The ∂⁴_t term is purely temporal damping at fourth order

    Lean: thirdOrder_count (Aristotle run 3eedcabb), cumulative_count_through_3
    """
    r = analyze_order(3, verbose=verbose)

    if verbose:
        pa = parity_alternation(3)
        print(f"\n{'─'*70}")
        print("PARITY ALTERNATION at third order:")
        print(f"  {pa['physical_interpretation']}")
        print(f"\n  Contrast with second order (N=2):")
        pa2 = parity_alternation(2)
        print(f"  {pa2['physical_interpretation']}")

        print(f"\n  The three third-order monomials:")
        labels = [
            ("γ_{3,1}", "quartic spatial dispersion — mirrors Bogoliubov ℏ²k⁴/4m²"),
            ("γ_{3,2}", "mixed temporal-spatial — ω²k² cross-term"),
            ("γ_{3,3}", "quartic temporal damping — pure time evolution"),
        ]
        for (d, (name, desc)) in zip(r.t_reversal_surviving, labels):
            d_str = repr(d)
            print(f"    {name}: ψ_a · {d_str} ψ_r — {desc}")

        print(f"\n  Spectral correction: δ^(3)(ω) ∝ ω⁴ (even in frequency)")
        print(f"  Units: γ_{{3,i}} have dimension [m⁴/s]")

    return r


# ═══════════════════════════════════════════════════════════════════
# Main analysis
# ═══════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    print("SK-EFT Transport Coefficient Counting in 1+1D")
    print("Extending Phase 1 (Lean-verified) to higher orders")
    print()

    # ─── Order 1 (Phase 1 validation) ───
    r1 = analyze_order(1, verbose=True)

    print(f"\n{'─'*70}")
    print(f"VALIDATION: Phase 1 Lean gives 2 free parameters (γ₁, γ₂)")
    if r1.n_transport_no_parity == 2:
        print("✓ PASSED: our counting gives 2 (without parity)")
    else:
        print(f"✗ FAILED: got {r1.n_transport_no_parity}")

    print("\nPhase 1 FDR (from Lean FirstOrderKMS):")
    print("  i₁·β = -r₂  (ψ_a² noise ← ∂²_x dissipation)")
    print("  i₂·β = r₁+r₂  ((∂_t ψ_a)² noise ← ∂²_t+∂²_x dissipation)")
    print("  i₃ = 0  ((∂_x ψ_a)² has no FDR partner)")

    # ─── Order 2 (new result) ───
    r2 = analyze_order(2, verbose=True)

    print(f"\nOrder 2 FDR relations (new transport coefficients):")
    for rel in fdr_relations(2):
        print(f"  {rel}")

    # Count imaginary sector
    im2 = count_imaginary_monomials(2)
    print(f"\nImaginary sector at order 2:")
    print(f"  Total candidate pairs: {im2['n_total']}")
    print(f"  After T-reversal + IBP: {im2['n_surviving']}")
    print(f"  All determined by FDR from {r2.n_transport_no_parity} real coefficients")

    # ─── Order 3 (for completeness) ───
    r3 = analyze_order(3, verbose=True)

    # ─── Summary table ───
    print(f"\n\n{'='*70}")
    print("SUMMARY: Transport coefficients in 1+1D SK-EFT")
    print(f"{'='*70}")
    print(f"{'Order':>6} {'Level':>6} {'No parity':>12} {'With parity':>13} {'Cumulative':>12}")
    print(f"{'─'*6} {'─'*6} {'─'*12} {'─'*13} {'─'*12}")

    cumul_np = 0
    cumul_p = 0
    for N in range(1, 5):
        r = analyze_order(N, verbose=False)
        cumul_np += r.n_transport_no_parity
        cumul_p += r.n_transport_with_parity
        parity_note = "" if r.n_transport_with_parity > 0 else " (none!)"
        print(f"{N:>6} {r.deriv_level:>6} {r.n_transport_no_parity:>12}"
              f" {r.n_transport_with_parity:>13}{parity_note} {cumul_np:>12}")

    print(f"\nKey result for Phase 2 paper:")
    print(f"  At second order (N=2), {r2.n_transport_no_parity} new transport coefficients")
    print(f"  appear in the SK-EFT for a BEC with background flow.")
    print(f"  These are:")
    for d in r2.t_reversal_surviving:
        d_str = repr(d)
        print(f"    ψ_a · {d_str} ψ_r  (m={d.n_t}, n={d.n_x})")

    print(f"\n  With spatial parity (no background flow):")
    print(f"    {r2.n_transport_with_parity} new coefficients"
          f" {'— NO new physics at this order!' if r2.n_transport_with_parity == 0 else ''}")

    print(f"\n  Physical interpretation:")
    print(f"    The two new coefficients parameterize:")
    print(f"    1. ψ_a · ∂²_t ∂_x ψ_r — flow-dependent temporal-spatial damping")
    print(f"    2. ψ_a · ∂³_x ψ_r — cubic spatial dispersion/damping")
    print(f"    These generate FREQUENCY-DEPENDENT corrections δ(ω) to the")
    print(f"    Hawking spectrum, going beyond the constant δ_diss of Paper 1.")
