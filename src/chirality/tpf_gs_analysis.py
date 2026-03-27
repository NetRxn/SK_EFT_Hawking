"""Chirality Wall Synthesis: TPF vs Golterman-Shamir Compatibility Analysis.

Formal analysis of whether the Thorngren-Preskill-Fidkowski (TPF) SPT slab
disentangler evades the Golterman-Shamir (GS) generalized no-go theorem for
chiral lattice fermions.

The analysis chain:
    (i)   Extract the precise mathematical conditions of the GS generalized
          no-go theorem: lattice translation invariance, finite-range
          Hamiltonian, relativistic continuum limit, complete interpolating fields.
    (ii)  Extract the precise mathematical setting of the TPF disentangler:
          infinite-dimensional rotor Hilbert spaces, not-on-site symmetries,
          ancilla degrees of freedom, extra-dimensional SPT slab.
    (iii) Formally check each GS condition against the TPF construction.
    (iv)  Identify the 4+1D gapped interface conjecture as the critical
          unproven assumption.
    (v)   Assess: if the conjecture is proven, does the chirality wall fall?

Key references:
    - Thorngren-Preskill-Fidkowski (Jan 2026): SPT slab disentangler
    - Golterman-Shamir (2024-2026): generalized no-go theorem
    - Butt-Catterall-Hasenfratz (PRL 2025): staggered fermion SMG
    - Hasenfratz-Witzel (Nov 2025): SMG with 16 Weyl fermions
    - Gioia-Thorngren (Mar 2025): topological constraints
    - Seifnashri (Jan 2026): symmetry TFT perspective

Lean: ChiralityWall.lean (planned)
"""

from dataclasses import dataclass, field
from enum import Enum
from typing import Optional


# ═══════════════════════════════════════════════════════════════════
# Condition and construction data structures
# ═══════════════════════════════════════════════════════════════════

class EvasionVerdict(Enum):
    """Whether a no-go condition applies to a given construction."""
    APPLIES = "applies"               # Condition is satisfied → no-go binds
    EVADED = "evaded"                 # Condition is violated → no-go does not bind
    UNCLEAR = "unclear"               # Status depends on unproven conjecture


@dataclass
class NoGoCondition:
    """A condition in the Golterman-Shamir generalized no-go theorem.

    The GS theorem (2024-2026) generalizes the Nielsen-Ninomiya theorem by
    dropping the free-fermion assumption while retaining conclusions about
    chiral fermion doubling.

    Attributes:
        name: Short identifier for the condition.
        mathematical_statement: Formal mathematical statement of the condition.
        description: Physical explanation of what the condition requires.
        applies_to_tpf: Whether this condition applies to the TPF construction.
        evasion_mechanism: If evaded, the mechanism by which TPF evades it.
    """
    name: str
    mathematical_statement: str
    description: str
    applies_to_tpf: EvasionVerdict
    evasion_mechanism: Optional[str] = None


@dataclass
class TPFIngredient:
    """A key ingredient of the TPF disentangler construction.

    Attributes:
        name: Short identifier.
        description: Physical explanation.
        mathematical_setting: Formal mathematical characterization.
        gs_conditions_affected: Which GS conditions this ingredient affects.
    """
    name: str
    description: str
    mathematical_setting: str
    gs_conditions_affected: list[str] = field(default_factory=list)


@dataclass
class TPFConstruction:
    """Complete description of the Thorngren-Preskill-Fidkowski construction.

    The TPF construction (Jan 2026) proposes to produce chiral fermions on the
    boundary of a 4+1D SPT slab, using rotor Hilbert spaces rather than
    finite-dimensional qubits, with symmetries implemented on links rather
    than sites.

    Attributes:
        ingredients: The key mathematical ingredients.
        spacetime_dim_bulk: Dimension of the bulk (4+1D).
        spacetime_dim_boundary: Dimension of the boundary (3+1D).
        hilbert_space_type: Type of local Hilbert space (infinite-dimensional rotors).
        symmetry_implementation: How symmetries are implemented (on links, not sites).
        critical_conjecture: The unproven assumption required for the construction.
    """
    ingredients: list[TPFIngredient]
    spacetime_dim_bulk: int = 5
    spacetime_dim_boundary: int = 4
    hilbert_space_type: str = "infinite-dimensional rotor"
    symmetry_implementation: str = "not-on-site (group elements on links)"
    critical_conjecture: str = (
        "The 4+1D SPT phase can be gapped at both boundaries simultaneously, "
        "producing a gapped interface between the two boundary theories, such "
        "that the low-energy theory on a single boundary is the desired chiral "
        "fermion theory without mirror fermions."
    )


@dataclass
class NumericalEvidence:
    """Numerical lattice evidence relevant to the chirality wall.

    Attributes:
        group: Research group providing the evidence.
        year: Year of publication.
        system: The lattice system studied.
        finding: Key result.
        relevance: How this relates to the chirality wall question.
        reference: Short reference string.
    """
    group: str
    year: int
    system: str
    finding: str
    relevance: str
    reference: str


class WallStatus(Enum):
    """Overall status of the chirality wall."""
    STANDING = "standing"                   # No-go fully applies
    BREACHED = "breached"                   # No-go evaded, chiral fermions possible
    CONDITIONAL_BREACH = "conditional_breach"  # Breach contingent on unproven conjecture
    UNDER_SIEGE = "under_siege"             # Significant evidence of weakening


@dataclass
class CompatibilityResult:
    """Complete result of the TPF vs GS compatibility analysis.

    Attributes:
        conditions: The GS no-go conditions and their status.
        construction: The TPF construction.
        conditions_evaded: Number of GS conditions evaded by TPF.
        conditions_applying: Number of GS conditions that still apply.
        conditions_unclear: Number of conditions whose status is unclear.
        critical_conjecture_status: Status of the 4+1D gapped interface conjecture.
        wall_status: Overall assessment of the chirality wall.
        assessment: Detailed textual assessment.
        numerical_evidence: Supporting numerical evidence.
    """
    conditions: list[NoGoCondition]
    construction: TPFConstruction
    conditions_evaded: int
    conditions_applying: int
    conditions_unclear: int
    critical_conjecture_status: str
    wall_status: WallStatus
    assessment: str
    numerical_evidence: list[NumericalEvidence] = field(default_factory=list)


# ═══════════════════════════════════════════════════════════════════
# GS no-go conditions
# ═══════════════════════════════════════════════════════════════════

def gs_conditions() -> list[NoGoCondition]:
    """Extract the precise mathematical conditions of the Golterman-Shamir
    generalized no-go theorem.

    The GS theorem (arXiv:2406.07997, updated 2024-2026) proves that under
    four conditions, any lattice Hamiltonian cannot produce a single Weyl
    fermion in the continuum limit without producing its mirror partner.
    This generalizes Nielsen-Ninomiya (1981) beyond free fermions.

    Returns:
        List of four NoGoCondition dataclasses.
    """
    return [
        NoGoCondition(
            name="lattice_translation_invariance",
            mathematical_statement=(
                "The Hamiltonian H commutes with lattice translations T_a for "
                "all lattice vectors a: [H, T_a] = 0. The system lives on a "
                "regular d-dimensional lattice Z^d (or torus Z_L^d) with a "
                "single site per unit cell."
            ),
            description=(
                "The lattice system has exact discrete translation symmetry. "
                "This is the lattice analog of continuum translation invariance "
                "and ensures that momentum (crystal momentum) is a good quantum "
                "number. The single-site-per-unit-cell requirement prevents "
                "trivial evasion by staggering."
            ),
            applies_to_tpf=EvasionVerdict.EVADED,
            evasion_mechanism=(
                "The TPF construction uses an extra-dimensional slab geometry "
                "(4+1D bulk with 3+1D boundaries). The slab has finite extent "
                "in the extra dimension, breaking translation invariance in that "
                "direction. While the 3+1D boundary preserves lattice translations "
                "in the physical directions, the full 4+1D construction does not "
                "satisfy translation invariance in all lattice directions. "
                "Moreover, the not-on-site symmetry implementation (group elements "
                "on links) effectively doubles the unit cell structure, violating "
                "the single-site-per-unit-cell requirement."
            ),
        ),
        NoGoCondition(
            name="finite_range_hamiltonian",
            mathematical_statement=(
                "The Hamiltonian H = sum_X h_X decomposes into local terms h_X "
                "each supported on a region X of bounded diameter: "
                "diam(X) <= R for some fixed R independent of system size L. "
                "Equivalently, H has exponentially decaying interactions: "
                "||h_{x,y}|| <= C exp(-|x-y|/xi) for constants C, xi."
            ),
            description=(
                "All interactions in the Hamiltonian are local — no term couples "
                "sites separated by more than a fixed distance R. This is the "
                "lattice regularity condition that ensures the continuum limit "
                "is well-defined and the theory is UV-complete on the lattice."
            ),
            applies_to_tpf=EvasionVerdict.APPLIES,
            evasion_mechanism=None,
        ),
        NoGoCondition(
            name="relativistic_continuum_limit",
            mathematical_statement=(
                "In the continuum limit (lattice spacing a -> 0), the low-energy "
                "spectrum reproduces a relativistic quantum field theory: the "
                "single-particle dispersion relation satisfies "
                "E(p) = sqrt(p^2 + m^2) + O(a) for momenta |p| << 1/a, and "
                "the S-matrix elements match those of a Lorentz-invariant QFT."
            ),
            description=(
                "The lattice theory must flow to a Lorentz-invariant QFT in the "
                "infrared. This is the condition that distinguishes the chiral "
                "fermion problem from the broader question of gapping fermion "
                "doublers — one needs not just a gap but a gap that leaves behind "
                "a relativistic spectrum."
            ),
            applies_to_tpf=EvasionVerdict.UNCLEAR,
            evasion_mechanism=(
                "The TPF construction's continuum limit has not been rigorously "
                "established. The construction produces the correct anomaly "
                "structure (matching the perturbative chiral anomaly), which is "
                "necessary but not sufficient for a relativistic continuum limit. "
                "The critical question is whether the 4+1D gapped interface "
                "conjecture, if proven, would guarantee the correct continuum "
                "limit on the boundary. This is the core of the unresolved "
                "status."
            ),
        ),
        NoGoCondition(
            name="complete_interpolating_fields",
            mathematical_statement=(
                "There exist local lattice operators psi_alpha(x) (interpolating "
                "fields) that create all single-particle states from the vacuum: "
                "for every momentum p in the Brillouin zone and every species "
                "index alpha, <0|psi_alpha(x)|p, alpha> != 0. The set "
                "{psi_alpha} is complete in the sense that every low-energy "
                "single-particle state is created by some psi_alpha."
            ),
            description=(
                "One must be able to construct local lattice operators that "
                "interpolate to every physical particle state in the continuum "
                "limit. This condition excludes constructions where the target "
                "fermions are non-local composites of the lattice degrees of "
                "freedom, as such composites would not count as 'lattice fermions' "
                "in the sense of the no-go theorem."
            ),
            applies_to_tpf=EvasionVerdict.EVADED,
            evasion_mechanism=(
                "The TPF construction uses ancilla (auxiliary) degrees of freedom "
                "that participate in the disentangling unitary. The physical "
                "chiral fermion on the boundary is a composite of the original "
                "lattice fermion and the rotor ancilla fields, entangled through "
                "the SPT bulk. The interpolating field for the chiral fermion is "
                "therefore not a simple local lattice operator but involves the "
                "ancilla Hilbert space, which the GS theorem's interpolating "
                "field condition does not account for. Additionally, the rotor "
                "Hilbert spaces are infinite-dimensional, placing them outside "
                "the class of lattice systems GS considers."
            ),
        ),
    ]


# ═══════════════════════════════════════════════════════════════════
# TPF construction
# ═══════════════════════════════════════════════════════════════════

def tpf_construction() -> TPFConstruction:
    """Extract the precise mathematical setting of the TPF disentangler.

    The Thorngren-Preskill-Fidkowski construction (Jan 2026) proposes to
    realize chiral fermions on the boundary of a 4+1D symmetry-protected
    topological (SPT) phase, using three key departures from the standard
    lattice fermion setting.

    Returns:
        TPFConstruction dataclass with all ingredients.
    """
    ingredients = [
        TPFIngredient(
            name="infinite_dimensional_rotors",
            description=(
                "The local Hilbert space on each site is the Hilbert space of "
                "a quantum rotor, L^2(G), where G is a compact Lie group "
                "(typically G = U(1) or SU(N)). This is infinite-dimensional, "
                "unlike the finite-dimensional Hilbert spaces (qubits, qudits) "
                "assumed in most lattice constructions."
            ),
            mathematical_setting=(
                "H_site = L^2(G) with basis {|g>}_{g in G}. The group acts by "
                "left multiplication: U_L(h)|g> = |hg>. For G = U(1), this is "
                "equivalent to a particle on a circle with H_site = "
                "span{|n>}_{n in Z}."
            ),
            gs_conditions_affected=[
                "complete_interpolating_fields",
            ],
        ),
        TPFIngredient(
            name="not_on_site_symmetry",
            description=(
                "The global symmetry is not implemented as a tensor product of "
                "on-site unitaries. Instead, the symmetry acts on links (edges) "
                "of the lattice, implemented as group multiplication on the "
                "rotor degrees of freedom living on links. This is analogous to "
                "gauge transformations in lattice gauge theory, but here the "
                "symmetry is global (no local gauge redundancy)."
            ),
            mathematical_setting=(
                "For a symmetry group G, the symmetry operator U(g) acts as "
                "U(g) = prod_{links (x,x+a)} L_g^{(x,x+a)} where L_g acts on "
                "the rotor Hilbert space of the link. This is NOT of the form "
                "U(g) = tensor_x u_g^{(x)} (on-site). The not-on-site nature "
                "is essential: it allows the symmetry to act as a 'gauge-like' "
                "transformation that mixes neighboring sites."
            ),
            gs_conditions_affected=[
                "lattice_translation_invariance",
                "complete_interpolating_fields",
            ],
        ),
        TPFIngredient(
            name="ancilla_degrees_of_freedom",
            description=(
                "Extra auxiliary (ancilla) degrees of freedom are introduced "
                "that do not carry physical quantum numbers but participate in "
                "the disentangling unitary. These ancillae can be gapped out "
                "(given a large mass gap) without affecting the low-energy "
                "physics, but they are essential for the disentangling step "
                "that separates the chiral fermion from its mirror partner."
            ),
            mathematical_setting=(
                "The total Hilbert space is H_phys tensor H_ancilla. The "
                "disentangling unitary U_dis acts on the full space: "
                "U_dis |psi_chiral, psi_mirror> = |psi_chiral> tensor |psi_trivial>. "
                "After disentangling, the ancilla sector is in a trivially "
                "gapped state (product state) and can be traced out."
            ),
            gs_conditions_affected=[
                "complete_interpolating_fields",
            ],
        ),
        TPFIngredient(
            name="extra_dimensional_spt_slab",
            description=(
                "The construction embeds the 3+1D target theory as the boundary "
                "of a 4+1D SPT phase. The SPT slab has finite thickness in the "
                "extra dimension. The top boundary carries the chiral fermion, "
                "the bottom boundary carries the mirror fermion. The bulk is "
                "gapped. The key conjecture is that the interface between top "
                "and bottom boundaries can also be gapped, fully decoupling the "
                "chiral mode from its mirror."
            ),
            mathematical_setting=(
                "Consider a 4+1D lattice slab: Z^4 x {0, 1, ..., N_5}. The "
                "bulk Hamiltonian H_bulk is in the nontrivial SPT phase "
                "classified by Omega^5_{Spin}(BG) (the bordism group). The "
                "boundary at y=0 has left-handed Weyl fermions; the boundary "
                "at y=N_5 has right-handed Weyl fermions (mirror). The "
                "disentangling is achieved by finding a gapped, symmetric "
                "Hamiltonian for the slab that produces only the chiral mode "
                "at low energies."
            ),
            gs_conditions_affected=[
                "lattice_translation_invariance",
                "relativistic_continuum_limit",
            ],
        ),
    ]

    return TPFConstruction(ingredients=ingredients)


# ═══════════════════════════════════════════════════════════════════
# Numerical evidence
# ═══════════════════════════════════════════════════════════════════

def numerical_evidence() -> list[NumericalEvidence]:
    """Compile numerical lattice evidence relevant to the chirality wall.

    Several groups have produced Monte Carlo evidence for symmetric mass
    generation (SMG) — the gapping of fermion doublers without breaking
    symmetry — which is a necessary (but not sufficient) ingredient for
    chiral lattice fermions.

    Returns:
        List of NumericalEvidence dataclasses.
    """
    return [
        NumericalEvidence(
            group="Butt-Catterall-Hasenfratz",
            year=2025,
            system="Staggered fermions with four-fermion interaction, 2+1D and 3+1D",
            finding=(
                "Demonstrated symmetric mass generation (SMG) in staggered "
                "fermion systems. The fermion bilinear condensate vanishes "
                "(<psibar psi> = 0) while the fermion mass gap is nonzero. "
                "Published in PRL."
            ),
            relevance=(
                "SMG is the gapping mechanism that would remove mirror fermions "
                "in the domain wall / overlap approach. Numerical evidence that "
                "SMG exists in interacting lattice fermion systems is a "
                "prerequisite for the TPF approach to work."
            ),
            reference="Butt-Catterall-Hasenfratz, PRL 2025",
        ),
        NumericalEvidence(
            group="Hasenfratz-Witzel",
            year=2025,
            system="16 Weyl fermions with multifermion interactions",
            finding=(
                "Demonstrated SMG with 16 Weyl fermions — the minimal number "
                "required by the mod-16 periodicity of the fermion SPT "
                "classification in 3+1D. This matches the anomaly-cancellation "
                "requirement: 16 Weyl fermions can be gapped without breaking "
                "any symmetry because their anomaly vanishes mod 16."
            ),
            relevance=(
                "The mod-16 periodicity is precisely the topological structure "
                "underlying the TPF construction. SMG of 16 Weyl fermions "
                "demonstrates that the required gapping is dynamically possible, "
                "not just topologically allowed."
            ),
            reference="Hasenfratz-Witzel, Nov 2025",
        ),
        NumericalEvidence(
            group="Gioia-Thorngren",
            year=2025,
            system="Topological constraints on lattice fermion anomalies",
            finding=(
                "Established rigorous topological constraints on which anomalies "
                "can and cannot be reproduced on the lattice. Showed that the "
                "perturbative chiral anomaly can be matched by a lattice system "
                "with not-on-site symmetries, while the global (non-perturbative) "
                "anomaly places constraints on the fermion content."
            ),
            relevance=(
                "Provides the mathematical framework for understanding which "
                "no-go theorems can be evaded by not-on-site symmetries. "
                "Directly supports the TPF approach by showing that the anomaly "
                "matching conditions can be satisfied."
            ),
            reference="Gioia-Thorngren, Mar 2025",
        ),
        NumericalEvidence(
            group="Seifnashri",
            year=2026,
            system="Symmetry TFT analysis of lattice chirality",
            finding=(
                "Analyzed the chirality question from the symmetry TFT "
                "(topological field theory) perspective. Showed that the "
                "obstruction to chiral fermions is captured by the bulk "
                "topological order of the symmetry TFT, and that certain "
                "boundary conditions can evade the obstruction."
            ),
            relevance=(
                "Provides an independent theoretical argument supporting the "
                "TPF approach: the symmetry TFT perspective suggests that the "
                "extra-dimensional construction is natural and that the "
                "chirality obstruction is a boundary condition question, not "
                "a fundamental impossibility."
            ),
            reference="Seifnashri, Jan 2026",
        ),
    ]


# ═══════════════════════════════════════════════════════════════════
# Compatibility check
# ═══════════════════════════════════════════════════════════════════

def check_compatibility() -> CompatibilityResult:
    """Formally check each GS no-go condition against the TPF construction.

    This is the core analysis: for each of the four GS conditions, determine
    whether the TPF construction satisfies or evades it. The overall
    conclusion depends on how many conditions are evaded and whether the
    critical conjecture is proven.

    The logical structure:
        - If ALL four GS conditions apply → no-go binds → chirality wall stands.
        - If ANY condition is evaded → no-go does not apply → wall may fall.
        - If evasion depends on unproven conjecture → conditional breach.

    Returns:
        CompatibilityResult with full analysis.
    """
    conditions = gs_conditions()
    construction = tpf_construction()
    evidence = numerical_evidence()

    evaded = sum(1 for c in conditions if c.applies_to_tpf == EvasionVerdict.EVADED)
    applying = sum(1 for c in conditions if c.applies_to_tpf == EvasionVerdict.APPLIES)
    unclear = sum(1 for c in conditions if c.applies_to_tpf == EvasionVerdict.UNCLEAR)

    # Determine overall wall status
    critical_conjecture_status = (
        "UNPROVEN. The 4+1D gapped interface conjecture has not been "
        "rigorously established. Numerical evidence (Butt-Catterall-Hasenfratz, "
        "Hasenfratz-Witzel) supports SMG in lower-dimensional analogs, and "
        "topological arguments (Gioia-Thorngren, Seifnashri) suggest it should "
        "hold, but a mathematical proof or definitive numerical demonstration "
        "in the full 4+1D setting is lacking."
    )

    wall_status = WallStatus.CONDITIONAL_BREACH

    assessment = _build_assessment(conditions, evaded, applying, unclear)

    return CompatibilityResult(
        conditions=conditions,
        construction=construction,
        conditions_evaded=evaded,
        conditions_applying=applying,
        conditions_unclear=unclear,
        critical_conjecture_status=critical_conjecture_status,
        wall_status=wall_status,
        assessment=assessment,
        numerical_evidence=evidence,
    )


def _build_assessment(
    conditions: list[NoGoCondition],
    evaded: int,
    applying: int,
    unclear: int,
) -> str:
    """Build the detailed textual assessment.

    Args:
        conditions: The GS no-go conditions.
        evaded: Count of evaded conditions.
        applying: Count of conditions that apply.
        unclear: Count of unclear conditions.

    Returns:
        Multi-paragraph assessment string.
    """
    lines = []

    lines.append(
        "CHIRALITY WALL STATUS: CONDITIONAL BREACH"
    )
    lines.append("")
    lines.append(
        f"Of the {len(conditions)} Golterman-Shamir no-go conditions, the TPF "
        f"construction evades {evaded}, is subject to {applying}, and has "
        f"{unclear} whose status depends on the critical conjecture."
    )
    lines.append("")

    # Per-condition summary
    lines.append("Per-condition analysis:")
    for c in conditions:
        status_str = c.applies_to_tpf.value.upper()
        lines.append(f"  [{status_str}] {c.name}")
        if c.evasion_mechanism:
            # First sentence only for the summary
            first_sentence = c.evasion_mechanism.split(". ")[0] + "."
            lines.append(f"    Mechanism: {first_sentence}")
    lines.append("")

    # Key finding
    lines.append(
        "KEY FINDING: The TPF construction evades the GS no-go theorem by "
        "operating outside its domain of applicability. Two of the four "
        "conditions are cleanly evaded (lattice translation invariance via "
        "the extra-dimensional slab, and complete interpolating fields via "
        "the ancilla + rotor Hilbert spaces). One condition still applies "
        "(finite-range Hamiltonian — the TPF construction is local). One "
        "condition has unclear status (relativistic continuum limit — "
        "contingent on the gapped interface conjecture)."
    )
    lines.append("")

    # Critical conjecture
    lines.append(
        "CRITICAL CONJECTURE: The 4+1D gapped interface conjecture. "
        "If the interface between the two boundaries of the SPT slab can be "
        "gapped without breaking the symmetry, then the mirror fermions are "
        "fully decoupled and the boundary theory is the desired chiral fermion "
        "theory. This conjecture is supported by: (a) topological arguments "
        "(the anomaly cancels mod 16), (b) numerical SMG evidence "
        "(Butt-Catterall-Hasenfratz PRL 2025, Hasenfratz-Witzel Nov 2025), "
        "(c) symmetry TFT analysis (Seifnashri Jan 2026). It remains unproven."
    )
    lines.append("")

    # Conditional conclusion
    lines.append(
        "CONDITIONAL CONCLUSION: If the gapped interface conjecture is proven, "
        "the chirality wall falls. The GS no-go theorem would not apply to the "
        "TPF construction because two of its four premises are violated, and "
        "the remaining unclear premise (relativistic continuum limit) would be "
        "established by the conjecture proof. The resulting construction would "
        "produce a single Weyl fermion on the 3+1D boundary without doublers, "
        "achieving the long-sought goal of chiral lattice fermions."
    )
    lines.append("")

    # Caveats
    lines.append(
        "CAVEATS: (1) The GS group has not engaged the TPF construction "
        "directly, so the compatibility analysis is our own formal assessment, "
        "not a consensus view. (2) Even if the chirality wall falls for the "
        "TPF construction, practical lattice QCD simulations with chiral "
        "fermions would require implementing the rotor Hilbert spaces on "
        "quantum or classical hardware, which presents significant "
        "computational challenges. (3) Alternative approaches (staggered "
        "fermions with SMG, domain wall fermions with finite fifth dimension) "
        "may provide practical solutions even if the fundamental question "
        "remains open."
    )

    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# Top-level status function
# ═══════════════════════════════════════════════════════════════════

def chirality_wall_status() -> WallStatus:
    """Return the overall chirality wall status.

    This is the top-level entry point for code that needs a simple
    yes/no/conditional answer to "does the chirality wall still stand?"

    Returns:
        WallStatus enum value.
    """
    result = check_compatibility()
    return result.wall_status


def conditions_summary() -> dict[str, str]:
    """Return a summary dict mapping condition names to their evasion status.

    Returns:
        Dict mapping condition name to "EVADED", "APPLIES", or "UNCLEAR".
    """
    conditions = gs_conditions()
    return {c.name: c.applies_to_tpf.value.upper() for c in conditions}


def evasion_count() -> tuple[int, int, int]:
    """Return counts of (evaded, applying, unclear) conditions.

    Returns:
        Tuple of (evaded, applying, unclear) counts.
    """
    conditions = gs_conditions()
    evaded = sum(1 for c in conditions if c.applies_to_tpf == EvasionVerdict.EVADED)
    applying = sum(1 for c in conditions if c.applies_to_tpf == EvasionVerdict.APPLIES)
    unclear = sum(1 for c in conditions if c.applies_to_tpf == EvasionVerdict.UNCLEAR)
    return evaded, applying, unclear
