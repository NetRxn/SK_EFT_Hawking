# Bundle L3 — Change Log

_Initial bookkeeping created 2026-05-01T04:18:23Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-01 — Lift-letter from `paper27_bh_thermodynamics_four_laws` (§1)

- Source title: BCH four laws by regime
- Lift action: Lift-letter
- Insertion point: §1
- Stage-13 redo required: yes
- Notes: Initial lift: paper27 → L3 PRL splash (BCH four-laws regime partition + sign-flip of dT_H/dt; Phase 6a W5; ships first wave with L1)

## 2026-05-06 — Lift-section from `_phase6n_W2a_lean_only` (§3)

- Source title: Glorioso-Liu axiomatic skeleton
- Lift action: Lift-section
- Insertion point: §3
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6n W2a Glorioso-Liu axiomatic skeleton (Glorioso_Liu_local_second_law cross-ref upgrade only; no prose change)

## 2026-08-15 — Full Stage-10 redraft (manuscript replaced, not edited)

- Lift action: Redraft (no new source registered; substrate unchanged)
- Stage-13 redo required: yes
- Sections: the manuscript was re-outlined from the charter rather than
  carried forward. New spine: Introduction / The critical mass / One
  substrate, both branches / The two branches and the criterion / What
  would refute this / Discussion. The former standalone "Four laws by
  regime" section was compressed to a scope paragraph inside the criterion
  section, after a read-through found it advanced the argument by zero
  steps while occupying a fifth of a four-page Letter.
- Substantive changes:
  - `M_c` is now presented via the identity `G_N^emerg · M_c = 1/Lambda_UV`
    (exact, verified symbolically and numerically against
    `src/bh_thermodynamics/regime_classifier.py::M_c_default`), replacing
    the prior "project-original dimensional ansatz, no derivation" framing.
    The residual free choice (the order-unity coefficient) is stated.
  - The cooling branch is re-attributed. Balbinot et al. compute a sonic
    hole at constant sound speed and explicitly defer the Bose--Einstein
    condensate; the prior "BEC-acoustic" framing was a misattribution.
  - Jacobson--Volovik 1998 is moved from the heating contrast case to the
    cooling branch, matching that paper's Eq. (5.7) and its own Discussion.
    The thin-film Jacobson--Koike texture remains the heating contrast.
    One superfluid hosting both branches is now the motivating argument.
  - The second-law slot is described as a recorded hypothesis on a supplied
    entropy-current divergence, not as a derivation; the "without invoking
    pointwise NEC" attribution to Glorioso--Liu is dropped as vacuous.
  - The zeroth- and third-law absence is stated as a present-tense fact.
  - Abstract rewritten to 594 characters for the PRL limit (prior: ~1900).
  - Reall 2024 dropped from the reference list with the third-law detour;
    Sakharov 1968, Adler 1982, Visser 2002 and Finazzi--Liberati--Sindoni
    2012 added.
- Compile: 4 pages, 0 TeX errors, 0 unresolved references, 2679 words plus
  one figure against a 3750 word-equivalent ceiling.
- Findings filed: `papers/AutomatedReviews/2026-08-15-l3-stage10-redraft/L3.md`
  (2 blocker, 5 required, 8 recommended). The two blockers are the
  primary-source misreadings above; both propagate beyond L3.

## 2026-11-04 — Deregister-lean-modules

- Modules deregistered: `EntropicGravityDarkEnergy`
- Stage-13 redo required: no (no content changed — this records a dependency the
  draft already does not have)
- Rationale: The August L3 redraft removed the ancillary Phase 6m Verlinde discussion. The live L3 draft does not rely on this module. The L3 four-laws obligations and separate Phase 6m result remain tracked.

## 2026-11-04 — Clarify the sonic-profile parameters

- Source: Balbinot, Fagnocchi and Fabbri, Phys. Rev. D 71, 064019 (2005).
- Correction: `A_0` is the nozzle throat area and `c^2\kappa` is the
  unperturbed sonic surface gravity in the source convention. The
  leading-order formula and its stated range of applicability are unchanged.
- Scoped verification: independent source review confirmed the parameter
  definitions against the primary text. A forced canonical scratch build
  rendered all four pages without errors, overfull boxes, or unresolved
  references.
- Stage-13 redo required: yes. The tracked PDF refresh and full bundle review
  remain pending.

## 2026-11-04 — Scope acoustic cooling to the source calculation

- Balbinot et al. §V and Eq. (8.4) give the initial cooling slope of the
  constant-sound-speed nozzle for `c κ t ≪ 1`. Their Eqs. (8.5)–(8.6)
  extrapolate the late-time tail, and §VIII leaves the condensate case open.
- The abstract, branch discussion, and figure caption identify the exponential
  as the model profile. Its asymptotic limit is distinct from the extrapolation.
- Stage-13 redo required. The partition sign construction, physical late-time
  dynamics, and any condensate transfer remain open. No gate or finding closure
  recorded.
- Independent source review accepted the final wording. The canonical
  scratch build rendered all four pages with zero errors, overfull boxes,
  unresolved references, or dropped class options. The tracked PDF
  refresh remains pending.

## 2026-11-04 — Refresh the L3 figure and PDF

- The manuscript names the falsifier section in prose. The figure producer
  identifies the blue curve as a representative exponential. Independent
  review confirmed the plotted values are unchanged.
- Regenerated the L3 figure at 3300 × 1800 pixels and rebuilt the tracked
  four-page PDF with the canonical compiler. The fresh compile reported
  zero errors, overfull boxes, unresolved references, and dropped options.
  Both corrections were confirmed in the render.
- The existing annotation overlap and the other figure copies remain
  open for visual review and propagation. Full Stage-13 review and the
  physical construction remain due.

## 2026-11-04 — Separate the blue annotation from the cooling curve

- Independent review confirmed the annotation clears both curves and the
  plotted data are identical. Refreshed the canonical PNG, the L3 PNG and
  the four-page PDF. The canonical compile passed.
- D3 and Paper 27 retain the older right panel. Their figure and caption
  updates require a separate coordinated review. Stage 13 remains due.

## 2026-11-04 — Formalize the two cutoff-length identities

- The bare Sakharov coupling gives `1/(α_ADW Λ_UV)` when multiplied
  by `M_c`. The emergent coupling gives `1/Λ_UV`. The two products
  agree exactly at unit `α_ADW` under the existing positivity assumptions.
- Independent source review accepted all three proofs. The full modified
  Lean file elaborated against local compiled imports using Lean 4.32.0.
  The three axiom queries reported only `propext`, `Classical.choice`,
  and `Quot.sound`.
- The authoritative build, declaration-registry refresh, and canonical
  finding §2.4 closure remain due.

## 2026-11-04 — Derive the local trajectory signs

- The additive profile criterion derives Schwarzschild heating by
  applying the chain rule to a positive mass profile with local mass
  loss. It derives the exact negative slope of the leading-order
  Balbinot nozzle profile in natural units.
- The nozzle branch requires the caller's short-time budget and a
  positive-temperature window. The equality boundary receives neither
  strict sign. The existing partition interface remains available.
- Independent source review accepted the scope and proofs. The modified
  file elaborated against local compiled imports, and all three new
  theorem axiom queries reported only `propext`, `Classical.choice`,
  and `Quot.sound`.
- The authoritative build, declaration refresh, manuscript propagation,
  and reconciliation of the §2.2 verifier remain due.

## 2026-11-04 — Connect the manuscript to the local profile proofs

- The abstract and branch section present the derived local signs,
  including the short-time and positive-temperature conditions.
  The caption keeps the plotted exponential distinct from the
  affine nozzle calculation.
- The cutoff discussion distinguishes the proved emergent identity
  from the physical choice of crossover scale. Source review
  checked both claims against the new declarations.
- The canonical compiler produced four pages with no errors,
  overfull boxes, unresolved references or dropped options.
  Visual inspection checked all four pages.
- The declaration registry, derived counts, theorem backing records,
  and §2.2 and §2.4 closure remain pending authoritative validation.

## 2026-11-04 — Declare the local profile and cutoff proof backing

- The two new apex entries name the exact emergent cutoff identity
  and local profile criterion. Independent source review matched them
  to the rendered claims. The exponential entry describes the
  illustrative model used in the figure.
- The focused apex gate could not measure this checkout. Its
  declaration extractor attempted to fetch the missing Physlib
  dependency and could not resolve the remote host. The registry
  refresh and authoritative validation remain due.

## 2026-11-04 — Prove the fixed-coupling Schwarzschild first law

- The area derivative uses geometric mass `m = G M`. At fixed
  positive `G`, the exact area and surface-gravity formulas give
  `dM = κ dA/(8πG)` along a differentiable positive mass profile.
  A varying-coupling control in the same algebraic family gives
  the additional term `M dG/G`.
- Independent review accepted the scope and algebra. The modified
  ExactSolutions file elaborated against local compiled imports,
  and the three new theorem axiom queries reported only `propext`,
  `Classical.choice` and `Quot.sound`.
- This supplies the Schwarzschild differential first-law component
  of §2.1. The ADW and nozzle laws, physical entropy-current
  construction, authoritative build and publication propagation
  remain open.

### Schwarzschild first-law manuscript propagation

The mechanics paragraph now states the proved fixed-coupling
Schwarzschild law and the varying-coupling control, including
the geometric-mass convention and the differentiability and
positivity assumptions. Independent source review checked the
identities and requested explicit varying-coupling hypotheses,
which are included in the final four-page render. The emergent
profile match, acoustic energy balance, and physical entropy
current remain open.

### Spherical exterior uniqueness under the reduced vacuum equation

The ExactSolutions construction proves constancy of the radial mass
function on the connected exterior. A prescribed asymptotic mass tail
fixes the unique lapse. On a regular chart containing its zero, the
construction gives the Schwarzschild area profile and the half-lapse
slope. Independent review accepted those statements and their domain.
The full modified file elaborated against local compiled imports,
and the three new declarations reported only the standard Lean axioms.
The ADW action derivation of the equation and tail, the geometric
Killing-horizon calculation, and authoritative validation remain open.

### Ingoing chart and horizon nonaffinity

The four-dimensional ingoing chart has a regular radial block at
the lapse zero. Away from the angular coordinate poles, the inverse
raises the null normal to the stationary coordinate generator. The
repository's Koszul formula and actual coordinate partials give
nonaffinity equal to half the lapse slope, hence the Schwarzschild
surface-gravity profile under the previously stated exterior
equation and mass tail. Independent source review checked the chart
domain and geometric interpretation. The full source elaborated
against local compiled imports, with standard axioms reported for
the inverse and final nonaffinity theorems. The ADW exterior
derivation and authoritative validation remain open.

### Ingoing-chart result in the manuscript

The mechanics discussion now propagates the conditional exterior
lapse and the chart calculation of horizon nonaffinity. Independent
prose review checked the equations against ExactSolutions and
requested explicit radial and asymptotic hypotheses, the raised
normal's normalization, and a narrower zeroth-law statement.
The final four-page PDF incorporates those revisions. The physical
ADW matching and acoustic energy balance remain open.

### Angular vacuum gives the exterior lapse equation

The ingoing chart now has a coordinate Ricci calculation using the
repository's Koszul connection and Riemann contraction. The angular
component is `R_theta theta = 1 - F - r F'` at regular chart points,
so angular vacuum gives the reduced radial equation used in the
exterior uniqueness proof. Independent source review checked all
four Ricci terms and the chart hypotheses. The full modified file
elaborated against local compiled imports, and both new result
declarations reported only standard axioms. Full tensor vacuum and
matching the metric and mass normalization to the ADW action
remain open, along with authoritative candidate validation.

### Full Ricci tensor on the stationary spherical chart

The ingoing chart calculation now covers every Ricci component.
With Q = F''/2 + F'/r and W = 1 - F - r F', the radial block
is (F Q, -Q; -Q, 0) and the angular block is W times the unit
sphere metric. Pointwise vacuum requires both scalars to vanish.
If the reduced equation holds on a neighborhood, differentiation
supplies the second condition under the stated radial regularity.
Independent review checked the repository convention and the
Schwarzschild-de Sitter control. Local elaboration passed with
two tactic-style warnings, and all three result declarations
reported only standard axioms. The ADW exterior derivation,
physical mass matching, and authoritative validation remain open.

### Spherical ADM surface charge

ADMFormalism now computes the spherical coordinate-sphere flux
from actual Cartesian derivatives. For the spatial metric
`delta_ij + A(r) n_i n_j`, contraction with the outward unit
normal gives `2 A(R)/R`. The round measure and radial pullback
give finite charge `R A(R)/(2G)`. For `A=F^(-1)-1`, a lapse
tending to one and a prescribed mass tail give the mass limit.
Independent review checked the outward sign, surface measure,
and limit. The full modified file elaborated locally with one
tactic-style warning. The three principal declarations report
only standard axioms. Applying this calculation to an emergent
solution still requires the static spacelike slicing, physical
mass normalization, and ADW exterior matching. Authoritative
validation remains open.

### Static slice for the spherical ADM charge

On a regular exterior patch with positive lapse, the radial
integral of the reciprocal lapse defines the ingoing time shift.
The coordinate partials and finite matrix pullback give the static
radial coefficient (F^{-1}). The polar Jacobian identifies the
Cartesian spatial profile used by the spherical surface-charge
calculation. Independent source review checked the integral
hypotheses, pullbacks, and chart scope. The combined candidate
source elaborated locally against compiled dependencies, and
the three main statements reported only standard Lean axioms.
This identifies the static spatial metric for the supplied
exterior. General ADM coordinate invariance, microscopic ADW
matching, and authoritative validation remain open.
