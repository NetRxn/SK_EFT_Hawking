# R6 live binding pilot

Measured at `7fadbe2b` using only the current `claims_review.json` for each bundle. Of 21 draft directories, 20 have a current review file. Excluding tombstones, 509 sentence rows have at least one `chain_proposed.links` entry of kind theorem. Forty-four contain a TeX reference of some kind. Eight contain a literal equation, align or bracketed display. These are discovery counts, not a complete inventory of live attributions. Exact whitespace-folded quote and display occurrence counts below are against the corresponding top-level TeX. Declaration types come from the existing `validate_helpers.load_lean_deps` reader.

| Recorded claim | Whole quote / display hits | Pilot disposition |
| --- | --- | --- |
| D11 `33af3a4f`, plaquette phase sum | 0 / 1 | Refresh attribution against live text. Four links include definitions. The displayed equality has one apparent theorem target, but position alone cannot select it. |
| D11 `d28d5e66_a`, Voigt–Reuss gap | 0 / 1 | Refresh quote before binding. Type exposes equality, two strict positivity premises and the fraction range. |
| D12 `5dd84a9e`, Poisson floor | 1 / 1 | Live positive control. The printed ≥ and Lean ≤ use opposite operand order. Match direction after binding operands. Count-rule admissibility remains a premise to trace. |
| D12 `525de555`, folklore exponent split | 1 / 1 | Escalate to SC. Display states an equality of exponents. The linked theorem's elaborated equality is between exponentials, one a product. Require an explicit checked bridge rather than accept because both have equality at the root. |
| D12 `bae3e554`, Johnson NEP | 1 / 1 | Live equality control. The type carries `1 + loopGain ≠ 0`. Claim audit must trace that premise in surrounding text. |
| I1 `4d1127c9`, Koszul identity | 0 / 0 | Stale record for this exact locator. Do not score a result without re-anchoring. |
| I2 `075e1bd7`, jackknife variance | 1 / 1 | Live implication and non-negativity control. The lower-bound premise and conclusion both appear in the elaborated type. |
| I2 `e0304f62`, fusion rules | 1 / 1 | Route to an actual declaration. The link names a module and supplies no unique elaborated theorem statement. |

Historical D3 round 1 demonstrates why `link_state: resolved` and `completeness: full` cannot substitute for correspondence. Its quote asserts the full interval while linking the endpoint theorem. The live D3 apex list is useful for discovery, but its claim string only identifies the endpoint result and a section, so it cannot bind a particular display.

The current records can seed live positive and adversarial controls without a parallel registry. Before gating, choose a stable location in the existing backing record for an explicit proposition-to-declaration binding and validate it against the current source. The discovery counts do not establish complete display coverage. Independent review is pending.
