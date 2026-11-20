# Exhaustive abstract/caption numeric acceptance remains open

The current 81-case scoped suite passed in 0.08s. This is positive current execution evidence. The manuscript's universal wording requires a complete value-to-computation/reference/assertion mapping. The following list describes gaps in that explicit mapping in the inspected tests/test_gravitational_waves.py assertions; it does not assert that the displayed values are false, or that no other validation exists elsewhere.

| Current output | Existing scoped evidence | Remaining explicit acceptance evidence |
|---|---|---|
| tau=3e-15 in abstract and caption | Tests consume GW_PARAMS cap; held Abbott body p7 section4.1 Eq1 states -3e-15/+7e-16 | Bind exact current manuscript cap to the actual source Eq1 and conservative max-of-absolute-endpoints operation; reading the same constant twice is not external reference validation |
| adopted [0.1,10] | Endpoints exercised, equal to GRAV prior; actual provenance marks adopted | Assert the manuscript's exact endpoints equal the adopted parameter records and distinguish adopted provenance from physical derivation |
| admitted [(1-tau)^2,(1+tau)^2] and width4tau | Rational preimage/ULP controls and Lean source biconditional/width theorem | Bind the quoted real interval and exact literal width1.2e-14 to exact decimal/rational tau3e-15; preserve rounded binary endpoints versus exact real width distinction |
| admitted width1.2e-14 versus adopted width9.9 | Width/ratio tests operate on binary constants and ULP budgets | Explicit assertion of exact declared decimal arithmetic and displayed literals; width9.9 is natural upper-lower, not an independently measured quantity |
| more than14 orders and anchorchi=1 | >1e14 tests; anchor/unity and strict nesting tests | Complete source-to-current-abstract/caption mapping, including anchor versus whole compatible set and strict inequality |
| caption deviation[-0.68,+2.16] and ~1e14 endpoint factors | sqrt endpoint comparisons and both factors>1e14 | Explicit two-decimal display checks from independent high-precision values -0.683772233983... and2.162277660168...; lower display differs by0.552% as a bare literal, correctly rounds to2 decimal places, and must not be called <0.5% literal agreement |
| caption cap drawn at0, unresolved width, gold star1 | Formula/grid tests; prior image review | Bind actual current plot inputs/labels/render to numeric reference. Scoped81 tests do not read the PNG or prove its labels/source equation pointer; independent figure review/repair owns this |

Do not discharge the original exhaustive acceptance requirement by deleting or narrowing the manuscript claim. Supply and independently accept the actual complete mapping and controls. Physical susceptibility normalization, derived range, microscopic mode/matter and transport/frequency matching remain separate original BUILD obligations.
