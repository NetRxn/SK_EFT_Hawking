"""Exact block-order, ambiguity, and two-bath minimax arithmetic."""
from fractions import Fraction as Q
from itertools import combinations
from math import prod
import json


def weight(order, attenuation):
    result = [Q(0) for _ in attenuation]
    p = Q(1)
    for bath in reversed(order):
        result[bath] = p * (1 - attenuation[bath])
        p *= attenuation[bath]
    return result


def mixing(attenuation, orders, coefficients):
    rows = [weight(order, attenuation) for order in orders]
    output = [sum(coef * value for coef, value in zip(coefficients, column, strict=True))
              for column in zip(*rows, strict=True)]
    assert sum(coefficients) == 1
    assert sum(output) == 1 - prod(attenuation)
    for size in range(1, len(attenuation)):
        for part in combinations(range(len(attenuation)), size):
            assert sum(output[i] for i in part) <= 1 - prod(attenuation[i] for i in part)
    return output


def main():
    equal = (Q(1, 2),) * 3
    control_left = weight((1, 2, 0), equal)
    control_right = weight((2, 1, 0), equal)
    assert control_left[0] == control_right[0] == Q(1, 2)
    assert control_left[1] - control_right[1] == -Q(1, 8)
    # Every target is I/4 plus its named level projector divided by four.
    memory_metric = sum(abs(left - right) for left, right in
                        zip(control_left, control_right, strict=True)) / 8
    assert memory_metric == Q(1, 32)
    fixed_sum = sum(control_left)
    common_attenuation = prod(equal)
    measured_a = common_attenuation / 3 + (fixed_sum + control_left[0]) / 4
    measured_b_left = common_attenuation / 3 + (fixed_sum + control_left[1]) / 4
    measured_b_right = common_attenuation / 3 + (fixed_sum + control_right[1]) / 4
    assert measured_b_right - measured_b_left == Q(1, 32)

    lo, hi = Q(1, 4), Q(1, 2)
    reading, noise = Q(11, 16), Q(1, 16)
    inferred = (reading - Q(13, 16)) / -Q(1, 2)
    eta = noise / Q(1, 2)
    compatible = (max(lo, inferred - eta), min(hi, inferred + eta))
    midpoint = sum(compatible) / 2
    assert compatible == (Q(1, 4), Q(3, 8))
    assert midpoint == Q(5, 16)
    clipped = max(lo, min(hi, inferred))
    clip_error = max(abs(value - clipped) for value in compatible) / 2
    midpoint_error = max(abs(value - midpoint) for value in compatible) / 2
    assert (clip_error, midpoint_error) == (Q(1, 16), Q(1, 32))
    global_minimax_radius = min(eta, (hi - lo) / 2) / 2
    middle_dose_attenuation = midpoint * 2
    first_dose_attenuation = Q(1, 2) / middle_dose_attenuation
    assert first_dose_attenuation * middle_dose_attenuation == Q(1, 2)

    print(json.dumps({
        "equal_mixed_weights": list(map(str, mixing(equal,
            ((0, 1, 2), (1, 2, 0), (2, 0, 1)), (Q(1, 3),) * 3))),
        "held_out_mixed_weights": list(map(str, mixing((Q(1, 2), Q(1, 3), Q(1, 5)),
            ((0, 2, 1), (1, 0, 2), (2, 1, 0)), (Q(1, 4), Q(1, 3), Q(5, 12))))),
        "one_detector_control": {
            "common_A_readout": str(measured_a),
            "B_readout_increase": str(measured_b_right - measured_b_left),
            "retained_diamond_distance": str(memory_metric),
        },
        "two_bath_minimax": {
            "compatible_weights": list(map(str, compatible)),
            "nominal_projected_weight": str(clipped),
            "compatible_midpoint_weight": str(midpoint),
            "compatible_diamond_diameter": str((compatible[1] - compatible[0]) / 2),
            "nominal_projection_worst_error": str(clip_error),
            "midpoint_worst_error": str(midpoint_error),
            "global_minimax_radius": str(global_minimax_radius),
            "realization_chronological_attenuations": [
                str(first_dose_attenuation), "1/2", str(middle_dose_attenuation)
            ],
        },
    }, indent=2))


if __name__ == "__main__":
    main()
