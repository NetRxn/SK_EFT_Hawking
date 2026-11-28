"""Replay the frozen deterministic multibath and minimax controls."""

import argparse
from fractions import Fraction as Q
import hashlib
from itertools import combinations
import json
import math
import os
from pathlib import Path


for variable in (
    "OPENBLAS_NUM_THREADS",
    "OMP_NUM_THREADS",
    "MKL_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "BLIS_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
):
    os.environ[variable] = "1"

import numpy as np


SEAL_FILE = "AnalyticEvidenceR2.sha256"
SEAL_SHA = "64514fb091fc57c54f402d58261ac86f714da6e07a0cf6bbeff3918c564e5678"
PUBLIC_SOURCE = {
    "lean/SKEFTHawking/FiniteGibbsResetSchedule.lean":
        "51d5ffe86e9715747c5d26afe925a64f61c58a1ee7cff60eb3140019cf8d0649",
    "lean/SKEFTHawking/FiniteGibbsResetScheduleChannelReadout.lean":
        "9616e7516aae4629476f9b1a44de65bf9448013dd649376ef9d835d65d8001d5",
    "lean/SKEFTHawking/FiniteGibbsResetScheduleReachability.lean":
        "e5eea0c17523f4164cd31b638c49f9a34de6f7dcb90579cc48bdebc7903c4a9b",
    "lean/SKEFTHawking/QuantumNetwork/DiamondNormSup.lean":
        "09f55e9eb890c22f8b779cd71fbb535b679a440130b5f0217084fac0f4bc1543",
}
TOL = 1e-10
LABELS = "ABC"
THREE_TARGETS = tuple(
    tuple(Q(1, 2) if level == bath else Q(1, 4) for level in range(3))
    for bath in range(3)
)
EQUAL = (Q(1, 2),) * 3
HELD_OUT = (Q(1, 2), Q(1, 3), Q(1, 5))


def checked_bytes(path, digest):
    data = path.read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if actual != digest:
        raise ValueError(f"SHA-256 mismatch for {path}: {actual} != {digest}")
    return data


def pinned_inputs(repo):
    for path, digest in PUBLIC_SOURCE.items():
        checked_bytes(repo / path, digest)
    local = Path(__file__).resolve().parent
    entries = {}
    for line in checked_bytes(local / SEAL_FILE, SEAL_SHA).decode().splitlines():
        digest, name = line.split()
        entries[name] = digest
    if set(entries) != {"Protocol.md", "Derivation.md", "CheckBounds.py", "Exact.json"}:
        raise ValueError("unexpected file set in analytic evidence seal")
    documents = {name: checked_bytes(local / name, digest) for name, digest in entries.items()}
    return json.loads(documents["Exact.json"]), entries


def small(scope, value):
    value = float(value)
    if not math.isfinite(value) or abs(value) > TOL:
        raise ArithmeticError(f"{scope}: absolute residual {value:.16g} exceeds {TOL}")
    return abs(value)


def exact_match(scope, actual, expected):
    if actual != expected:
        raise ArithmeticError(f"{scope}: {actual!r} != {expected!r}")


def chronological_coefficients(steps, count):
    """Fold forward: attenuate all previous weights, then add this bath."""
    p = Q(1)
    weights = [Q(0)] * count
    for bath, attenuation in steps:
        p *= attenuation
        weights = [weight * attenuation for weight in weights]
        weights[bath] += 1 - attenuation
    return p, tuple(weights)


def order_coefficients(order, attenuations):
    return chronological_coefficients(((bath, attenuations[bath]) for bath in order),
                                      len(attenuations))


def subset_constraints(attenuations, weights):
    constraints = []
    for size in range(len(attenuations) + 1):
        for subset in combinations(range(len(attenuations)), size):
            mass = sum((weights[bath] for bath in subset), Q(0))
            cap = 1 - math.prod(attenuations[bath] for bath in subset)
            if mass > cap or (size == len(attenuations) and mass != cap):
                raise ArithmeticError(f"subset {subset}: weight {mass} violates cap {cap}")
            constraints.append((subset, mass, cap))
    return constraints


def common_cells(attenuations, orders, mixing):
    # An endpoint is represented by exp(-s) as an exact rational. Coincident
    # endpoints from different summation orders therefore share one boundary.
    blocks = []
    for order in orders:
        backward = []
        start = Q(1)
        for bath in reversed(order):
            end = start * attenuations[bath]
            if end < start:
                backward.append((start, end, bath))
            start = end
        blocks.append(backward)
    endpoints = sorted({value for row in blocks for lo, hi, _ in row for value in (lo, hi)},
                       reverse=True)
    cells = []
    for start, end in zip(endpoints, endpoints[1:]):
        fractions = [Q(0)] * len(attenuations)
        for mass, row in zip(mixing, blocks, strict=True):
            bath = next(bath for lo, hi, bath in row if lo >= start and end >= hi)
            fractions[bath] += mass
        cells.append((-math.log(float(start)), -math.log(float(end)), fractions))
    return cells


def interval_mass(left, right):
    return math.exp(-left) * -math.expm1(left - right)


def pieces_mass(pieces):
    return math.fsum(interval_mass(left, right) for left, right in pieces)


def split_window(pieces, window_left, window_right):
    """Map a compressed left/right window back to the original dose pieces."""
    selected, leftovers = [], []
    offset = 0.0
    for original_left, original_right in pieces:
        end = offset + (original_right - original_left)
        left = max(offset, window_left)
        right = min(end, window_right)
        if left < right:
            a = original_left if left == offset else original_left + (left - offset)
            b = original_right if right == end else original_left + (right - offset)
            a, b = max(original_left, a), min(original_right, b)
            if a < b:
                selected.append((a, b))
                if original_left < a:
                    leftovers.append((original_left, a))
                if b < original_right:
                    leftovers.append((b, original_right))
            else:
                leftovers.append((original_left, original_right))
        else:
            leftovers.append((original_left, original_right))
        offset = end
    return selected, leftovers


def cut_fraction(pieces, fraction):
    length = math.fsum(right - left for left, right in pieces)
    # Match the cumulative coordinate used in split_window at its right edge.
    coordinate_length = sum(right - left for left, right in pieces)
    width = float(fraction) * coordinate_length
    target_mass = float(fraction) * pieces_mass(pieces)
    lo, hi = 0.0, coordinate_length - width
    for _ in range(80):
        mid = (lo + hi) / 2
        selected, _ = split_window(pieces, mid, mid + width)
        if pieces_mass(selected) > target_mass:
            lo = mid
        else:
            hi = mid
    left = (lo + hi) / 2
    selected, remaining = split_window(pieces, left, left + width)
    small("window dose", math.fsum(end - start for start, end in selected)
          - float(fraction) * length)
    small("window mass", pieces_mass(selected) - target_mass)
    return selected, remaining


def colour_cell(left, right, fractions):
    unassigned = [(left, right)]
    remaining_fraction = Q(1)
    colours = []
    for bath, fraction in enumerate(fractions):
        if fraction == 0:
            continue
        if fraction == remaining_fraction:
            picked, unassigned = unassigned, []
        else:
            picked, unassigned = cut_fraction(unassigned, fraction / remaining_fraction)
        remaining_fraction -= fraction
        colours.extend((a, b, bath) for a, b in picked)
        small("cell label dose", math.fsum(b - a for a, b in picked) - float(fraction) * (right - left))
        small("cell label mass", pieces_mass(picked) - float(fraction) * interval_mass(left, right))
    exact_match("unassigned cell pieces", unassigned, [])
    exact_match("unassigned cell fraction", remaining_fraction, Q(0))
    colours.sort()
    if len(colours) > 2 * len(fractions) - 1:
        raise ArithmeticError("cell exceeds the finite piece bound")
    cursor = left
    for start, stop, _ in colours:
        small("cell partition boundary", start - cursor)
        if stop <= start:
            raise ArithmeticError("nonpositive coloured interval")
        cursor = stop
    small("cell partition end", cursor - right)
    return colours


def target_matrix(rows, weights):
    return np.diag([sum(float(weight) * float(row[level])
                        for row, weight in zip(rows, weights, strict=True))
                    for level in range(len(rows[0]))])


def spectator_marginal(joint, system_dimension):
    spectator = joint.shape[0] // system_dimension
    return np.trace(joint.reshape(system_dimension, spectator, system_dimension, spectator),
                    axis1=0, axis2=2)


def trace_norm(matrix):
    return float(np.linalg.svd(matrix, compute_uv=False).sum())


def apply_schedule(joint, steps, targets):
    dimension = len(targets[0])
    state = joint.copy()
    for bath, attenuation in steps:
        marginal = spectator_marginal(state, dimension)
        state = attenuation * state + (1 - attenuation) * np.kron(targets[bath], marginal)
    return state


def pure_density(state):
    return np.outer(state, state.conj())


def prepared_inputs():
    plus = np.ones(2) / math.sqrt(2)
    product_input = np.kron(np.eye(3) / 3, pure_density(plus))
    bell = np.zeros(6)
    bell[[0, 3]] = 1 / math.sqrt(2)
    unequal = np.zeros(6)
    unequal[[1, 4]] = (math.sqrt(2 / 3), math.sqrt(1 / 3))
    trace_zero = np.zeros((6, 6), dtype=complex)
    trace_zero[0, 0], trace_zero[3, 3] = 1 + 0.25j, -1 - 0.25j
    trace_zero[0, 1], trace_zero[5, 2] = 0.3 + 0.4j, -0.2 + 0.7j
    small("complex input trace", abs(np.trace(trace_zero)))
    marginal = spectator_marginal(trace_zero, 3)
    if trace_norm(marginal) <= TOL:
        raise ArithmeticError("trace-zero input has a vanishing spectator marginal")
    return {
        "mixed_system_product_spectator": product_input,
        "bell_like": pure_density(bell),
        "nonmaximally_entangled": pure_density(unequal),
        "trace_zero_complex": trace_zero,
    }


def closed_action(joint, p, accumulated_target):
    return p * joint + np.kron(accumulated_target,
                               spectator_marginal(joint, len(accumulated_target)))


def occupation(joint, system_dimension, level):
    spectator = joint.shape[0] // system_dimension
    start = level * spectator
    value = np.trace(joint[start:start + spectator, start:start + spectator])
    small("occupation imaginary part", value.imag)
    return float(value.real)


def two_detectors(joint, p, expected):
    a, b = (occupation(joint, 3, level) for level in (0, 1))
    total = 1 - p
    w_a = 4 * (a - p / 3) - total
    w_b = 4 * (b - p / 3) - total
    fitted = (w_a, w_b, total - w_a - w_b)
    gap = small("two detector recovered weights",
                max(abs(value - float(weight))
                    for value, weight in zip(fitted, expected, strict=True)))
    return {"level_A": a, "level_B": b, "recovered_weights": fitted, "residual": gap}


def interior_case(attenuations, orders, mixing, expected_strings, inputs):
    count = len(attenuations)
    exact_match("mixture sum", sum(mixing), Q(1))
    block_weights = [order_coefficients(order, attenuations)[1] for order in orders]
    weights = tuple(sum((factor * row[bath]
                         for factor, row in zip(mixing, block_weights, strict=True)), Q(0))
                    for bath in range(count))
    exact_match("independently accumulated mixed weights", weights, tuple(map(Q, expected_strings)))
    p = math.prod(attenuations)
    exact_match("exact total attenuation", sum(weights) + p, Q(1))
    constraints = subset_constraints(attenuations, weights)

    cells = common_cells(attenuations, orders, mixing)
    max_cells = count * (count - 1) + 1
    if len(cells) > max_cells:
        raise ArithmeticError("too many common-refinement cells")
    pieces = [piece for lo, hi, fractions in cells for piece in colour_cell(lo, hi, fractions)]
    max_slices = max_cells * (2 * count - 1)
    if len(pieces) > max_slices:
        raise ArithmeticError("too many chronological slices")
    chronological = [(bath, right - left) for left, right, bath in reversed(pieces)]
    steps = [(bath, math.exp(-dose)) for bath, dose in chronological]
    dose_residuals = []
    mass_residuals = []
    actual_masses = []
    for bath in range(count):
        length = math.fsum(dose for label, dose in chronological if label == bath)
        dose_residuals.append(small("schedule bath dose", length + math.log(float(attenuations[bath]))))
        mass = pieces_mass((left, right) for left, right, label in pieces if label == bath)
        actual_masses.append(mass)
        mass_residuals.append(small("schedule bath mass", mass - float(weights[bath])))
    actual_p = math.prod(a for _, a in steps)
    attenuation_residual = small("schedule total attenuation", actual_p - float(p))
    small("schedule total weight", math.fsum(actual_masses) + actual_p - 1)
    for subset, _, cap in constraints:
        small("constructed subset mass exceeds cap",
              max(0.0, math.fsum(actual_masses[i] for i in subset) - float(cap)))

    targets = tuple(target_matrix((row,), (1,)) for row in THREE_TARGETS)
    accumulated = target_matrix(THREE_TARGETS, weights)
    errors = {}
    for name, joint in inputs.items():
        actual = apply_schedule(joint, steps, targets)
        expected = closed_action(joint, float(p), accumulated)
        errors[name] = {
            "closed_action_trace_norm_residual": small(name, trace_norm(actual - expected)),
            "retained_spectator_trace_norm_residual": small(
                name, trace_norm(spectator_marginal(actual, 3) - spectator_marginal(joint, 3))
            ),
            "input_trace_abs": float(abs(np.trace(joint))),
            "output_trace_abs": float(abs(np.trace(actual))),
        }
        small(f"{name} trace preservation", abs(np.trace(actual) - np.trace(joint)))
    calibration = apply_schedule(inputs["mixed_system_product_spectator"], steps, targets)
    return {
        "block_orders": ["".join(LABELS[i] for i in order) for order in orders],
        "mixture": list(map(str, mixing)),
        "exact_order_weights": [list(map(str, row)) for row in block_weights],
        "exact_mixed_weights": list(map(str, weights)),
        "exact_total_attenuation": str(p),
        "subset_constraints": [{"subset": "".join(LABELS[i] for i in subset),
                                "weight": str(mass), "upper": str(cap)}
                               for subset, mass, cap in constraints],
        "common_cell_count": len(cells),
        "maximum_slice_count": max_slices,
        "chronological_slices": [{"bath": LABELS[bath], "dose": dose, "attenuation": a}
                                 for (bath, dose), (_, a) in zip(chronological, steps, strict=True)],
        "dose_residuals": dose_residuals,
        "weight_residuals": mass_residuals,
        "total_attenuation_residual": attenuation_residual,
        "input_checks": errors,
        "two_readout_coefficient_fit": two_detectors(calibration, float(p), weights),
    }


def ordering_control(frozen, inputs):
    orders = ((1, 2, 0), (2, 1, 0))
    (p, first), (p2, second) = (order_coefficients(order, EQUAL) for order in orders)
    exact_match("block control attenuation", p, p2)
    steps = [[(bath, float(EQUAL[bath])) for bath in order] for order in orders]
    targets = tuple(target_matrix((row,), (1,)) for row in THREE_TARGETS)
    # Accumulate the signed diagonal independently of the floating-point channels.
    delta = tuple(sum((right - left) * row[level] for left, right, row
                      in zip(first, second, THREE_TARGETS, strict=True)) for level in range(3))
    exact_distance = sum(map(abs, delta)) / 2
    exact_a = p / 3 + (sum(first) + first[0]) / 4
    exact_match("exact common A weight", first[0], second[0])
    exact_match("exact A detector", exact_a, Q(frozen["common_A_readout"]))
    exact_match("exact B detector increase", delta[1], Q(frozen["B_readout_increase"]))
    exact_match("exact retained distance", exact_distance, Q(frozen["retained_diamond_distance"]))
    data = {}
    for name, joint in inputs.items():
        left, right = (apply_schedule(joint, order, targets) for order in steps)
        marginal = spectator_marginal(joint, 3)
        actual_difference = right - left
        expected = np.kron(np.diag(list(map(float, delta))), marginal)
        distance = trace_norm(actual_difference) / 2
        input_norm = trace_norm(joint)
        marginal_norm = trace_norm(marginal)
        bound = float(exact_distance) * input_norm
        small("partial trace norm contraction", max(0.0, marginal_norm - input_norm))
        data[name] = {
            "tensor_difference_residual": small(name, trace_norm(actual_difference - expected)),
            "retained_output_trace_distance": distance,
            "spectator_marginal_trace_norm": marginal_norm,
            "tensor_trace_norm_formula_residual": small(name, distance - float(exact_distance) * marginal_norm),
            "induced_bound_for_input": bound,
            "bound_excess": small(name, max(0.0, distance - bound)),
        }
        if name != "trace_zero_complex":
            data[name]["exact_density_distance_residual"] = small(name, distance - float(exact_distance))
        else:
            data[name]["trace_zero_output_difference_residual"] = small(
                "trace-zero output difference", abs(np.trace(actual_difference))
            )

    calibration = inputs["mixed_system_product_spectator"]
    first_fit, second_fit = (two_detectors(apply_schedule(calibration, order, targets), float(p), w)
                             for order, w in zip(steps, (first, second), strict=True))
    small("common A detector", first_fit["level_A"] - second_fit["level_A"])
    small("A detector exact reference", first_fit["level_A"] - float(exact_a))
    small("B detector increase", second_fit["level_B"] - first_fit["level_B"] - float(delta[1]))
    return {
        "same_dose_chronological_orders": ["BCA", "CBA"],
        "exact_weights": [list(map(str, row)) for row in (first, second)],
        "exact_A_detector": str(exact_a),
        "exact_B_detector_increase": str(delta[1]),
        "exact_density_trace_distance": str(exact_distance),
        "coefficient_fits": [first_fit, second_fit],
        "retained_input_checks": data,
    }


def two_bath_minimax(frozen):
    a, b = (Q(3, 4), Q(1, 4)), (Q(1, 4), Q(3, 4))
    attenuation = Q(1, 2)
    p = attenuation ** 2
    reachable = ((1 - attenuation) * attenuation, 1 - attenuation)
    y0 = p + (1 - p) * a[0]
    slope = b[0] - a[0]
    datum, error = Q(11, 16), Q(1, 16)
    inferred = (datum - y0) / slope
    eta = error / abs(slope)
    compatible = (max(reachable[0], inferred - eta), min(reachable[1], inferred + eta))
    if compatible[1] < compatible[0]:
        raise ArithmeticError("compatible interval is empty")
    clipped = max(reachable[0], min(reachable[1], inferred))
    midpoint = sum(compatible) / 2
    c = sum(abs(x - y) for x, y in zip(a, b, strict=True)) / 2
    clip_errors = tuple(c * abs(endpoint - clipped) for endpoint in compatible)
    midpoint_errors = tuple(c * abs(endpoint - midpoint) for endpoint in compatible)
    diameter = c * (compatible[1] - compatible[0])
    global_radius = c * min(eta, (reachable[1] - reachable[0]) / 2)
    last_a = midpoint / (1 - attenuation)
    first_a = attenuation / last_a
    steps = ((0, first_a), (1, attenuation), (0, last_a))
    exact = {
        "compatible_weights": list(map(str, compatible)),
        "nominal_projected_weight": str(clipped),
        "compatible_midpoint_weight": str(midpoint),
        "compatible_diamond_diameter": str(diameter),
        "nominal_projection_worst_error": str(max(clip_errors)),
        "midpoint_worst_error": str(max(midpoint_errors)),
        "global_minimax_radius": str(global_radius),
        "realization_chronological_attenuations": [str(step) for _, step in steps],
    }
    exact_match("two-bath frozen comparisons", exact, frozen)
    exact_match("minimax compatible half-diameter", max(midpoint_errors), diameter / 2)
    exact_match("A midpoint schedule dose", first_a * last_a, attenuation)
    exact_match("midpoint schedule coefficients",
                chronological_coefficients(steps, 2), (p, (1 - p - midpoint, midpoint)))

    targets = tuple(target_matrix((row,), (1,)) for row in (a, b))
    calibration = np.diag([1.0, 0.0])
    actual = apply_schedule(calibration, [(bath, float(value)) for bath, value in steps], targets)
    expected = closed_action(calibration, float(p), target_matrix((a, b), (1 - p - midpoint, midpoint)))
    return {
        **exact,
        "reachable_weights": list(map(str, reachable)),
        "datum": str(datum),
        "detector_error_allowance": str(error),
        "detector_offset": str(y0),
        "detector_weight_slope": str(slope),
        "raw_inferred_weight": str(inferred),
        "compatibility_weight_radius": str(eta),
        "endpoint_errors_of_projected_nominal": list(map(str, clip_errors)),
        "endpoint_errors_of_compatible_midpoint": list(map(str, midpoint_errors)),
        "midpoint_schedule_order": "ABA",
        "midpoint_schedule_trace_norm_residual": small("midpoint schedule", trace_norm(actual - expected)),
        "midpoint_detector_residual": small(
            "midpoint detector", occupation(actual, 2, 0) - float(y0 + slope * midpoint)
        ),
    }


def replay(repo):
    frozen, documents = pinned_inputs(repo)
    inputs = prepared_inputs()
    equal = interior_case(EQUAL, ((0, 1, 2), (1, 2, 0), (2, 0, 1)), (Q(1, 3),) * 3,
                          frozen["equal_mixed_weights"], inputs)
    held_out = interior_case(HELD_OUT, ((0, 2, 1), (1, 0, 2), (2, 1, 0)),
                             (Q(1, 4), Q(1, 3), Q(5, 12)), frozen["held_out_mixed_weights"], inputs)
    return {
        "analytic_evidence_seal_sha256": SEAL_SHA,
        "analytic_evidence_file_sha256": documents,
        "public_source_sha256": PUBLIC_SOURCE,
        "absolute_floating_point_tolerance": TOL,
        "equal_dose_interior": equal,
        "held_out_interior": held_out,
        "one_detector_ambiguity": ordering_control(frozen["one_detector_control"], inputs),
        "two_bath_minimax": two_bath_minimax(frozen["two_bath_minimax"]),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(replay(args.repo), indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
