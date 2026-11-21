"""Changed-factorization one-word algebra control; never the22-word sum."""
from time import perf_counter
STARTED = perf_counter()
from fractions import Fraction as F
from itertools import product
import resource
import both_unused_trace_fourth_control as K
import nearest_trace as N


def main():
    tensors, kernel_guard = K.main()
    kernel_products = kernel_guard.products
    _, _, _, ns = N.machinery()
    from l1_normalization_opposed_fourth import curv_moment
    # Derive the physical pair-contraction coefficient from the actual
    # integrated tensor, not from a proposed action-word numerical answer.
    sample_mask = 60 << 16
    tensor_coefficient = tensors[0, 0, 1, 1][sample_mask]
    assert tensor_coefficient.is_ground and tensor_coefficient.const().y == 0
    beta = F(int(tensor_coefficient.const().x), N.Q[60] * 96 * 8 ** 4)
    assert beta == F(1, 32)
    pairings = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))
    integer_sum = calls = 0
    for first, second in product(pairings, repeat=2):
        for i, j, k, l in product(range(4), repeat=4):
            a, b = [0] * 4, [0] * 4
            for value, block in zip((i, j), first):
                for position in block:
                    a[position] = value
            for value, block in zip((k, l), second):
                for position in block:
                    b[position] = value
            integer_sum += curv_moment(tuple(sorted(zip(a, b))))
            calls += 1
    curvature = F(integer_sum, 2025)
    guard = N.Guard(product_offset=kernel_products)
    original_wedge = ns['wedge']
    ns['wedge'] = lambda a, b: guard.join(a, b, original_wedge, 'factory')
    try:
        local = ns['square']((1, 0, 1, 1, 1))
    finally:
        ns['wedge'] = original_wedge
    coefficient = local[255 << 8]
    assert coefficient.is_ground and coefficient.const().y == 0
    # Two private-curvature factor cancels the action-square2!; frame-pair
    # averages contribute8², four raw coframes contribute4^4.
    private = F(int(coefficient.const().x), 8 ** 2 * 4 ** 4)
    # Reuse the identical outgoing-link tensor under even block relabeling.
    # Qcenter² top108 and the repeated commutator action's4! are explicit.
    remote = curvature * beta ** 2 * F(108, 24)
    result = private * remote
    assert calls == 2304
    assert kernel_products + guard.products <= 3000000
    print('CHANGED_FACTORIZATION_ONE_WORD_CONTROL', 'quartet_beta', str(beta),
          'curvature_scalar_calls', calls, 'curvature_integer_sum', integer_sum,
          'curvature_contraction', str(curvature), 'local_square_raw', int(coefficient.const().x),
          'private_pair_including_2_factorial', str(private),
          'remote_including_4_factorial', str(remote), 'one_word_raw_g2_6', str(result),
          'combined_exterior_candidate_products', kernel_products + guard.products,
          'kernel_peak_rows', kernel_guard.peak_rows, 'local_peak_rows', guard.peak_rows,
          'maxrss_kib', resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
          'seconds', perf_counter() - STARTED, flush=True)
    if perf_counter() - STARTED >= 60:
        raise TimeoutError('whole-control60-second cap')
    print('Only the(2,4)pilot word; no22-word sum or complete diagonal result.', flush=True)


if __name__ == '__main__':
    main()
