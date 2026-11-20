#pragma once

// Keep the four original factors and their orientations. The closed path
// traverses the rightmost factor first in the end-to-start Wilson convention.
inline Mat diagonal_plaquette(const Mat& a, const Mat& b, const Mat& c, const Mat& d) {
#ifdef L1_CLOSED_ORDER
    return mul(mul(d, c), mul(b, a));
#else
    return mul(mul(a, b), mul(c, d));
#endif
}
