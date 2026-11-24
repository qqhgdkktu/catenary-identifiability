#!/usr/bin/env python3
"""Exact rational tangent ranks in §§4–6 for seven endpoint-input placements.

Run with Python 3.8+ and the standard library: python3 referee_exact_tangent.py
Vertices use one-based indices. The input is 1. At J0, diagonal entry t is
-10*t and every edge product beta_t = c_t**2 is 1. The physical matrix
used for gains is J0-I. The shift s -> s+1 in every spectral polynomial
preserves its differential kernel, so spectral rows may be evaluated at J0.
"""

from fractions import Fraction
from functools import lru_cache


def rank(rows):
    """Incremental Gaussian elimination over the rational numbers."""
    pivots = {}
    for original in rows:
        row = list(map(Fraction, original))
        for column in sorted(pivots):
            factor = row[column]
            if factor:
                row = [a - factor * b for a, b in zip(row, pivots[column])]
        column = next((i for i, value in enumerate(row) if value), None)
        if column is not None:
            pivot = row[column]
            pivots[column] = [value / pivot for value in row]
    return len(pivots)


@lru_cache(maxsize=None)
def characteristic(left, right, s):
    """det(sI - J0[left:right]), with both endpoints included."""
    if left > right:
        return 1
    if left == right:
        return s + 10 * right
    return ((s + 10 * right) * characteristic(left, right - 1, s)
            - characteristic(left, right - 2, s))


def differential(n, left, right, s):
    """Coordinate order: J_11,...,J_nn, beta_1,...,beta_(n-1)."""
    row = [0] * (2 * n - 1)
    # A diagonal derivative deletes its vertex. Differentiating in beta_t
    # selects the transposition of t and t+1 and deletes those two vertices.
    for t in range(left, right + 1):
        row[t - 1] = -characteristic(left, t - 1, s) * characteristic(t + 1, right, s)
    for t in range(left, right):
        row[n + t - 1] = -characteristic(left, t - 1, s) * characteristic(t + 2, right, s)
    return row


def edge_product_differential(n, left, right):
    """d(product of beta_left,...,beta_(right-1)) at beta=1."""
    row = [0] * (2 * n - 1)
    for t in range(left, right):
        row[n + t - 1] = 1
    return row


def gain_log_differential(n, v, leak):
    """Compute d(g_v)/g_v at J0-I from the tridiagonal cofactor formula."""
    def logpoly(left, right):
        value = characteristic(left, right, 1)
        return [Fraction(x, value) for x in differential(n, left, right, 1)]

    # Write L_t, R_t for prefix/suffix determinants at s=1 in J0.
    # The gain is L_(v-1) if v <= leak. Otherwise it is the product of
    # beta_leak,...,beta_(v-1), multiplied by L_(leak-1) R_(v+1)/R_(leak+1).
    if v <= leak:
        return logpoly(1, v - 1)
    contributions = zip(edge_product_differential(n, leak, v),
                        logpoly(1, leak - 1), logpoly(v + 1, n), logpoly(leak + 1, n))
    return [product + left + right - denominator
            for product, left, right, denominator in contributions]


def ranks_for_placement(n, j, k):
    columns = 2 * n - 1
    # A monic degree-m polynomial has a variation of degree at most m-1.
    # Its values at 0,...,m-1 therefore determine every differential coefficient.
    spectral_rows = [differential(n, left, n, s)
                     for left in (1, j + 1, k + 1)
                     for s in range(n - left + 1)]
    dim_t = columns - rank(spectral_rows)
    dim_t0 = columns - rank(spectral_rows + [edge_product_differential(n, j, k)])
    gain_ranks = []
    for leak in range(1, n + 1):
        rows = spectral_rows + [gain_log_differential(n, v, leak) for v in (j, k)]
        gain_ranks.append(rank(rows))
    return dim_t, dim_t0, gain_ranks


if __name__ == "__main__":
    # n, j, k, expected dim T, expected dim T0, expected joint rank at each leak
    cases = [(3, 2, 3, 1, 0, 5), (4, 3, 4, 2, 1, 7), (5, 3, 5, 2, 1, 9),
             (6, 2, 4, 0, 0, 11), (7, 4, 6, 2, 1, 13), (7, 4, 7, 3, 2, 12),
             (9, 5, 7, 2, 1, 17)]
    print("n j k | dim T | dim T0 | joint ranks for leak=1,...,n")
    for n, j, k, expected_t, expected_t0, expected_rank in cases:
        result = ranks_for_placement(n, j, k)
        dim_t, dim_t0, joint_ranks = result
        print(f"{n} {j} {k} | {dim_t:5} | {dim_t0:6} |", *joint_ranks)
        if result != (expected_t, expected_t0, [expected_rank] * n):
            raise SystemExit(f"Unexpected rational rank for (n,j,k)={(n, j, k)}")
