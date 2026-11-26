"""Check the exceptional-block construction with exact polynomial arithmetic.

Each case has input 1, leak 1 and outputs 3, r, n. The finite checks exercise
the hypotheses used in the all-length proof, including preservation of the
extra numerator's monic polynomial and its spectral norm.
"""

from fractions import Fraction as Q
from math import prod
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify_multiplicity import add, continuant, divide, inverse_mod, mul


def jacobi_block(nodes):
    """Strip the Jacobi matrix of the uniform measure on these nodes."""
    full = [1]
    for x in nodes:
        full = mul(full, [-x, 1])
    # Its endpoint Weyl function is (1/m) sum 1/(x-node) = F'/(mF).
    minor = [Q(j * v, len(nodes)) for j, v in enumerate(full) if j]
    diagonal, edges = [], []
    while len(full) > 1:
        quotient, remainder = divide(full, minor)
        assert len(quotient) == 2 and quotient[1] == 1
        diagonal.insert(0, -quotient[0])
        if len(minor) == 1:
            break
        assert len(remainder) == len(minor) - 1 and remainder[-1] < 0
        edges.insert(0, -remainder[-1])
        full, minor = minor, [v / remainder[-1] for v in remainder]
    return diagonal, edges


def verify_case(n, r):
    # The positive-spectral convention P(x)=det(xI-T) is used throughout.
    c, e = 3, 5
    diagonal = [4] * n
    edges = [Q(1, 64)] * (n - 1)  # squared off-diagonals
    edges[0] = 1
    if r < n - 1:
        diagonal[2:] = [c] * (n - 2)
        for left, right in ((4, r - 1), (r + 1, n - 1)):
            for j in range(left, right + 1):
                degree = int(j > left) + int(j < right)
                diagonal[j - 1] = c + Q(degree, 8)
    else:
        nodes = [c, e, *range(6, n - 1)]
        old_block, old_edges = jacobi_block(nodes)
        assert len(old_block) == n - 5
        diagonal[3:n - 2], edges[3:n - 3] = old_block, old_edges

    def block(left, right):
        return continuant([-u for u in diagonal[left - 1:right]],
                          edges[left - 1:right - 1])

    F, G, H = block(1, n), block(4, n), block(1, n - 1)
    L2, left_minor, extra = block(1, 2), block(1, r - 1), block(r + 1, n)
    assert min(edges) > 0
    assert all((-1) ** j * block(1, j)[0] > 0 for j in range(1, n + 1))
    assert L2 == mul([-c, 1], [-e, 1])
    inverse = inverse_mod(G, F)

    def evaluate(poly, x):
        return sum(a * x ** i for i, a in enumerate(poly))

    def norm_row(poly):
        # sum poly(lambda_i)/(F'(lambda_i) G(lambda_i)) by Lagrange interpolation
        _, remainder = divide(mul(poly, inverse), F)
        return remainder[n - 1] if len(remainder) == n else 0

    K = prod(edges[2:])
    assert norm_row([K * z for z in L2]) == 1
    linear_c, linear_e = [-e, 1], [-c, 1]  # L2/(x-c), L2/(x-e)
    nc, ne = norm_row(linear_c), norm_row(linear_e)
    assert ne != 0  # normalization and leading coefficient are independent
    assert evaluate(left_minor, c) == 0
    assert all(evaluate(F, x) and evaluate(G, x) for x in (c, e))
    if r < n - 1:
        assert evaluate(block(4, r - 1), c) == evaluate(block(r + 1, n - 1), c) == 0
        assert evaluate(H, c) == nc == 0 and evaluate(H, e) != 0
        direction = linear_c
    else:
        assert evaluate(left_minor, e) == 0
        assert all(evaluate(H, x) for x in (c, e)) and nc != 0
        direction = add([v * ne for v in linear_c], linear_e, -nc)
    assert direction and not norm_row(direction)

    signed = mul(extra, direction)
    for j in range(n - r):
        assert norm_row([0] * j + signed) == 0
    assert norm_row(mul(extra, signed)) == 0  # the squared norm is fixed


if __name__ == "__main__":
    cases = [(n, r) for n in range(7, 13) for r in range(5, n)]
    for n, r in cases:
        verify_case(n, r)
    print(f"Verified {len(cases)} exceptional-block cases, 7 <= n <= 12.")
