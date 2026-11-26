"""Exact rational collision at outputs 3, 6, 7 with input 1 and leak 5.

Run with Python 3. Polynomial lists are in increasing order of degree.
"""

from fractions import Fraction as Q
from math import prod
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify_multiplicity import add, continuant, divide, inverse_mod, jacobian, mul


def from_roots(roots):
    polynomial = [1]
    for root in roots:
        polynomial = mul(polynomial, [-root, 1])
    return polynomial


def physical_rates(full, leading_minor):
    """Strip the last site in det(xI-T) repeatedly, then split rates at leak 5."""
    diagonal, edges = [], []
    current, previous = full, leading_minor
    while len(current) > 1:
        quotient, remainder = divide(current, previous)
        assert len(quotient) == 2 and quotient[1] == 1
        diagonal.insert(0, -quotient[0])
        if len(previous) == 1:
            break
        assert len(remainder) == len(previous) - 1 and remainder[-1] < 0
        edges.insert(0, -remainder[-1])
        current, previous = previous, [v / remainder[-1] for v in remainder]

    a, b = [Q(0)] * 6, [Q(0)] * 6
    for j in range(4):
        a[j] = diagonal[j] - (b[j - 1] if j else 0)
        b[j] = edges[j] / a[j]
    for j in (6, 5):
        b[j - 1] = diagonal[j] - (a[j] if j < 6 else 0)
        a[j - 1] = edges[j - 1] / b[j - 1]
    h = diagonal[4] - a[4] - b[3]
    return a + b + [h]


def laplace(polynomial):
    """det(xI-T) -> det(sI+T) for the same principal block."""
    degree = len(polynomial) - 1
    return [v * (-1) ** (degree - i) for i, v in enumerate(polynomial)]


def verify():
    # F,W,V,M,H below are in the positive spectral variable x.
    W = from_roots([3, 7, 9, 16])
    V = from_roots([4, 10, 17])
    M = from_roots([5, 19])
    F = add(mul(V, W), M, 80)
    _, inverse_remainder = divide(mul([0, 1], inverse_mod(W, F)), F)
    B = inverse_remainder[-1]
    assert len(inverse_remainder) == 7 and B == Q(287, 10137600)
    H0 = [v / B for v in inverse_remainder]

    p, q = Q(95), Q(2674979300, 82101)
    a6, b6 = Q(1504800, 531811), Q(1853, 287)
    expected = (laplace(F), [p * v for v in laplace(W)],
                [q * b6 / a6, q / a6], [q])
    cases = [
        (Q(9000), Q(38362500957359744, 5672745222405219), -1),
        (Q(971185627456000, 106036807641),
         Q(149303720272872436416340353, 21445474271243680437492328), 1),
    ]
    for u, expected_h, determinant_sign in cases:
        H = add(H0, V, -u / 80)
        # Since F=VW+80M, H is the monic remainder for U=x/B+uM.
        _, residue = divide(add(mul(W, H), add([0, 1 / B], M, u), -1), F)
        assert not residue
        theta = physical_rates(F, H)
        a, b, h = theta[:6], theta[6:12], theta[12]
        assert min(theta) > 0 and h == expected_h
        assert (a[-1], b[-1]) == (a6, b6)

        # Independent forward cofactors in the Laplace variable s.
        diagonal = [aa + bb + (h if site == 5 else 0)
                    for site, (aa, bb) in enumerate(zip(a + [0], [0] + b), 1)]
        edges = [aa * bb for aa, bb in zip(a, b)]
        D = continuant(diagonal, edges)
        numerators = []
        for r in (3, 6, 7):
            gain = prod(a[:r - 1])
            numerators.append([gain * c for c in continuant(diagonal[r:], edges[r:])])
        assert (D, *numerators) == expected
        assert continuant(diagonal[:-1], edges[:-1]) == laplace(H)
        assert jacobian(theta, 5) * determinant_sign > 0
    print("Two positive regular models with identical G3, G6 and G7.")
    print(f"p={p}, q={q}, a6={a6}, b6={b6}; Jacobian signs: -, +.")


if __name__ == "__main__":
    verify()
