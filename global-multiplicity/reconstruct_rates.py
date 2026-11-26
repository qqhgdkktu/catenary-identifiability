"""Exact inverse of the two-output coefficient map on the coprime locus.

Requires SymPy 1.14. All input coefficients are rational; output coordinates
can be real algebraic. Polynomials use ascending powers, including the leading 1.
Run with a JSON object on stdin or pass its file path, e.g.
  echo '{"n":5,"ell":4,"D":[24,150,206,96,17,1],"W":[8,7,1],"p":2,"q":6}' | python reconstruct_rates.py
Quote fractions in JSON. Output order is a_1,...,a_(n-1),b_1,...,b_(n-1),h.
"""

from dataclasses import dataclass
from fractions import Fraction
from math import prod
from numbers import Integral, Rational

import sympy as sp


@dataclass(frozen=True)
class Reconstruction:
    status: str
    solutions: tuple
    detail: str
    singular_count: int | None = 0


def _rational(value):
    if isinstance(value, str):
        value = Fraction(value)
    if isinstance(value, (Rational, sp.Rational)) and not isinstance(value, bool):
        return sp.Rational(value)
    raise ValueError("Expected an exact rational coefficient (integer or fraction)")


def _coefficient_line(D, W, ell, p, q, t):
    # P = c_0+c_1*s+c_2*s^2, H = P/W mod D. H is monic of degree n-1.
    s = D.gen
    inv = W.invert(D)
    basis = [(inv * sp.Poly(s**j, s, domain=sp.QQ)).rem(D) for j in range(3)]
    rows = [[b.nth(D.degree() - 1) for b in basis] + [1]]
    if ell <= 2:
        rows.append([0, 0, 1, q * W.nth(0) / p])
    else:
        rows.append([1, 0, -p, 0])
    matrix, pivots = sp.Matrix(rows).rref()
    if 3 in pivots:
        return None, "Inconsistent affine gain or normalization", 0
    if len(pivots) < 2:
        return (
            None,
            "Dependent affine conditions; every positive preimage is singular",
            None,
        )
    free = next(j for j in range(3) if j not in pivots)
    c = [t] * 3
    for i, col in enumerate(pivots):
        c[col] = matrix[i, 3] - matrix[i, free] * t
    H = [sum(b.nth(j) * a for a, b in zip(c, basis)) for j in range(D.degree())]
    return (c, H), "", 0


def _gain_equation(D, W, ell, H, c, p, q, t):
    n = D.degree()
    if ell == 3:
        expr = c[2] - q * W.nth(0) / p
    elif ell == n:
        expr = H[0] - q
    else:
        # H(s)/D(s) = sum_j (-1)^j mu_j/s^(j+1) at infinity.
        d = n - ell
        coefficients = []
        for j in range(2 * d):
            value = H[n - 1 - j] if j < n else 0
            value -= sum(
                D.nth(n - i) * coefficients[j - i] for i in range(1, min(j, n) + 1)
            )
            coefficients.append(sp.expand(value))
        mu = [(-1) ** j * v for j, v in enumerate(coefficients)]
        top = [(H[0] - q) / D.nth(0), *mu[:d]]
        block = [top] + [[mu[i], *mu[i + 1 : i + d + 1]] for i in range(d)]
        matrix = sp.Matrix(block).to_DM()
        expr = matrix.domain.to_sympy(matrix.det())
    return sp.Poly(expr, t, domain=sp.QQ)


class _RealEmbedding:
    """Arithmetic in Q(root), with certified signs in the chosen real embedding."""

    def __init__(self, factor, root, interval):
        self.rational = bool(root.is_Rational)
        self.field = sp.QQ if self.rational else sp.QQ.algebraic_field(root)
        self.value = self.field.convert(root) if self.rational else self.field.unit
        self.factor = factor
        self.left, self.right = interval

    def positive(self, value):
        if self.rational:
            return value > 0
        if not value:
            return False
        # Interval Horner evaluation of the reduced field element. A nonzero
        # representative has smaller degree than the minimal polynomial, so
        # continued bisection must eventually separate its value from zero.
        coeffs = [sp.QQ.to_sympy(c) for c in value.to_list()]
        while True:
            lo = hi = sp.S.Zero
            for c in coeffs:
                endpoints = (
                    lo * self.left,
                    lo * self.right,
                    hi * self.left,
                    hi * self.right,
                )
                lo, hi = min(endpoints) + c, max(endpoints) + c
            if lo > 0 or hi < 0:
                return lo > 0
            mid = (self.left + self.right) / 2
            if self.factor.eval(self.left) * self.factor.eval(mid) < 0:
                self.right = mid
            else:
                self.left = mid


def _recover_candidate(D, H, W, p, q, ell, embedding):
    # Strip the last site repeatedly: L_j = (s+d_j)L_(j-1)-beta_(j-1)L_(j-2).
    n = len(D) - 1
    zero, one = embedding.field.zero, embedding.field.one
    current, previous = D, H
    diag, beta = [], []
    while len(current) > 1:
        d = current[-2] - (previous[-2] if len(previous) > 1 else zero)
        diag.append(d)
        if len(current) == 2:
            break
        rest = [
            d * previous[i] + (previous[i - 1] if i else zero) - current[i]
            for i in range(len(previous) - 1)
        ]
        if not embedding.positive(rest[-1]):
            return None
        beta.append(rest[-1])
        current, previous = previous, [v / rest[-1] for v in rest]
    diag.reverse()
    beta.reverse()

    # Nonleaking balance equations propagate inward from the two endpoints.
    a, b = [zero] * n, [zero] * n  # a[n-1] = b[-1] = 0 are the boundary rates.
    for i in range(ell - 1):
        a[i] = diag[i] - b[i - 1]
        if not embedding.positive(a[i]):
            return None
        b[i] = beta[i] / a[i]
    for i in range(n - 1, ell - 1, -1):
        b[i - 1] = diag[i] - a[i]
        if not embedding.positive(b[i - 1]):
            return None
        a[i - 1] = beta[i - 1] / b[i - 1]
    h = diag[ell - 1] - a[ell - 1] - b[ell - 2]
    if not embedding.positive(h):
        return None

    # Check the observed tail and gains in the field, including cleared poles.
    older, tail = [], [one]
    for i in range(n - 1, 2, -1):
        next_tail = [zero] * (len(tail) + 1)
        for j, v in enumerate(tail):
            next_tail[j] += diag[i] * v
            next_tail[j + 1] += v
        for j, v in enumerate(older):
            next_tail[j] -= beta[i] * v
        older, tail = tail, next_tail
    if tail != W or a[0] * a[1] != p or prod(a[:-1], start=one) != q:
        return None
    return tuple(embedding.field.to_sympy(v) for v in (*a[:-1], *b[:-1], h))


def reconstruct_rates(n, ell, D, W, p, q):
    """Return all positive regular solutions for exact rational coprime data.

    A result has status 'ok', 'no_regular' or 'noncoprime'. singular_count
    counts positive isolated singular roots for a nonzero scalar equation.
    None means the computation encountered a dependent constraint (or the
    unsupported noncoprime locus) and does not count singular solutions.
    """
    if (
        isinstance(n, bool)
        or isinstance(ell, bool)
        or not isinstance(n, Integral)
        or not isinstance(ell, Integral)
        or n < 4
        or not 1 <= ell <= n
    ):
        raise ValueError("Require integer n >= 4 and 1 <= ell <= n")
    s, t = sp.symbols("s t")
    D, W = (tuple(map(_rational, coeffs)) for coeffs in (D, W))
    if len(D) != n + 1 or len(W) != n - 2 or D[-1] != 1 or W[-1] != 1:
        raise ValueError("D,W must be monic of degrees n,n-3 in ascending order")
    p, q = _rational(p), _rational(q)
    den, tail = (
        sp.Poly.from_list(list(reversed(poly)), s, domain=sp.QQ) for poly in (D, W)
    )
    if den.gcd(tail).degree() > 0:
        return Reconstruction(
            "noncoprime",
            (),
            "D and W share a factor; use undivided spectral equations",
            None,
        )
    if (
        min(p, q, D[0], W[0]) <= 0
        or den.gcd(den.diff()).degree() > 0
        or den.count_roots(-sp.oo, 0) != n
    ):
        return Reconstruction(
            "no_regular",
            (),
            "Positive rates require positive gains and simple negative poles",
        )
    line, detail, singular_count = _coefficient_line(den, tail, ell, p, q, t)
    if line is None:
        return Reconstruction("no_regular", (), detail, singular_count)
    c, H = line
    equation = _gain_equation(den, tail, ell, H, c, p, q, t)
    if equation.is_zero:
        return Reconstruction(
            "no_regular",
            (),
            "Identical gain on the affine line; every positive preimage is singular",
            None,
        )

    affine_H = [(v.subs(t, 0), v.diff(t)) for v in H]
    solutions, singular_count = [], 0
    for factor, multiplicity in equation.factor_list()[1]:
        roots = factor.real_roots(radicals=False)
        for root, (interval, _) in zip(roots, factor.intervals(), strict=True):
            embedding = _RealEmbedding(factor, root, interval)
            cast = embedding.field.convert
            values = [
                cast(offset) + cast(slope) * embedding.value
                for offset, slope in affine_H
            ]
            found = _recover_candidate(
                list(map(cast, D)),
                values,
                list(map(cast, W)),
                cast(p),
                cast(q),
                ell,
                embedding,
            )
            if found is not None:
                if multiplicity == 1:
                    solutions.append(found)
                else:
                    singular_count += 1
    status = "ok" if solutions else "no_regular"
    return Reconstruction(
        status,
        tuple(solutions),
        "Exact enumeration of the coprime fiber",
        singular_count,
    )


if __name__ == "__main__":
    import argparse
    import json
    import sys

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "input", nargs="?", type=argparse.FileType("r"), default=sys.stdin
    )
    result = reconstruct_rates(**json.load(parser.parse_args().input))
    print(
        json.dumps(
            {
                "status": result.status,
                "detail": result.detail,
                "singular_count": result.singular_count,
                "solutions": [list(map(str, row)) for row in result.solutions],
            },
            indent=2,
        )
    )
