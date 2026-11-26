"""Exact acceptance checks. Run from global-multiplicity:

    uv run --with sympy==1.14.0 python verification/verify_reconstruction.py

D and W include their monic coefficient, in ascending powers. The solver
receives only these polynomials, the leak position, p, and q. Expected rates
are used after reconstruction for comparison.
"""

import sys
from math import prod
from pathlib import Path

from sympy import CRootOf, Poly, QQ, Rational, Symbol, eye, simplify
from sympy.polys.matrices import DomainMatrix

from verify_preterminal import compartment_matrix, jacobian_det, rates

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from reconstruct_rates import reconstruct_rates
from verify_multiplicity import observations


S = Symbol("s")
SEED_D = (24, 150, 206, 96, 17, 1)
SEED_W = (8, 7, 1)


def check_five_site_pair(d, w, p, q, first, second, determinants, delta4):
    result = reconstruct_rates(5, 4, d, w, p, q)
    assert result.status == "ok", result
    assert len(result.solutions) == 2 and set(result.solutions) == {first, second}

    numerators = []
    for theta, determinant in zip((first, second), determinants):
        assert all(value > 0 for value in theta)
        matrix = compartment_matrix(theta)
        assert tuple(reversed(matrix.charpoly().all_coeffs())) == d
        assert tuple(reversed(matrix[3:, 3:].charpoly().all_coeffs())) == w
        assert theta[0] * theta[1] == p and prod(theta[:4]) == q
        assert determinant != 0 and jacobian_det(theta) == determinant
        pencil = S * eye(5) - matrix
        numerators.append([Poly(pencil.cofactor(0, j), S) for j in range(5)])

    differences = [left - right for left, right in zip(*numerators)]
    assert [i + 1 for i, delta in enumerate(differences) if not delta.is_zero] == [1, 2, 4]
    assert (differences[3] - Poly(delta4, S)).is_zero
    print(f"five sites: p={p}, q={q}, h=({first[-1]}, {second[-1]}), "
          f"Jacobians={determinants}, N4 difference={differences[3].as_expr()}")


def check_four_site_leaks():
    # Each row supplies only the coefficient map and the independently known
    # complete regular fibre. Rows 1-2 have two solutions, rows 3-4 have one.
    fixtures = (
        (1, (8, 35, 32, 10, 1), (2, 1), ("1 1 1 1 2 2 2", "1 1 1 2 1 2 2")),
        (2, (2, 12, 18, 8, 1), (1, 1), ("1 1 1 1 1 1 2", "1 1 1 1 2 1 1")),
        (3, (1, 8, 14, 7, 1), (1, 1), ("1 1 1 1 1 1 1",)),
        (4, (1, 10, 15, 7, 1), (2, 1), ("1 1 1 1 1 1 1",)),
    )
    for ell, d, w, expected in fixtures:
        result = reconstruct_rates(4, ell, d, w, 1, 1)
        assert result.status == "ok", result
        assert len(result.solutions) == len(expected)
        assert set(result.solutions) == {rates(row) for row in expected}
    print("four sites: leak positions 1, 2, 3, 4 give 2, 2, 1, 1 solutions")


def check_exceptions():
    # The all-ones positive vector with a leak at site 1 gives D(-1)=W(-1)=0.
    common = reconstruct_rates(4, 1, (1, 10, 15, 7, 1), (1, 1), 1, 1)
    assert common.status == "noncoprime" and not common.solutions, common
    # With the leak at 2, the all-ones vector has coprime spectra but is singular.
    double = reconstruct_rates(4, 2, (1, 8, 14, 7, 1), (1, 1), 1, 1)
    assert double.status == "no_regular" and not double.solutions, double
    assert double.singular_count == 1, double
    # On the five-site slice, q=7 gives a negative discriminant.
    empty = reconstruct_rates(5, 4, SEED_D, SEED_W, 2, 7)
    assert empty.status == "no_regular" and not empty.solutions, empty
    print("common spectral root, positive singular solution and unattainable data checked")


def check_irrational_solutions():
    q = Rational(25, 4)
    result = reconstruct_rates(5, 4, SEED_D, SEED_W, 2, q)
    assert result.status == "ok" and len(result.solutions) == 2, result
    # The published slice obeys q=k+6-96/(20-k), k=a3*b3*a4*b4.
    # For this q its roots have sum 81/4 and product 101.
    ks = [simplify(t[2] * t[6] * t[3] * t[7]) for t in result.solutions]
    assert simplify(sum(ks) - Rational(81, 4)) == 0
    assert simplify(prod(ks) - 101) == 0
    assert simplify((ks[0] - ks[1]) ** 2 - Rational(97, 16)) == 0
    print("irrational positive inverse branches at q=25/4 checked exactly")


def check_seven_site_counterexample():
    # The original Jacobi matrix has all diagonals 3 and all squared
    # off-diagonals 1. These data specify the two outputs at sites 3 and 7.
    c = [Poly(1, S), Poly(S + 3, S)]
    for _ in range(2, 8):
        c.append(c[1] * c[-1] - c[-2])
    d, w = (poly.all_coeffs()[::-1] for poly in (c[7], c[4]))
    p, q = Rational(55, 377), Rational(1, 377)
    result = reconstruct_rates(7, 1, d, w, p, q)
    assert result.status == "ok" and len(result.solutions) == 2
    t = Symbol("t")
    quintic = Poly(393*t**5 - 11851*t**4 + 142179*t**3 - 848220*t**2
                   + 2516181*t - 2968908, t)
    lo, hi = Rational(301, 50), Rational(603, 100)
    assert quintic.is_irreducible and quintic.count_roots(lo, hi) == 1
    lo, hi = quintic.refine_root(lo, hi, eps=Rational(1, 10**9))
    algebraic_rows = 0
    for theta in result.solutions:
        roots = set().union(*(v.atoms(CRootOf) for v in theta))
        if roots:
            algebraic_rows += 1
            root, = roots
            assert root.poly.all_coeffs() == quintic.all_coeffs() and lo < root < hi
            field = QQ.algebraic_field(root)
            values = []
            for v in theta:
                representative = Poly(v.xreplace({root: t}), t, domain=QQ)
                # Strict positivity of this rate on the entire isolating interval.
                assert representative.count_roots(lo, hi) == 0 and representative.eval(lo) > 0
                values.append(field.new([QQ.convert(a) for a in representative.all_coeffs()]))
        else:
            assert all(v > 0 for v in theta)
            field = QQ
            values = [QQ.convert(v) for v in theta]
        expected = [field.convert(v) for v in (*d[:-1], *w[:-1], p, q)]
        base = observations(values, 1)
        assert base == expected
        # G6/G7 = (s+b6)/a6. The exact values are the same on both branches.
        assert values[5] == field.convert(Rational(1, 3)) and values[11] == field.convert(3)
        # The forward coefficient map is affine in each individual rate.
        # A unit shift gives a column of its exact physical-coordinate Jacobian.
        columns = []
        for j in range(13):
            shifted = values.copy()
            shifted[j] += field.one
            columns.append([field.convert(a-b) for a, b in zip(observations(shifted, 1), base)])
        determinant = DomainMatrix(columns, (13, 13), field).det()
        assert determinant
        if field == QQ:
            assert determinant == QQ(-990, 142129)
    assert algebraic_rows == 1
    print("seven sites: two positive regular solutions give identical outputs at 3, 6, 7; "
          "the second branch has 301/50 < t < 603/100")


if __name__ == "__main__":
    check_five_site_pair(
        SEED_D, SEED_W, 2, 6, rates("1 2 3 1 3 1 2 2 2"),
        rates("16/29 29/8 9/4 4/3 481/232 3/2 8/9 3 16/9"),
        (3456, -4698), 3 * (S - 1) / 2,
    )
    check_five_site_pair(
        (96, 560, 672, 230, 27, 1), (6, 11, 1), 12, 192,
        rates("3 4 4 4 3 2 4 1 2"), rates("44/17 51/11 10/3 24/5 332/187 11/3 3 6/5 2"),
        (-2359296, 3760128), 8 * S,
    )
    check_four_site_leaks()
    check_exceptions()
    check_irrational_solutions()
    check_seven_site_counterexample()
