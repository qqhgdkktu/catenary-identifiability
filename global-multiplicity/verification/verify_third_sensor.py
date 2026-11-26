"""Exact rank and reconstruction witnesses for adding a third output.

Run with SymPy 1.14. Coefficients use increasing powers of s. The moments
below belong to the nodes -lambda, so the first endpoint moment is -d_n.
"""

import sys
from fractions import Fraction
from math import prod
from pathlib import Path

from sympy import Matrix

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify_multiplicity import add, continuant, divide, inverse_mod, mul


def moment_basis(D, W):
    """Columns correspond to U=1,s,s^2 in H=U/W mod D."""
    n = len(D) - 1
    inverse = inverse_mod(W, D)
    H = []
    moments = []
    for k in range(3):
        _, h = divide([0] * k + inverse, D)
        h += [0] * (n - len(h))
        H.append(h)
        series = []
        for j in range(2 * n):
            value = h[n - 1 - j] if j < n else 0
            value -= sum(D[n - i] * series[j - i] for i in range(1, min(j, n) + 1))
            series.append(value)
        moments.append(series)
    return Matrix(H).T, Matrix(moments).T


def physical_rates(diag, beta, ell):
    """Recover rates from the successive zero-frequency elimination pivots."""
    n = len(diag)
    a, b = [Fraction(0)] * n, [Fraction(0)] * n
    for j in range(ell - 1):
        a[j] = diag[j] - b[j - 1]
        b[j] = beta[j] / a[j]
    for j in range(n - 1, ell - 1, -1):
        b[j - 1] = diag[j] - a[j]
        a[j - 1] = beta[j - 1] / b[j - 1]
    h = diag[ell - 1] - a[ell - 1] - b[ell - 2]
    assert min(*a[:-1], *b[:-1], h) > 0
    return a[:-1], b[:-1], h


def measured_system(D, moments, Qr, q, ell, r):
    """Only the full denominator, spectrum data and measured gains enter here."""
    n = len(D) - 1
    amplitude = Qr[-1]
    P = [Fraction(v, amplitude) for v in Qr]
    m = n - r
    rows = [moments.row(0)]
    rhs = [1]
    for i in range(m):
        rows.append(Matrix([P]) * moments[i : i + m + 1, :])
        rhs.append(0)
    if r == n - 1:
        # G_(n-1)/G_n=(s+d_n)/a_(n-1).  For terminal leak, mass
        # balance at the steady state of a unit input gives h=D(0)/q.
        z = P[0]
        a = Fraction(q, amplitude)
        b = z - (Fraction(D[0], q) if ell == n else 0)
        rows.append(moments.row(2))
        rhs.append(z * z + a * b)
    return Matrix.vstack(*rows), Matrix(rhs)


def five_site_penultimate(D, W, p, q, N4, ell):
    """The adjacent gains also supply beta_3, including a leak at 4 or 5."""
    d5 = Fraction(N4[0], N4[-1])
    d4 = W[1] - d5
    h4 = Fraction(D[0], N4[0]) if ell == 4 else 0
    h5 = Fraction(D[0], q) if ell == 5 else 0
    a3, a4 = Fraction(N4[-1], p), Fraction(q, N4[-1])
    beta3 = a3 * (d4 - a4 - h4)
    beta4 = a4 * (d5 - h5)
    assert beta3 > 0 and beta4 > 0
    R5 = [d5, 1]
    assert W == add(mul([d4, 1], R5), [1], -beta4)
    # L2 is monic degree two and L2 == -D/(beta3 R5) modulo W.
    _, residue = divide(mul(D, inverse_mod(R5, W)), W)
    L2 = add(W, residue, -1 / beta3)
    L3, rem = divide(add(D, mul(L2, R5), beta3), W)
    assert not rem
    H = add(mul([d4, 1], L3), L2, -beta3)
    return H


def check_witness(n):
    diag = [Fraction(8 + 2 * j + (j * j) % 5) for j in range(n)]
    beta = [Fraction(1 + j % 3) for j in range(n - 1)]
    D = continuant(diag, beta)
    W = continuant(diag[3:], beta[3:])
    H = continuant(diag[:-1], beta[:-1])
    Hbasis, moments = moment_basis(D, W)
    _, U = divide(mul(W, H), D)
    assert len(U) == 3
    outcomes = {}
    for r in range(1, n):
        if r == 3:
            continue
        tail = continuant(diag[r:], beta[r:])
        for ell in range(1, n + 1):
            a, b, h = physical_rates(diag, beta, ell)
            assert [
                x + y + h * (j == ell)
                for j, (x, y) in enumerate(zip([*a, 0], [0, *b]), 1)
            ] == diag
            assert [x * y for x, y in zip(a, b)] == beta
            Qr = [prod(a[: r - 1]) * v for v in tail]
            matrix, rhs = measured_system(D, moments, Qr, prod(a), ell, r)
            assert matrix * Matrix(U) == rhs
            rank = matrix.rank()
            if rank == 3:
                coeffs, _ = matrix.gauss_jordan_solve(rhs)
                assert Hbasis * coeffs == Matrix(H)
            elif n == 5 and r == 4:
                assert five_site_penultimate(D, W, prod(a[:2]), prod(a), Qr, ell) == H
            else:
                raise AssertionError(f"Unexpected rank {rank} at {(n, ell, r)}")
            outcomes[ell, r] = rank
    return outcomes


def check_toeplitz():
    n = 7
    diag = [Fraction(3)] * n
    beta = [Fraction(1)] * (n - 1)
    D = continuant(diag, beta)
    W = continuant(diag[3:], beta[3:])
    _, moments = moment_basis(D, W)
    a, _, _ = physical_rates(diag, beta, 4)
    Qr = [prod(a[:-1]) * v for v in (diag[-1], 1)]
    matrix, rhs = measured_system(D, moments, Qr, prod(a), 4, n - 1)
    rank = matrix.rank()
    assert rank == matrix.row_join(rhs).rank()
    assert rank == 2 and matrix.nullspace() == [Matrix([3, 1, 0])]
    print("Toeplitz n=7, r=6: rank 2, kernel generated by s+3")

    # A second leak location besides the ell=1 case in verify_reconstruction.
    # On the affine line U=s^2+t*s+3*t-10 the second branch is cubic.
    from reconstruct_rates import reconstruct_rates

    a, b, h = physical_rates(diag, beta, 2)
    p, q = prod(a[:2]), prod(a)
    assert (p, q) == (Fraction(55, 48), Fraction(1, 48))
    res = reconstruct_rates(n, 2, D, W, p, q)
    assert res.status == "ok" and len(res.solutions) == 2 and res.singular_count == 0
    assert (*a, *b, h) in res.solutions
    for rates in res.solutions:
        assert (rates[n - 2], rates[2 * n - 3]) == (Fraction(1, 3), 3)
    print("Toeplitz n=7, ell=2: two regular solutions also agree at output 6")


if __name__ == "__main__":
    for n in range(4, 12):
        outcomes = check_witness(n)
        covered = sum(rank == 3 for rank in outcomes.values())
        fallback = len(outcomes) - covered
        assert fallback == (5 if n == 5 else 0)
        print(
            f"n={n}: rank-three witnesses {covered}, adjacent-gain reconstructions {fallback}"
        )
    check_toeplitz()
