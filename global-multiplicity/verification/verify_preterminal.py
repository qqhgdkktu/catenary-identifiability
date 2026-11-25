"""Exact certificates for Section 10. Run: uv run --with sympy==1.14.0 verify_preterminal.py"""
from math import prod

from sympy import Matrix, Poly, Rational, Symbol, zeros


def rates(text):
    return tuple(map(Rational, text.split()))


def compartment_matrix(theta):
    n = (len(theta) + 1) // 2
    matrix = zeros(n)
    for j, (a, b) in enumerate(zip(theta[:n - 1], theta[n - 1:-1])):
        matrix[j + 1, j] = a
        matrix[j, j + 1] = b
        matrix[j, j] -= a
        matrix[j + 1, j + 1] -= b
    matrix[n - 2, n - 2] -= theta[-1]
    return matrix


def observations(theta):
    matrix = compartment_matrix(theta)
    d = matrix.charpoly().all_coeffs()[1:][::-1]
    w = matrix[3:, 3:].charpoly().all_coeffs()[1:][::-1]
    return Matrix([*d, *w, theta[0] * theta[1], prod(theta[:matrix.rows - 1])])


def jacobian_det(theta):
    # Each rate affects one matrix column. Both principal determinants and the
    # two path products are affine in each rate separately, so a unit forward
    # difference gives the exact partial derivative at theta.
    base = observations(theta)
    columns = []
    for j in range(len(theta)):
        shifted = list(theta)
        shifted[j] += 1
        columns.append(observations(shifted) - base)
    return Matrix.hstack(*columns).det()


def verify(first, second, dets, same_h, *, d_coeffs, w_coeffs, gains):
    first, second = rates(first), rates(second)
    assert min(*first, *second) > 0
    data = observations(first)
    assert observations(second) == data
    n = (len(first) + 1) // 2
    s = Symbol("s")
    d = Poly.from_list([1, *reversed(data[:n])], s)
    w = Poly.from_list([1, *reversed(data[n:-2])], s)
    assert tuple(d.all_coeffs()) == d_coeffs and tuple(w.all_coeffs()) == w_coeffs
    assert tuple(data[-2:]) == gains
    assert d.gcd(w).is_one
    assert (jacobian_det(first), jacobian_det(second)) == dets
    assert first[-2] != second[-2] and (first[-1] == second[-1]) == same_h
    g = data[-1] / data[0]
    moments = []
    for theta in (first, second):
        # Diagonal moments are invariant under diagonal similarity to T.
        t = -compartment_matrix(theta)
        z, v, r = t[-1, -1], (t*t)[-1, -1], t.inv()[-1, -1]
        assert z == theta[-2] and g == r - 1/z
        assert theta[-1] == (v - z*z)/(g*z*z)
        moments.append((z, r, v))
    (x, rx, vx), (y, ry, vy) = moments
    alpha, gamma = (rx - ry)/(x - y), (vx - vy)/(x - y)
    beta, delta = rx - alpha*x, vx - gamma*x
    assert alpha*x*y == -1
    residual = gamma - delta*(g - beta)
    assert (residual == 0) == same_h
    assert (y-x)*residual == g*x*y*(first[-1] - second[-1])
    print(f"n={n}, g={g}, h=({first[-1]}, {second[-1]}), det={dets}, "
          f"resultant={d.resultant(w)}, criterion residual={residual}")


if __name__ == "__main__":
    verify("1 2 3 1 3 1 2 2 2",
           "16/29 29/8 9/4 4/3 481/232 3/2 8/9 3 16/9",
           (3456, -4698), False, d_coeffs=(1, 17, 96, 206, 150, 24),
           w_coeffs=(1, 7, 8), gains=(2, 6))
    verify("2 1 1 3 4 2 4 2 1 1 2",
           "63/41 82/63 5/6 24/5 3 7306/2583 7/2 6/5 5/4 2 3/4",
           (-27648, 62976), False, d_coeffs=(1, 23, 191, 687, 976, 294, 12),
           w_coeffs=(1, 13, 40, 12), gains=(2, 24))
    verify("3 4 4 4 3 2 4 1 2",
           "44/17 51/11 10/3 24/5 332/187 11/3 3 6/5 2",
           (-2359296, 3760128), True, d_coeffs=(1, 27, 230, 672, 560, 96),
           w_coeffs=(1, 11, 6), gains=(12, 192))
