"""Dense exact-polynomial audit of the condensation and adjugate identities."""
from itertools import combinations
from math import factorial, prod


def determinant(block):
    a = [r.copy() for r in block]
    if not a:
        return 1
    previous = sign = 1
    for c in range(len(a) - 1):
        if not a[c][c]:
            p = next((r for r in range(c + 1, len(a)) if a[r][c]), None)
            if p is None:
                return 0
            a[c], a[p] = a[p], a[c]
            sign = -sign
        for i in range(c + 1, len(a)):
            for j in range(c + 1, len(a)):
                q, rem = divmod(a[i][j] * a[c][c] - a[i][c] * a[c][j], previous)
                assert not rem
                a[i][j] = q
        previous = a[c][c]
    return sign * a[-1][-1]


def canonical(values):
    result = list(values)
    while result and result[-1] == 0:
        result.pop()
    return result


def combine(a, b, scale=1):
    c = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] += x
    for i, x in enumerate(b):
        c[i] += scale * x
    return canonical(c)


def multiply(a, b):
    out = [0] * (len(a) + len(b))
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return canonical(out)


def interpolate(values):
    # Forward finite differences in the falling-factorial basis. Values were
    # sampled at exact integers 0,...,degree.
    result, basis = [], [1]
    column = values.copy()
    for k in range(len(values)):
        q, rem = divmod(column[0], factorial(k))
        assert not rem
        result = combine(result, basis, q)
        basis = multiply(basis, [-k, 1])
        column = [b - a for a, b in zip(column, column[1:])]
    return result


def monic_divmod(poly, divisor):
    assert divisor[-1] == 1
    rem = poly.copy()
    quotient = [0] * max(0, len(poly) - len(divisor) + 1)
    while len(rem) >= len(divisor):
        degree = len(rem) - len(divisor)
        quotient[degree] = rem[-1]
        rem = combine(rem, [0] * degree + divisor, -rem[-1])
    return canonical(quotient), rem


def fixture(n, family):
    if family == 'witness':
        c = [1] * (n - 1)
        d = [-10 * (r + 1) for r in range(n)]
    elif family == 'uniform':
        c = [2] * (n - 1)
        d = [-6] * n
    else:
        c = [2 + 3 * (r + 1) % 5 for r in range(n - 1)]
        d = [-(1 + (c[r - 1] if r else 0) + (c[r] if r + 1 < n else 0)
               + (17 * r + 5) % 11) for r in range(n)]
    j = [[0] * n for _ in range(n)]
    for i, x in enumerate(d):
        j[i][i] = x
    for i, x in enumerate(c):
        j[i][i + 1] = j[i + 1][i] = x
    return c, j


def check(n, family):
    c, matrix = fixture(n, family)
    def minor(rows, cols):
        values = [determinant([[s * (i == j) - matrix[i][j] for j in cols] for i in rows])
                  for s in range(len(rows) + 1)]
        return interpolate(values)
    # Intervals are half-open internally, vertex numbers are zero-based.
    blocks = {(i, j): minor(range(i, j), range(i, j))
              for i in range(n + 1) for j in range(i, n + 1)}
    adj = {}
    for v in range(n):
        for leak in range(n):
            cofactor = minor([i for i in range(n) if i != leak],
                             [j for j in range(n) if j != v])
            adj[v, leak] = multiply([(-1) ** (v + leak)], cofactor)
    d = blocks[0, n]
    condensation = divisibility = zero_quotients = 0
    for j, k in combinations(range(n), 2):
        w, u, b = blocks[j + 1, n], blocks[k + 1, n], blocks[j + 1, k]
        h, e, gain = blocks[0, k], blocks[0, j], prod(c[j:k]) ** 2
        assert multiply(d, b) == combine(multiply(w, h), multiply(u, e), -gain)
        condensation += 1
    for v in range(n):
        for leak in range(n):
            diff = combine(multiply([prod(c[:v])], adj[v, leak]),
                           multiply(blocks[0, v], adj[0, leak]), -1)
            quotient, rem = monic_divmod(diff, d)
            assert not rem, (n, family, v, leak, rem)
            expected = (multiply([-prod(c[:leak])], blocks[leak + 1, v])
                        if leak < v else [])
            assert quotient == expected, (n, family, v, leak)
            divisibility += 1
            zero_quotients += (quotient == [])
    if n == 3 and family == 'uniform':
        value = sum(x * (-6) ** k for k, x in enumerate(adj[0, 1]))
        assert value == 0
        print('At n=3, uniform J, lambda=-6, ell=2: adj(1,ell)=',
              adj[0, 1], '(ascending coefficients); denominator at lambda =', value)
    return condensation, divisibility, zero_quotients


if __name__ == '__main__':
    counts = [0, 0, 0]
    for n in range(2, 13):
        for family in ['witness', 'uniform', 'asymmetric']:
            counts = [a + b for a, b in zip(counts, check(n, family))]
    print('n=2..12, 3 integer families: DB identities, D divisibility, zero quotients',
          counts)
