"""Run: python3 verify_chain.py  (Python 3.8+, standard library).

Two sets of four integer determinants certify full generic rank. The independent finite
survey uses Markov parameters modulo 65537. Its ranks are lower bounds for
generic rank over Q; a sampled rank defect does not prove nonidentifiability.
"""

from itertools import combinations, permutations
from math import prod


def four_coefficients(rates, leak):
    a1, a2, a3, b1, b2, b3, h = rates
    diag = [a1, b1 + a2, b2 + a3, b3]
    diag[leak - 1] += h
    # Leading principal determinants, coefficients in increasing powers of s.
    prev, curr = [], [1]
    for diagonal, ab in zip(diag, [0, a1 * b1, a2 * b2, a3 * b3]):
        nxt = [0] + curr
        for t, v in enumerate(curr):
            nxt[t] += diagonal * v
        for t, v in enumerate(prev):
            nxt[t] -= ab * v
        prev, curr = curr, nxt
    p = a1 * a2
    return curr[-2::-1] + [p, p * diag[-1], p * a3]


def four_values(rates, leak):
    d3, d2, d1, d0, p, n3_zero, n4_zero = four_coefficients(rates, leak)
    values = [(((s + d3) * s + d2) * s + d1) * s + d0 for s in range(4)]
    return values + [p, n3_zero, n4_zero]


def four_determinant(leak, observe):
    rates = list(range(1, 8))
    base = observe(rates, leak)
    columns = []
    for r in range(7):
        point = rates.copy()
        point[r] += 1  # Each observed coefficient is affine in each one rate.
        columns.append([v - b for v, b in zip(observe(point, leak), base)])
    total = 0
    for perm in permutations(range(7)):
        inversions = sum(a > b for a, b in combinations(perm, 2))
        total += (-1) ** inversions * prod(columns[c][row] for row, c in enumerate(perm))
    return total


PRIME = 65537


def markov_rows(n, leak, inlet, rates):
    # Zero-based vertices. Each edge contributes -rate at its source and
    # +rate at its destination. The leak has no destination in the model.
    forward = [(s, s + 1) for s in range(n - 1)]
    backward = [(s + 1, s) for s in range(n - 1)]
    edges = forward + backward + [(leak, None)]
    m = len(edges)
    v = [int(x == inlet) for x in range(n)]
    dv = [[0] * m for _ in range(n)]
    rows = [[] for _ in range(n)]
    for _ in range(2 * n):
        for stream, grad in zip(rows, dv):
            stream.append(grad)
        w, dw = [0] * n, [[0] * m for _ in range(n)]
        for r, ((src, dst), rate) in enumerate(zip(edges, rates)):
            # Differentiate rate * v[src] in w = A v.
            flux = rate * v[src]
            w[src] -= flux
            if dst is not None:
                w[dst] += flux
            for p, deriv in enumerate(dv[src]):
                dflux = rate * deriv + (v[src] if p == r else 0)
                dw[src][p] -= dflux
                if dst is not None:
                    dw[dst][p] += dflux
        v = [x % PRIME for x in w]
        dv = [[x % PRIME for x in row] for row in dw]
    return rows


def rank_mod(rows):
    a = [row.copy() for row in rows]
    rank = 0
    for c in range(len(a[0])):
        pivot = next((p for p in range(rank, len(a)) if a[p][c]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inverse = pow(a[rank][c], -1, PRIME)
        for p in range(rank + 1, len(a)):
            factor = a[p][c] * inverse % PRIME
            if factor:
                for q in range(c, len(a[p])):
                    a[p][q] = (a[p][q] - factor * a[rank][q]) % PRIME
        rank += 1
    return rank


def main():
    dets = [four_determinant(leak, four_coefficients) for leak in range(1, 5)]
    if dets != [-25920, -16560, -8640, -4320]:
        raise ValueError(f"unexpected four-compartment determinants: {dets}")
    print("Integer determinants for leaks 1, 2, 3, 4:", *dets)
    value_dets = [four_determinant(leak, four_values) for leak in range(1, 5)]
    if value_dets != [-311040, -198720, -103680, -51840]:
        raise ValueError(f"unexpected evaluation determinants: {value_dets}")
    print("Determinants for F=(D(0),D(1),D(2),D(3),p,N3(0),N4(0)):", *value_dets)
    seed, full, deficient = 99173, 0, 0
    for n in range(3, 9):
        for leak in range(n):
            rates = []
            for _ in range(2 * n - 1):  # Reproducible Park–Miller sequence.
                seed = 48271 * seed % 2147483647
                rates.append(1 + seed % 200)
            for inlet in range(n):
                rows = markov_rows(n, leak, inlet, rates)
                i = inlet + 1
                for j, k in combinations(range(1, n + 1), 2):
                    rank = rank_mod(rows[j - 1] + rows[k - 1])
                    prediction = j + k - n - 2 <= i <= j + k + 1
                    if (rank == 2 * n - 1) != prediction:
                        raise ValueError((n, i, j, k, leak + 1, rank, prediction))
                    full += int(prediction)
                    deficient += int(not prediction)
    if full + deficient != 3734:
        raise ValueError("incomplete survey")
    print(f"n=3..8: {full + deficient} placements, {full} full rank, "
          f"{deficient} deficient at sampled point, 0 mismatches (mod {PRIME})")


if __name__ == "__main__":
    main()
