#!/usr/bin/env python3
"""Independent bidirectional-chain rank checks, Python 3.8+, stdlib only.

Default: exact four-site determinants; all placements for n=3,...,12;
selected threshold and reflected placements for n=16,24.
"""
import argparse
from collections import Counter, defaultdict
from itertools import combinations
from random import Random


def edges(n, leak):
    return ([(r, r + 1) for r in range(n - 1)]
            + [(r + 1, r) for r in range(n - 1)] + [(leak, None)])


def neg_generator(n, edge_list, rates):
    matrix = [[0] * n for _ in range(n)]
    for (source, target), rate in zip(edge_list, rates):
        matrix[source][source] += rate
        if target is not None:
            matrix[target][source] -= rate
    return matrix


def shifted(matrix, frequency):
    return [[v + frequency * (i == j) for j, v in enumerate(row)]
            for i, row in enumerate(matrix)]


def determinant(matrix):
    # Bareiss elimination over the integers with row interchanges.
    a = [row.copy() for row in matrix]
    if not a:
        return 1
    denominator = sign = 1
    for k in range(len(a) - 1):
        if a[k][k] == 0:
            pivot = next((r for r in range(k + 1, len(a)) if a[r][k]), None)
            if pivot is None:
                return 0
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        for r in range(k + 1, len(a)):
            for c in range(k + 1, len(a)):
                v = a[k][k] * a[r][c] - a[r][k] * a[k][c]
                assert v % denominator == 0
                a[r][c] = v // denominator
        denominator = a[k][k]
    return sign * a[-1][-1]


def subdet_value_gradient(matrix, edge_list, rows, cols):
    block = [[matrix[row][col] for col in cols] for row in rows]
    jet = [determinant(block)]
    for source, target in edge_list:
        if source not in cols:
            jet.append(0)
            continue
        # Multilinearity: only this column carries the chosen rate.
        replaced = [one.copy() for one in block]
        for index, row in enumerate(rows):
            replaced[index][cols.index(source)] = (row == source) - (row == target)
        jet.append(determinant(replaced))
    return jet


def cofactor(matrix, edge_list, inlet, output):
    rows = [i for i in range(len(matrix)) if i != inlet]
    cols = [i for i in range(len(matrix)) if i != output]
    sign = (-1) ** (inlet + output)
    return [sign * x for x in subdet_value_gradient(matrix, edge_list, rows, cols)]


def exact_four():
    theta = list(range(1, 8))
    observed = []
    for leak in range(4):
        edge_list = edges(4, leak)
        b = neg_generator(4, edge_list, theta)
        whole = list(range(4))
        values = [subdet_value_gradient(shifted(b, s), edge_list, whole, whole)
                  for s in range(4)]
        # c3 through c0 are sums of principal minors of successive sizes.
        coeffs = []
        for size in range(1, 5):
            jets = [subdet_value_gradient(b, edge_list, ix, ix)
                    for ix in combinations(whole, size)]
            coeffs.append([sum(xs) for xs in zip(*jets)])
        n30 = cofactor(b, edge_list, 0, 2)
        n31 = cofactor(shifted(b, 1), edge_list, 0, 2)
        n40 = cofactor(b, edge_list, 0, 3)
        p = [x - y for x, y in zip(n31, n30)]
        extra = [p, n30, n40]
        det_f = determinant([jet[1:] for jet in values + extra])
        det_c = determinant([jet[1:] for jet in coeffs + extra])
        assert det_f == 12 * det_c
        observed.append((det_f, det_c))
        print('four', leak + 1, 'D(0:3)', [j[0] for j in values],
              'c3..c0', [j[0] for j in coeffs], 'last', [j[0] for j in extra],
              'det F', det_f, 'det Fc', det_c)
    expected = [(-311040, -25920), (-198720, -16560),
                (-103680, -8640), (-51840, -4320)]
    if observed != expected:
        raise ArithmeticError(f'four-site determinant mismatch: {observed}')


def inverse(matrix, prime):
    n = len(matrix)
    a = [[x % prime for x in row] + [int(r == c) for c in range(n)]
         for r, row in enumerate(matrix)]
    for c in range(n):
        r = next((r for r in range(c, n) if a[r][c]), None)
        if r is None:
            return None
        a[r], a[c] = a[c], a[r]
        scale = pow(a[c][c], -1, prime)
        a[c] = [x * scale % prime for x in a[c]]
        for r in range(n):
            if r != c and a[r][c]:
                scale = a[r][c]
                a[r] = [(x - scale * y) % prime for x, y in zip(a[r], a[c])]
    return [row[n:] for row in a]


def frequencies(b, prime):
    n = len(b)
    samples = {}
    s = 1
    while len(samples) < 2 * n:
        r = inverse(shifted(b, s), prime)
        if r is not None:
            samples[s] = r
        s += 1
    return samples


def gradient(resolvent, edge_list, inlet, output, prime):
    # dR = R (dA) R, for R = (s I - A)^(-1).
    row = resolvent[output]
    return [(((row[target] if target is not None else 0) - row[source])
             * resolvent[source][inlet]) % prime
            for source, target in edge_list]


def add_row(basis, row, prime):
    for c in range(len(basis)):
        if not row[c]:
            continue
        if basis[c] is None:
            scale = pow(row[c], -1, prime)
            basis[c] = row[:c] + [scale * x % prime for x in row[c:]]
            return 1
        scale = row[c]
        row = row[:c] + [(x - scale * y) % prime
                         for x, y in zip(row[c:], basis[c][c:])]
    return 0


def output_basis(samples, edge_list, inlet, output, prime):
    basis = [None] * len(edge_list)
    rank = 0
    for r in samples.values():
        rank += add_row(basis, gradient(r, edge_list, inlet, output, prime), prime)
        if rank == len(basis):
            break
    return rank, basis


def joint_rank(left, right, prime):
    if right[0] > left[0]:
        left, right = right, left
    rank = left[0]
    basis = left[1].copy()
    if rank < len(basis):
        for row in right[1]:
            if row is not None:
                rank += add_row(basis, row, prime)
                if rank == len(basis):
                    break
    return rank


def deficiency_bound(n, inlet, j, k):
    # Distance to the nearer output, less units available past the farther one.
    if inlet < j:
        return max(0, j - inlet - (n - 1 - k) - 2)
    if inlet > k:
        return max(0, inlet - k - j - 2)
    return 0


def check_mirror(b, theta, leak, samples, prime):
    n = len(b)
    eref = edges(n, n - 1 - leak)
    reflected = neg_generator(n, eref, theta[-2::-1] + theta[-1:])
    s, r = next(iter(samples.items()))
    rref = inverse(shifted(reflected, s), prime)
    direct = edges(n, leak)
    for inlet in range(n):
        for output in range(n):
            a, v = n - 1 - inlet, n - 1 - output
            assert r[output][inlet] == rref[v][a]
            jac = gradient(rref, eref, a, v, prime)
            assert gradient(r, direct, inlet, output, prime) == jac[-2::-1] + jac[-1:]
    return n * n


def boundary_layouts(n):
    # On threshold, one site on each side, two exterior inlet choices, and mirrors.
    layouts = set()
    for inlet in (0, n // 4):
        for tail in (0, n // 5, n // 3):
            k = n - 1 - tail
            for delta in (-1, 0, 1):
                j = inlet + tail + 2 + delta
                if inlet < j < k:
                    layouts.add((inlet, j, k))
                    layouts.add((n - 1 - inlet, n - 1 - k, n - 1 - j))
    layouts.update([(0, 0, n - 1), (n - 1, 0, n - 1), (n // 2, 0, n - 1)])
    return sorted(layouts)


def survey(n, exhaustive, prime, seed):
    all_layouts = ([(i, j, k) for i in range(n) for j, k in combinations(range(n), 2)]
                   if exhaustive else boundary_layouts(n))
    leaks = (range(n) if exhaustive else sorted({0, n // 4, n // 2, n - 1}))
    by_input = defaultdict(list)
    for i, j, k in all_layouts:
        by_input[i].append((j, k))
    rng = Random(seed + 1777 * n)
    gaps = Counter()
    disagreements = lower_than_ceiling = mirror_count = 0
    examples = []
    for leak in leaks:
        edge_list = edges(n, leak)
        rates = [rng.randint(1, 20000) for _ in edge_list]
        b = neg_generator(n, edge_list, rates)
        samples = frequencies(b, prime)
        mirror_count += check_mirror(b, rates, leak, samples, prime)
        for i, pairs in by_input.items():
            bases = {v: output_basis(samples, edge_list, i, v, prime)
                     for v in sorted({v for pair in pairs for v in pair})}
            for j, k in pairs:
                rank = joint_rank(bases[j], bases[k], prime)
                gap = len(edge_list) - rank
                predicted = deficiency_bound(n, i, j, k)
                gaps[gap] += 1
                disagreements += (gap == 0) != (predicted == 0)
                lower_than_ceiling += gap > predicted
                if gap < predicted or ((gap == 0) != (predicted == 0)):
                    examples.append((leak + 1, i + 1, j + 1, k + 1, rank, predicted))
                if n == 7 and i == 0 and j == 3 and k in (5, 6) and leak == 3:
                    print('boundary example n=7 leak=4:', (i + 1, j + 1, k + 1), rank)
    print(f'n={n} exhaustive={exhaustive} count={sum(gaps.values())} full={gaps[0]} '
          f'deficient={sum(gaps.values()) - gaps[0]} mismatches={disagreements} '
          f'below_ceiling={lower_than_ceiling} mirror_rows={mirror_count} '
          f'defect_distribution={dict(sorted(gaps.items()))}', flush=True)
    if examples:
        raise ArithmeticError(f'rank discrepancy at sampled point: {examples[:10]}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--through', type=int, default=12)
    parser.add_argument('--from-n', type=int, default=3)
    parser.add_argument('--boundary', nargs='*', type=int, default=[16, 24])
    parser.add_argument('--prime', type=int, choices=[1000003, 1000000007], default=1000000007)
    parser.add_argument('--seed', type=int, default=8966363)
    args = parser.parse_args()
    exact_four()
    for size in range(args.from_n, args.through + 1):
        survey(size, True, args.prime, args.seed)
    for size in args.boundary:
        survey(size, False, args.prime, args.seed)
