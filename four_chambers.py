"""Exact checks of the four-chamber example using only the Python standard library."""
from itertools import permutations
from math import prod


def determinant(matrix):
    """Leibniz formula, used only for matrices of order at most seven."""
    n = len(matrix)
    result = 0
    for perm in permutations(range(n)):
        inversions = sum(perm[i] > perm[j] for i in range(n) for j in range(i + 1, n))
        result += (-1) ** inversions * prod(matrix[row][col] for row, col in enumerate(perm))
    return result


def pencil(theta, leak, s):
    """Matrix sI-A; chamber numbers in this helper start at zero."""
    matrix = [[s * int(row == col) for col in range(4)] for row in range(4)]
    for edge in range(3):
        a, b = theta[edge], theta[3 + edge]
        matrix[edge][edge] += a
        matrix[edge + 1][edge] -= a
        matrix[edge + 1][edge + 1] += b
        matrix[edge][edge + 1] -= b
    matrix[leak][leak] += theta[-1]
    return matrix


def signals(theta, leak, s):
    matrix = pencil(theta, leak, s)

    def numerator(output):
        minor = [[row[col] for col in range(4) if col != output] for row in matrix[1:]]
        return (-1) ** output * determinant(minor)

    return determinant(matrix), numerator(2), numerator(3)


def observations(theta, leak):
    rows = [signals(theta, leak, s) for s in range(4)]
    return [row[0] for row in rows] + [rows[1][1] - rows[0][1], rows[0][1], rows[0][2]]


def jacobian_det(theta, leak):
    # Each independent rate occurs only in its source column. Every determinant
    # and cofactor is affine in that rate, so a unit difference is its exact derivative.
    baseline = observations(theta, leak)
    columns = []
    for pos in range(7):
        moved = list(theta)
        moved[pos] += 1
        updated = observations(moved, leak)
        columns.append([new - old for new, old in zip(updated, baseline)])
    return determinant(list(zip(*columns)))


if __name__ == "__main__":
    witness = (1, 2, 3, 4, 5, 6, 7)
    expected = (-311040, -198720, -103680, -51840)
    for leak, target in enumerate(expected):
        value = jacobian_det(witness, leak)
        assert value == target
        print(f"Leak chamber {leak + 1}: determinant {value}")

    first = (1, 1, 1, 1, 1, 1, 2)
    second = (1, 1, 1, 1, 2, 1, 1)
    assert first != second
    for theta in [first, second]:
        # Five distinct integer evaluations determine the polynomial of degree four
        # and its cofactors of degree at most three.
        for s in range(5):
            assert signals(theta, 1, s) == (s**4 + 8*s**3 + 18*s**2 + 12*s + 2, s + 1, 1)
    values = (jacobian_det(first, 1), jacobian_det(second, 1))
    assert values == (12, -24)
    print(f"Equal transfers at two distinct positive points. Determinants: {values}")
