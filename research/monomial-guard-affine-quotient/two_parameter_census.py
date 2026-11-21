"""Exact distances for normalized ternary inputs with two named slope columns."""
import json
from collections import Counter, deque
from itertools import combinations_with_replacement, product
from math import factorial, prod


def signed_row(row):
    """A row and its negative belong to the same free orbit."""
    return min(row, tuple(-entry % 3 for entry in row))


ROWS = sorted({signed_row(row) for row in product(range(3), repeat=4)})
CODE = {row: index for index, row in enumerate(ROWS)}
SEPARATED = [i for i, (u, x, y, _) in enumerate(ROWS) if u*x % 3 == u*y % 3 == 0]
SCALAR = [(u*b + 1) % 3 - 1 for u, _, _, b in ROWS]
DIRECTION = [signed_row((x, y)) for _, x, y, _ in ROWS]


def pair_moves(left, right):
    """All one-addition replacements on these types, in both orientations."""
    result = set()
    for target, donor in ((left, right), (right, left)):
        u, *dual = ROWS[target]
        v, *other_dual = ROWS[donor]
        for c in (1, 2):
            target_row = signed_row(((u + c*v) % 3, *dual))
            donor_row = signed_row((v, *((w - c*z) % 3 for w, z in zip(other_dual, dual))))
            result.add(tuple(sorted((CODE[target_row], CODE[donor_row]))))
    result.discard((left, right))
    return result


MOVES = {pair: pair_moves(*pair) for pair in combinations_with_replacement(range(len(ROWS)), 2)}


def census(m):
    """A simultaneous BFS from all successful free orbits."""
    distance = {
        state: 0 for state in combinations_with_replacement(SEPARATED, m)
        if sum(SCALAR[i] for i in state) in (1, -2)
    }
    queue = deque(distance)
    while queue:
        state = queue.popleft()
        for i in range(m):
            if i and state[i] == state[i-1]:
                continue
            for j in range(i+1, m):
                if j > i+1 and state[j] == state[j-1]:
                    continue
                rest = state[:i] + state[i+1:j] + state[j+1:]
                for pair in MOVES[state[i], state[j]]:
                    target = tuple(sorted(rest + pair))
                    if target not in distance:
                        distance[target] = distance[state] + 1
                        queue.append(target)

    by_rank = [Counter() for _ in range(3)]
    for state, cost in distance.items():
        directions = {DIRECTION[i] for i in state} - {(0, 0)}
        rank = min(2, len(directions))
        permutations = factorial(m) // prod(factorial(n) for n in Counter(state).values())
        nonzero_rows = m - state.count(CODE[(0, 0, 0, 0)])
        by_rank[rank][cost] += permutations * 2**nonzero_rows

    # Fix u and b. The two slope columns are an ordered pair from u-perp.
    q = 3**(m-1)
    choices = (1, 4*(q-1), (q-1)*(q-3))
    expected = [(3**m - 1)*q*count for count in choices]
    if [sum(hist.values()) for hist in by_rank] != expected:
        raise AssertionError(f"labeled coverage failed at m={m}")
    return {
        "m": m,
        "row_orbits": len(distance),
        "maxima_by_rank": [max(hist, default=None) for hist in by_rank],
        "labeled_histograms_by_rank": [dict(sorted(hist.items())) for hist in by_rank],
    }


if __name__ == "__main__":
    print(json.dumps([census(m) for m in range(1, 7)], indent=2))
