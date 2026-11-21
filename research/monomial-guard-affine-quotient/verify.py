"""Exact finite checks for the affine-image quotient. Python 3, standard library only."""

from collections import Counter, deque
from functools import cache
from itertools import permutations, product


MODES = ("rows", "translations", "affine")


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def rref_basis(rows):
    """Nonzero rows of the unique reduced row-echelon form over F_3."""
    a = [list(row) for row in rows]
    rank = 0
    for col in range(len(a[0]) if a else 0):
        pivot = next((i for i in range(rank, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        scale = a[rank][col]  # Both nonzero elements of F_3 are self-inverse.
        a[rank] = [(scale * x) % 3 for x in a[rank]]
        for i, row in enumerate(a):
            if i != rank and row[col]:
                a[i] = [(x - row[col] * y) % 3 for x, y in zip(row, a[rank])]
        rank += 1
    return tuple(tuple(row) for row in a[:rank])


def check_image_key():
    """Compare the homogeneous row-space key with literal affine point sets."""
    key_to_points, points_to_key = {}, {}
    count = 0
    for d in range(3):
        for columns in product(product(range(3), repeat=2), repeat=d):
            for b in product(range(3), repeat=2):
                count += 1
                key = rref_basis([v + (0,) for v in columns] + [b + (1,)])
                points = frozenset(
                    tuple((b[i] + sum(a[j] * columns[j][i] for j in range(d))) % 3
                          for i in range(2))
                    for a in product(range(3), repeat=d)
                )
                check(key_to_points.setdefault(key, points) == points, "image-key collision")
                check(points_to_key.setdefault(points, key) == key, "redundant parameter mismatch")
    check((count, len(key_to_points), len(points_to_key)) == (819, 22, 22), "affine image census")
    print("Two rows, d=0,1,2: 819 presentations, 22 distinct affine images.")


def paid_moves(n):
    return tuple((i, j, c) for i, j in permutations(range(n), 2) for c in (1, 2))


def add(state, move):
    """A one-parameter state is a tuple of labeled rows (u_i,w_i,b_i)."""
    i, j, c = move
    ui, wi, bi = state[i]
    uj, wj, bj = state[j]
    result = list(state)
    result[i] = ((ui + c * uj) % 3, wi, bi)
    result[j] = (uj, (wj - c * wi) % 3, (bj - c * bi) % 3)
    return tuple(result)


@cache
def signature(state, mode):
    shifts = (0,) if mode == "rows" else range(3)
    factors = (1, 2) if mode == "affine" else (1,)
    keys = []
    for shift, factor in product(shifts, factors):
        rows = []
        for u, w, b in state:
            row = (u, factor * w % 3, (b + shift * w) % 3)
            rows.append(min(row, tuple(-x % 3 for x in row)))
        keys.append(tuple(sorted(rows)))
    return min(keys)


def passing_order(state):
    for order in permutations(range(len(state))):
        scalar = slope = 0
        for i in order[:-1]:
            u, w, b = state[i]
            scalar, slope = (scalar + u * b) % 3, (slope + u * w) % 3
            if slope or scalar == 1:
                break
        else:
            return order
    return None


@cache
def determinant(matrix):
    if not matrix:
        return 1
    terms = []
    for j, entry in enumerate(matrix[0]):
        if entry:
            minor = tuple(row[:j] + row[j+1:] for row in matrix[1:])
            terms.append((-1)**j * entry * determinant(minor))
    return sum(terms) % 3


def literal_pass(state):
    """Evaluate actual leading minors of I-u z^T, in the given order."""
    for a in range(3):
        z = [(b + a * w) % 3 for _, w, b in state]
        for k in range(1, len(state)):
            minor = tuple(tuple((int(i == j) - state[i][0] * z[j]) % 3
                                for j in range(k)) for i in range(k))
            if determinant(minor) == 0:
                return False
    return True


def dense_generators(n):
    """Physical moves, with independently computed inverse transposes."""
    identity = [[int(i == j) for j in range(n)] for i in range(n)]
    matrices = []
    for i, j, c in paid_moves(n):
        matrix = [row[:] for row in identity]
        matrix[i][j] = c
        matrices.append((1, matrix))
    for i in range(n):
        matrix = [row[:] for row in identity]
        matrix[i][i] = 2
        matrices.append((0, matrix))
    for i in range(n-1):
        matrix = [row[:] for row in identity]
        matrix[i], matrix[i+1] = matrix[i+1], matrix[i]
        matrices.append((0, matrix))
    for cost, matrix in matrices:
        reduced = rref_basis([r + unit for r, unit in zip(matrix, identity)])
        inverse = [row[n:] for row in reduced]
        yield cost, matrix, tuple(zip(*inverse))


def matvec(matrix, vector):
    return tuple(sum(a*b for a, b in zip(row, vector)) % 3 for row in matrix)


def labeled_distances(states):
    """Multi-source 0-1 BFS, with literal goals and explicit free operations."""
    moves = tuple(dense_generators(3))
    dist = {s: 0 for s in states if literal_pass(s)}
    queue = deque(dist)
    while queue:
        state = queue.popleft()
        u, w, b = zip(*state)
        for cost, primal, dual in moves:
            successor = tuple(zip(matvec(primal, u), matvec(dual, w), matvec(dual, b)))
            depth = dist[state] + cost
            if successor not in dist or depth < dist[successor]:
                dist[successor] = depth
                if cost:
                    queue.append(successor)
                else:
                    queue.appendleft(successor)
    return dist


def three_row_census():
    rows = tuple(product(range(3), repeat=3))
    states = [s for s in product(rows, repeat=3)
              if sum(u*w for u, w, b in s) % 3 == 0 and sum(u*b for u, w, b in s) % 3 == 1]
    reference = labeled_distances(states)
    check(set(reference) == set(states) and len(states) == 2106, "labeled-state coverage")
    check(Counter(reference.values()) == {0: 882, 1: 1080, 2: 144}, "labeled cost histogram")
    moves = paid_moves(3)
    for mode, expected in zip(MODES, (58, 26, 24)):
        representatives = {signature(s, mode): s for s in states}
        dist = {k: 0 for k, s in representatives.items() if passing_order(s) is not None}
        queue = deque(dist)
        while queue:
            key = queue.popleft()
            for move in moves:
                new = signature(add(representatives[key], move), mode)
                if new not in dist:
                    dist[new] = dist[key] + 1
                    queue.append(new)
        check(len(dist) == len(representatives) == expected, f"{mode}: quotient coverage")
        check(all(reference[s] == dist[signature(s, mode)] for s in states), f"{mode}: costs")
        print(f"Three rows, {mode}: {len(dist)} classes; all 2106 individual distances agree.")
    print("Input counts at costs 0,1,2: 882, 1080, 144.")


def five_row_census():
    start = ((1, 1, 1),) * 4 + ((1, 2, 0),)
    moves = paid_moves(len(start))
    expected = ((1, 6, 40, 166), (1, 6, 40, 126), (1, 6, 35, 80))
    for mode, counts in zip(MODES, expected):
        first = signature(start, mode)
        layer, sizes = [first], []
        representatives, parents = {first: start}, {first: None}
        witness = None
        for depth in range(4):
            sizes.append(len(layer))
            for key in layer:
                order = passing_order(representatives[key])
                if order is not None and witness is None:
                    witness = key, order, depth
            if depth == 3:
                break
            next_layer = []
            for key in layer:
                for move in moves:
                    state = add(representatives[key], move)
                    new = signature(state, mode)
                    if new not in representatives:
                        representatives[new] = state
                        parents[new] = key, move
                        next_layer.append(new)
            layer = next_layer
        check(tuple(sizes) == counts, f"{mode}: exact-distance shells")
        check(witness is not None and witness[2] == 3, f"{mode}: optimum")
        key, order, _ = witness
        path = []
        while parents[key] is not None:
            key, move = parents[key]
            path.append(move)
        path.reverse()
        state = start
        for move in path:
            state = add(state, move)
        check(len(path) == 3 and literal_pass(tuple(state[i] for i in order)), "witness replay")
        print(f"Five rows, {mode}: {sizes}; replayed {path}, final order {order}.")
    state = start
    for move in ((0, 1, 1), (0, 2, 1), (3, 4, 2)):
        state = add(state, move)
    check(literal_pass(state), "published witness in its original row order")
    left = ((1, 0, 1), (0, 1, 0))
    right = ((1, 0, 1), (0, 1, 1))
    check(signature(left, "rows") != signature(right, "rows") and
          signature(left, "affine") == signature(right, "affine"), "labeled endpoint example")


if __name__ == "__main__":
    check_image_key()
    three_row_census()
    five_row_census()
