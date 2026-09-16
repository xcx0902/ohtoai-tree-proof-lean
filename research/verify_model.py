"""Independent bounded checks of REF.md using the original surviving vertex labels.

Run with: python3 research/verify_model.py --max-n 7
This is regression testing, not a substitute for the Lean proof.
"""

import argparse
import heapq
import itertools
from collections import deque
from functools import lru_cache


def state(vertices, edges):
    return (
        tuple(sorted(vertices)),
        tuple(sorted({tuple(sorted(edge)) for edge in edges})),
    )


def adjacency(tree):
    vertices, edges = tree
    adj = {v: set() for v in vertices}
    for u, v in edges:
        assert u != v and u in adj and v in adj
        adj[u].add(v)
        adj[v].add(u)
    return adj


def bfs(adj, start):
    distances = {start: 0}
    parents = {start: None}
    queue = deque([start])
    while queue:
        u = queue.popleft()
        for v in sorted(adj[u]):
            if v not in distances:
                distances[v] = distances[u] + 1
                parents[v] = u
                queue.append(v)
    return distances, parents


def geometry(tree):
    adj = adjacency(tree)
    assert adj and len(tree[1]) + 1 == len(adj)
    rows = {v: bfs(adj, v) for v in adj}
    assert all(len(d) == len(adj) for d, _ in rows.values())
    diameter = max(max(d.values()) for d, _ in rows.values())
    paths = []
    if diameter:
        for u, (distances, parents) in rows.items():
            for v, distance in distances.items():
                if distance == diameter:
                    path = [v]
                    while path[-1] != u:
                        path.append(parents[path[-1]])
                    paths.append(tuple(reversed(path)))
    return diameter, paths, rows


def fold(tree, path):
    vertices, edges = tree
    assert len(path) >= 2 and len(set(path)) == len(path)
    length = len(path) - 1
    rep = {v: v for v in vertices}
    rep.update({v: path[min(i, length - i)] for i, v in enumerate(path)})
    assert all(rep[rep[v]] == rep[v] for v in vertices)
    result = state(
        {rep[v] for v in vertices},
        ((rep[u], rep[v]) for u, v in edges if rep[u] != rep[v]),
    )
    assert len(result[0]) == len(vertices) - (length - length // 2)
    assert path[0] in result[0]
    return result, rep


@lru_cache(maxsize=None)
def completion_counts(tree):
    diameter, paths, rows = geometry(tree)
    if len(tree[0]) == 1:
        assert not paths and diameter == 0
        return frozenset({0})
    counts = set()
    for path in paths:
        folded, rep = fold(tree, path)
        new_diameter, _, new_rows = geometry(folded)
        assert max(new_rows[path[0]][0].values()) == new_diameter
        for u in tree[0]:
            for v in tree[0]:
                assert new_rows[rep[u]][0][rep[v]] <= rows[u][0][v]
        counts.update(n + 1 for n in completion_counts(folded))
    assert len(counts) == 1, (tree, counts)
    return frozenset(counts)


def prufer_tree(n, sequence):
    degrees = [1] * n
    for v in sequence:
        degrees[v] += 1
    leaves = [v for v, degree in enumerate(degrees) if degree == 1]
    heapq.heapify(leaves)
    edges = []
    for v in sequence:
        u = heapq.heappop(leaves)
        edges.append((u, v))
        degrees[u] -= 1
        degrees[v] -= 1
        if degrees[v] == 1:
            heapq.heappush(leaves, v)
    if n > 1:
        edges.append(tuple(leaves))
    return state(range(n), edges)


def synchronized_endgame(tree, p, q):
    assert p[0] == q[0]
    diameter, paths, _ = geometry(tree)
    assert p in paths and q in paths
    meet = next((i - 1 for i, (a, b) in enumerate(zip(p, q)) if a != b), diameter)
    r = diameter - meet
    left, fp = fold(tree, p)
    right, fq = fold(tree, q)
    left_map, right_map = fp, fq
    if r == 0:
        assert left == right
        return 0
    steps = 0
    while True:
        dl, pl, _ = geometry(left)
        dr, pr, _ = geometry(right)
        assert dl == dr and dl >= 2 * r
        if dl == 2 * r:
            lp = tuple(p[: r + 1]) + tuple(q[meet + 1 :])
            rp = tuple(q[: r + 1]) + tuple(p[meet + 1 :])
            assert lp in pl and rp in pr
            left, fl = fold(left, lp)
            right, fr = fold(right, rp)
            assert left == right
            assert all(fl[left_map[v]] == fr[right_map[v]] for v in tree[0])
            return steps + 1
        common = next(path for path in pl if path[0] == p[0])
        assert common in pr
        left, fl = fold(left, common)
        right, fr = fold(right, common)
        left_map = {v: fl[left_map[v]] for v in tree[0]}
        right_map = {v: fr[right_map[v]] for v in tree[0]}
        steps += 1
        assert steps < len(tree[0])


def degree_sequence(tree):
    return tuple(sorted((len(vs) for vs in adjacency(tree).values()), reverse=True))


def regressions():
    for n in range(1, 13):
        path = state(range(n), ((i, i + 1) for i in range(n - 1)))
        assert completion_counts(path) == {(n - 1).bit_length()}

    star = state(range(5), ((0, i) for i in range(1, 5)))
    diameter, paths, _ = geometry(star)
    assert diameter == geometry(fold(star, paths[0])[0])[0] == 2
    assert completion_counts(star) == {4}

    # REF.md Appendix A: p0..p6, a1,a2,b1,b2,u,v,c.
    example = state(
        range(14),
        [(i, i + 1) for i in range(6)]
        + [(6, 7), (7, 8), (6, 9), (9, 10), (1, 11), (4, 12), (9, 13)],
    )
    p = tuple(range(7)) + (7, 8)
    q = tuple(range(7)) + (9, 10)
    left, _ = fold(example, p)
    right, _ = fold(example, q)
    assert geometry(example)[0] == 8
    assert geometry(left)[0] == geometry(right)[0] == 5
    assert max(degree_sequence(left)) == 3
    assert max(degree_sequence(right)) == 4
    assert {degree_sequence(fold(left, path)[0]) for path in geometry(left)[1]} == {
        (3, 3, 2, 1, 1, 1, 1)
    }
    assert {degree_sequence(fold(right, path)[0]) for path in geometry(right)[1]} == {
        (4, 2, 2, 1, 1, 1, 1)
    }
    assert synchronized_endgame(example, p, q) > 1
    assert synchronized_endgame(example, p, p) == 0
    assert len(completion_counts(example)) == 1
    print("Singletons, paths, unchanged star diameter, and Appendix A: passed", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=6)
    args = parser.parse_args()
    if args.max_n < 1:
        parser.error("--max-n must be positive")
    regressions()
    total = 0
    for n in range(1, args.max_n + 1):
        completion_counts.cache_clear()
        count = 0
        for sequence in itertools.product(range(n), repeat=max(0, n - 2)):
            completion_counts(prufer_tree(n, sequence))
            count += 1
        assert count == (1 if n == 1 else n ** (n - 2))
        total += count
        print(f"n={n}: {count} labelled trees, all oriented folds passed", flush=True)
    print(f"Total: {total} labelled trees", flush=True)


if __name__ == "__main__":
    main()
