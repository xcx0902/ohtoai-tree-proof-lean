"""Empirical check of REF.md §7 (the delayed exchange lemma) in the exact setting of the
formalization: states are (alive set, graph), a fold is along a diameter path with the canonical
representative map v |-> P[min(i, D-i)], and folding is always towards the fixed endpoint s.

Checked claims, for random trees and s a diameter endpoint, with P, Q two diameter paths from s:
  (1) after r = D - l further folds towards s, the two folded states coincide exactly
      (l = last index where P and Q agree, D = diameter);
  (2) the number of folds towards s needed to reach a single vertex is the same from both sides.
"""
import random
from collections import deque

def random_tree(n, rng):
    adj = {i: set() for i in range(n)}
    for v in range(1, n):
        u = rng.randrange(v)
        adj[u].add(v); adj[v].add(u)
    return adj

def bfs(adj, src, vertices):
    dist = {src: 0}; par = {src: None}
    q = deque([src])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v in vertices and v not in dist:
                dist[v] = dist[u] + 1; par[v] = u; q.append(v)
    return dist, par

def farthest(adj, src, vertices):
    dist, par = bfs(adj, src, vertices)
    x = max(dist, key=lambda v: dist[v])
    return x, dist[x], par, dist

def diam_path_from(adj, s, vertices):
    x, d, par, _ = farthest(adj, s, vertices)
    path = [x]
    while path[-1] != s:
        path.append(par[path[-1]])
    return path[::-1], d          # path[0] = s, length d = diameter

def fold(adj, alive, path):
    D = len(path) - 1
    idx = {v: i for i, v in enumerate(path)}
    def rep(v):
        i = idx.get(v)
        return v if i is None else path[min(i, D - i)]
    new_alive = {v for v in alive if rep(v) == v}
    new_adj = {v: set() for v in new_alive}
    for u in alive:
        for v in adj[u]:
            if v in alive and u < v:
                a, b = rep(u), rep(v)
                if a != b and a in new_alive and b in new_alive:
                    new_adj[a].add(b); new_adj[b].add(a)
    return new_alive, new_adj

def state_of(alive, adj):
    return (frozenset(alive), frozenset(frozenset((u, v)) for u in alive for v in adj[u] if u < v))

def fold_towards(adj, alive, s):
    """one fold towards s; returns the new state (or None if already single)"""
    if len(alive) <= 1:
        return None
    path, _ = diam_path_from(adj, s, alive)
    return fold(adj, alive, path)

def length_towards(adj, alive, s, cap=100):
    k = 0
    while len(alive) > 1 and k < cap:
        r = fold_towards(adj, alive, s)
        if r is None:
            break
        alive, adj = r; k += 1
    return k

def path_to(dist_par, s, y):
    par = dist_par
    q = [y]
    while q[-1] != s:
        q.append(par[q[-1]])
    return q[::-1]

def check(n, rng):
    adj = random_tree(n, rng)
    V = set(range(n))
    x, _, _, _ = farthest(adj, 0, V)          # one end of a diameter
    s, _, _, _ = farthest(adj, x, V)          # the other end: s is a diameter endpoint
    P, D = diam_path_from(adj, s, V)
    _, par = bfs(adj, s, V)
    dist, _ = bfs(adj, s, V)
    cands = sorted(v for v in V if dist[v] == D and v != P[-1])
    if not cands:
        return None
    y = rng.choice(cands)                      # a different diameter from s
    Q = path_to(par, s, y)
    assert len(Q) - 1 == D
    l = 0
    while l + 1 < len(P) and l + 1 < len(Q) and P[l + 1] == Q[l + 1]:
        l += 1
    r = D - l
    aP, gP = fold(adj, V, P)
    aQ, gQ = fold(adj, V, Q)
    for _ in range(r):
        fP = fold_towards(gP, aP, s)
        fQ = fold_towards(gQ, aQ, s)
        if fP is None or fQ is None:
            break
        aP, gP = fP
        aQ, gQ = fQ
    return state_of(aP, gP) == state_of(aQ, gQ), length_towards(gP, aP, s) == length_towards(gQ, aQ, s), l, r, D

rng = random.Random(12345)
bad_state = bad_len = total = 0
for n in range(3, 15):
    for _ in range(400):
        res = check(n, rng)
        if res is None:
            continue
        same, eqlen, l, r, D = res
        total += 1
        if not same:
            bad_state += 1
            if bad_state <= 3:
                print(f"  states differ: n={n} l={l} r={r} D={D}")
        if not eqlen:
            bad_len += 1
            if bad_len <= 3:
                print(f"  lengths differ: n={n} l={l} r={r} D={D}")
print(f"checked {total} random (tree, endpoint, pair of diameters) instances")
print(f"  states coincide after r further folds: {total - bad_state}/{total}")
print(f"  lengths towards s agree:               {total - bad_len}/{total}")
