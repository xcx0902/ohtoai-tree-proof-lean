"""Validate the two-phase strategy for REF.md Lemma 5 (delayed exchange).

Strategy under test:
  * T_P = fold(S, P), T_Q = fold(S, Q)   (fold = identify p_i with p_{D-i})
  * r = D - l, l = last common index of P and Q
  * PHASE 1: while diam(T_P) = diam(T_Q) = H > 2r, fold BOTH along the SAME
    vertex path s = z_0,...,z_H (chosen as a farthest-from-s path in T_P),
    asserting it is a diameter of both and identical as a sequence.
  * PHASE 2 (H = 2r): fold T_P along s--Q.last and T_Q along s--P.last.
  * assert the two end states are literally equal.
"""
import random
from collections import deque
from itertools import combinations

def rand_tree(n, rng):
    adj = [[] for _ in range(n)]
    for v in range(1, n):
        u = rng.randrange(v)
        adj[u].append(v); adj[v].append(u)
    return adj

def bfs(adj, s):
    n = len(adj)
    d = [-1]*n; par = [-1]*n
    d[s] = 0; q = deque([s])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if d[w] < 0:
                d[w] = d[u]+1; par[w] = u; q.append(w)
    return d, par

def path_to(adj, s, x):
    _, par = bfs(adj, s)
    p = [x]
    while p[-1] != s:
        p.append(par[p[-1]])
    return p[::-1]

def diam(adj):
    best = (-1, None)
    for s in range(len(adj)):
        d, _ = bfs(adj, s)
        m = max(d)
        if m > best[0]:
            best = (m, s)
    return best

def endpoints(adj):
    D, u = diam(adj)
    d, _ = bfs(adj, u)
    v = max(range(len(adj)), key=lambda w: d[w])
    return D, u, v

def fold(adj, path, alive_old):
    """fold along `path` (list of vertices, path[0] is the anchor)."""
    D = len(path) - 1
    idx = {v: i for i, v in enumerate(path)}
    rep = {}
    for v in range(len(adj)):
        if v in idx:
            i = idx[v]
            rep[v] = path[min(i, D-i)]
        else:
            rep[v] = v
    newadj = [set() for _ in adj]
    for u in alive_old:
        for w in adj[u]:
            a, b = rep[u], rep[w]
            if a != b:
                newadj[a].add(b); newadj[b].add(a)
    alive = sorted(set(rep[v] for v in alive_old))
    return [list(s) for s in newadj], alive, rep

def tree_from(adj, alive):
    """restrict to alive set; keep a full-size adjacency for simplicity"""
    n = len(adj)
    new = [set() for _ in range(n)]
    for u in alive:
        for w in adj[u]:
            if w in alive:
                new[u].add(w)
    return [sorted(s) for s in new], alive

def common_prefix_len(P, Q):
    l = -1
    for i in range(min(len(P), len(Q))):
        if P[i] == Q[i]:
            l = i
        else:
            break
    return l

def connected_state(adj, alive):
    if not alive:
        return True
    s = alive[0]
    seen = {s}
    q = deque([s])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if w in alive and w not in seen:
                seen.add(w); q.append(w)
    return len(seen) == len(alive)

def dist_in(adj, alive, s):
    """distances inside the induced tree on alive"""
    d = {s: 0}
    q = deque([s])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if w in alive and w not in d:
                d[w] = d[u]+1; q.append(w)
    return d

def state_diam(adj, alive, s):
    d = dist_in(adj, alive, s)
    return max(d.values()), d

def restrict_adj(adj, alive):
    n = len(adj)
    new = [set() for _ in range(n)]
    for u in alive:
        for w in adj[u]:
            if w in alive:
                new[u].add(w)
    return [sorted(s) for s in new]

def run(n, rng, verbose=False):
    adj = rand_tree(n, rng)
    D, u, v = endpoints(adj)
    if D < 2:
        return None
    # all far vertices from s=u
    du, _ = bfs(adj, u)
    fars = [x for x in range(n) if du[x] == D]
    if len(fars) < 2:
        return None
    x, y = rng.sample(fars, 2)
    P = path_to(adj, u, x)
    Q = path_to(adj, u, y)
    assert len(P) == len(Q) == D+1
    l = common_prefix_len(P, Q)
    r = D - l
    assert 2*r <= D, (D, l, r)   # REF Lemma 4
    allv = list(range(len(adj)))
    T1, a1, rep1 = fold(adj, P, allv)
    T2, a2, rep2 = fold(adj, Q, allv)
    T1 = restrict_adj(T1, a1); T2 = restrict_adj(T2, a2)
    nphase1 = 0
    while True:
        H1, d1 = state_diam(T1, a1, u)
        H2, d2 = state_diam(T2, a2, u)
        if H1 != H2:
            return ("DIAM-MISMATCH", n, D, l, r, H1, H2)
        if H1 > 2*r:
            if d1.get(x, 10**9) != d2.get(x, 10**9):
                pass
            z = max(d1, key=lambda w: d1[w])
            Z1 = path_to(T1, u, z)
            Z2 = path_to(T2, u, z)
            if Z1 != Z2:
                return ("PATH-MISMATCH", n, D, l, r, H1, Z1, Z2)
            if len(Z1)-1 != H1:
                return ("BAD-DIAM-PATH", n)
            # check the difference region is fixed: p_0..p_r must be fixed
            T1b, b1, _ = fold(T1, Z1, a1)
            T2b, b2, _ = fold(T2, Z2, a2)
            T1 = restrict_adj(T1b, b1); T2 = restrict_adj(T2b, b2)
            a1, a2 = b1, b2
            nphase1 += 1
        else:
            assert H1 == 2*r, (H1, r)
            break
    # phase 2
    Z1 = path_to(T1, u, y)   # Q.last
    Z2 = path_to(T2, u, x)   # P.last
    if len(Z1)-1 != 2*r or len(Z2)-1 != 2*r:
        return ("ENDGAME-PATH", n, D, l, r, len(Z1)-1, len(Z2)-1)
    U1, c1, _ = fold(T1, Z1, a1)
    U2, c2, _ = fold(T2, Z2, a2)
    U1 = restrict_adj(U1, c1); U2 = restrict_adj(U2, c2)
    if c1 != c2 or U1 != U2:
        return ("ENDGAME-DIFF", n, D, l, r, c1, c2)
    return ("OK", nphase1)

def main():
    rng = random.Random(12345)
    counts = {}
    bad = []
    trials = 0
    for _ in range(4000):
        n = rng.randint(4, 16)
        res = run(n, rng)
        if res is None:
            continue
        trials += 1
        counts[res[0]] = counts.get(res[0], 0) + 1
        if res[0] != "OK" and len(bad) < 5:
            bad.append(res)
    print("trials:", trials)
    print("counts:", counts)
    for b in bad:
        print("BAD:", b)

main()
