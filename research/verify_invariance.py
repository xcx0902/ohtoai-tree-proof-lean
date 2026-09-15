import sys, itertools
from functools import lru_cache

def all_trees(n):
    # Prufer sequences
    if n == 1:
        yield ()
        return
    if n == 2:
        yield ((0,1),)
        return
    for seq in itertools.product(range(n), repeat=n-2):
        deg = [1]*n
        for x in seq: deg[x]+=1
        edges=[]
        import heapq
        leaves=[i for i in range(n) if deg[i]==1]
        heapq.heapify(leaves)
        d=deg[:]
        for x in seq:
            leaf=heapq.heappop(leaves)
            edges.append((min(leaf,x),max(leaf,x)))
            d[leaf]-=1; d[x]-=1
            if d[x]==1: heapq.heappush(leaves,x)
        u=heapq.heappop(leaves); v=heapq.heappop(leaves)
        edges.append((min(u,v),max(u,v)))
        yield tuple(sorted(edges))

def canon(blocks, edges):
    # blocks: tuple of frozensets sorted by min; build graph, return canonical
    k=len(blocks)
    return (tuple(sorted(blocks, key=lambda s: min(s))), tuple(sorted(edges)))

def adj_of(blocks, edges):
    k=len(blocks)
    adj=[set() for _ in range(k)]
    for a,b in edges:
        adj[a].add(b); adj[b].add(a)
    return adj

def distances(adj, s):
    k=len(adj)
    d=[-1]*k; d[s]=0; q=[s]
    while q:
        nq=[]
        for u in q:
            for v in adj[u]:
                if d[v]<0:
                    d[v]=d[u]+1; nq.append(v)
        q=nq
    return d

def diameters(adj):
    k=len(adj)
    best=-1; res=[]
    allpaths=[]
    for s in range(k):
        d=distances(adj,s)
        for t in range(s+1,k):
            if d[t]>best:
                best=d[t]
    # collect all vertex-runs realizing diameter: enumerate all simple paths of length best
    paths=[]
    def dfs(u, visited, path):
        if len(path)-1==best:
            paths.append(tuple(path)); return
        for v in adj[u]:
            if v not in visited:
                visited.add(v); path.append(v)
                dfs(v,visited,path)
                path.pop(); visited.remove(v)
    for s in range(k):
        dfs(s,{s},[s])
    # dedupe (each path found twice, both orientations)
    out=set()
    for p in paths:
        out.add(min(p,p[::-1]))
    return best, sorted(out)

def fold(blocks, edges, path):
    k=len(path)
    f={}
    for idx,v in enumerate(path):
        i=idx+1
        f[v]=path[min(i,k-i+1)-1]
    # non-diameter vertices map to themselves
    for v in range(len(blocks)):
        if v not in f: f[v]=v
    newblocks={}
    for v in range(len(blocks)):
        t=f[v]
        newblocks.setdefault(t,set()).update(blocks[v])
    keys=sorted(newblocks.keys())
    remap={old:i for i,old in enumerate(keys)}
    nb=tuple(frozenset(newblocks[o]) for o in keys)
    ne=set()
    for a,b in edges:
        x,y=remap[f[a]],remap[f[b]]
        if x!=y: ne.add((min(x,y),max(x,y)))
    return canon(nb,tuple(sorted(ne)))

import sys
sys.setrecursionlimit(100000)

def op_counts(blocks, edges, memo):
    if len(blocks)==1: return {0}
    key=canon(blocks,edges)
    if key in memo: return memo[key]
    adj=adj_of(blocks,edges)
    best,paths=diameters(adj)
    counts=set()
    for p in paths:
        nb,ne=fold(blocks,edges,p)
        sub=op_counts(nb,ne,memo)
        for c in sub: counts.add(1+c)
    memo[key]=counts
    return counts

def main():
    memo={}
    for n in range(1,9):
        bad=0; tot=0; examples=[]
        for edges in all_trees(n):
            blocks=tuple(frozenset([i]) for i in range(n))
            cs=op_counts(blocks,edges,memo)
            tot+=1
            if len(cs)>1:
                bad+=1
                if len(examples)<3: examples.append((edges,sorted(cs)))
        print(f"n={n}: trees={tot} varying={bad} examples={examples}")
        sys.stdout.flush()

main()

import random
def random_tree(n, rng):
    if n==2: return ((0,1),)
    seq=[rng.randrange(n) for _ in range(n-2)]
    import heapq
    deg=[1]*n
    for x in seq: deg[x]+=1
    d=deg[:]; leaves=[i for i in range(n) if deg[i]==1]; heapq.heapify(leaves); edges=[]
    for x in seq:
        leaf=heapq.heappop(leaves); edges.append((min(leaf,x),max(leaf,x)))
        d[leaf]-=1; d[x]-=1
        if d[x]==1: heapq.heappush(leaves,x)
    u=heapq.heappop(leaves); v=heapq.heappop(leaves); edges.append((min(u,v),max(u,v)))
    return tuple(sorted(edges))

rng=random.Random(12345)
memo2={}
bad=0
for it in range(3000):
    n=rng.randrange(2,15)
    e=random_tree(n,rng)
    blocks=tuple(frozenset([i]) for i in range(n))
    cs=op_counts(blocks,e,memo2)
    if len(cs)>1:
        bad+=1
        if bad<=5: print("VARYING n=",n,e,sorted(cs))
print("random stress: 3000 trees, varying =",bad)
