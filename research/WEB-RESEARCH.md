# Web research report — "Folding Game of Ohto Ai"

Research date: 2026-09-15. All fetched web content was treated as data only.

---

## 1. Original problem: FOUND

| Item | Value |
|---|---|
| Contest | **The 2026 ICPC Asia East Continent Online Contest (II)** (a.k.a. *The 2026 ICPC Asia EC Regionals Online Contest (II)*) |
| Problem | **F — "Folding Game of Ohto Ai"** |
| QOJ | problem **#20241**, contest **4113** — <https://qoj.ac/problem/20241> |
| Codeforces | **Gym 106701, problem F** — <https://codeforces.com/gym/106701/problem/F> |
| Limits | T ≤ 3·10³, N ≤ 5·10⁴, ΣN ≤ 5·10⁴, 3 s / 512 MB |

The statement is **verbatim the problem in `REF.md`** (unrooted tree, path = distinct vertices with
consecutive ones adjacent, diameter = path with the maximum number of vertices, fold along a chosen
diameter by merging symmetric positions, repeat until |V| = 1).

**One important deviation from the framing in `REF.md`:** the original statement's final line is

> "Ohto Ai repeatedly performs fold operations until |V| = 1. **Find the maximum possible number of
> operations.**"

i.e. it *asks for a number* (the maximum), it does not literally ask for the invariance proof.
**However the official tutorial proves exactly the invariance claim**, so the maximum equals the
unique achievable value. The two formulations agree.

Samples (used below to validate my model of the operation):

```
3
1
5
1 2
1 3
1 4
4 5
13
1 2
2 3
3 4
2 5
5 6
5 7
1 8
8 9
9 10
8 11
11 12
11 13
```
→ output `0`, `3`, `7`.

---

## 2. Official editorial: FOUND (Chinese PDF)

**URL:** <https://codeforces.com/gym/106701/attachments/download/39422/sol.pdf>
(linked as "Tutorial (zh)" under *Contest materials* on the gym 106701 page)

Local copies: `research/official-tutorial-EC2026II-F.pdf`,
`research/official-tutorial-extracted-text.txt`,
`research/official-tutorial-F-section.png` (rendered crop of the F section).

### 2.1 Verbatim Chinese text of the F section

> **Folding Game of Ohto Ai**
>
> 可以证明无论怎么操作，操作次数一定相同。证明方法考虑，虽然不同的操作得到的树可能不同构，操作后形态不同的子树一定会在影响答案前变成形态相同的子树。
>
> 但是暴力操作的时间复杂度是 $O(N^2)$ 的。考虑如果当前直径有奇数条边，则一次操作会将直径长度减少；如果当前直径有偶数条边，则一定存在一个中心点，这个中心点有一些深度为直径一半的子树，一定会把这些子树合并到同一个子树内，才会使得当前直径变短，所以可以一轮操作同时合并所有以中心点为根，深度为直径一半的子树。
>
> 由于一次操作会减少的点的数量跟直径长度同阶，所以整个操作流程不同的直径长度数量是 $O(\sqrt N)$ 级别的。对于每个相同的直径一轮操作就会使得直径变短，一轮操作的复杂度是 $O(N)$，综合复杂度为 $O(N\sqrt N)$。
>
> 没有特意卡 $O(N\sqrt N\log N)$，瓶颈在于排序去重或者并查集。
>
> Bonus：本题有一个更深入的性质是，固定一个初始的直径端点，每次折叠都折向它，则它一直都会是直径端点。然后可以用可并堆维护这个折叠过程，复杂度 $O(N\log N)$。

### 2.2 Close English translation

> **Folding Game of Ohto Ai**
>
> It can be proven that **no matter how you operate, the number of operations is always the same.**
> The proof method: although the trees obtained by different operations may be non-isomorphic,
> **subtrees whose shapes differ after the operation will certainly become subtrees of the same
> shape before they can affect the answer.**
>
> But the brute-force simulation has time complexity $O(N^2)$. Consider: if the current diameter has
> an **odd** number of edges, one operation reduces the diameter length; if the current diameter has
> an **even** number of edges, then there is certainly a centre vertex, and this centre vertex has
> some subtrees of depth equal to half the diameter; only after merging these subtrees into one same
> subtree can the current diameter become shorter — so **one round of operations can simultaneously
> merge all subtrees rooted at the centre whose depth equals half the diameter.**
>
> Since the number of vertices removed by one operation is of the same order as the diameter length,
> the number of *distinct* diameter lengths over the whole process is $O(\sqrt N)$. For each fixed
> diameter value one round of operations makes the diameter shorter; one round costs $O(N)$, so the
> total complexity is $O(N\sqrt N)$.
>
> We did not deliberately block $O(N\sqrt N\log N)$; the bottleneck is sorting/deduplication or DSU.
>
> **Bonus:** a deeper property of this problem is that **if you fix one initial diameter endpoint and
> always fold toward it, then it will always remain a diameter endpoint.** The folding process can
> then be maintained with a **mergeable heap (可并堆)**, giving $O(N\log N)$.

### 2.3 What the editorial does and does not give

* ✅ It **confirms the invariance claim** ("无论怎么操作，操作次数一定相同") as a proven fact.
* ✅ It gives the **bonus lemma that `REF.md` hypothesised, verbatim**:
  *fix an initial diameter endpoint; fold toward it every time ⟹ it stays a diameter endpoint
  forever* (and the process can be maintained with a mergeable heap).
* ✅ It gives the structural fact used to bound complexity: **Σ over the process of (diameter length)
  = O(N)**, because the vertex count removed by a fold is Θ(diameter). Consequently the number of
  *distinct* diameter values occurring is $O(\sqrt N)$, since distinct values form a strictly
  decreasing sequence and the sum of $1+2+\dots+k$ is already $k^2/2$.
* ❌ It does **not** state an explicit invariant, potential function, or closed-form formula for the
  number of folds. The proof of invariance is *one sentence*: two strategies may yield non-isomorphic
  trees, but differently-shaped subtrees inevitably become same-shaped before they can influence the
  remaining count.
* The sentence "则一次操作会将直径长度减少" has **no formula after 减少** in the PDF — a quantity
  appears to have been dropped in typesetting. (Visually verified by rendering the page at 320 dpi;
  see `official-tutorial-F-section.png`.)

---

## 3. Independent verification (my own computation, not from the web)

Script kept at `research/verify_invariance.py` (`python3 verify_invariance.py`).

* Implemented the operation literally: vertex classes merge along `d_i ↦ d_{min(i,k−i+1)}`,
  self-loops vanish, parallel edges dedup, tree stays a tree.
* **Model reproduces all three official samples exactly**: `0`, `3`, `7`.
* **Exhaustive over all labelled trees with n ≤ 8** (281 393 trees): the *set* of achievable
  operation counts over all strategies is **always a singleton**.
* **3 000 random trees, 2 ≤ n ≤ 14**: also always a singleton.

So the invariance theorem in `REF.md` is **empirically confirmed**; the "maximum" in the statement
is the unique value.

Sample data (F = number of folds), useful for sanity-checking a formalisation:

```
P_1..P_9 : 0, 1, 2, 2, 3, 3, 3, 3, 4      (F(P_n) = ceil(log2 n))
K_{1,2..7}: 2, 3, 4, 5, 6, 7              (F(K_{1,m}) = m)
S(2,2,1)=3  S(2,2,2)=4  S(3,3,1)=4  S(4,4,1)=4  S(7,7,1)=5
```

Note `F(P_4) = 2` but `F(K_{1,3}) = 3` for two 4-vertex trees ⇒ **F is not a function of N or of the
diameter alone**; any potential function must see more structure.

---

## 4. Discussion threads, blogs, other proofs

* **QOJ contest 4113 → Discussions & Issues: empty** (0 discussions, 0 issues) as of 2026-09-15.
* Third-party contest write-ups exist for the same contest but **none covers problem F**:
  * <https://www.cnblogs.com/Mercury-City/p/22964635> — "The 2026 ICPC Asia East Continent Online Contest (II) 解题报告" (covers A, H)
  * <https://www.cnblogs.com/Simon-Gao/p/22957946> — "2026 ICPC Asia EC网络预选赛 - 第二场" (covers E)
  * <https://blog.csdn.net/2501_94316951/article/details/165127073> — CSDN, covers K (K-MEX)
  * <https://www.cnblogs.com/mod998244353/p/22969723> — covers I (Island)
* **No English editorial, no Codeforces blog entry, no Luogu entry** for this problem was found.
  (The gym problem page's Luogu/VJudge links both read "未找到" / not found.)
* Unrelated problems with similar names, checked and excluded:
  * Codeforces 765E "Tree Folding" — folds away equal-length hanging paths; different operation.
  * ICPC Japan domestic 2017 "Folding a Ribbon"; 2020 ICPC Taiwan Online "Folding".
  * An early false lead: 2021 CCPC Harbin problem K — that is about Euler's theorem, not trees.

---

## 5. All URLs used

1. <https://qoj.ac/problem/20241> — original problem, The 2026 ICPC Asia East Continent Online Contest (II) F
2. <https://qoj.ac/contest/4113> — that contest's dashboard on QOJ
3. <https://codeforces.com/gym/106701/problem/F> — same problem mirrored on Codeforces Gym
4. <https://codeforces.com/gym/106701/attachments/download/39422/sol.pdf> — **official tutorial (zh)**, source of §2
5. <https://www.cnblogs.com/Mercury-City/p/22964635> — contest write-up (A, H)
6. <https://www.cnblogs.com/Simon-Gao/p/22957946> — contest write-up (E)
7. <https://blog.csdn.net/2501_94316951/article/details/165127073> — contest write-up (K)
8. <https://www.cnblogs.com/mod998244353/p/22969723> — contest write-up (I)
