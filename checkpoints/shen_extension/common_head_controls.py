#!/usr/bin/env python3
"""Finite controls for the common-head return theorem.

Run with plain Python. The first family uses powers of the directed (q+1)-cycle.
The second uses the 29-vertex circulant of Balister and Bollobas, Pair dominating
graphs, https://www.memphis.edu/msci/people/pbalistr/pairdom.pdf (p. 3). Its
four-cycle substitution also has a common predecessor for every vertex pair.
Both computations are outside the critical order.
"""

from itertools import combinations, product


def cycle_power(q):
    base = q + 1
    words = list(product(range(base), repeat=3))

    def arc(x, y):
        for a, b in zip(x, y):
            if a != b:
                return (b - a) % base == 1
        return False

    out = [{i for i, y in enumerate(words) if arc(x, y)} for x in words]
    n = len(words)
    s = (n - 1) // q
    assert all(len(row) == s for row in out)
    # The bank consists of 000 and 001.
    p, h = 0, 1
    survivors = set(range(n)) - {p, h}
    targets = out[p] & out[h]
    shorts = {u for u in survivors if {p, h} <= out[u]}
    assert len(targets) == max(len(a & b) for a, b in combinations(out, 2)) == s - 1

    def level(v):
        return next(j for j, digit in enumerate(words[v]) if digit)

    for u in shorts:
        j = level(u)
        offers = targets - out[u]
        assert offers == {z for z in targets if level(z) == j}
        width = base ** (2 - j)
        assert len(offers) == len({v for v in shorts if level(v) == j}) == width
        blocks = [
            {v for v in survivors if words[v][:j] == (0,) * j and words[v][j] == digit}
            for digit in range(2, base - 1)
        ]
        assert all(len(block) == width for block in blocks)
        for z in offers:
            layers = [{z}, *blocks, {u}]
            assert all(all(right <= out[x] for x in left) for left, right in zip(layers, layers[1:]))
    # Every terminal in the same level chooses a target in that level. Thus all
    # last arcs occur on some assigned return, regardless of the assignment.
    minimum = min(base ** (2 - level(u)) for u in shorts) ** (q - 1)
    print(f"Cycle power: q={q}, n={n}, s={s}, order excess={n-(q*(s-1)+2)}, walks>={minimum}")


def pair_dominating_product():
    steps = {2, 3, 11, 14, 17, 19, 21}
    order = 29
    base = [{(v + d) % order for d in steps} for v in range(order)]
    before = [{v for v in range(order) if u in base[v]} for u in range(order)]
    pool = set()
    for u in before[0]:
        for z in base[0] - base[u]:
            middles = base[z] & before[u]
            assert len(middles) >= 2
            pool.update(middles)
    assert len(pool) == 14

    graph = [
        {4*y + j for y in row for j in range(4)} | {4*i + (c+1) % 4}
        for i, row in enumerate(base) for c in range(4)
    ]
    vertices = range(len(graph))
    parents = [{v for v in vertices if u in graph[v]} for u in vertices]
    assert len(graph) == len({frozenset(row) for row in graph}) == 116
    assert all(len(row) == 29 for row in graph + parents)
    assert all(parents[a] & parents[b] for a, b in combinations(vertices, 2))
    assert all(i not in graph[i] and graph[i].isdisjoint(parents[i]) for i in vertices)
    assert all(parents[i].isdisjoint(graph[j]) for i in vertices for j in graph[i])

    maximum = max(len(graph[a] & graph[b]) for a, b in combinations(vertices, 2))
    banks = [(a,b) for a,b in combinations(vertices, 2) if len(graph[a] & graph[b]) == maximum]
    assert maximum == 28 and len(banks) == 174
    for a, b in banks:
        assert a // 4 == b // 4
        targets = graph[a] & graph[b]
        shorts = parents[a] & parents[b]
        pool_here = {(a//4 + shift) % order for shift in pool}
        assert len(shorts) == 28
        for u in shorts:
            assert len(targets - graph[u]) == 20
            for z in targets - graph[u]:
                middles = graph[z] & parents[u]
                full_classes = {k for k in pool_here if {4*k+j for j in range(4)} <= middles}
                assert len(full_classes) >= 2
    # 28 rows each use >=2 of 14 classes, so one class serves >=4 distinct
    # rows. All 4 physical middles in the class serve all these rows. A target
    # chosen by any one of them reaches all four middles via assigned arcs.
    print(f"Pair-dominating product: n=116, s=29, banks={len(banks)}, walks>=16, critical order=86")


if __name__ == "__main__":
    for cutoff in (3, 4, 5):
        cycle_power(cutoff)
    pair_dominating_product()
