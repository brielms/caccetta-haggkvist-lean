"""Controls for the cyclic layer count (CyclicLayerCount.lean).

Both graphs are outside the critical order, so neither is a source.

1. Lexicographic cube of the directed (q+1)-cycle (order q*s+1).
2. The 29-vertex pair-dominating circulant of Balister and Bollobas with each
   vertex replaced by a directed 4-cycle (116 vertices, degree 29, cutoff 3).

For a vertex p the layers are the steps of closed walks of length q+1 through
p. A row of least internal outdegree is chosen in each layer. The script
prints the backward arcs B, the repeated exterior heads D and the number o of
vertices outside the layers.

For the second graph it also tests every pair {a, b} as a replacement bank:
short rows = common predecessors, targets = common heads. An assignment of a
missed target to every short row is clash-free when no vertex y has y -> u,
y -> v, f(u) -> y and f(v) -> y for two rows u, v. In a source a clash-free
assignment would give a host.

Run:  python layer_count_controls.py        (needs ortools for part 2)
"""
import itertools
from itertools import product


def cycle_power(q, depth=3):
    base = q + 1
    words = list(product(range(base), repeat=depth))

    def arc(x, y):
        for a, b in zip(x, y):
            if a != b:
                return (b - a) % base == 1
        return False

    return [{i for i, y in enumerate(words) if arc(x, y)} for x in words]


def pair_dominating_product():
    steps = {2, 3, 11, 14, 17, 19, 21}
    base = [{(v + d) % 29 for d in steps} for v in range(29)]
    return [{4 * y + j for y in row for j in range(4)} | {4 * i + (c + 1) % 4}
            for i, row in enumerate(base) for c in range(4)]


def parents(out):
    inn = [set() for _ in out]
    for u, row in enumerate(out):
        for v in row:
            inn[v].add(u)
    return inn


def layer_report(out, p, q, name):
    n, s = len(out), len(out[0])
    inn = parents(out)
    fwd, bwd = [{p}], [{p}]
    for _ in range(q):
        fwd.append(set().union(*(out[v] for v in fwd[-1])))
        bwd.append(set().union(*(inn[v] for v in bwd[-1])))
    L = [fwd[j] & bwd[q + 1 - j] for j in range(1, q + 1)] + [{p}]
    inside = set().union(*L)
    rows = [min(sorted(L[i]), key=lambda x: len(out[x] & L[i])) for i in range(q)] + [p]
    back = []
    for i in range(q + 1):
        earlier = set().union(*([set()] + (L[1:q] if i == q else L[:i])))
        back.append(len(out[rows[i]] & earlier))
    ext = [out[r] - inside for r in rows]
    D = sum(len(e) for e in ext) - len(set().union(*ext))
    into_first = [len(out[rows[i]] & L[0]) for i in range(1, q)]
    common_with_p = [len(out[rows[i]] & out[p]) for i in range(1, q)]
    crit = q * (s - 1) + 2
    print(f"{name}: n={n} s={s} critical order={crit} layers={[len(x) for x in L]} o={n - len(inside)}")
    print(f"    internal={[len(out[rows[i]] & L[i]) for i in range(q + 1)]} backward={back} "
          f"B={sum(back)} D={D}")
    print(f"    backward arcs of rows 2..q into layer 1: {into_first}; "
          f"their common heads with p: {common_with_p}")


def clash_free(out, inn, a, b, seconds=20.0):
    from ortools.sat.python import cp_model
    S = sorted(inn[a] & inn[b])
    T = sorted(out[a] & out[b])
    dom = {u: [z for z in T if z not in out[u]] for u in S}
    if any(not d for d in dom.values()):
        return 'a row sees every target', len(S), len(T)
    m = cp_model.CpModel()
    x = {(u, z): m.NewBoolVar('') for u in S for z in dom[u]}
    for u in S:
        m.AddExactlyOne(x[u, z] for z in dom[u])
    for u, v in itertools.combinations(S, 2):
        ys = inn[u] & inn[v]
        for z in dom[u]:
            for z2 in dom[v]:
                if any(y in out[z] and y in out[z2] for y in ys):
                    m.AddBoolOr([x[u, z].Not(), x[v, z2].Not()])
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    status = solver.StatusName(solver.Solve(m))
    return {'INFEASIBLE': 'no clash-free assignment', 'OPTIMAL': 'clash-free assignment',
            'FEASIBLE': 'clash-free assignment'}.get(status, status), len(S), len(T)


if __name__ == '__main__':
    for q in (3, 4):
        layer_report(cycle_power(q), 0, q, f"cycle power, q={q}")
    G = pair_dominating_product()
    layer_report(G, 0, 3, "pair-dominating product")
    inn = parents(G)
    tally = {}
    # rotation of the circulant moves any vertex into class 0
    for a in range(4):
        for b in range(a + 1, len(G)):
            key = clash_free(G, inn, a, b)
            tally[key] = tally.get(key, 0) + 1
    print("pair-dominating product, every pair with one vertex in class 0 as a bank")
    print("  (outcome, short rows, common heads): count")
    for key in sorted(tally):
        print("  ", key, tally[key])
