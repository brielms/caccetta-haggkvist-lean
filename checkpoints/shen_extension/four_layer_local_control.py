"""Local control for the complete four layers with one exterior vertex.

Labels: short rows a b c, middles x j, targets u w z, exterior vertex m.
Fixed arcs: x, j -> a, b, c;  u, w, z -> x, j;  u, w, z -> m;  m -> a.
Options: x -> j or not; m -> x, m -> j, both, or m absent; the shape of the
arcs among the three targets.

An edit adds arcs from a row, a middle or m to a target and cuts old arcs
between labels. It is valid when no directed cycle of length at most three
remains on the labels, every row gains one arc net, and every other label
loses at most one arc net.

This is a model of the nine labels only. It does not model returns through
other vertices, and it only allows new heads inside the chosen triple. A
count of zero means: no edit of that kind exists on these labels. It is not
a statement about a source.

Run:  python four_layer_local_control.py        (needs ortools)
"""
import itertools
from ortools.sat.python import cp_model

L = ['a', 'b', 'c', 'x', 'j', 'u', 'w', 'z', 'm']
ROWS, MID, T = ['a', 'b', 'c'], ['x', 'j'], ['u', 'w', 'z']

SHAPES = {
    'no arcs (3 sinks)': set(),
    'u>w (2 sinks)': {('u', 'w')},
    'u>w u>z (2 sinks)': {('u', 'w'), ('u', 'z')},
    'u>w z>w (1 sink)': {('u', 'w'), ('z', 'w')},
    'u>z>w path (1 sink)': {('u', 'z'), ('z', 'w')},
    'u>z>w u>w transitive (1 sink)': {('u', 'z'), ('z', 'w'), ('u', 'w')},
}


def arcs(shape, xj, m_mode):
    A = set(SHAPES[shape])
    for mid in MID:
        A |= {(mid, r) for r in ROWS} | {(t, mid) for t in T}
    if xj:
        A.add(('x', 'j'))
    if m_mode != 'absent':
        A |= {(t, 'm') for t in T} | {('m', 'a')}
        if 'x' in m_mode:
            A.add(('m', 'x'))
        if 'j' in m_mode:
            A.add(('m', 'j'))
    return A


def edits(A, sources, limit=400):
    mdl = cp_model.CpModel()
    new = {(s, t): mdl.NewBoolVar(f"n_{s}{t}") for s in sources for t in T}
    cut = {e: mdl.NewBoolVar(f"c_{e[0]}{e[1]}") for e in A}

    def present(i, k):
        lits = []
        if (i, k) in new:
            lits.append(new[i, k])
        if (i, k) in A:
            lits.append(cut[i, k].Not())
        return lits

    for i, k in itertools.combinations(L, 2):
        for p in present(i, k):
            for q in present(k, i):
                mdl.AddBoolOr([p.Not(), q.Not()])
    for i, k, l in itertools.permutations(L, 3):
        if i < k and i < l:
            for p in present(i, k):
                for q in present(k, l):
                    for r in present(l, i):
                        mdl.AddBoolOr([p.Not(), q.Not(), r.Not()])
    for v in L:
        gain = sum(new[v, t] for t in T if (v, t) in new)
        loss = sum(cut[e] for e in A if e[0] == v)
        mdl.Add(gain - loss >= (1 if v in ROWS else -1))
    for r in ROWS:
        mdl.Add(sum(new[r, t] for t in T) == 1)
    for e in new:
        if e in A:
            mdl.Add(new[e] == 0)

    found = []

    class Collect(cp_model.CpSolverSolutionCallback):
        def on_solution_callback(self):
            found.append((tuple(sorted(k for k in new if self.Value(new[k]))),
                          tuple(sorted(k for k in cut if self.Value(cut[k])))))
            if len(found) >= limit:
                self.StopSearch()

    solver = cp_model.CpSolver()
    solver.parameters.enumerate_all_solutions = True
    solver.parameters.num_workers = 1
    solver.Solve(mdl, Collect())
    return found, len(found) >= limit


def show(arc_list):
    return ' '.join(s + '>' + t for s, t in arc_list)


if __name__ == '__main__':
    print("number of distinct sets of new arcs (0 = no edit on these labels;")
    print("a trailing + means the enumeration stopped at its limit)")
    for shape in SHAPES:
        for xj in (True, False):
            cells = []
            for m_mode in ('absent', 'x', 'j', 'xj'):
                src = ROWS + MID + ([] if m_mode == 'absent' else ['m'])
                found, more = edits(arcs(shape, xj, m_mode), src)
                count = f"{len({n for n, _ in found})}{'+' if more else ''}"
                cells.append(f"m->{m_mode}: {count}" if m_mode != 'absent'
                             else f"no m: {count}")
            print(f"  {shape:30s} x>j={str(xj):5s}  " + '   '.join(cells))
    print()
    print("the edits left when m points to x only, one sink, x>j:")
    for shape in list(SHAPES)[3:]:
        for n, c in edits(arcs(shape, True, 'x'), ROWS + MID + ['m'])[0]:
            print(f"  {shape}: new {show(n)} | cut {show(c)}")
