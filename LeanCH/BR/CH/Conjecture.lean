namespace CH

/--
A directed graph on natural-number labels.

For an order-`n` graph, only labels strictly below `n` are vertices. Keeping
the bound as an explicit proposition avoids proof-valued subtype fields.
The Boolean edge relation is computational, and parallel arcs are absent
because an ordered pair has one edge value.
-/
abbrev Digraph := Nat → Nat → Bool

/-- The order-`n` graph has no directed loops. -/
def Loopless (G : Digraph) (n : Nat) : Prop :=
  ∀ v, v < n → G v v = false

/--
Vertex `v` has at least `r` distinct out-neighbours.

A duplicate-free list of exactly `r` bounded vertices is a direct
cardinality witness.
-/
def OutdegreeAtLeast (G : Digraph) (n v r : Nat) : Prop :=
  ∃ neighbours : List Nat,
    neighbours.length = r ∧
    neighbours.Nodup ∧
    ∀ w, w ∈ neighbours → w < n ∧ G v w = true

/-- Every vertex has at least `r` distinct out-neighbours. -/
def MinOutdegreeAtLeast (G : Digraph) (n r : Nat) : Prop :=
  ∀ v, v < n → OutdegreeAtLeast G n v r

/-- Check the directed edges between consecutive entries of a list. -/
def EdgesFrom (G : Digraph) (previous : Nat) :
    List Nat → Prop
  | [] => True
  | next :: rest => G previous next = true ∧ EdgesFrom G next rest

/--
`vertices` lists the vertices of a simple directed cycle in cyclic order.

The tail must be nonempty, so cycle length is at least two. `Nodup` makes
the cycle simple. The final conjunct closes the last vertex back to the
first.
-/
def IsDirectedCycle (G : Digraph) (n : Nat) :
    List Nat → Prop
  | [] => False
  | first :: rest =>
      rest ≠ [] ∧
      (first :: rest).Nodup ∧
      (∀ v, v ∈ first :: rest → v < n) ∧
      EdgesFrom G first rest ∧
      G (rest.getLastD first) first = true

/-- The graph has a simple directed cycle of length at most `bound`. -/
def HasDirectedCycleAtMost (G : Digraph) (n bound : Nat) : Prop :=
  ∃ vertices : List Nat,
    IsDirectedCycle G n vertices ∧ vertices.length ≤ bound

/--
There is no bounded directed cycle in a graph of order zero.

This regression theorem makes explicit why the conventional positive-order
hypothesis cannot be omitted merely because minimum outdegree is positive:
our universal minimum-degree predicate is vacuous when there are no vertices.
-/
theorem noDirectedCycleAtOrderZero (G : Digraph) (bound : Nat) :
    ¬HasDirectedCycleAtMost G 0 bound := by
  intro witness
  obtain ⟨vertices, cycle, _⟩ := witness
  cases vertices with
  | nil =>
      exact cycle
  | cons first rest =>
      have impossible : first < 0 :=
        cycle.2.2.1 first (List.Mem.head rest)
      exact (Nat.not_lt_zero first) impossible

/--
Ceiling division for a positive denominator.

The conjecture quantifies over `0 < n` and `0 < r`; positivity of `r` is the
condition under which this is the ordinary natural-number ceiling of `n / r`.
-/
def ceilDiv (n r : Nat) : Nat :=
  (n + r - 1) / r

/--
The standard finite simple-digraph Caccetta--Haggkvist conjecture.

This is the project's final target proposition. It is deliberately a
definition, not an asserted theorem: a completed project must construct a
term of this type. The conventional graph order and minimum outdegree
parameters are both positive.
-/
def CaccettaHaggkvistConjecture : Prop :=
  ∀ (n r : Nat) (G : Digraph),
    0 < n →
    0 < r →
    Loopless G n →
    MinOutdegreeAtLeast G n r →
    HasDirectedCycleAtMost G n (ceilDiv n r)

end CH
