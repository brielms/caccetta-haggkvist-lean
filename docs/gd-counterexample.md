# A counterexample to a joint neighborhood bound

The proposed bound (GD) asks for a vertex in a triangle-free oriented graph with both in-degree and proper second out-neighborhood size at least the minimum out-degree of the graph. The proper second out-neighborhood consists of vertices at directed distance exactly two. The stronger bound (GS) asks for both counts to be at least the out-degree of the chosen vertex. The two bounds coincide on out-regular graphs, and both fail for the graph below.

## Construction

Take six blocks B₀ through B₅ of sizes (6, 7, 5, 3, 10, 5). Label the vertices in each block from zero. Inside Bᵢ, include the forward cyclic steps from 1 through kᵢ, where k = (0, 2, 0, 0, 3, 1).

The table gives the target blocks for external arcs. Each listed pair gives all arcs from the source block to the target block, with the single restriction that arcs from B₃ to B₄ end only at labels 0 through 7.

| Source block | External targets |
| --- | --- |
| 0 | 2, 3 |
| 1 | 0 |
| 2 | 3, 5 |
| 3 | 4, labels 0 through 7 |
| 4 | 5 |
| 5 | 1 |

The graph has 36 vertices and 288 arcs. Each vertex has out-degree 8. The quotient on the six blocks has no positive closed walk of length at most three, so any digon or directed triangle would have to lie inside one block. Inside Bᵢ, a walk of length at most three advances by at most 3kᵢ < |Bᵢ| cyclically. Thus the graph has no digons or directed triangles.

## Neighborhood counts

The table counts distinct vertices. The in-degree column comes from incoming block arcs and the internal cyclic predecessors. For the last column, take the union of the out-neighborhoods of the direct successors, then remove the original vertex and its direct successors.

| Vertex block | In-degree | Proper second out-neighborhood size |
| --- | ---: | ---: |
| 0 | 7 | 13 |
| 1 | 7 | 10 |
| 2 | 6 | 15 |
| 3 | 11 | 7 |
| 4, labels 0 through 7 | 6 | 10 |
| 4, labels 8 and 9 | 3 | 10 |
| 5 | 16 | 7 |

Every vertex misses at least one bound.

For a family with minimum out-degree tending to n/3, take the circulant on 3s + 1 vertices with forward steps 1 through s, for s ≥ 1. Replace each vertex with a copy of this graph and every circulant arc with all arcs between the corresponding copies. The circulant has in-degree and out-degree s, and its proper second out-neighbors are the s vertices at offsets s + 1 through 2s. In the resulting graph, each of the three counts increases by 36s, and the same closed-walk argument rules out digons and directed triangles. Thus (GD) also fails for n = 108s + 36 = 3δ⁺ + 12, where δ⁺ = 36s + 8.
