import InverseGreedy.EdgeSetGraphs

/-!
# S043: formal Boolean edge encoding of every six-vertex simple graph

The rank/pair tables give the 15 canonical undirected vertex pairs of
`Fin 6`. Together with the proved generic `nbOf_fOf`, every symmetric,
loop-free six-vertex neighbour map has a 15-bit Boolean encoding.

This is an encoding theorem, not an exhaustive Lean orbit certificate.
-/

namespace InverseGreedy

/-- Lexicographically ordered undirected edges on six vertices. -/
def pair6 : Fin 15 → Fin 6 × Fin 6 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
    (1, 2), (1, 3), (1, 4), (1, 5),
    (2, 3), (2, 4), (2, 5),
    (3, 4), (3, 5), (4, 5)]

/-- Edge index for `i < j`; unused entries are zero. -/
def rank6 : Fin 6 → Fin 6 → Fin 15 :=
  ![![0, 0, 1, 2, 3, 4],
    ![0, 0, 5, 6, 7, 8],
    ![0, 0, 0, 9, 10, 11],
    ![0, 0, 0, 0, 12, 13],
    ![0, 0, 0, 0, 0, 14],
    ![0, 0, 0, 0, 0, 0]]

theorem pair6_rank6 (i j : Fin 6) (h : i < j) :
    pair6 (rank6 i j) = (i, j) := by
  revert i j
  decide +kernel

/-- All undirected simple graphs on six vertices arise from 15 bits. -/
theorem every_fin6_graph_is_edge_vector (nb : Fin 6 → Finset (Fin 6))
    (hs : ∀ x y, y ∈ nb x → x ∈ nb y)
    (hi : ∀ v, v ∉ nb v) :
    nbOf rank6 (fOf pair6 nb) = nb :=
  nbOf_fOf rank6 pair6 pair6_rank6 nb hs hi

end InverseGreedy
