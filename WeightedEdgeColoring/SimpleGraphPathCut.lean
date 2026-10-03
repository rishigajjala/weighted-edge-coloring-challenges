import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Cutting an edge of the unique path in a tree

This is the small path fact used after recolouring one edge of a critical
Kempe chain.  Any graph contained in the tree with an edge of its unique
`x,y` path deleted cannot connect `x` to `y`.
-/

namespace WeightedEdgeColoring
namespace SimpleGraph

universe u

variable {V : Type u} [DecidableEq V]

theorem not_reachable_of_le_deleteEdges_of_mem_path
    (H H' : _root_.SimpleGraph V)
    (htree : H.IsTree) {x y u v : V}
    (p : H.Path x y) (huv : s(u, v) ∈ p.1.edges)
    (hle : H' ≤ H.deleteEdges {s(u, v)}) :
    ¬H'.Reachable x y := by
  intro hreach
  rcases hreach with ⟨q⟩
  let qD : (H.deleteEdges {s(u, v)}).Walk x y := q.mapLe hle
  let qH : H.Walk x y := qD.mapLe (H.deleteEdges_le {s(u, v)})
  have hnot : s(u, v) ∉ qD.edges := by
    intro hmem
    have hedgeSet := qD.edges_subset_edgeSet hmem
    rw [H.edgeSet_deleteEdges] at hedgeSet
    exact hedgeSet.2 (by simp)
  have hpathEq : qH.toPath = p :=
    htree.2.path_unique qH.toPath p
  have hinPath : s(u, v) ∈ qH.toPath.1.edges := by
    rw [hpathEq]
    exact huv
  have hinWalk : s(u, v) ∈ qH.edges :=
    qH.edges_toPath_subset hinPath
  apply hnot
  simpa [qH, qD] using hinWalk

/-- Every vertex visited by a walk that starts in a connected component
stays in that component. -/
theorem walk_support_subset_connectedComponent
    (H : _root_.SimpleGraph V) (C : H.ConnectedComponent)
    {x y : V} (hx : x ∈ C.supp) (p : H.Walk x y) :
    ∀ z ∈ p.support, z ∈ C.supp := by
  induction p with
  | nil => simpa
  | @cons x w y hxw p ih =>
      intro z hz
      simp only [_root_.SimpleGraph.Walk.support, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hx
      · apply ih
        · exact (C.mem_supp_congr_adj hxw).mp hx
        · exact hz

/-- Equality of connected-component names gives a concrete walk. -/
theorem reachable_of_connectedComponentMk_eq
    (H : _root_.SimpleGraph V) {x y : V}
    (hxy : H.connectedComponentMk x = H.connectedComponentMk y) :
    H.Reachable x y := by
  let C : H.ConnectedComponent := H.connectedComponentMk x
  have hxC : x ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hyC : y ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact hxy.symm
  let X : C := ⟨x, hxC⟩
  let Y : C := ⟨y, hyC⟩
  rcases C.connected_toSimpleGraph.preconnected X Y with ⟨p⟩
  exact ⟨p.map (_root_.SimpleGraph.Embedding.induce C.supp).toHom⟩

/-- Component form of the path-cut lemma.  The ambient graph may have
cyclic components elsewhere; only the component containing the displayed
path is required to be a tree. -/
theorem not_reachable_of_le_deleteEdges_of_mem_componentPath
    (H H' : _root_.SimpleGraph V) (C : H.ConnectedComponent)
    (htree : C.toSimpleGraph.IsTree)
    (X Y U W : C) (p : C.toSimpleGraph.Path X Y)
    (hUW : s(U, W) ∈ p.1.edges)
    (hle : H' ≤ H.deleteEdges {s(U.1, W.1)}) :
    ¬H'.Reachable X.1 Y.1 := by
  intro hreach
  rcases hreach with ⟨q⟩
  let qD : (H.deleteEdges {s(U.1, W.1)}).Walk X.1 Y.1 := q.mapLe hle
  let qH : H.Walk X.1 Y.1 :=
    qD.mapLe (H.deleteEdges_le {s(U.1, W.1)})
  have hnot : s(U.1, W.1) ∉ qH.edges := by
    intro hmem
    have hmemD : s(U.1, W.1) ∈ qD.edges := by
      simpa [qH] using hmem
    have hedgeSet := qD.edges_subset_edgeSet hmemD
    rw [H.edgeSet_deleteEdges] at hedgeSet
    exact hedgeSet.2 (by simp)
  have hsupp : ∀ z ∈ qH.support, z ∈ C.supp :=
    walk_support_subset_connectedComponent H C X.2 qH
  let qC0 := qH.induce C.supp hsupp
  let qC : C.toSimpleGraph.Walk X Y :=
    qC0.copy (Subtype.ext (by rfl)) (Subtype.ext (by rfl))
  have hpathEq : qC.toPath = p :=
    htree.2.path_unique qC.toPath p
  have hinPath : s(U, W) ∈ qC.toPath.1.edges := by
    rw [hpathEq]
    exact hUW
  have hinQC : s(U, W) ∈ qC.edges :=
    qC.edges_toPath_subset hinPath
  have hinMapped :
      s(U.1, W.1) ∈
        (qC.map (_root_.SimpleGraph.Embedding.induce C.supp).toHom).edges := by
    rw [_root_.SimpleGraph.Walk.edges_map]
    apply List.mem_map.mpr
    exact ⟨s(U, W), hinQC, by simp⟩
  apply hnot
  simpa [qC, qC0, qH] using hinMapped

end SimpleGraph
end WeightedEdgeColoring
