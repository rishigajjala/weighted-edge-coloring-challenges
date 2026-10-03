import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Adding an edge inside one component does not change reachability
-/

namespace WeightedEdgeColoring
namespace SimpleGraph

universe u

variable {V : Type u}

/-- Deleting one existing simple edge and then adjoining it recovers the
original graph. -/
theorem deleteEdges_sup_edge_eq_of_adj
    (H : _root_.SimpleGraph V) {x z : V} (hxz : H.Adj x z) :
    H.deleteEdges {s(x, z)} ⊔ _root_.SimpleGraph.edge x z = H := by
  ext u v
  constructor
  · intro huv
    change (H.deleteEdges {s(x, z)}).Adj u v ∨
      (_root_.SimpleGraph.edge x z).Adj u v at huv
    rcases huv with huv | huv
    · exact (H.deleteEdges_le {s(x, z)}) huv
    · have hends :
          (u = x ∧ v = z) ∨ (u = z ∧ v = x) := by
        have hends' :
            ((u = x ∧ v = z) ∨ (u = z ∧ v = x)) ∧ u ≠ v := by
          simpa [_root_.SimpleGraph.edge] using huv
        exact hends'.1
      rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxz
      · exact hxz.symm
  · intro huv
    by_cases hp : s(u, v) = s(x, z)
    · right
      rcases Sym2.eq_iff.mp hp with h | h
      · simpa [h.1, h.2, _root_.SimpleGraph.edge] using hxz.ne
      · simpa [h.1, h.2, _root_.SimpleGraph.edge] using hxz.ne.symm
    · left
      rw [_root_.SimpleGraph.deleteEdges_adj]
      exact ⟨huv, by simpa using hp⟩

/-- If `x` and `y` are already connected, adjoining the edge `xy` does
not change which pairs of vertices are connected. -/
theorem reachable_sup_edge_iff_of_reachable
    (H : _root_.SimpleGraph V) {x y u v : V}
    (hxy : H.Reachable x y) :
    (H ⊔ _root_.SimpleGraph.edge x y).Reachable u v ↔
      H.Reachable u v := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact ⟨.nil⟩
    | @cons u w v huw p ih =>
        have huwReach : H.Reachable u w := by
          change H.Adj u w ∨ (_root_.SimpleGraph.edge x y).Adj u w at huw
          rcases huw with huw | huw
          · exact huw.reachable
          · have hends :
                (u = x ∧ w = y) ∨ (u = y ∧ w = x) := by
              have hends' :
                  ((u = x ∧ w = y) ∨ (u = y ∧ w = x)) ∧ u ≠ w := by
                simpa [_root_.SimpleGraph.edge] using huw
              exact hends'.1
            rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hxy
            · exact hxy.symm
        exact huwReach.trans ih
  · exact fun h ↦ h.mono le_sup_left

/-- A walk to `x` after adjoining `xz` started in the old component of
either `x` or `z`.  This is the component-side dichotomy for a cut edge. -/
theorem reachable_left_or_right_of_reachable_sup_edge
    (H : _root_.SimpleGraph V) {x z y : V}
    (h : (H ⊔ _root_.SimpleGraph.edge x z).Reachable y x) :
    H.Reachable y x ∨ H.Reachable y z := by
  rcases h with ⟨p⟩
  have aux : ∀ {u v : V},
      (H ⊔ _root_.SimpleGraph.edge x z).Walk u v → v = x →
        H.Reachable x u ∨ H.Reachable z u := by
    intro u v q
    induction q with
    | nil =>
        intro hu
        exact Or.inl (by simpa [hu] using
          (_root_.SimpleGraph.Reachable.refl x))
    | @cons u w v huw q ih =>
        intro hv
        have ih' := ih hv
        change H.Adj u w ∨ (_root_.SimpleGraph.edge x z).Adj u w at huw
        rcases huw with huw | huw
        · rcases ih' with hxw | hzw
          · exact Or.inl (hxw.trans huw.symm.reachable)
          · exact Or.inr (hzw.trans huw.symm.reachable)
        · have hends :
              (u = x ∧ w = z) ∨ (u = z ∧ w = x) := by
            have hends' :
                ((u = x ∧ w = z) ∨ (u = z ∧ w = x)) ∧ u ≠ w := by
              simpa [_root_.SimpleGraph.edge] using huw
            exact hends'.1
          rcases hends with hdirect | hswap
          · exact Or.inl (by simpa [hdirect.1] using
              (_root_.SimpleGraph.Reachable.refl x))
          · exact Or.inr (by simpa [hswap.1] using
              (_root_.SimpleGraph.Reachable.refl z))
  have hsymmetric : H.Reachable x y ∨ H.Reachable z y := aux p rfl
  exact hsymmetric.imp
    _root_.SimpleGraph.Reachable.symm
    _root_.SimpleGraph.Reachable.symm

/-- Deleting an edge of a tree puts every vertex on one of its two sides. -/
theorem reachable_endpoint_or_endpoint_deleteEdges_of_isTree
    (H : _root_.SimpleGraph V) (htree : H.IsTree)
    {x z y : V} (hxz : H.Adj x z) :
    (H.deleteEdges {s(x, z)}).Reachable y x ∨
      (H.deleteEdges {s(x, z)}).Reachable y z := by
  let D := H.deleteEdges {s(x, z)}
  have hyx : H.Reachable y x := htree.1.preconnected y x
  have hrecover : D ⊔ _root_.SimpleGraph.edge x z = H := by
    simpa [D] using deleteEdges_sup_edge_eq_of_adj H hxz
  have hyx' : (D ⊔ _root_.SimpleGraph.edge x z).Reachable y x := by
    simpa [hrecover] using hyx
  exact reachable_left_or_right_of_reachable_sup_edge D hyx'

/-- In the preceding dichotomy the two alternatives are exclusive. -/
theorem not_reachable_other_endpoint_of_isTree
    (H : _root_.SimpleGraph V) (htree : H.IsTree)
    {x z y : V} (hxz : H.Adj x z)
    (hyx : (H.deleteEdges {s(x, z)}).Reachable y x) :
    ¬(H.deleteEdges {s(x, z)}).Reachable y z := by
  intro hyz
  have hxzDelete := hyx.symm.trans hyz
  have hbridge : H.IsBridge s(x, z) :=
    (_root_.SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp htree.2) hxz
  exact (H.isBridge_iff.mp hbridge).2 hxzDelete

/-- A subgraph of a cut graph plus an edge internal to one cut side still
cannot reach the other side. -/
theorem not_reachable_of_le_sup_edge_of_reachable
    (D H' : _root_.SimpleGraph V) {x y z : V}
    (hxy : D.Reachable x y) (hyz : ¬D.Reachable y z)
    (hle : H' ≤ D ⊔ _root_.SimpleGraph.edge x y) :
    ¬H'.Reachable y z := by
  intro hreach
  have hsup : (D ⊔ _root_.SimpleGraph.edge x y).Reachable y z :=
    hreach.mono hle
  have hD : D.Reachable y z :=
    (reachable_sup_edge_iff_of_reachable D hxy).mp hsup
  exact hyz hD

end SimpleGraph
end WeightedEdgeColoring
