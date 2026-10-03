import WeightedEdgeColoring.KempeComponentEndpoints
import WeightedEdgeColoring.SimpleGraphDegreeTwoTree

/-!
# A two-colour component with an active vertex is a tree

In a proper colouring every two-colour component has maximum degree two.
If one vertex misses exactly one of the two colours, it has degree one.
The handshaking lemma supplies a second odd-degree vertex; its degree is
also one.  The component is therefore a tree.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

noncomputable local instance activeTreeDecidableSimpleGraphAdj
    (H : SimpleGraph G.V) : DecidableRel H.Adj :=
  Classical.decRel _

noncomputable local instance activeTreeDecidableSetMembership (s : Set G.V) :
    DecidablePred (fun v : G.V ↦ v ∈ s) :=
  Classical.decPred _

noncomputable local instance activeTreeFiniteConnectedComponentSupport
    (H : SimpleGraph G.V) (C : H.ConnectedComponent) : Fintype C :=
  @Subtype.fintype G.V (fun v ↦ v ∈ C.supp)
    (activeTreeDecidableSetMembership G C.supp) G.instFintypeV

/-- A connected two-colour component containing an active vertex is a tree. -/
theorem twoColorComponent_isTree_of_active
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    (hproper : G.IsProperOn F color) {a b : Fin k}
    (C : G.TwoColorComponent F color a b)
    (y : G.V) (hyC : y ∈ C.supp)
    (hyActive : G.IsTwoColorActive F color a b y) :
    C.toSimpleGraph.IsTree := by
  classical
  let H := G.twoColorGraph F color a b
  have hcomponentNeighborSubset (v : C) : H.neighborSet v.1 ⊆ C.supp := by
    intro w hw
    exact (C.mem_supp_congr_adj hw).mp v.2
  have hcomponentDegree (v : C) :
      C.toSimpleGraph.degree v = H.degree v.1 := by
    change (H.induce C.supp).degree v = H.degree v.1
    exact H.degree_induce_of_neighborSet_subset (hcomponentNeighborSubset v)
  have hcomponentMax (v : C) : C.toSimpleGraph.degree v ≤ 2 := by
    rw [hcomponentDegree v]
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      F color hproper a b v.1
  let Y : C := ⟨y, hyC⟩
  have hYone : C.toSimpleGraph.degree Y = 1 := by
    rw [hcomponentDegree Y]
    exact G.twoColorGraph_degree_eq_one_of_active
      F color hproper a b y hyActive
  obtain ⟨Z, hZY, hZodd⟩ :=
    C.toSimpleGraph.exists_ne_odd_degree_of_exists_odd_degree Y (by
      simpa [hYone])
  have hZone : C.toSimpleGraph.degree Z = 1 := by
    have hle := hcomponentMax Z
    rcases hZodd with ⟨m, hm⟩
    omega
  exact WeightedEdgeColoring.SimpleGraph.isTree_of_connected_of_degree_le_two_of_two_degree_one
    C.toSimpleGraph C.connected_toSimpleGraph hcomponentMax hZY.symm
      hYone hZone

end WeightedMultigraph
end WeightedEdgeColoring
