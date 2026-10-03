import WeightedEdgeColoring.BPOrdinaryCriticalComponent
import WeightedEdgeColoring.SimpleGraphDegreeTwoTree

/-!
# A critical two-colour component is a tree

The common component of the two endpoints has maximum degree two and the
two endpoints have degree one.  Degree-sum counting therefore makes the
component a tree.  In particular, every adjacency of the critical chain is
a bridge; this is the structural fact needed when the final common-missing
pair in Andersen's Lemma 3 becomes adjacent.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

noncomputable local instance treeDecidableSimpleGraphAdj
    (H : SimpleGraph G.V) : DecidableRel H.Adj :=
  Classical.decRel _

noncomputable local instance treeDecidableSetMembership (s : Set G.V) :
    DecidablePred (fun v : G.V ↦ v ∈ s) :=
  Classical.decPred _

noncomputable local instance treeFiniteConnectedComponentSupport
    (H : SimpleGraph G.V) (C : H.ConnectedComponent) : Fintype C :=
  @Subtype.fintype G.V (fun v ↦ v ∈ C.supp)
    (treeDecidableSetMembership G C.supp) G.instFintypeV

/-- The component induced by a critical pair of endpoint-missing colours is
a finite tree. -/
theorem critical_twoColorComponent_isTree
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e)) :
    let H := G.twoColorGraph (F.erase e) color a b
    let C : H.ConnectedComponent := H.connectedComponentMk (G.fst e)
    C.toSimpleGraph.IsTree := by
  classical
  dsimp only
  let H := G.twoColorGraph (F.erase e) color a b
  let C : H.ConnectedComponent := H.connectedComponentMk (G.fst e)
  have hxycomponent := G.critical_endpoints_same_twoColorComponent
    hcritical heF hproper ha hb
  have hactive := G.critical_endpoints_twoColorActive
    hcritical heF hproper ha hb
  have hxC : G.fst e ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hyC : G.snd e ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    simpa [C, H] using hxycomponent.symm
  let X : C := ⟨G.fst e, hxC⟩
  let Y : C := ⟨G.snd e, hyC⟩
  have hXY : X ≠ Y := by
    intro h
    exact G.noLoop e (congrArg Subtype.val h)
  have hcomponentNeighborSubset (v : C) : H.neighborSet v.1 ⊆ C.supp := by
    intro w hw
    exact (C.mem_supp_congr_adj hw).mp v.2
  have hcomponentDegree (v : C) :
      C.toSimpleGraph.degree v = H.degree v.1 := by
    change (H.induce C.supp).degree v = H.degree v.1
    exact H.degree_induce_of_neighborSet_subset
      (hcomponentNeighborSubset v)
  have hcomponentMax (v : C) : C.toSimpleGraph.degree v ≤ 2 := by
    rw [hcomponentDegree v]
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase e) color hproper a b v.1
  have hxDegree : C.toSimpleGraph.degree X = 1 := by
    rw [hcomponentDegree X]
    exact G.twoColorGraph_degree_eq_one_of_active
      (F.erase e) color hproper a b (G.fst e) hactive.1
  have hyDegree : C.toSimpleGraph.degree Y = 1 := by
    rw [hcomponentDegree Y]
    exact G.twoColorGraph_degree_eq_one_of_active
      (F.erase e) color hproper a b (G.snd e) hactive.2
  exact WeightedEdgeColoring.SimpleGraph.isTree_of_connected_of_degree_le_two_of_two_degree_one
    C.toSimpleGraph C.connected_toSimpleGraph hcomponentMax hXY
      hxDegree hyDegree

/-- Every non-endpoint vertex of a critical component has (simple-graph)
degree exactly two. -/
theorem critical_chain_internal_degree_eq_two
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    {z : G.V}
    (hzcomponent :
      (G.twoColorGraph (F.erase e) color a b).connectedComponentMk z =
        (G.twoColorGraph (F.erase e) color a b).connectedComponentMk
          (G.fst e))
    (hzfst : z ≠ G.fst e) (hzsnd : z ≠ G.snd e) :
    (G.twoColorGraph (F.erase e) color a b).degree z = 2 := by
  classical
  let H := G.twoColorGraph (F.erase e) color a b
  let C : H.ConnectedComponent := H.connectedComponentMk (G.fst e)
  have hxycomponent := G.critical_endpoints_same_twoColorComponent
    hcritical heF hproper ha hb
  have hactive := G.critical_endpoints_twoColorActive
    hcritical heF hproper ha hb
  have hxC : G.fst e ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hyC : G.snd e ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    simpa [C, H] using hxycomponent.symm
  have hzC : z ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    simpa [C, H] using hzcomponent
  let X : C := ⟨G.fst e, hxC⟩
  let Y : C := ⟨G.snd e, hyC⟩
  let Z : C := ⟨z, hzC⟩
  have hXY : X ≠ Y := by
    intro h
    exact G.noLoop e (congrArg Subtype.val h)
  have hXZ : X ≠ Z := by
    intro h
    exact hzfst (congrArg Subtype.val h).symm
  have hYZ : Y ≠ Z := by
    intro h
    exact hzsnd (congrArg Subtype.val h).symm
  have hcomponentNeighborSubset (v : C) : H.neighborSet v.1 ⊆ C.supp := by
    intro w hw
    exact (C.mem_supp_congr_adj hw).mp v.2
  have hcomponentDegree (v : C) :
      C.toSimpleGraph.degree v = H.degree v.1 := by
    change (H.induce C.supp).degree v = H.degree v.1
    exact H.degree_induce_of_neighborSet_subset
      (hcomponentNeighborSubset v)
  have hxDegree : C.toSimpleGraph.degree X = 1 := by
    rw [hcomponentDegree X]
    exact G.twoColorGraph_degree_eq_one_of_active
      (F.erase e) color hproper a b (G.fst e) hactive.1
  have hyDegree : C.toSimpleGraph.degree Y = 1 := by
    rw [hcomponentDegree Y]
    exact G.twoColorGraph_degree_eq_one_of_active
      (F.erase e) color hproper a b (G.snd e) hactive.2
  have hzNotOne : C.toSimpleGraph.degree Z ≠ 1 := by
    intro hzDegree
    let ends : Finset C :=
      (Finset.univ : Finset C).filter fun v ↦
        C.toSimpleGraph.degree v = 1
    have hthree : ({X, Y, Z} : Finset C) ⊆ ends := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxDegree⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyDegree⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzDegree⟩
    have hcardThree : ({X, Y, Z} : Finset C).card = 3 := by
      simp [hXY, hXZ, hYZ]
    have hge : 3 ≤ ends.card := by
      rw [← hcardThree]
      exact Finset.card_le_card hthree
    have hle : ends.card ≤ 2 := by
      apply WeightedEdgeColoring.SimpleGraph.card_degreeOne_le_two_of_connected_of_degree_le_two
        C.toSimpleGraph C.connected_toSimpleGraph
      intro v
      rw [hcomponentDegree v]
      exact G.twoColorGraph_degree_le_two_of_isProperOn
        (F.erase e) color hproper a b v.1
    omega
  have hzPos : 0 < C.toSimpleGraph.degree Z := by
    rw [hcomponentDegree Z]
    have huses := (G.critical_chain_internal_uses_both
      hcritical heF hproper ha hb hzcomponent hzfst hzsnd).1
    exact G.twoColorGraph_degree_pos_of_not_mem_missingColorsAt
      (F.erase e) color a b a (Or.inl rfl) z huses
  have hzLe : C.toSimpleGraph.degree Z ≤ 2 := by
    rw [hcomponentDegree Z]
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase e) color hproper a b z
  rw [← hcomponentDegree Z]
  omega

end WeightedMultigraph
end WeightedEdgeColoring
