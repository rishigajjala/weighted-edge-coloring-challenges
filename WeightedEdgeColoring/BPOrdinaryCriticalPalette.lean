import WeightedEdgeColoring.BPOrdinaryCriticalBridge
import WeightedEdgeColoring.SimpleGraphPathCut

/-!
# Adjacent palettes on a critical chain are disjoint

This is the terminal step of Andersen's Lemma 3.  If adjacent vertices of
the critical path missed a common third colour, recolour the unique chain
edge with that colour.  The old chain component is a tree, so this deletes
an edge of its unique endpoint-to-endpoint path.  The critical endpoints
can no longer be joined by their two colours, contradicting the elementary
Kempe-component lemma.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

theorem not_common_missing_of_mem_criticalPath_edge
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    {u v : G.V} (hpathEdge : s(u, v) ∈ p.1.edges)
    {c : Fin k}
    (huc : c ∈ G.missingColorsAt (F.erase e) color u)
    (hvc : c ∈ G.missingColorsAt (F.erase e) color v) :
    False := by
  classical
  let R := F.erase e
  let H := G.twoColorGraph R color a b
  have huvAdj : H.Adj u v := p.1.adj_of_mem_edges hpathEdge
  have huv : u ≠ v := huvAdj.ne
  have hucomponent :
      H.connectedComponentMk u = H.connectedComponentMk (G.fst e) := by
    have huSupport : u ∈ p.1.support := p.1.fst_mem_support_of_mem_edges hpathEdge
    let q := p.1.takeUntil u huSupport
    have hreach : H.Reachable (G.fst e) u := ⟨q⟩
    let C : H.ConnectedComponent := H.connectedComponentMk (G.fst e)
    have hxC : G.fst e ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    have hsupp := WeightedEdgeColoring.SimpleGraph.walk_support_subset_connectedComponent
      H C hxC q
    have huC : u ∈ C.supp := hsupp u q.end_mem_support
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff C u).mp huC
  have hvcomponent :
      H.connectedComponentMk v = H.connectedComponentMk (G.fst e) := by
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      huvAdj.symm).trans hucomponent
  have hca : c ≠ a := by
    intro h
    subst c
    have huEq := G.eq_fst_of_mem_missing_chain_leftColor
      hcritical heF hproper ha hb hucomponent huc
    have hvEq := G.eq_fst_of_mem_missing_chain_leftColor
      hcritical heF hproper ha hb hvcomponent hvc
    exact huv (huEq.trans hvEq.symm)
  have hcb : c ≠ b := by
    intro h
    subst c
    have huEq := G.eq_snd_of_mem_missing_chain_rightColor
      hcritical heF hproper ha hb hucomponent huc
    have hvEq := G.eq_snd_of_mem_missing_chain_rightColor
      hcritical heF hproper ha hb hvcomponent hvc
    exact huv (huEq.trans hvEq.symm)
  rcases G.exists_twoColorWitnessEdge R color a b huvAdj with
    ⟨g, hgR, hgu, hgv, hgcolor⟩
  have endpoint_missing (z : G.V) (hzg : G.Inc z g) :
      c ∈ G.missingColorsAt R color z := by
    by_cases hzu : z = u
    · simpa [R, hzu] using huc
    · have huz : u ≠ z := fun h ↦ hzu h.symm
      have hzOther := G.kempeOtherEndpoint_eq_of_incident hgu hzg huz
      have hvOther := G.kempeOtherEndpoint_eq_of_incident hgu hgv huv
      have hzv : z = v := hzOther.symm.trans hvOther
      simpa [R, hzv] using hvc
  have hproperNew :
      G.IsProperOn R (G.assignEdgeColor color g c) := by
    exact G.isProperOn_replaceEdgeColor_of_missing_endpoints hproper hgR
      (endpoint_missing (G.fst g) (Or.inl rfl))
      (endpoint_missing (G.snd g) (Or.inr rfl))
  have haNew :
      a ∈ G.missingColorsAt R (G.assignEdgeColor color g c) (G.fst e) := by
    exact G.mem_missingColorsAt_assignEdgeColor_of_ne hca.symm ha
  have hbNew :
      b ∈ G.missingColorsAt R (G.assignEdgeColor color g c) (G.snd e) := by
    exact G.mem_missingColorsAt_assignEdgeColor_of_ne hcb.symm hb
  have hunique : ∀ r, r ∈ R → G.Inc u r → G.Inc v r →
      (color r = a ∨ color r = b) → r = g := by
    intro r hrR hru hrv hrcolor
    exact (G.critical_chain_adj_has_unique_witness
      hcritical heF hproper ha hb huv hucomponent
      hgR hrR hgu hgv hru hrv hgcolor hrcolor).symm
  let Hnew := G.twoColorGraph R (G.assignEdgeColor color g c) a b
  have hle : Hnew ≤ H.deleteEdges {s(u, v)} := by
    exact G.twoColorGraph_assignEdgeColor_le_deleteEdges
      hca hcb hunique
  let C : H.ConnectedComponent := H.connectedComponentMk (G.fst e)
  have hxC : G.fst e ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hyC : G.snd e ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (G.critical_endpoints_same_twoColorComponent
      hcritical heF hproper ha hb).symm
  have huC : u ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact hucomponent
  have hvC : v ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact hvcomponent
  let X : C := ⟨G.fst e, hxC⟩
  let Y : C := ⟨G.snd e, hyC⟩
  let U : C := ⟨u, huC⟩
  let W : C := ⟨v, hvC⟩
  have hpSupport : ∀ z ∈ p.1.support, z ∈ C.supp :=
    WeightedEdgeColoring.SimpleGraph.walk_support_subset_connectedComponent H C hxC p.1
  let pC0 := p.1.induce C.supp hpSupport
  let pC : C.toSimpleGraph.Walk X Y :=
    pC0.copy (Subtype.ext (by rfl)) (Subtype.ext (by rfl))
  have hpCPath : pC.IsPath := by
    apply SimpleGraph.Walk.IsPath.of_map
      (f := (_root_.SimpleGraph.Embedding.induce C.supp).toHom)
    simpa [pC, pC0] using p.property
  let P : C.toSimpleGraph.Path X Y := ⟨pC, hpCPath⟩
  have hpathEdgeMapped :
      s(u, v) ∈
        (pC.map (_root_.SimpleGraph.Embedding.induce C.supp).toHom).edges := by
    simpa [pC, pC0] using hpathEdge
  have hUW : s(U, W) ∈ P.1.edges := by
    rw [SimpleGraph.Walk.edges_map] at hpathEdgeMapped
    rcases List.mem_map.mp hpathEdgeMapped with ⟨d, hd, hdmap⟩
    have hdEq : d = s(U, W) := by
      apply (Sym2.map.injective
        (_root_.SimpleGraph.Embedding.induce (G := H) C.supp).injective)
      simpa [U, W] using hdmap
    simpa [P, hdEq] using hd
  have htree : C.toSimpleGraph.IsTree := by
    simpa [C, H, R] using
      G.critical_twoColorComponent_isTree hcritical heF hproper ha hb
  have hnotReach : ¬Hnew.Reachable (G.fst e) (G.snd e) := by
    exact WeightedEdgeColoring.SimpleGraph.not_reachable_of_le_deleteEdges_of_mem_componentPath
      H Hnew C htree X Y U W P hUW hle
  apply hnotReach
  apply WeightedEdgeColoring.SimpleGraph.reachable_of_connectedComponentMk_eq Hnew
  exact G.critical_endpoints_same_twoColorComponent
    hcritical heF hproperNew haNew hbNew

end WeightedMultigraph
end WeightedEdgeColoring
