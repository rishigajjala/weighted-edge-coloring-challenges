import WeightedEdgeColoring.SubtwoActualObjectGrouping

/-! Pull actual colors on the preprocessed objects back to the original objects. -/

set_option maxHeartbeats 4000000
open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
noncomputable section
universe u
variable {G : WeightedMultigraph.{u}} {S : ℕ}
  (P : G.GeneralTinyThresholdPacketization ((1 : ℝ)/S)) (M : ℕ)

theorem exists_recover_coreGroupedObjects_partialColor
    (hM : 0 < M) (hS : 0 < S) {n : ℕ}
    (hlocal : P.mixedObjectGraph.LocallyPacksInto n)
    (R : Finset (P.coreGroupedPacketization M).mixedObjectGraph.E)
    (K : ℕ) (hK : 0 < K)
    (color : (P.coreGroupedPacketization M).mixedObjectGraph.E → Fin K)
    (hcolor : (P.coreGroupedPacketization M).mixedObjectGraph.IsFeasibleOn R color)
    (loss : ℝ)
    (hleft : ∀ v, (∑ e ∈ Finset.univ \ R,
      if (P.coreGroupedPacketization M).mixedObjectGraph.Inc v e then
        (P.coreGroupedPacketization M).mixedObjectGraph.weight e else 0) ≤ loss) :
    ∃ A : Finset P.mixedObjectGraph.E, ∃ lifted : P.mixedObjectGraph.E → Fin K,
      P.mixedObjectGraph.IsFeasibleOn A lifted ∧
      ∀ v, (∑ e ∈ Finset.univ \ A,
        if P.mixedObjectGraph.Inc v e then P.mixedObjectGraph.weight e else 0) ≤
          (2*(S : ℝ)/M)*n+loss := by
  classical
  let Q := (P.coreGroupedPacketization M).mixedPacketization
  let A := Q.originalEdgesOfPackets R
  have hfeasible : (P.coreGroupedGraph M).IsFeasibleOn A (Q.expandColor color) :=
    Q.isFeasibleOn_originalEdgesOfPackets R color hcolor
  have hresidual : ∀ v, (∑ e ∈ Finset.univ \ A,
      if (P.coreGroupedGraph M).Inc v e then (P.coreGroupedGraph M).weight e else 0) ≤ loss := by
    intro v
    rw [show Finset.univ \ A = Q.originalEdgesOfPackets (Finset.univ \ R) from
      (Q.originalEdgesOfPackets_compl R).symm]
    rw [Q.restrictedWeight_originalEdgesOfPackets]
    exact hleft v
  obtain ⟨A',lifted,hfeas,_,hres⟩ := SubtwoMixedCoreGrouping.exists_original_partialColor
    P.mixedObjectGraph P.coreObjects M hM S hS
    (fun e he => P.coreObject_weight_ge he) hlocal A K hK
    (Q.expandColor color) hfeasible loss hresidual
  exact ⟨A',lifted,hfeas,hres⟩

end
end WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
