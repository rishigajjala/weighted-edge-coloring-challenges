import WeightedEdgeColoring.SubtwoPacketQuotientBase
import WeightedEdgeColoring.SubtwoMixedOneTinyFloorResidual

/-! Transfer the proved original floor residual bound to the actual colored
physical quotient base. The two residual graphs arrange their subtype
indices differently but name exactly the same crossing edges. -/

set_option maxHeartbeats 4000000
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G : WeightedMultigraph.{u})
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

theorem quotientBase_residualGraph_pairMultiplicityAtMost
    (block : G.V → Q) (F : Finset G.E) {K L : ℕ}
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (hfull : C.fullEdges = G.subtwoQuotientSelectedEdges block F)
    (hmult : ((G.edgeRestriction (Finset.univ \ F)).subtwoQuotient block).PairMultiplicityAtMost L) :
    C.residualGraph.PairMultiplicityAtMost L := by
  classical
  let H := (G.edgeRestriction (Finset.univ \ F)).subtwoQuotient block
  have hrem : ∀ e : C.residualGraph.E, e.val.val ∈ Finset.univ \ F := by
    intro e
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro heF
    have hnot := (Finset.mem_sdiff.mp e.property).2
    apply hnot
    rw [hfull]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heF⟩
  let embed : C.residualGraph.E ↪ H.E := {
    toFun := fun e => ⟨⟨e.val.val,hrem e⟩,e.val.property⟩
    inj' := by
      intro e f hef
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun e : H.E => e.val.val) hef }
  intro a b
  have hsub : (C.residualGraph.endpointPairCell a b).map embed ⊆ H.endpointPairCell a b := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_map.mp he
    apply (H.mem_endpointPairCell_iff a b _).2
    exact (C.residualGraph.mem_endpointPairCell_iff a b f).1 hf
  calc
    _ = ((C.residualGraph.endpointPairCell a b).map embed).card := (Finset.card_map embed).symm
    _ ≤ (H.endpointPairCell a b).card := Finset.card_le_card hsub
    _ ≤ L := hmult a b

theorem subtwoFloorPhysicalColoredPacketBase_residualMultiplicity
    {K L : ℕ} (hK : 0 < K) (n : ℕ)
    (color : (G.subtwoFloorQuotient n).E → Fin K)
    (hproper : (G.subtwoFloorQuotient n).IsProperOn (G.subtwoFloorQuotientEdges n) color)
    (hmult : ((G.edgeRestriction G.floorResidualEdges).subtwoQuotient
      (G.subtwoFloorBlock n)).PairMultiplicityAtMost L) :
    (G.subtwoFloorPhysicalColoredPacketBase hK n color hproper).residualGraph.PairMultiplicityAtMost L := by
  apply G.quotientBase_residualGraph_pairMultiplicityAtMost (G.subtwoFloorBlock n)
    (G.floorPacketization.originalEdgesOfPackets G.fullFloorPacketSet)
    (G.subtwoFloorPhysicalColoredPacketBase hK n color hproper)
  · exact G.floorPacketization.subtwoQuotientColoredPacketBase_fullEdges
      hK (G.subtwoFloorBlock n) G.fullFloorPacketSet color hproper
  · exact hmult

theorem subtwoFloorBlock_fiber_card_le_five {n : ℕ} (hn : 0 < n)
    (hlocal : G.LocallyPacksInto n) (q : (G.subtwoFloorQuotient n).V) :
    (G.subtwoFiber (G.subtwoFloorBlock n) q).card ≤ 5 := by
  have hcard := G.floorPacketization.groupedGraph.subtwoFinalBlock_fiber_card
    (G.subtwoFloorCost n) (G.subtwoFloorCost_nonneg n)
    (G.subtwoFloorCost_pair_le hn hlocal) (G.subtwoFloorCost_degree_le hn hlocal) q
  have hrank : G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q ≤ 2 := by
    unfold subtwoFinalRank
    split_ifs <;> omega
  change (G.subtwoFiber (G.subtwoFloorBlock n) q).card =
    1+2*G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q at hcard
  omega

/-- All graph-side multiplicity premises of the proposal factory are now
supplied by the actual grouped graph and its selected floor packets. -/
theorem subtwoFloorPhysicalColoredPacketBase_residualMultiplicity_of_oneTiny
    (D S : ℕ) {K n : ℕ} (hK : 0 < K) (hn : 0 < n)
    (hlocal : G.LocallyPacksInto n) (hfloor : G.FloorBundleAtMostOneTiny D S)
    (color : (G.subtwoFloorQuotient n).E → Fin K)
    (hproper : (G.subtwoFloorQuotient n).IsProperOn (G.subtwoFloorQuotientEdges n) color) :
    (G.subtwoFloorPhysicalColoredPacketBase hK n color hproper).residualGraph.PairMultiplicityAtMost
      (25*((D+1)*(((S+1)^(D+1)*S+S)+1))) := by
  apply G.subtwoFloorPhysicalColoredPacketBase_residualMultiplicity hK n color hproper
  exact G.floorResidualQuotient_pairMultiplicityAtMost_of_oneTiny
    D S (G.subtwoFloorBlock n) (G.subtwoFloorBlock_fiber_card_le_five hn hlocal) hfloor

end
end WeightedEdgeColoring.WeightedMultigraph
