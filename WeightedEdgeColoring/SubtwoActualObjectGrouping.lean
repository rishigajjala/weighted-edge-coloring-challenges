import WeightedEdgeColoring.SubtwoMixedCoreGroupingRecovery
import WeightedEdgeColoring.SubtwoGroupedOneTinyFloor
import WeightedEdgeColoring.SubtwoIdentityTinyPacketization

/-! The global preprocessing applied to the actual tiny-threshold objects. -/

set_option maxHeartbeats 4000000
open scoped BigOperators Sym2
namespace WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
noncomputable section
universe u
variable {G : WeightedMultigraph.{u}} {S : ℕ}
  (P : G.GeneralTinyThresholdPacketization ((1 : ℝ)/S)) (M : ℕ)

def coreGroupedGraph : WeightedMultigraph.{u} :=
  SubtwoMixedCoreGrouping.graph P.mixedObjectGraph P.coreObjects M

theorem outsideCore_endpoint_injective :
    Function.Injective (fun e : {e : P.Object // e ∉ P.coreObjects} =>
      s(P.mixedObjectGraph.fst e.val,P.mixedObjectGraph.snd e.val)) := by
  intro e f hef
  have he : e.val ∈ P.smallObjects := by simpa [coreObjects] using e.property
  have hf : f.val ∈ P.smallObjects := by simpa [coreObjects] using f.property
  have h := P.smallObjects_endpoint_injective (a₁ := ⟨e.val,he⟩) (a₂ := ⟨f.val,hf⟩) hef
  exact Subtype.ext (congrArg (fun x : {o : P.Object // o ∈ P.smallObjects} => x.val) h)

theorem coreGroupedGraph_locallyPacksInto (hM : 0 < M) {n : ℕ}
    (hlocal : P.mixedObjectGraph.LocallyPacksInto n) :
    (P.coreGroupedGraph M).LocallyPacksInto n :=
  SubtwoMixedCoreGrouping.locallyPacksInto P.mixedObjectGraph P.coreObjects M hM hlocal

theorem coreGroupedGraph_card_bundle_weight_types_le (k : G.V × G.V) :
    Fintype.card ((P.coreGroupedGraph M).EdgeSetWeightType ((P.coreGroupedGraph M).floorBundle k)) ≤
      2*M+1 :=
  SubtwoMixedCoreGrouping.card_bundle_weight_types_le
    P.mixedObjectGraph P.coreObjects M P.outsideCore_endpoint_injective k

theorem coreGroupedGraph_below_endpoint_injective :
    Function.Injective
      (fun e : ((P.coreGroupedGraph M).belowRestriction ((1 : ℝ)/S)).E =>
        s((P.coreGroupedGraph M).fst e.val,(P.coreGroupedGraph M).snd e.val)) := by
  intro e f hef
  have hh := SubtwoMixedCoreGrouping.below_endpoint_injective
    P.mixedObjectGraph P.coreObjects M ((1 : ℝ)/S)
    (fun e he => P.coreObject_weight_ge he) P.outsideCore_endpoint_injective
  have h := hh
    (a₁ := ⟨e.val, ((P.coreGroupedGraph M).mem_edgesBelow_iff _ _).mp e.property⟩)
    (a₂ := ⟨f.val, ((P.coreGroupedGraph M).mem_edgesBelow_iff _ _).mp f.property⟩) hef
  exact Subtype.ext (congrArg
    (fun x : {e : (P.coreGroupedGraph M).E // (P.coreGroupedGraph M).weight e < (1 : ℝ)/S} => x.val) h)

def coreGroupedPacketization :
    (P.coreGroupedGraph M).GeneralTinyThresholdPacketization ((1 : ℝ)/S) :=
  (P.coreGroupedGraph M).identityTinyPacketization ((1 : ℝ)/S)
    (by positivity) (P.coreGroupedGraph_below_endpoint_injective M)

theorem coreGroupedPacketization_locallyPacksInto (hM : 0 < M) {n : ℕ}
    (hlocal : P.mixedObjectGraph.LocallyPacksInto n) :
    (P.coreGroupedPacketization M).mixedObjectGraph.LocallyPacksInto n :=
  (P.coreGroupedGraph M).identityTinyPacketization_mixedObjectGraph_locallyPacksInto
    (by positivity) (P.coreGroupedGraph_below_endpoint_injective M)
    (P.coreGroupedGraph_locallyPacksInto M hM hlocal)

theorem coreGroupedGraph_oneTinyFloor (hS : 0 < S) :
    (P.coreGroupedGraph M).FloorBundleAtMostOneTiny (2*M) S :=
  SubtwoMixedCoreGrouping.floorBundleAtMostOneTiny
    P.mixedObjectGraph P.coreObjects M S hS
    (fun e he => P.coreObject_weight_ge he) P.outsideCore_endpoint_injective

end
end WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
