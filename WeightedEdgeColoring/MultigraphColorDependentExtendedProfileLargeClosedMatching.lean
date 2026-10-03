import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileLargeClosedIteration
import WeightedEdgeColoring.BoundedMultiplicityLargeEdgeTraceLiftBridge

/-!
# Decoding a closed color-dependent large-edge iteration

This removes the last structural matching arguments from the large decoder:
the accumulated matching, its residual-active identity, the uniform initial
degree, and the endpoint trace bound are all extracted from one closed trace.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k N reserve C steps L K : ℕ}
variable {s β q r proposalGamma extraGamma rho omega traceLoss : ℝ}
variable {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

theorem exists_colorDependentLargeMatchingData_of_closedTrace
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hB : 0 < B) (hk : 0 < k)
    (selected : G.ColorDependentSelectedStates proposal R)
    (hCN : C ≤ N) (hNC : 0 < N - C)
    (hchoices : ∀ e,
      (B * k) * explicitLargeSlotBound β q r *
          explicitLargeSlotBound β q r +
        DivisibleLocalExtraChoice.supportCount G.fst G.snd
          (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L)
          (G.boundedDyadicExtraSlotCount
            (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L)
            (G.selectedColorDependentLargeResidual proposal R rho omega selected)
            extraGamma reserve) e ≤ C)
    (hdyadicCover : 1 ≤ dyadicScale β L)
    (hdyadicTop : dyadicScale β L ≤ 2)
    (hreserve : 0 < reserve) (hextraGamma1 : extraGamma < 1)
    (a delta : ℝ) :
    let Hbase := G.colorDependentSelectedDyadicSystem
      (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
      proposal R proposalGamma extraGamma rho omega selected
    letI : DecidableEq (Hbase.ActiveJobOption (G.largeEdgeJobs β)) :=
      inferInstance
    let Hlarge := G.largeEdgeJobSystem Hbase β
    ∀ (final : RankThreeOptionSystem.OriginalIterationState Hlarge)
    (T : RankThreeOptionSystem.OriginalIterationState.Multigraph.EndpointSharpTrace
      (G.largeEdgeRestriction β) β a delta L K steps
      (RankThreeOptionSystem.OriginalIterationState.full Hlarge) final)
    (hstate : ∀ v,
      RankThreeOptionSystem.OriginalIterationState.Multigraph.stateActiveStarWeight
        (G.largeEdgeRestriction β) final v ≤ traceLoss),
    ∃ (M : Finset (OrdinarySlotChoice G.E (Fin (B * k))
          (explicitLargeSlotBound β q r)))
      (hM : (OrdinarySlotChoice.system G.fst G.snd
          (explicitLargeSlotBound β q r)).IsPartialMatching M),
      G.ordinarySelectedEdges M ⊆ G.largeEdgeJobs β ∧
      (∀ e ∈ G.ordinarySelectedEdges M,
        0 < proposal e (finProdFinEquiv.symm
          (G.extendSelectedOrdinaryColor (Nat.mul_pos hB hk) M hM e))) ∧
      (∀ v c,
        G.selectedOrdinaryIntegralColorLoad M hM v (finProdFinEquiv c) ≤
          ∑ i, G.colorDependentExtendedProfileConcreteSlotSize R v c
            (selected v c.1 c.2) i) ∧
      ∀ v,
        (∑ e ∈ G.retainedMacroscopicEdges proposal proposalGamma β \
            G.ordinarySelectedEdges M,
          if G.Inc v e then G.weight e else 0) ≤
        traceLoss +
          4 * G.weightedResidualStar
            (G.selectedColorDependentRetainedMacroscopicResidual
              proposal R proposalGamma β rho omega
              (G.encodedColorDependentSelectedBlock proposal R selected)) v /
              (1 - extraGamma) +
          8 * (1 + (reserve : ℝ)) := by
  dsimp only
  let Hbase := G.colorDependentSelectedDyadicSystem
    (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
    proposal R proposalGamma extraGamma rho omega selected
  letI : DecidableEq (Hbase.ActiveJobOption (G.largeEdgeJobs β)) :=
    inferInstance
  let Hlarge := G.largeEdgeJobSystem Hbase β
  classical
  intro final T hstate
  have hactive0 : ∀ j, j ∈ Hlarge.activeJobs := by
    intro j
    rw [RankThreeOptionSystem.mem_activeJobs]
    apply Finset.card_pos.mp
    exact hNC.trans_le
      (G.colorDependentSelectedDyadicLarge_jobDegree_lower proposal R
        hs hq hr0 hleft homega0 homega1 hrho selected hCN hchoices j)
  have huncoveredBound : ∀ v,
      G.uncoveredLargeStarWeight Hbase β
        (G.liftLargeEdgeJobSet Hbase β final.matching) v ≤ traceLoss := by
    intro v
    have hstateEq := G.endpointSharpTrace_uncoveredLargeStarWeight_lift_eq_state
      Hbase T hactive0 v
    rw [hstateEq]
    exact hstate v
  let input : G.LargeMatchingDecoderInput Hbase β traceLoss := {
    options := G.liftLargeEdgeJobSet Hbase β final.matching
    isPartialMatching := G.liftLargeEdgeJobSet_isPartialMatching Hbase β
      final.matching_isPartial
    owner_large := fun _ hq ↦ G.owner_large_of_mem_liftLargeEdgeJobSet Hbase hq
    uncoveredBound := huncoveredBound
  }
  exact G.exists_colorDependentLargeMatchingData_of_restrictedMatching
    proposal R hs hq hr0 hleft homega0 homega1 rho proposalGamma extraGamma
    traceLoss hrho hproposal0 hB hk selected hdyadicCover hdyadicTop hreserve
    hextraGamma1 input

end WeightedMultigraph

end

end WeightedEdgeColoring
