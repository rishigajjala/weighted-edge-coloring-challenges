import WeightedEdgeColoring.ExtendedProfileSelectedDyadicEndpointIteration
import WeightedEdgeColoring.ExtendedProfileSelectedResidualStar
import WeightedEdgeColoring.DyadicLargeEdgeExtraCaptureBuckets
import WeightedEdgeColoring.DyadicLargeEdgeWholeLoss
import WeightedEdgeColoring.LargeEdgeTraceLiftBridge

/-!
# Decoding the selected local-dyadic endpoint iteration

This is the deterministic outer composition.  It lifts the final matching
from the large-job restriction, keeps only its ordinary options, jointly
rounds the tiny options, and adds the four residual charges: endpoint-trace
loss, selected-extra loss, fractional tiny residual, and the additive tiny
rounding error.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})
variable {B k N reserve L K steps : ℕ}
variable {s β q r extraGamma rho omega nibbleA nibbleDelta tinyA tinyDelta : ℝ}
variable {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- Decode one completed endpoint trace into a feasible partial coloring.
The displayed loss is fully explicit in the trace bound and the selected
profile's quadratic error. -/
theorem exists_partialColoring_of_selectedBlockDyadicTrace
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (hrs : rho * s ≤ 1)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (hcapacityTiny : ∀ v c,
      G.selectedBlockNormalizedTinyReservoirLoad R0 rho omega choice (v, c) ≤
        tinyA * G.extendedProfileReservoirSize R0 v
          (G.decodedExtendedProfileBlockSelection R0 choice v c) + tinyDelta)
    (htinyA0 : 0 ≤ tinyA) (htinyA1 : tinyA ≤ 1)
    (hjointError : tinyDelta + 2 * β ≤ (1 - tinyA) * r)
    (hreserve : 0 < reserve) (hextraGamma1 : extraGamma < 1)
    (hdyadicCover : 1 ≤ dyadicScale β L)
    (hdyadicTop : dyadicScale β L ≤ 2)
    (final : RankThreeOptionSystem.OriginalIterationState
      (G.largeEdgeJobSystem
        (G.selectedBlockDyadicQuantizedSystem
          (N := N) (reserve := reserve) (gamma := extraGamma) R0 omega rho choice
          (dyadicBucket β L G.weight)) β))
    (T : RankThreeOptionSystem.OriginalIterationState.EndpointSharpTrace
      (G.largeEdgeRestriction β) β nibbleA nibbleDelta L K steps
      (RankThreeOptionSystem.OriginalIterationState.full
        (G.largeEdgeJobSystem
          (G.selectedBlockDyadicQuantizedSystem
            (N := N) (reserve := reserve) (gamma := extraGamma) R0 omega rho choice
            (dyadicBucket β L G.weight)) β)) final)
    (hactive0 : ∀ j, j ∈
      (G.largeEdgeJobSystem
        (G.selectedBlockDyadicQuantizedSystem
          (N := N) (reserve := reserve) (gamma := extraGamma) R0 omega rho choice
          (dyadicBucket β L G.weight)) β).activeJobs)
    (traceBound sigma : G.V → ℝ)
    (htrace : ∀ v,
      RankThreeOptionSystem.OriginalIterationState.stateActiveStarWeight
        (G.largeEdgeRestriction β) final v ≤ traceBound v)
    (hsigma0 : ∀ v, 0 ≤ sigma v)
    (hquad : ∀ v,
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedExtendedProfileTotalOptionMass
          R0 rho omega choice e.1 - rho * s) ^ 2) ≤ sigma v) :
    ∃ (P : Finset G.E) (color : G.E → Fin (B * k)),
      G.asMultigraph.IsFeasibleOn P color ∧
      ∀ v,
        (∑ e ∈ Finset.univ \ P,
          if G.Inc v e then G.weight e else 0) ≤
        traceBound v +
          4 * ((1 - rho * s) * G.starWeight v +
            Real.sqrt (G.starWeight v * sigma v)) / (1 - extraGamma) +
          8 * (1 + (reserve : ℝ)) +
          ((1 - rho * s) * G.starWeight v +
            Real.sqrt (G.starWeight v * sigma v)) + 2 * β := by
  let bucket : G.E → Fin (L + 1) := dyadicBucket β L G.weight
  let residual : G.E → ℝ :=
    G.selectedBlockLargeResidual R0 omega rho choice
  let x := G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice
  let Hbase := G.selectedBlockDyadicQuantizedSystem
    (N := N) (reserve := reserve) (gamma := extraGamma) R0 omega rho choice bucket
  let M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket
        extraGamma reserve residual x)) :=
    G.liftLargeEdgeJobSet Hbase β final.matching
  have hM : Hbase.IsPartialMatching M :=
    G.liftLargeEdgeJobSet_isPartialMatching Hbase β final.matching_isPartial
  obtain ⟨decision, hfeasible, htinyLoss⟩ :=
    G.exists_selectedBlockTinyColorDecision_dyadic_joint_isFeasibleOn R0
      hn hs hq hr0 hr1 hleft rho omega homega0 homega1 hrho choice
      bucket M hM tinyA tinyDelta htinyA0 htinyA1 hcapacityTiny hjointError
  let O := G.selectedDyadicOrdinaryBaseOptions
    (B * k) (explicitLargeSlotBound β q r) N bucket extraGamma reserve
    residual x M
  let hO := G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
    (B * k) (explicitLargeSlotBound β q r) N bucket extraGamma reserve
    residual x M hM
  let P := G.ordinarySelectedEdges O ∪
    G.tinyDecisionColoredEdges (G.selectedBlockTinyEdges β) decision
  let color := G.ordinaryTinyJointColor hn O hO
    (G.selectedBlockTinyEdges β) decision
  refine ⟨P, color, ?_, ?_⟩
  · simpa [P, color, O, hO, bucket, residual, x, Hbase, M] using hfeasible
  · intro v
    have hdisjoint : Disjoint (G.ordinarySelectedEdges O)
        (G.selectedBlockTinyEdges β) := by
      dsimp [O]
      exact G.selectedDyadicNormalizedLargeMatching_disjoint_tinyEdges
        R0 rho omega choice bucket M
    have hwhole := G.uncolored_dyadic_joint_starWeight_eq
      (B * k) (explicitLargeSlotBound β q r) N β bucket extraGamma reserve
      residual x M decision hdisjoint v
    have huncovered :
        G.uncoveredLargeStarWeight Hbase β M v =
          RankThreeOptionSystem.OriginalIterationState.stateActiveStarWeight
            (G.largeEdgeRestriction β) final v := by
      exact G.endpointSharpTrace_uncoveredLargeStarWeight_lift_eq_state
        Hbase T hactive0 v
    have hlarge := G.dyadicLargeRemainingStarWeight_le_uncovered_add_extra
      (explicitLargeSlotBound β q r) N β bucket extraGamma reserve residual x
      M hM v
    have hres0 : ∀ e, 0 ≤ residual e := by
      exact G.selectedBlockLargeResidual_nonneg R0 hn hs hq hr0 hleft
        omega homega0 homega1 rho hrho choice
    have hsupport : ∀ e, 0 < residual e → β ≤ G.weight e := by
      intro e he
      by_cases hlargeEdge : β ≤ G.weight e
      · exact hlargeEdge
      · simp [residual, selectedBlockLargeResidual, hlargeEdge] at he
    have hextra := G.selectedDyadicExtraEdges_starWeight_le_dyadic_support
      (explicitLargeSlotBound β q r) N β L extraGamma reserve residual x M hM
      hβ hdyadicCover hdyadicTop hres0 hsupport hreserve hextraGamma1 v
    have hresLarge :=
      G.weightedResidualStar_selectedBlockLargeResidual_le_sqrt
        R0 rho omega choice hrs v (sigma v) (hsigma0 v) (hquad v)
    have hresAll := G.weightedResidualStar_selectedBlockResidual_le_sqrt
      R0 rho omega choice hrs v (sigma v) (hsigma0 v) (hquad v)
    have htinyFractional :=
      G.tinyResidualLossLoad_selectedBlockResidual_le_weightedResidualStar
        R0 rho omega choice hn hs hq hr0 hleft homega0 homega1 hrho v
    have hgap : 0 < 1 - extraGamma := sub_pos.mpr hextraGamma1
    rw [show (∑ e ∈ Finset.univ \ P,
        if G.Inc v e then G.weight e else 0) =
        G.dyadicLargeRemainingStarWeight
          (explicitLargeSlotBound β q r) N β bucket extraGamma reserve
          residual x M v + G.tinyResidualIntegralLossLoad decision v by
      simpa [P, O] using hwhole]
    calc
      G.dyadicLargeRemainingStarWeight
          (explicitLargeSlotBound β q r) N β bucket extraGamma reserve
          residual x M v + G.tinyResidualIntegralLossLoad decision v ≤
        (G.uncoveredLargeStarWeight Hbase β M v +
          ∑ e ∈ (G.selectedDyadicExtraEdges
            (explicitLargeSlotBound β q r) N bucket extraGamma reserve
            residual x M).filter (G.Inc v), G.weight e) +
          (G.tinyResidualLossLoad (G.selectedBlockTinyEdges β)
            (fun e ↦ G.selectedBlockResidualOptionMass
              R0 rho omega choice e.1) v + 2 * β) := by
        exact add_le_add hlarge (htinyLoss v)
      _ ≤ traceBound v +
          (4 * G.weightedResidualStar residual v / (1 - extraGamma) +
            8 * (1 + (reserve : ℝ))) +
          (G.weightedResidualStar
            (G.selectedBlockResidualOptionMass R0 rho omega choice) v +
              2 * β) := by
        rw [huncovered]
        exact add_le_add
          (add_le_add (htrace v) hextra)
          (add_le_add htinyFractional le_rfl)
      _ ≤ traceBound v +
          4 * ((1 - rho * s) * G.starWeight v +
            Real.sqrt (G.starWeight v * sigma v)) / (1 - extraGamma) +
          8 * (1 + (reserve : ℝ)) +
          ((1 - rho * s) * G.starWeight v +
            Real.sqrt (G.starWeight v * sigma v)) + 2 * β := by
        have hscaled :
            4 * G.weightedResidualStar residual v / (1 - extraGamma) ≤
              4 * ((1 - rho * s) * G.starWeight v +
                Real.sqrt (G.starWeight v * sigma v)) /
                (1 - extraGamma) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hresLarge (by norm_num)) hgap.le
        have hsmall :
            G.weightedResidualStar
                (G.selectedBlockResidualOptionMass R0 rho omega choice) v +
                2 * β ≤
              ((1 - rho * s) * G.starWeight v +
                Real.sqrt (G.starWeight v * sigma v)) + 2 * β := by
          exact add_le_add hresAll le_rfl
        linarith

end WeightedSimpleGraph

end

end WeightedEdgeColoring
