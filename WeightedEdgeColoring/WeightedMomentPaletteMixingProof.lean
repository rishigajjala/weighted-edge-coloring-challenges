import WeightedEdgeColoring.WeightedMomentEstimateReduction
import WeightedEdgeColoring.WeightedMomentEstimateMixingProof

/-! The proved moment estimates close the weighted-moment palette-mixing
interface used by the packet completion arguments. -/

namespace WeightedEdgeColoring

universe u

theorem weightedMomentPaletteMixing_proved :
    WeightedMomentPaletteMixing.{u} :=
  weightedMomentPaletteMixing_of_estimateMixing
    weightedMomentEstimateMixing

end WeightedEdgeColoring
