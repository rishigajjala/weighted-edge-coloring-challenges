import WeightedEdgeColoring.BPGeneralPatternTwoBagExtraction
import WeightedEdgeColoring.FiniteFractionalPatternCoverMinimum

/-!
# Unconditional minimum-cover two-bag extraction

For finite bin-packing instances, minimum fractional pattern covers exist.
Combining that compactness fact with the operational two-bag construction
removes the last chosen-minimum-cover hypotheses from the extraction step.
-/

namespace WeightedEdgeColoring

noncomputable section

universe u v

namespace BinPackingInstance.FractionalPatternCover

variable (A : BinPackingInstance.{u}) (B : BinPackingInstance.{v})

/-- A joint fractional pattern cover canonically yields minimum separated
covers together with the required two-bag mass certificate. -/
theorem exists_minimumCovers_with_twoBagMassCertificate
    (C : (A.sum B).FractionalPatternCover) :
    ∃ CA : A.FractionalPatternCover,
      ∃ CB : B.FractionalPatternCover,
        CA.IsMinimumCost ∧ CB.IsMinimumCost ∧
          TwoBagMassCertificate CA.cost CB.cost C.cost := by
  obtain ⟨CA, hCA⟩ := exists_minimumCost A
  obtain ⟨CB, hCB⟩ := exists_minimumCost B
  exact ⟨CA, CB, hCA, hCB,
    C.toTwoBagMassCertificate_of_minimumCosts CA CB hCA hCB⟩

end BinPackingInstance.FractionalPatternCover

end

end WeightedEdgeColoring
