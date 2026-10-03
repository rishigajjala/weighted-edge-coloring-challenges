import WeightedEdgeColoring.BipartiteHarmonicChargeColoringProof
import WeightedEdgeColoring.BoundedMultiplicityDeficitAwareRoundingProof

/-!
# Unconditional bipartite harmonic-charge coloring

The proved deficit-aware bounded-multiplicity rounder closes the sole input
of the finite-harmonic-plus-tiny construction.
-/

namespace WeightedEdgeColoring

universe u

/-- Uniform bipartite harmonic-charge coloring. -/
theorem bipartiteHarmonicChargeColoring_proved :
    BipartiteHarmonicChargeColoring.{u} :=
  bipartiteHarmonicChargeColoring_of_deficitAwareBoundedMultiplicityWholeEdgeUniformRounding
    deficitAwareBoundedMultiplicityWholeEdgeUniformRounding_proved

/-- Sharp bipartite multigraph bin-packing asymptotics. -/
theorem bipartiteMultigraphBPAsymptotic_proved :
    BipartiteMultigraphBPAsymptotic.{u} :=
  bipartiteMultigraphBPAsymptotic_of_deficitAwareBoundedMultiplicityWholeEdgeUniformRounding
    deficitAwareBoundedMultiplicityWholeEdgeUniformRounding_proved

end WeightedEdgeColoring
