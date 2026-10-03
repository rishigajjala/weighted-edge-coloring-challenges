import WeightedEdgeColoring.MultigraphDyadicLargeEdgeMatchingExtraction
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeTotalLoss
import WeightedEdgeColoring.BoundedMultiplicityLargeEdgeRestriction

/-!
# Large owners survive ordinary-option extraction

This small lemma keeps the bookkeeping proof out of concrete decoder
theorems.  It is stated directly for a dyadic option system, so elaboration
never has to unfold a large application-specific system abbreviation.
-/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]

/-- If every selected quantized copy has a `beta`-large owner, then every
edge extracted from its ordinary summand is a `beta`-large edge. -/
theorem ordinarySelectedEdges_selectedDyadicOrdinaryBaseOptions_subset_largeEdgeJobs
    {q K N : ℕ}
    (bucket : G.E → Class) (gamma beta : ℝ) (reserveCount : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Fin q → Fin K → Fin K → ℝ)
    (Q : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserveCount residual x)))
    (howner : ∀ copy ∈ Q,
      beta ≤ G.weight
        ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserveCount residual).owner
          copy.1)) :
    G.ordinarySelectedEdges
        (G.selectedDyadicOrdinaryBaseOptions q K N bucket gamma reserveCount
          residual x Q) ⊆
      G.largeEdgeJobs beta := by
  intro e he
  rcases (G.mem_ordinarySelectedEdges_iff _ e).mp he with ⟨o, ho, rfl⟩
  have hinl : Sum.inl o ∈ RankThreeOptionSystem.baseOptionSet N
      (G.dyadicLargeEdgeMass K bucket gamma reserveCount residual x) Q :=
    (RankThreeOptionSystem.mem_leftOptionSet_iff _ o).mp ho
  rcases (RankThreeOptionSystem.mem_baseOptionSet_iff N _ Q
      (Sum.inl o)).mp hinl with ⟨copy, hcopy, hcopyBase⟩
  apply G.mem_largeEdgeJobs.mpr
  have hlarge := howner copy hcopy
  rw [hcopyBase] at hlarge
  exact hlarge

end WeightedMultigraph

end

end WeightedEdgeColoring
