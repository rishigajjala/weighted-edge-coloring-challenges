import WeightedEdgeColoring.MultigraphDyadicLargeEdgeTotalLoss
import WeightedEdgeColoring.MultigraphExtendedProfileSelectedDyadicJointLoad

/-!
# Whole residual after the local-dyadic and tiny decoders

The palette decoder colors the ordinary part of the large-edge matching and
the `some` part of the tiny-edge decision.  The complement splits exactly
into the remaining large edges and the `none` tiny decisions.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]

theorem ordinarySelectedEdges_selectedDyadicOrdinaryBaseOptions
    (q K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Fin q → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))) :
    G.ordinarySelectedEdges
        (G.selectedDyadicOrdinaryBaseOptions q K N bucket gamma reserve
          residual x M) =
      G.selectedDyadicOrdinaryEdges K N bucket gamma reserve residual x M := by
  rfl

/-- The integral tiny loss is the star weight of tiny edges whose decision
is `none`. -/
theorem tinyResidualIntegralLossLoad_eq_sum_sdiff
    {q : ℕ} (R : Finset G.E)
    (decision : {e : G.E // e ∈ R} → Option (Fin q)) (v : G.V) :
    G.tinyResidualIntegralLossLoad decision v =
      ∑ e ∈ R \ G.tinyDecisionColoredEdges R decision,
        if G.Inc v e then G.weight e else 0 := by
  classical
  unfold tinyResidualIntegralLossLoad tinyDecisionColoredEdges
  rw [show R \ R.filter
      (fun e ↦ G.tinyDecisionAt R decision e ≠ none) =
      R.filter (fun e ↦ G.tinyDecisionAt R decision e = none) by
        ext e
        simp only [Finset.mem_sdiff, Finset.mem_filter]
        constructor
        · rintro ⟨heR, hnot⟩
          refine ⟨heR, ?_⟩
          by_contra hne
          exact hnot ⟨heR, hne⟩
        · rintro ⟨heR, heq⟩
          refine ⟨heR, ?_⟩
          rintro ⟨_, hne⟩
          exact hne heq]
  rw [Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun e : G.E ↦ e ∈ R) R
    (by intro e; simp)]
  apply Finset.sum_congr rfl
  intro e _he
  rw [G.tinyDecisionAt_of_mem R decision e.2]
  by_cases hinc : G.Inc v e.1
  · cases hdecision : decision e <;> simp [hinc, hdecision]
  · simp [hinc]

/-- Exact large/tiny partition of the uncolored set. -/
theorem uncolored_dyadic_joint_eq_large_union_tiny
    (q K N : ℕ) (beta : ℝ) (bucket : G.E → Class) (gamma : ℝ)
    (reserve : ℕ) (residual : G.E → ℝ)
    (x : G.E → Fin q → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (decision : {e : G.E // e ∈ G.selectedBlockTinyEdges beta} →
      Option (Fin q))
    (hdisjoint : Disjoint
      (G.ordinarySelectedEdges
        (G.selectedDyadicOrdinaryBaseOptions q K N bucket gamma reserve
          residual x M))
      (G.selectedBlockTinyEdges beta)) :
    Finset.univ \ (G.ordinarySelectedEdges
        (G.selectedDyadicOrdinaryBaseOptions q K N bucket gamma reserve
          residual x M) ∪
      G.tinyDecisionColoredEdges (G.selectedBlockTinyEdges beta) decision) =
      G.dyadicLargeEdgesRemainingAfterOrdinary K N beta bucket gamma reserve
          residual x M ∪
        (G.selectedBlockTinyEdges beta \
          G.tinyDecisionColoredEdges (G.selectedBlockTinyEdges beta)
            decision) := by
  classical
  ext e
  have hordTiny : e ∈ G.ordinarySelectedEdges
        (G.selectedDyadicOrdinaryBaseOptions q K N bucket gamma reserve
          residual x M) → e ∉ G.selectedBlockTinyEdges beta := by
    intro heOrd heTiny
    exact Finset.disjoint_left.mp hdisjoint heOrd heTiny
  have htinyColored : e ∈ G.tinyDecisionColoredEdges
      (G.selectedBlockTinyEdges beta) decision →
      e ∈ G.selectedBlockTinyEdges beta := by
    intro he
    exact (Finset.mem_filter.mp he).1
  rw [G.ordinarySelectedEdges_selectedDyadicOrdinaryBaseOptions]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
    dyadicLargeEdgesRemainingAfterOrdinary, G.mem_largeEdgeJobs,
    G.mem_selectedBlockTinyEdges]
  by_cases hlarge : beta ≤ G.weight e
  · have hnotTiny : ¬G.weight e < beta := not_lt.mpr hlarge
    have hnotTinyColored : e ∉ G.tinyDecisionColoredEdges
        (G.selectedBlockTinyEdges beta) decision := by
      intro he
      exact hnotTiny (G.mem_selectedBlockTinyEdges.mp (htinyColored he))
    simp [hlarge, hnotTiny, hnotTinyColored]
  · have htiny : G.weight e < beta := lt_of_not_ge hlarge
    have hnotOrdinary : e ∉ G.selectedDyadicOrdinaryEdges K N bucket gamma
        reserve residual x M := by
      rw [← G.ordinarySelectedEdges_selectedDyadicOrdinaryBaseOptions]
      intro he
      exact hordTiny he (G.mem_selectedBlockTinyEdges.mpr htiny)
    simp [hlarge, htiny, hnotOrdinary]

/-- Exact star-weight decomposition after both decoders. -/
theorem uncolored_dyadic_joint_starWeight_eq
    (q K N : ℕ) (beta : ℝ) (bucket : G.E → Class) (gamma : ℝ)
    (reserve : ℕ) (residual : G.E → ℝ)
    (x : G.E → Fin q → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (decision : {e : G.E // e ∈ G.selectedBlockTinyEdges beta} →
      Option (Fin q))
    (hdisjoint : Disjoint
      (G.ordinarySelectedEdges
        (G.selectedDyadicOrdinaryBaseOptions q K N bucket gamma reserve
          residual x M))
      (G.selectedBlockTinyEdges beta)) (v : G.V) :
    (∑ e ∈ Finset.univ \ (G.ordinarySelectedEdges
        (G.selectedDyadicOrdinaryBaseOptions q K N bucket gamma reserve
          residual x M) ∪
      G.tinyDecisionColoredEdges (G.selectedBlockTinyEdges beta) decision),
        if G.Inc v e then G.weight e else 0) =
      G.dyadicLargeRemainingStarWeight K N beta bucket gamma reserve residual x
          M v + G.tinyResidualIntegralLossLoad decision v := by
  classical
  rw [G.uncolored_dyadic_joint_eq_large_union_tiny q K N beta bucket gamma
    reserve residual x M decision hdisjoint]
  have hparts : Disjoint
      (G.dyadicLargeEdgesRemainingAfterOrdinary K N beta bucket gamma reserve
        residual x M)
      (G.selectedBlockTinyEdges beta \
        G.tinyDecisionColoredEdges (G.selectedBlockTinyEdges beta)
          decision) := by
    rw [Finset.disjoint_left]
    intro e heLarge heTiny
    have hge := (Finset.mem_sdiff.mp heLarge).1
    have hlt := G.mem_selectedBlockTinyEdges.mp (Finset.mem_sdiff.mp heTiny).1
    exact (not_lt_of_ge (G.mem_largeEdgeJobs.mp hge)) hlt
  rw [Finset.sum_union hparts]
  unfold dyadicLargeRemainingStarWeight
  rw [Finset.sum_filter]
  rw [G.tinyResidualIntegralLossLoad_eq_sum_sdiff]

end WeightedMultigraph

end

end WeightedEdgeColoring
