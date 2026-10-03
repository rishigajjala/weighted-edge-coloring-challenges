import WeightedEdgeColoring.LargeEdgeJobRestrictionBridge
import WeightedEdgeColoring.RankThreeOriginalTypeEndpointIteration

/-!
# Lifting an endpoint trace back to the original large edges
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

universe u v w

variable (G : WeightedSimpleGraph.{u})
  {Slot : Type v} {Option : Type w}
  [Fintype Slot] [Fintype Option]
  [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem G.E Slot Option)

/-- The uncovered large-edge weight of a lifted matching is exactly the
complement-of-covered-jobs sum on the large-edge restriction. -/
theorem uncoveredLargeStarWeight_lift_eq_restricted_complement
    (beta : ℝ)
    (A : Finset (H.ActiveJobOption (G.largeEdgeJobs beta))) (v : G.V) :
    G.uncoveredLargeStarWeight H beta (G.liftLargeEdgeJobSet H beta A) v =
      ∑ e ∈ Finset.univ \
          (Finset.univ.filter ((G.largeEdgeJobSystem H beta).Covers A)),
        if (G.largeEdgeRestriction beta).Inc v e then
          (G.largeEdgeRestriction beta).weight e else 0 := by
  classical
  unfold uncoveredLargeStarWeight activeStarEdgeSet
  rw [Finset.sum_filter]
  let S : Finset (G.largeEdgeRestriction beta).E :=
    Finset.univ \
      Finset.univ.filter ((G.largeEdgeJobSystem H beta).Covers A)
  have hset :
      G.uncoveredLargeEdges H beta (G.liftLargeEdgeJobSet H beta A) =
        S.image (fun e : (G.largeEdgeRestriction beta).E ↦ e.1) := by
    ext e
    constructor
    · intro he
      rcases (G.mem_uncoveredLargeEdges H).mp he with
        ⟨heLarge, heUncovered⟩
      let ee : (G.largeEdgeRestriction beta).E :=
        ⟨e, G.mem_largeEdgeJobs.mpr heLarge⟩
      apply Finset.mem_image.mpr
      refine ⟨ee, ?_, rfl⟩
      have heNotCovered :
          ¬ (G.largeEdgeJobSystem H beta).Covers A ee := by
        intro heCovered
        exact heUncovered
          ((G.covers_liftLargeEdgeJobSet_iff H beta A ee).mpr heCovered)
      simp [S, heNotCovered]
    · intro he
      rcases Finset.mem_image.mp he with ⟨ee, heS, rfl⟩
      have heNotCovered :
          ¬ (G.largeEdgeJobSystem H beta).Covers A ee := by
        simpa [S] using heS
      apply (G.mem_uncoveredLargeEdges H).mpr
      refine ⟨G.mem_largeEdgeJobs.mp ee.2, ?_⟩
      intro heCovered
      exact heNotCovered
        ((G.covers_liftLargeEdgeJobSet_iff H beta A ee).mp heCovered)
  have hinj : Set.InjOn
      (fun e : (G.largeEdgeRestriction beta).E ↦ e.1) (S : Set _) := by
    intro e _ f _ hef
    exact Subtype.ext hef
  change (∑ e ∈ G.uncoveredLargeEdges H beta
      (G.liftLargeEdgeJobSet H beta A),
        if G.Inc v e then G.weight e else 0) = _
  rw [hset, Finset.sum_image hinj]
  rfl

/- Consequently the trace's final active-star quantity is already the
uncovered weight needed by the graph decoder. -/
set_option maxHeartbeats 800000 in
theorem endpointSharpTrace_uncoveredLargeStarWeight_lift_eq_state
    {beta a delta : ℝ} {L K steps : ℕ}
    {Afinal : RankThreeOptionSystem.OriginalIterationState
      (G.largeEdgeJobSystem H beta)}
    (T : RankThreeOptionSystem.OriginalIterationState.EndpointSharpTrace
      (G.largeEdgeRestriction beta) beta a delta L K steps
      (RankThreeOptionSystem.OriginalIterationState.full
        (G.largeEdgeJobSystem H beta)) Afinal)
    (hactive0 : ∀ j, j ∈ (G.largeEdgeJobSystem H beta).activeJobs)
    (v : G.V) :
    G.uncoveredLargeStarWeight H beta
        (G.liftLargeEdgeJobSet H beta Afinal.matching) v =
      RankThreeOptionSystem.OriginalIterationState.stateActiveStarWeight
        (G.largeEdgeRestriction beta) Afinal v := by
  rw [G.uncoveredLargeStarWeight_lift_eq_restricted_complement H beta
    Afinal.matching v]
  exact T.uncoveredStar_eq_stateActiveStarWeight
    (G.largeEdgeRestriction beta)
    ((RankThreeOptionSystem.OriginalIterationState.full_activeJobs_eq_uncovered
      (H := G.largeEdgeJobSystem H beta) (G.largeEdgeRestriction beta)) hactive0) v

end WeightedSimpleGraph

end

end WeightedEdgeColoring
