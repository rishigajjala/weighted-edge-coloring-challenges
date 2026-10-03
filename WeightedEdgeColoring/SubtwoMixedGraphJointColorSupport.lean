import WeightedEdgeColoring.SubtwoMixedGraphProposalSupport
import WeightedEdgeColoring.SubtwoMixedGraphFeasibleRelativeDecoderSupport

/-! The actual joint color retains its selected ordinary or tiny option. -/

namespace WeightedEdgeColoring
open scoped BigOperators
noncomputable section
namespace WeightedMultigraph
universe u
variable (G : WeightedMultigraph.{u})

/-- On a selected ordinary edge, the joint color equals the unique matching
option's color.  The arbitrary default outside the selected set is irrelevant. -/
theorem ordinaryTinyJointColor_selectedOption
    {q K : ℕ} (hq : 0 < q)
    (O : Finset (OrdinarySlotChoice G.E (Fin q) K))
    (hO : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching O)
    (T : Finset G.E)
    (decision : {e : G.E // e ∈ T} → Option (Fin q))
    {e : G.E} (he : e ∈ G.ordinarySelectedEdges O) :
    ∃ o ∈ O, o.job = e ∧
      G.ordinaryTinyJointColor hq O hO T decision e = o.color := by
  let o := G.selectedOrdinaryOption O hO e he
  refine ⟨o, G.selectedOrdinaryOption_mem O hO e he,
    G.selectedOrdinaryOption_job O hO e he, ?_⟩
  simp [ordinaryTinyJointColor, he, selectedOrdinaryColor, o]

/-- On a selected tiny edge outside the ordinary set, the joint color is
exactly the tiny decision's selected color. -/
theorem ordinaryTinyJointColor_tinyDecision
    {q K : ℕ} (hq : 0 < q)
    (O : Finset (OrdinarySlotChoice G.E (Fin q) K))
    (hO : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching O)
    (T : Finset G.E)
    (decision : {e : G.E // e ∈ T} → Option (Fin q))
    (hdisj : Disjoint (G.ordinarySelectedEdges O) T)
    {e : G.E} (he : e ∈ G.tinyDecisionColoredEdges T decision) :
    ∃ hT : e ∈ T,
      decision ⟨e,hT⟩ = some
        (G.ordinaryTinyJointColor hq O hO T decision e) := by
  have hT : e ∈ T := (Finset.mem_filter.mp he).1
  have hnot : e ∉ G.ordinarySelectedEdges O := by
    intro hOrd
    exact Finset.disjoint_left.mp hdisj hOrd hT
  have hne : G.tinyDecisionAt T decision e ≠ none :=
    (Finset.mem_filter.mp he).2
  have hsome : ∃ d, G.tinyDecisionAt T decision e = some d := by
    cases h : G.tinyDecisionAt T decision e with
    | none => exact (hne h).elim
    | some d => exact ⟨d,rfl⟩
  obtain ⟨d,hd⟩ := hsome
  refine ⟨hT, ?_⟩
  have hdecision : decision ⟨e,hT⟩ = some d := by
    simpa [G.tinyDecisionAt_of_mem T decision hT] using hd
  rw [hdecision]
  simp [ordinaryTinyJointColor, hnot, G.tinyDecisionAt_of_mem T decision hT,
    hdecision]

end WeightedMultigraph
end
end WeightedEdgeColoring
