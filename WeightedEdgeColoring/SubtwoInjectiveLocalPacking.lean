import WeightedEdgeColoring.WeightedMultigraph

/-! Local bins pull back along an injection into heavier original edges. -/

open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u

theorem locallyPacksInto_of_injective_heavier_edges
    (G H : WeightedMultigraph.{u}) (vertex : H.V → G.V) (edge : H.E → G.E)
    (hinj : Function.Injective edge)
    (hinc : ∀ v e, H.Inc v e → G.Inc (vertex v) (edge e))
    (hweight : ∀ e, H.weight e ≤ G.weight (edge e))
    {n : ℕ} (hlocal : G.LocallyPacksInto n) : H.LocallyPacksInto n := by
  classical
  intro v
  obtain ⟨bin, hbin⟩ := hlocal (vertex v)
  let embed : H.StarEdge v ↪ G.StarEdge (vertex v) :=
    ⟨fun e => ⟨edge e.val, hinc v e.val e.property⟩, by
      intro e f hef
      exact Subtype.ext (hinj (congrArg Subtype.val hef))⟩
  let newbin : H.StarEdge v → Fin n := fun e => bin (embed e)
  refine ⟨newbin, ?_⟩
  intro c
  calc
    H.starBinLoad newbin c ≤
        ∑ e : H.StarEdge v, if bin (embed e) = c then G.weight (edge e.val) else 0 := by
      apply Finset.sum_le_sum
      intro e _
      change (if bin (embed e) = c then H.weight e.val else 0) ≤ _
      split_ifs
      · exact hweight e.val
      · exact le_rfl
    _ = ∑ e ∈ Finset.univ.map embed, if bin e = c then G.weight e.val else 0 := by
      rw [Finset.sum_map]
      rfl
    _ ≤ G.starBinLoad bin c := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intro e _ _
        split_ifs
        · exact G.weight_nonneg e.val
        · exact le_rfl)
    _ ≤ 1 := hbin c

end
end WeightedEdgeColoring.WeightedMultigraph
