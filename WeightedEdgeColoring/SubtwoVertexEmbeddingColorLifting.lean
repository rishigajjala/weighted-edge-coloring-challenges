import WeightedEdgeColoring.SubtwoInjectiveColorLifting

/-! A partial coloring on a vertex-induced block lifts to the ambient graph. -/

open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G H : WeightedMultigraph.{u})
variable (vertex : H.V ↪ G.V) (edge : H.E → G.E)

/-- Incidence at a retained vertex is preserved by a graph embedding. -/
theorem subtwoEmbedding_inc
    (hfst : ∀ e, G.fst (edge e) = vertex (H.fst e))
    (hsnd : ∀ e, G.snd (edge e) = vertex (H.snd e))
    (v : H.V) (e : H.E) : G.Inc (vertex v) (edge e) ↔ H.Inc v e := by
  unfold Inc
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl (vertex.injective ((hfst e).symm.trans h))
    · exact Or.inr (vertex.injective ((hsnd e).symm.trans h))
  · intro h
    rcases h with h | h
    · exact Or.inl ((hfst e).trans (congrArg vertex h))
    · exact Or.inr ((hsnd e).trans (congrArg vertex h))

/-- The lifted coloring has zero load outside the embedded vertex block.
At its actual vertices, selected colors and leftover weights are exact. -/
theorem exists_lift_vertexEmbedded_partialColor
    (hinj : Function.Injective edge)
    (hfst : ∀ e, G.fst (edge e) = vertex (H.fst e))
    (hsnd : ∀ e, G.snd (edge e) = vertex (H.snd e))
    (hweight : ∀ e, H.weight e = G.weight (edge e))
    (R : Finset H.E) (K : ℕ) (hK : 0 < K)
    (color : H.E → Fin K) (hcolor : H.IsFeasibleOn R color) :
    ∃ lifted : G.E → Fin K,
      G.IsFeasibleOn (R.image edge) lifted ∧
      (∀ e ∈ R, lifted (edge e) = color e) ∧
      ∀ v : H.V, (∑ e ∈ (Finset.univ.image edge) \ (R.image edge),
        if G.Inc (vertex v) e then G.weight e else 0) =
        ∑ e ∈ Finset.univ \ R, if H.Inc v e then H.weight e else 0 := by
  classical
  let lifted : G.E → Fin K := fun e =>
    if h : ∃ f ∈ R, edge f = e then color (Classical.choose h) else ⟨0,hK⟩
  have hsame : ∀ e ∈ R, lifted (edge e) = color e := by
    intro e he
    have hex : ∃ f ∈ R, edge f = edge e := ⟨e,he,rfl⟩
    have heq : Classical.choose hex = e := hinj (Classical.choose_spec hex).2
    simp only [lifted, dif_pos hex, heq]
  refine ⟨lifted, ?_, hsame, ?_⟩
  · intro v c
    by_cases hv : v ∈ Set.range vertex
    · obtain ⟨w,rfl⟩ := hv
      have heq : G.colorLoadOn (R.image edge) lifted (vertex w) c =
          H.colorLoadOn R color w c := by
        unfold colorLoadOn
        rw [Finset.sum_image hinj.injOn]
        apply Finset.sum_congr rfl
        intro e he
        simp only [hsame e he, G.subtwoEmbedding_inc H vertex edge hfst hsnd, ← hweight e]
      rw [heq]
      exact hcolor w c
    · have hzero : G.colorLoadOn (R.image edge) lifted v c = 0 := by
        unfold colorLoadOn
        rw [Finset.sum_image hinj.injOn]
        apply Finset.sum_eq_zero
        intro e _
        have hi : ¬G.Inc v (edge e) := by
          intro h
          rcases h with h | h
          · exact hv ⟨H.fst e,(hfst e).symm.trans h⟩
          · exact hv ⟨H.snd e,(hsnd e).symm.trans h⟩
        simp [hi]
      rw [hzero]
      norm_num
  · intro v
    have hsets : (Finset.univ.image edge) \ (R.image edge) =
        (Finset.univ \ R).image edge := by
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨f,hf⟩, hn⟩
        exact ⟨f,fun hr => hn ⟨f,hr,hf⟩,hf⟩
      · rintro ⟨f,hf,hfe⟩
        refine ⟨⟨f,hfe⟩, ?_⟩
        rintro ⟨g,hg,hge⟩
        exact hf (hinj (hfe.trans hge.symm) ▸ hg)
    rw [hsets, Finset.sum_image hinj.injOn]
    apply Finset.sum_congr rfl
    intro e _
    simp only [G.subtwoEmbedding_inc H vertex edge hfst hsnd, ← hweight e]

end
end WeightedEdgeColoring.WeightedMultigraph
