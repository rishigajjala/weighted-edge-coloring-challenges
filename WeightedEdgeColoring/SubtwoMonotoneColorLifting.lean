import WeightedEdgeColoring.SubtwoInjectiveColorLifting

/-! Colors on rounded-up edges also color their smaller physical targets. -/

open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G H : WeightedMultigraph.{u}) (vertex : G.V → H.V) (edge : H.E → G.E)

theorem exists_lift_injective_partialColor_le
    (hinj : Function.Injective edge)
    (hinc : ∀ v e, H.Inc (vertex v) e ↔ G.Inc v (edge e))
    (hweight : ∀ e, G.weight (edge e) ≤ H.weight e)
    (R : Finset H.E) (K : ℕ) (hK : 0 < K)
    (color : H.E → Fin K) (hcolor : H.IsFeasibleOn R color) :
    ∃ lifted : G.E → Fin K,
      G.IsFeasibleOn (R.image edge) lifted ∧
      (∀ e ∈ R, lifted (edge e) = color e) ∧
      ∀ v, (∑ e ∈ (Finset.univ.image edge) \ (R.image edge),
        if G.Inc v e then G.weight e else 0) ≤
        ∑ e ∈ Finset.univ \ R, if H.Inc (vertex v) e then H.weight e else 0 := by
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
    calc
      G.colorLoadOn (R.image edge) lifted v c ≤ H.colorLoadOn R color (vertex v) c := by
        unfold colorLoadOn
        rw [Finset.sum_image hinj.injOn]
        apply Finset.sum_le_sum
        intro e he
        simp only [hsame e he, ← hinc v e]
        split_ifs
        · exact hweight e
        · exact le_rfl
      _ ≤ 1 := hcolor (vertex v) c
  · intro v
    have hsets : (Finset.univ.image edge) \ (R.image edge) =
        (Finset.univ \ R).image edge := by
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨f,hf⟩, hn⟩
        refine ⟨f, ?_, hf⟩
        exact fun hr => hn ⟨f,hr,hf⟩
      · rintro ⟨f, hf, hfe⟩
        refine ⟨⟨f,hfe⟩, ?_⟩
        rintro ⟨g,hg,hge⟩
        exact hf (hinj (hfe.trans hge.symm) ▸ hg)
    rw [hsets, Finset.sum_image hinj.injOn]
    apply Finset.sum_le_sum
    intro e _
    simp only [← hinc v e]
    split_ifs
    · exact hweight e
    · exact le_rfl

end
end WeightedEdgeColoring.WeightedMultigraph
