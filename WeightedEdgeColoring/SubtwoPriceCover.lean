import WeightedEdgeColoring.SubtwoTrianglePriceSort
import Mathlib.Tactic

/-! Every disjoint-packet price vector is either below one half or is
dominated, after a vertex relabeling, by the two-model simplex. -/

namespace WeightedEdgeColoring.Subtwo.PriceCover

open EndpointPotential TwoModelGeometry PriceRelabel TrianglePriceSort

private theorem price_eq_of_pair (p : Bundle → ℝ) (e : Bundle)
    (u v : Vertex) (huv : u ≠ v) (he : edge e = {u, v}) :
    p e = p (pairIndex u v huv) := by
  congr 1
  exact edge_injective (he.trans (edge_pairIndex u v huv).symm)

theorem no_high_or_model (p : Bundle → ℝ)
    (hdisjoint : ∀ e f : Bundle,
      Disjoint (edge e) (edge f) → p e + p f ≤ 1) :
    (∀ e : Bundle, p e ≤ (1 / 2 : ℝ)) ∨
      ∃ π : Equiv.Perm Vertex, ∃ a x y : ℝ,
        1 / 2 < a ∧ 1 - a ≤ y ∧ y ≤ x ∧ x ≤ a ∧
        ∀ e : Bundle, permutePrices π.symm p e ≤ M a x y e := by
  by_cases hnone : ∀ e : Bundle, p e ≤ (1 / 2 : ℝ)
  · exact Or.inl hnone
  right
  have hne : ∃ e : Bundle, (1 / 2 : ℝ) < p e := by
    push_neg at hnone
    exact hnone
  rcases high_price_support_star_or_triangle_fin10 p hdisjoint hne with
    ⟨v, hv⟩ | ⟨u, v, w, huv, huw, hvw, htri⟩
  · exact exists_star_model_cover p hdisjoint ⟨v, hv⟩ hne
  · by_cases hUV : (1 / 2 : ℝ) < p (pairIndex u v huv)
    · by_cases hUW : (1 / 2 : ℝ) < p (pairIndex u w huw)
      · by_cases hVW : (1 / 2 : ℝ) < p (pairIndex v w hvw)
        · exact exists_triangle_model_cover p hdisjoint u v w huv huw hvw hUV hUW hVW
        · have hstar : ∀ e : Bundle, (1 / 2 : ℝ) < p e → u ∈ edge e := by
            intro e he
            rcases htri e he with heuv | heuw | hevw
            · rw [heuv]; simp
            · rw [heuw]; simp
            · have hp := price_eq_of_pair p e v w hvw hevw
              linarith
          exact exists_star_model_cover p hdisjoint ⟨u, hstar⟩ hne
      · have hstar : ∀ e : Bundle, (1 / 2 : ℝ) < p e → v ∈ edge e := by
          intro e he
          rcases htri e he with heuv | heuw | hevw
          · rw [heuv]; simp
          · have hp := price_eq_of_pair p e u w huw heuw
            linarith
          · rw [hevw]; simp
        exact exists_star_model_cover p hdisjoint ⟨v, hstar⟩ hne
    · have hstar : ∀ e : Bundle, (1 / 2 : ℝ) < p e → w ∈ edge e := by
        intro e he
        rcases htri e he with heuv | heuw | hevw
        · have hp := price_eq_of_pair p e u v huv heuv
          linarith
        · rw [heuw]; simp
        · rw [hevw]; simp
      exact exists_star_model_cover p hdisjoint ⟨w, hstar⟩ hne

end WeightedEdgeColoring.Subtwo.PriceCover
