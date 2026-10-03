import WeightedEdgeColoring.SubtwoMixedCoreGroupingTypes

/-! Recover original edge colors after global core grouping. -/

set_option maxHeartbeats 4000000
open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
namespace SubtwoMixedCoreGrouping
variable (G : WeightedMultigraph.{u}) (F : Finset G.E) (M : ℕ)

theorem exists_original_partialColor
    (hM : 0 < M) (S : ℕ) (hS : 0 < S)
    (hlower : ∀ e ∈ F, (1 : ℝ)/S ≤ G.weight e) {n : ℕ}
    (hlocal : G.LocallyPacksInto n)
    (R : Finset (graph G F M).E) (K : ℕ) (hK : 0 < K)
    (color : (graph G F M).E → Fin K)
    (hcolor : (graph G F M).IsFeasibleOn R color)
    (loss : ℝ)
    (hresidual : ∀ v, (∑ e ∈ Finset.univ \ R,
      if (graph G F M).Inc v e then (graph G F M).weight e else 0) ≤ loss) :
    ∃ A : Finset G.E, ∃ lifted : G.E → Fin K,
      G.IsFeasibleOn A lifted ∧
      (∀ e ∈ R, target G F M e ∈ A ∧ lifted (target G F M e) = color e) ∧
      ∀ v, (∑ e ∈ Finset.univ \ A, if G.Inc v e then G.weight e else 0) ≤
        (2*(S : ℝ)/M)*n+loss := by
  classical
  obtain ⟨lifted,hlift,hsame,hleft⟩ := G.exists_lift_injective_partialColor_le
    (graph G F M) id (target G F M) (target_injective G F M)
    (target_inc G F M) (target_weight_le G F M) R K hK color hcolor
  let A := R.image (target G F M)
  let T := retained G F M
  have hAT : A ⊆ T := Finset.image_subset_image (Finset.subset_univ R)
  have hdisj : Disjoint (Finset.univ \ T) (T \ A) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (Finset.mem_sdiff.mp he).2 (Finset.mem_sdiff.mp hf).1
  have hsplit : Finset.univ \ A = (Finset.univ \ T) ∪ (T \ A) := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro ha
      by_cases ht : e ∈ T
      · exact Or.inr ⟨ht,ha⟩
      · exact Or.inl ht
    · rintro (ht | ⟨_,ha⟩)
      · exact fun ha => ht (hAT ha)
      · exact ha
  refine ⟨A,lifted,hlift,?_,?_⟩
  · intro e he
    exact ⟨Finset.mem_image.mpr ⟨e,he,rfl⟩,hsame e he⟩
  · intro v
    rw [hsplit, Finset.sum_union hdisj]
    exact add_le_add (omitted_weight_le G F M hM S hS hlower hlocal v)
      ((hleft v).trans (hresidual v))

/-- The grouping width depends on the cutoff and error, before any graph. -/
theorem exists_uniform_groupingWidth (S : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ M : ℕ, 0 < M ∧ (2*(S : ℝ)/M) ≤ η := by
  let M : ℕ := max 1 (Nat.ceil (2*(S : ℝ)/η))
  have hM : 0 < M := by dsimp [M]; omega
  have hb : 2*(S : ℝ)/η ≤ M := (Nat.le_ceil _).trans (by
    dsimp only [M]
    exact_mod_cast le_max_right 1 (Nat.ceil (2*(S : ℝ)/η)))
  refine ⟨M,hM,?_⟩
  apply (div_le_iff₀ (by exact_mod_cast hM : (0 : ℝ)<M)).2
  have h := (div_le_iff₀ hη).1 hb
  nlinarith

theorem exists_original_partialColor_of_groupingWidth
    (hM : 0 < M) (S : ℕ) (hS : 0 < S) (η : ℝ)
    (hwidth : 2*(S : ℝ)/M ≤ η)
    (hlower : ∀ e ∈ F, (1 : ℝ)/S ≤ G.weight e) {n : ℕ}
    (hlocal : G.LocallyPacksInto n)
    (R : Finset (graph G F M).E) (K : ℕ) (hK : 0 < K)
    (color : (graph G F M).E → Fin K)
    (hcolor : (graph G F M).IsFeasibleOn R color)
    (loss : ℝ)
    (hresidual : ∀ v, (∑ e ∈ Finset.univ \ R,
      if (graph G F M).Inc v e then (graph G F M).weight e else 0) ≤ loss) :
    ∃ A : Finset G.E, ∃ lifted : G.E → Fin K,
      G.IsFeasibleOn A lifted ∧
      ∀ v, (∑ e ∈ Finset.univ \ A, if G.Inc v e then G.weight e else 0) ≤ η*n+loss := by
  obtain ⟨A,lifted,hfeasible,_,hleft⟩ := exists_original_partialColor G F M
    hM S hS hlower hlocal R K hK color hcolor loss hresidual
  refine ⟨A,lifted,hfeasible,?_⟩
  intro v
  exact (hleft v).trans (add_le_add
    (mul_le_mul_of_nonneg_right hwidth (Nat.cast_nonneg n)) le_rfl)

end SubtwoMixedCoreGrouping
end
end WeightedEdgeColoring.WeightedMultigraph
