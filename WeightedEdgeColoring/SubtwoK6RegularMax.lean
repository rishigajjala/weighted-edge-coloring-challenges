import WeightedEdgeColoring.SubtwoK6RegularCompletion
import WeightedEdgeColoring.SubtwoLinearQuadraticMax

/-! A regular fractional matching maximizing any price has no nonzero
symmetric feasible perturbation after a secondary square maximization. -/

namespace WeightedEdgeColoring.Subtwo.K6MatchingDeficits

def RegularFeasible (x : Edge → ℝ) : Prop :=
  (∀ e, 0 ≤ x e) ∧ (∀ v, degree x v = 1) ∧
    ∀ S : Finset Vertex, S.card = 3 → triangleMass x S ≤ 1

theorem continuous_degree (v : Vertex) : Continuous (fun x : Edge → ℝ ↦ degree x v) := by
  simp_rw [degree_eq_incidence_sum]
  apply continuous_finset_sum
  intro e _
  by_cases h : v ∈ ends e
  · simpa only [if_pos h] using (continuous_apply e : Continuous (fun x : Edge → ℝ ↦ x e))
  · simpa only [if_neg h] using (continuous_const : Continuous (fun _ : Edge → ℝ ↦ (0 : ℝ)))

theorem continuous_triangleMass (S : Finset Vertex) :
    Continuous (fun x : Edge → ℝ ↦ triangleMass x S) := by
  simp_rw [mass_eq_coeff]
  exact continuous_finset_sum _ fun e _ ↦ continuous_const.mul (continuous_apply e)

theorem regular_isClosed : IsClosed {x : Edge → ℝ | RegularFeasible x} := by
  have hlo : IsClosed {x : Edge → ℝ | ∀ e, 0 ≤ x e} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun e ↦ isClosed_le continuous_const (continuous_apply e)
  have hd : IsClosed {x : Edge → ℝ | ∀ v, degree x v = 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun v ↦ isClosed_eq (continuous_degree v) continuous_const
  have ht : IsClosed {x : Edge → ℝ | ∀ S : Finset Vertex,
      S.card = 3 → triangleMass x S ≤ 1} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro S
    apply isClosed_iInter
    intro _hS
    exact isClosed_le (continuous_triangleMass S) continuous_const
  exact hlo.inter (hd.inter ht)

theorem regular_isCompact : IsCompact {x : Edge → ℝ | RegularFeasible x} := by
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc (a := fun _ : Edge ↦ (0 : ℝ)) (b := fun _ ↦ (1 : ℝ)))
    regular_isClosed
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro e
  obtain ⟨v, hv⟩ := ends_nonempty e
  exact (edge_le_degree x hx.1 e v hv).trans_eq (hx.2.1 v)

theorem exists_regular_max (p x : Edge → ℝ) (hx : RegularFeasible x) :
    ∃ y : Edge → ℝ, RegularFeasible y ∧
      (∑ e, p e * x e) ≤ (∑ e, p e * y e) ∧
      ∀ d : Edge → ℝ, (∃ e, d e ≠ 0) →
        RegularFeasible (fun e ↦ y e + d e) →
        RegularFeasible (fun e ↦ y e - d e) → False := by
  obtain ⟨y, hy, hmax, hsq⟩ := LinearQuadraticMax.exists_max
    {z : Edge → ℝ | RegularFeasible z} regular_isCompact ⟨x, hx⟩ p
  refine ⟨y, hy, hmax x hx, ?_⟩
  intro d hd hp hm
  exact LinearQuadraticMax.no_symmetric_perturbation _ p y hmax hsq d hd hp hm

end WeightedEdgeColoring.Subtwo.K6MatchingDeficits
