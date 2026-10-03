import WeightedEdgeColoring.SubtwoK6MatchingPrice

/-! The explicit decompositions in the K₆ matching proof use only perfect matchings.
This version asks for their price rows alone. -/

namespace WeightedEdgeColoring.Subtwo.K6MatchingDeficits
open K6SupportReal

def IsPerfectMatching (M : Finset Edge) : Prop :=
  IsMatching M ∧ M.card = 3

theorem unitMatching_isPerfect : ∀ h i, IsPerfectMatching (unitMatching h i) := by
  intro h i
  constructor
  · exact unitMatching_isMatching h i
  · decide +revert

theorem allTriangleMatching_isPerfect : ∀ h i j,
    IsPerfectMatching (allTriangleMatching h i j) := by
  intro h i j
  constructor
  · exact allTriangleMatching_isMatching h i j
  · decide +revert

theorem weighted_sum_le_one_of_unit_edge_perfect (x p : Edge → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hd : ∀ v : Vertex, degree x v = 1)
    (h : Edge) (he : x h = 1)
    (hp : ∀ M : Finset Edge, IsPerfectMatching M → (∑ e ∈ M, p e) ≤ 1) :
    (∑ e : Edge, p e * x e) ≤ 1 := by
  rw [weighted_sum_eq_unitMatchings x p hx hd h he]
  calc
    (∑ i : Fin 3, x (unitCoefficientEdge h i) * (∑ e ∈ unitMatching h i, p e)) ≤
        ∑ i : Fin 3, x (unitCoefficientEdge h i) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_of_le_one_right (hx _) (hp _ (unitMatching_isPerfect h i))
    _ = 1 := unitCoefficientMass_eq_one x hx hd h he

theorem weighted_sum_le_one_of_tight_triangle_perfect (x p : Edge → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hd : ∀ v : Vertex, degree x v = 1)
    (S : Finset Vertex) (hS : S.card = 3) (ht : triangleMass x S = 1)
    (hp : ∀ M : Finset Edge, IsPerfectMatching M → (∑ e ∈ M, p e) ≤ 1) :
    (∑ e : Edge, p e * x e) ≤ 1 := by
  obtain ⟨h, rfl⟩ := exists_allTriangle S hS
  rw [weighted_sum_eq_allTrianglePairs x p h hd ht]
  calc
    (∑ i : Fin 3, ∑ j : Fin 3,
      x (allCross h i j) * (∑ e ∈ allTriangleMatching h i j, p e)) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, x (allCross h i j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_of_le_one_right (hx _) (hp _ (allTriangleMatching_isPerfect h i j))
    _ = 1 := allTriangleCross_mass x h hd ht

theorem weighted_sum_le_one_of_regular_perfect (x p : Edge → ℝ)
    (hx : RegularFeasible x)
    (hp : ∀ M : Finset Edge, IsPerfectMatching M → (∑ e ∈ M, p e) ≤ 1) :
    (∑ e : Edge, p e * x e) ≤ 1 := by
  obtain ⟨y, hy, hxy, hno⟩ := exists_regular_max p x hx
  apply hxy.trans
  by_cases ht : ∃ S : Finset Vertex, S.card = 3 ∧ triangleMass y S = 1
  · obtain ⟨S, hS, hmass⟩ := ht
    exact weighted_sum_le_one_of_tight_triangle_perfect y p hy.1 hy.2.1 S hS hmass hp
  · have hstrict : ∀ S : Finset Vertex, S.card = 3 → triangleMass y S < 1 := by
      intro S hS
      have hle := hy.2.2 S hS
      have hne : triangleMass y S ≠ 1 := by
        intro heq
        exact ht ⟨S, hS, heq⟩
      exact lt_of_le_of_ne hle hne
    have hlow := strict_no_symmetric_implies_low_support y hy hstrict hno
    obtain ⟨e, he⟩ := low_support_has_unit_edge y hy hlow
    exact weighted_sum_le_one_of_unit_edge_perfect y p hy.1 hy.2.1 e he hp

theorem weighted_sum_le_one_of_fractional_matching_perfect (x p : Edge → ℝ)
    (hp0 : ∀ e, 0 ≤ p e)
    (hx0 : ∀ e, 0 ≤ x e)
    (hd : ∀ v, degree x v ≤ 1)
    (ht : ∀ S : Finset Vertex, S.card = 3 → triangleMass x S ≤ 1)
    (hf : ∀ v, omitFive x v ≤ 2)
    (hp : ∀ M : Finset Edge, IsPerfectMatching M → (∑ e ∈ M, p e) ≤ 1) :
    (∑ e : Edge, p e * x e) ≤ 1 := by
  obtain ⟨y, hxy, hy0, hyd, hyt⟩ := exists_regular_completion x hx0 hd ht hf
  have hprofit : (∑ e : Edge, p e * x e) ≤ (∑ e : Edge, p e * y e) := by
    apply Finset.sum_le_sum
    intro e _
    exact mul_le_mul_of_nonneg_left (hxy e) (hp0 e)
  exact hprofit.trans (weighted_sum_le_one_of_regular_perfect y p ⟨hy0, hyd, hyt⟩ hp)

theorem weighted_sum_le_scale_of_perfect_prices (x p : Edge → ℝ) (a : ℝ)
    (ha : 0 < a)
    (hp0 : ∀ e, 0 ≤ p e)
    (hx0 : ∀ e, 0 ≤ x e)
    (hd : ∀ v, degree x v ≤ a)
    (ht : ∀ S : Finset Vertex, S.card = 3 → triangleMass x S ≤ a)
    (hf : ∀ v, omitFive x v ≤ 2 * a)
    (hp : ∀ M : Finset Edge, IsPerfectMatching M → (∑ e ∈ M, p e) ≤ 1) :
    (∑ e : Edge, p e * x e) ≤ a := by
  let z : Edge → ℝ := fun e => x e / a
  have hz0 : ∀ e, 0 ≤ z e := fun e => div_nonneg (hx0 e) ha.le
  have hzd : ∀ v, degree z v ≤ 1 := by
    intro v
    rw [degree_div]
    exact (div_le_one ha).mpr (hd v)
  have hzt : ∀ S : Finset Vertex, S.card = 3 → triangleMass z S ≤ 1 := by
    intro S hS
    rw [triangleMass_div]
    exact (div_le_one ha).mpr (ht S hS)
  have hzf : ∀ v, omitFive z v ≤ 2 := by
    intro v
    rw [omitFive_div]
    exact (div_le_iff₀ ha).mpr (by nlinarith [hf v])
  have hbound := weighted_sum_le_one_of_fractional_matching_perfect z p hp0 hz0 hzd hzt hzf hp
  have hsum : (∑ e : Edge, p e * z e) = (∑ e : Edge, p e * x e) / a := by
    calc
      (∑ e : Edge, p e * z e) = ∑ e : Edge, (p e * x e) / a := by
        apply Finset.sum_congr rfl
        intro e _
        simp [z]
        ring
      _ = (∑ e : Edge, p e * x e) / a := by rw [Finset.sum_div]
  rw [hsum] at hbound
  exact (div_le_one ha).mp hbound

end WeightedEdgeColoring.Subtwo.K6MatchingDeficits
