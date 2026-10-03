import WeightedEdgeColoring.SubtwoK6RegularMax

/-! A regular six-vertex fractional matching with a unit edge is a
mixture of the three perfect matchings of the remaining four vertices. -/

set_option maxHeartbeats 0

namespace WeightedEdgeColoring.Subtwo.K6MatchingDeficits

def unitCoefficientEdge : Edge → Fin 3 → Edge := ![![9, 10, 11], ![6, 7, 8], ![5, 7, 8], ![5, 6, 8], ![5, 6, 7], ![2, 3, 4], ![1, 3, 4], ![1, 2, 4], ![1, 2, 3], ![0, 3, 4], ![0, 2, 4], ![0, 2, 3], ![0, 1, 4], ![0, 1, 3], ![0, 1, 2]]
def unitMatching : Edge → Fin 3 → Finset Edge := ![![{0, 9, 14}, {0, 10, 13}, {0, 11, 12}], ![{1, 6, 14}, {1, 7, 13}, {1, 8, 12}], ![{2, 5, 14}, {2, 7, 11}, {2, 8, 10}], ![{3, 5, 13}, {3, 6, 11}, {3, 8, 9}], ![{4, 5, 12}, {4, 6, 10}, {4, 7, 9}], ![{5, 2, 14}, {5, 3, 13}, {5, 4, 12}], ![{6, 1, 14}, {6, 3, 11}, {6, 4, 10}], ![{7, 1, 13}, {7, 2, 11}, {7, 4, 9}], ![{8, 1, 12}, {8, 2, 10}, {8, 3, 9}], ![{9, 0, 14}, {9, 3, 8}, {9, 4, 7}], ![{10, 0, 13}, {10, 2, 8}, {10, 4, 6}], ![{11, 0, 12}, {11, 2, 7}, {11, 3, 6}], ![{12, 0, 11}, {12, 1, 8}, {12, 4, 5}], ![{13, 0, 10}, {13, 1, 7}, {13, 3, 5}], ![{14, 0, 9}, {14, 1, 6}, {14, 2, 5}]]

set_option maxRecDepth 10000 in
theorem unitMatching_isMatching : ∀ h i, IsMatching (unitMatching h i) := by
  unfold IsMatching
  decide

theorem unitCoefficientMass_eq_one (x : Edge → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hd : ∀ v : Vertex, degree x v = 1)
    (h : Edge) (he : x h = 1) :
    (∑ i : Fin 3, x (unitCoefficientEdge h i)) = 1 := by
  have hn0 := hx 0
  have hn1 := hx 1
  have hn2 := hx 2
  have hn3 := hx 3
  have hn4 := hx 4
  have hn5 := hx 5
  have hn6 := hx 6
  have hn7 := hx 7
  have hn8 := hx 8
  have hn9 := hx 9
  have hn10 := hx 10
  have hn11 := hx 11
  have hn12 := hx 12
  have hn13 := hx 13
  have hn14 := hx 14
  have hd0 := hd 0
  have hd1 := hd 1
  have hd2 := hd 2
  have hd3 := hd 3
  have hd4 := hd 4
  have hd5 := hd 5
  simp [degree] at hd0 hd1 hd2 hd3 hd4 hd5
  fin_cases h <;> simp [unitCoefficientEdge, Fin.sum_univ_succ] at he ⊢ <;> linarith

def unitMarginal (x : Edge → ℝ) (h e : Edge) : ℝ :=
  ∑ i : Fin 3, if e ∈ unitMatching h i then x (unitCoefficientEdge h i) else 0

theorem unitMarginal_eq (x : Edge → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hd : ∀ v : Vertex, degree x v = 1)
    (h : Edge) (he : x h = 1) : ∀ e : Edge, unitMarginal x h e = x e := by
  have hn0 := hx 0
  have hn1 := hx 1
  have hn2 := hx 2
  have hn3 := hx 3
  have hn4 := hx 4
  have hn5 := hx 5
  have hn6 := hx 6
  have hn7 := hx 7
  have hn8 := hx 8
  have hn9 := hx 9
  have hn10 := hx 10
  have hn11 := hx 11
  have hn12 := hx 12
  have hn13 := hx 13
  have hn14 := hx 14
  have hd0 := hd 0
  have hd1 := hd 1
  have hd2 := hd 2
  have hd3 := hd 3
  have hd4 := hd 4
  have hd5 := hd 5
  simp [degree] at hd0 hd1 hd2 hd3 hd4 hd5
  intro e
  fin_cases h <;> fin_cases e <;>
    simp [unitMarginal, unitMatching, unitCoefficientEdge, Fin.sum_univ_succ] at he ⊢ <;> linarith

theorem weighted_sum_eq_unitMatchings (x p : Edge → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hd : ∀ v : Vertex, degree x v = 1)
    (h : Edge) (he : x h = 1) :
    (∑ e : Edge, p e * x e) =
      ∑ i : Fin 3, x (unitCoefficientEdge h i) * (∑ e ∈ unitMatching h i, p e) := by
  calc
    (∑ e : Edge, p e * x e) =
        ∑ e : Edge, p e * unitMarginal x h e := by
      apply Finset.sum_congr rfl
      intro e _
      rw [unitMarginal_eq x hx hd h he e]
    _ = _ := by
      simp only [unitMarginal, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp [mul_ite, mul_comm]

theorem weighted_sum_le_one_of_unit_edge (x p : Edge → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hd : ∀ v : Vertex, degree x v = 1)
    (h : Edge) (he : x h = 1)
    (hp : ∀ M : Finset Edge, IsMatching M → (∑ e ∈ M, p e) ≤ 1) :
    (∑ e : Edge, p e * x e) ≤ 1 := by
  rw [weighted_sum_eq_unitMatchings x p hx hd h he]
  calc
    (∑ i : Fin 3, x (unitCoefficientEdge h i) * (∑ e ∈ unitMatching h i, p e)) ≤
        ∑ i : Fin 3, x (unitCoefficientEdge h i) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_of_le_one_right (hx _) (hp _ (unitMatching_isMatching h i))
    _ = 1 := unitCoefficientMass_eq_one x hx hd h he

end WeightedEdgeColoring.Subtwo.K6MatchingDeficits
