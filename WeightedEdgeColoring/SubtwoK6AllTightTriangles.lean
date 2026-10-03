import WeightedEdgeColoring.SubtwoK6RegularMax

set_option maxHeartbeats 0

/-! Explicit nine-matching decompositions for all twenty tight triangles. -/

namespace WeightedEdgeColoring.Subtwo.K6MatchingDeficits

def allTriangle : Fin 20 → Finset Vertex := ![{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 1, 5}, {0, 2, 3}, {0, 2, 4}, {0, 2, 5}, {0, 3, 4}, {0, 3, 5}, {0, 4, 5}, {1, 2, 3}, {1, 2, 4}, {1, 2, 5}, {1, 3, 4}, {1, 3, 5}, {1, 4, 5}, {2, 3, 4}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}]
def allCross : Fin 20 → Fin 3 → Fin 3 → Edge := ![![![2, 3, 4], ![6, 7, 8], ![9, 10, 11]], ![![1, 3, 4], ![5, 7, 8], ![9, 12, 13]], ![![1, 2, 4], ![5, 6, 8], ![10, 12, 14]], ![![1, 2, 3], ![5, 6, 7], ![11, 13, 14]], ![![0, 3, 4], ![5, 10, 11], ![6, 12, 13]], ![![0, 2, 4], ![5, 9, 11], ![7, 12, 14]], ![![0, 2, 3], ![5, 9, 10], ![8, 13, 14]], ![![0, 1, 4], ![6, 9, 13], ![7, 10, 14]], ![![0, 1, 3], ![6, 9, 12], ![8, 11, 14]], ![![0, 1, 2], ![7, 10, 12], ![8, 11, 13]], ![![0, 7, 8], ![1, 10, 11], ![2, 12, 13]], ![![0, 6, 8], ![1, 9, 11], ![3, 12, 14]], ![![0, 6, 7], ![1, 9, 10], ![4, 13, 14]], ![![0, 5, 8], ![2, 9, 13], ![3, 10, 14]], ![![0, 5, 7], ![2, 9, 12], ![4, 11, 14]], ![![0, 5, 6], ![3, 10, 12], ![4, 11, 13]], ![![1, 5, 11], ![2, 6, 13], ![3, 7, 14]], ![![1, 5, 10], ![2, 6, 12], ![4, 8, 14]], ![![1, 5, 9], ![3, 7, 12], ![4, 8, 13]], ![![2, 6, 9], ![3, 7, 10], ![4, 8, 11]]]
def allOppositeIn : Fin 20 → Fin 3 → Edge := ![![5, 1, 0], ![6, 2, 0], ![7, 3, 0], ![8, 4, 0], ![9, 2, 1], ![10, 3, 1], ![11, 4, 1], ![12, 3, 2], ![13, 4, 2], ![14, 4, 3], ![9, 6, 5], ![10, 7, 5], ![11, 8, 5], ![12, 7, 6], ![13, 8, 6], ![14, 8, 7], ![12, 10, 9], ![13, 11, 9], ![14, 11, 10], ![14, 13, 12]]
def allOppositeOut : Fin 20 → Fin 3 → Edge := ![![14, 13, 12], ![14, 11, 10], ![13, 11, 9], ![12, 10, 9], ![14, 8, 7], ![13, 8, 6], ![12, 7, 6], ![11, 8, 5], ![10, 7, 5], ![9, 6, 5], ![14, 4, 3], ![13, 4, 2], ![12, 3, 2], ![11, 4, 1], ![10, 3, 1], ![9, 2, 1], ![8, 4, 0], ![7, 3, 0], ![6, 2, 0], ![5, 1, 0]]

theorem allTriangle_card : ∀ i : Fin 20, (allTriangle i).card = 3 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem exists_allTriangle : ∀ S : Finset Vertex, S.card = 3 →
    ∃ i : Fin 20, allTriangle i = S := by decide

def allTriangleMatching (h : Fin 20) (i j : Fin 3) : Finset Edge :=
  {allCross h i j, allOppositeIn h i, allOppositeOut h j}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem allTriangleMatching_isMatching : ∀ h i j,
    IsMatching (allTriangleMatching h i j) := by
  unfold IsMatching
  decide

theorem allTriangle_mass (x : Edge → ℝ) (h : Fin 20) :
    triangleMass x (allTriangle h) = ∑ i : Fin 3, x (allOppositeIn h i) := by
  fin_cases h <;>
    simp [triangleMass, Finset.sum_filter, allTriangle, allOppositeIn,
      ends, Finset.subset_iff, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 0 in
theorem allTriangleCross_mass (x : Edge → ℝ) (h : Fin 20)
    (hd : ∀ v : Vertex, degree x v = 1)
    (ht : triangleMass x (allTriangle h) = 1) :
    (∑ i : Fin 3, ∑ j : Fin 3, x (allCross h i j)) = 1 := by
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have h3 := hd 3
  have h4 := hd 4
  have h5 := hd 5
  simp [degree] at h0 h1 h2 h3 h4 h5
  rw [allTriangle_mass] at ht
  fin_cases h <;>
    simp [allCross, allOppositeIn, Fin.sum_univ_succ] at ht ⊢ <;> linarith

def allTriangleMarginal (x : Edge → ℝ) (h : Fin 20) (e : Edge) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    if e ∈ allTriangleMatching h i j then x (allCross h i j) else 0

set_option maxHeartbeats 0 in
theorem allTriangleMarginal_eq (x : Edge → ℝ) (h : Fin 20)
    (hd : ∀ v : Vertex, degree x v = 1)
    (ht : triangleMass x (allTriangle h) = 1) :
    ∀ e : Edge, allTriangleMarginal x h e = x e := by
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have h3 := hd 3
  have h4 := hd 4
  have h5 := hd 5
  simp [degree] at h0 h1 h2 h3 h4 h5
  rw [allTriangle_mass] at ht
  intro e
  fin_cases h <;> fin_cases e <;>
    simp [allTriangleMarginal, allTriangleMatching, allCross,
      allOppositeIn, allOppositeOut, Fin.sum_univ_succ] at ht ⊢ <;> linarith

theorem weighted_sum_eq_allTrianglePairs (x p : Edge → ℝ) (h : Fin 20)
    (hd : ∀ v : Vertex, degree x v = 1)
    (ht : triangleMass x (allTriangle h) = 1) :
    (∑ e : Edge, p e * x e) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        x (allCross h i j) * (∑ e ∈ allTriangleMatching h i j, p e) := by
  calc
    (∑ e : Edge, p e * x e) =
        ∑ e : Edge, p e * allTriangleMarginal x h e := by
      apply Finset.sum_congr rfl
      intro e _
      rw [allTriangleMarginal_eq x h hd ht e]
    _ = _ := by
      simp only [allTriangleMarginal, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp [mul_ite, Finset.mul_sum, mul_comm]

theorem weighted_sum_le_one_of_any_tight_triangle (x p : Edge → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hd : ∀ v : Vertex, degree x v = 1)
    (S : Finset Vertex) (hS : S.card = 3) (ht : triangleMass x S = 1)
    (hp : ∀ M : Finset Edge, IsMatching M → (∑ e ∈ M, p e) ≤ 1) :
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
      exact mul_le_of_le_one_right (hx _) (hp _ (allTriangleMatching_isMatching h i j))
    _ = 1 := allTriangleCross_mass x h hd ht

end WeightedEdgeColoring.Subtwo.K6MatchingDeficits
