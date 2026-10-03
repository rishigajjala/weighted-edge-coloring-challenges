import WeightedEdgeColoring.WeightedMomentPairingContraction

/-!
# Orthogonal splitting of symmetric two-color arrays

The pair-moment contraction has two nonconstant invariant subspaces.  This
file constructs their decomposition for a symmetric off-diagonal array by
finite sums.  It removes the scalar splitting hypotheses from
`WeightedMomentPairingContraction.pairEnergy_le_half`.
-/

namespace WeightedEdgeColoring.WeightedMomentPairArray

open scoped BigOperators
open WeightedEdgeColoring.WeightedMomentPairingContraction

noncomputable section

variable {Color : Type*} [Fintype Color] [DecidableEq Color]

/-- Sum over all indices except one distinguished index. -/
theorem sum_ne_eq_sum_sub (f : Color → ℝ) (i : Color) :
    (∑ j : Color, if i = j then 0 else f j) = (∑ j, f j) - f i := by
  calc
    (∑ j : Color, if i = j then 0 else f j) =
        ∑ j : Color, (f j - if i = j then f j else 0) := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hij : i = j <;> simp [hij]
    _ = (∑ j : Color, f j) - ∑ j : Color, (if i = j then f j else 0) :=
      by
        simpa only using
          (Finset.sum_sub_distrib (s := (Finset.univ : Finset Color))
            f (fun j : Color ↦ if i = j then f j else 0))
    _ = (∑ j : Color, f j) - f i := by simp

/-- Off-diagonal row sum.  Diagonal values are ignored throughout. -/
def rowSum (h : Color → Color → ℝ) (i : Color) : ℝ :=
  ∑ j : Color, if i = j then 0 else h i j

/-- Total of an off-diagonal array, with both orientations counted. -/
def total (h : Color → Color → ℝ) : ℝ := ∑ i : Color, rowSum h i

/-- Squared norm of an off-diagonal array, with both orientations counted. -/
def energy (h : Color → Color → ℝ) : ℝ :=
  ∑ i : Color, ∑ j : Color, if i = j then 0 else (h i j) ^ 2

theorem energy_nonneg (h : Color → Color → ℝ) : 0 ≤ energy h := by
  unfold energy
  positivity

/-- The vertex coefficient obtained by dividing the row sum by `K-2`. -/
def vertexCoefficient (h : Color → Color → ℝ) (i : Color) : ℝ :=
  rowSum h i / ((Fintype.card Color : ℝ) - 2)

/-- The `b_i+b_j` component, with zero diagonal. -/
def vertexPart (h : Color → Color → ℝ) (i j : Color) : ℝ :=
  if i = j then 0 else vertexCoefficient h i + vertexCoefficient h j

/-- The residual after subtracting the vertex component. -/
def rowZeroPart (h : Color → Color → ℝ) (i j : Color) : ℝ :=
  h i j - vertexPart h i j

theorem sum_vertexCoefficient_eq_zero
    (h : Color → Color → ℝ) (htotal : total h = 0)
    (hcard : 3 ≤ Fintype.card Color) :
    ∑ i : Color, vertexCoefficient h i = 0 := by
  have hcardReal : (3 : ℝ) ≤ (Fintype.card Color : ℝ) := by
    exact_mod_cast hcard
  have hden : ((Fintype.card Color : ℝ) - 2) ≠ 0 := by
    linarith
  unfold vertexCoefficient
  rw [← Finset.sum_div, show (∑ i : Color, rowSum h i) = total h by rfl,
    htotal, zero_div]

theorem rowSum_vertexPart
    (h : Color → Color → ℝ) (i : Color)
    (hsum : ∑ j : Color, vertexCoefficient h j = 0) :
    rowSum (vertexPart h) i =
      ((Fintype.card Color : ℝ) - 2) * vertexCoefficient h i := by
  unfold rowSum
  have hcollapse :
      (∑ j : Color, if i = j then 0 else vertexPart h i j) =
        ∑ j : Color, if i = j then 0 else
          (vertexCoefficient h i + vertexCoefficient h j) := by
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hij : i = j <;> simp [vertexPart, hij]
  rw [hcollapse, sum_ne_eq_sum_sub
    (fun j : Color ↦ vertexCoefficient h i + vertexCoefficient h j) i]
  simp_rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hsum]
  ring

theorem rowSum_rowZeroPart_eq_zero
    (h : Color → Color → ℝ) (htotal : total h = 0)
    (hcard : 3 ≤ Fintype.card Color) (i : Color) :
    rowSum (rowZeroPart h) i = 0 := by
  have hsum := sum_vertexCoefficient_eq_zero h htotal hcard
  have hv := rowSum_vertexPart h i hsum
  have hcardReal : (3 : ℝ) ≤ (Fintype.card Color : ℝ) := by
    exact_mod_cast hcard
  have hden : ((Fintype.card Color : ℝ) - 2) ≠ 0 := by
    linarith
  change (∑ j : Color, if i = j then 0 else
    (h i j - vertexPart h i j)) = 0
  calc
    (∑ j : Color, if i = j then 0 else
      (h i j - vertexPart h i j)) =
        ∑ j : Color, (
          (if i = j then 0 else h i j) -
            (if i = j then 0 else vertexPart h i j)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hij : i = j <;> simp [hij]
    _ = (∑ j : Color, if i = j then 0 else h i j) -
          ∑ j : Color, if i = j then 0 else vertexPart h i j := by
      simpa only using
        (Finset.sum_sub_distrib (s := (Finset.univ : Finset Color))
          (fun j : Color ↦ if i = j then 0 else h i j)
          (fun j : Color ↦ if i = j then 0 else vertexPart h i j))
    _ = 0 := by
      change rowSum h i - rowSum (vertexPart h) i = 0
      rw [hv]
      unfold vertexCoefficient
      field_simp
      ring

theorem vertexPart_symmetric (h : Color → Color → ℝ) :
    ∀ i j, vertexPart h i j = vertexPart h j i := by
  intro i j
  unfold vertexPart
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := by
      intro hji
      exact hij hji.symm
    simp [hij, hji, add_comm]

theorem rowZeroPart_symmetric (h : Color → Color → ℝ)
    (hsym : ∀ i j, h i j = h j i) :
    ∀ i j, rowZeroPart h i j = rowZeroPart h j i := by
  intro i j
  unfold rowZeroPart
  rw [hsym, vertexPart_symmetric h]

/-- A symmetric array with zero row sums is orthogonal to every vertex
array `b_i+b_j`. -/
theorem rowZero_orthogonal_vertexPart
    (h : Color → Color → ℝ) (htotal : total h = 0)
    (hcard : 3 ≤ Fintype.card Color)
    (hsym : ∀ i j, h i j = h j i) :
    (∑ i : Color, ∑ j : Color,
      if i = j then 0 else
        rowZeroPart h i j * vertexPart h i j) = 0 := by
  let g := rowZeroPart h
  let b := vertexCoefficient h
  have hgrow : ∀ i, rowSum g i = 0 :=
    rowSum_rowZeroPart_eq_zero h htotal hcard
  have hgsym : ∀ i j, g i j = g j i :=
    rowZeroPart_symmetric h hsym
  have hfirst :
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else g i j * b i) = 0 := by
    calc
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else g i j * b i) =
          ∑ i : Color, rowSum g i * b i := by
        apply Finset.sum_congr rfl
        intro i _hi
        unfold rowSum
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hij : i = j <;> simp [hij]
      _ = 0 := by simp [hgrow]
  have hsecond :
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else g i j * b j) = 0 := by
    calc
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else g i j * b j) =
          ∑ j : Color, ∑ i : Color,
            if j = i then 0 else g j i * b j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _hj
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases hij : i = j
        · subst j
          simp
        · have hji : j ≠ i := by
            intro hji
            exact hij hji.symm
          simp [hij, hji, hgsym]
      _ = 0 := hfirst
  calc
    (∑ i : Color, ∑ j : Color,
      if i = j then 0 else
        rowZeroPart h i j * vertexPart h i j) =
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else g i j * b i) +
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else g i j * b j) := by
      simp only [g, b, vertexPart]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hij : i = j <;> simp [hij]
      ring
    _ = 0 := by rw [hfirst, hsecond, zero_add]

/-- Exact Pythagorean identity for the vertex and row-zero components. -/
theorem energy_eq_vertex_add_rowZero
    (h : Color → Color → ℝ) (htotal : total h = 0)
    (hcard : 3 ≤ Fintype.card Color)
    (hsym : ∀ i j, h i j = h j i) :
    energy h = energy (vertexPart h) + energy (rowZeroPart h) := by
  have horth := rowZero_orthogonal_vertexPart h htotal hcard hsym
  unfold energy
  calc
    (∑ i : Color, ∑ j : Color, if i = j then 0 else h i j ^ 2) =
        ∑ i : Color, ∑ j : Color,
          if i = j then 0 else
            (vertexPart h i j + rowZeroPart h i j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hij : i = j
      · simp [hij]
      · congr 2
        unfold rowZeroPart
        ring
    _ = ∑ i : Color, ∑ j : Color, (
        (if i = j then 0 else (vertexPart h i j) ^ 2) +
        (if i = j then 0 else (rowZeroPart h i j) ^ 2) +
        (if i = j then 0 else
          rowZeroPart h i j * vertexPart h i j) +
        (if i = j then 0 else
          rowZeroPart h i j * vertexPart h i j)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hij : i = j
      · simp [hij]
      · simp [hij]
        ring
    _ =
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else (vertexPart h i j) ^ 2) +
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else (rowZeroPart h i j) ^ 2) +
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else
            rowZeroPart h i j * vertexPart h i j) +
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else
            rowZeroPart h i j * vertexPart h i j) := by
      simp only [Finset.sum_add_distrib]
    _ =
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else (vertexPart h i j) ^ 2) +
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else (rowZeroPart h i j) ^ 2) := by
      simp only [horth]
      ring

/-- Fully array-level contraction: once an averaged pairing operator acts by
the two manuscript eigenvalues on the two explicit components, its energy is
at most half the original energy.  Nonnegativity and the orthogonal split are
now conclusions rather than hypotheses. -/
theorem averagedEnergy_le_half
    (h : Color → Color → ℝ) (htotal : total h = 0)
    (hcard : 4 ≤ Fintype.card Color)
    (hsym : ∀ i j, h i j = h j i)
    (averagedEnergy : ℝ)
    (haverage : averagedEnergy =
      pairVertexEigenvalue (Fintype.card Color) * energy (vertexPart h) +
        pairRowZeroEigenvalue (Fintype.card Color) * energy (rowZeroPart h)) :
    averagedEnergy ≤ energy h / 2 := by
  apply pairEnergy_le_half (K := Fintype.card Color) hcard
    (energy_nonneg (vertexPart h)) (energy_nonneg (rowZeroPart h))
  · exact energy_eq_vertex_add_rowZero h htotal (by omega) hsym
  · exact haverage

end

end WeightedEdgeColoring.WeightedMomentPairArray
