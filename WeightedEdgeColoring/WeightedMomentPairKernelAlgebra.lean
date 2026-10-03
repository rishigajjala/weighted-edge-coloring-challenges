import WeightedEdgeColoring.FiniteColorPairingOperators

/-!
# Quadratic algebra for the averaged two-color pairing kernel

This file evaluates the two combinatorial sums in
`FiniteColorPairingOperators.average_pairAverage`.  The calculation is over
ordered off-diagonal pairs.  It identifies the resulting quadratic form with
the two eigenspaces constructed in `WeightedMomentPairArray`, and therefore
closes the pair-energy contraction without any spectral hypothesis.
-/

namespace WeightedEdgeColoring.WeightedMomentPairKernelAlgebra

open scoped BigOperators
open WeightedEdgeColoring.FiniteColorPairing
open WeightedEdgeColoring.FiniteColorPairingOperators
open WeightedEdgeColoring.WeightedMomentPairingContraction
open WeightedEdgeColoring.WeightedMomentPairArray

noncomputable section

variable {Color : Type*} [Fintype Color] [DecidableEq Color]

/-- Delete two distinct terms from a finite sum. -/
theorem sum_ite_away_two (f : Color → ℝ) {i j : Color} (hij : i ≠ j) :
    (∑ k : Color, if k = i ∨ k = j then 0 else f k) =
      (∑ k : Color, f k) - f i - f j := by
  calc
    (∑ k : Color, if k = i ∨ k = j then 0 else f k) =
        ∑ k : Color,
          (f k - (if k = i then f k else 0) -
            (if k = j then f k else 0)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      by_cases hki : k = i
      · subst k
        simp [hij]
      · by_cases hkj : k = j
        · subst k
          simp [hki]
        · simp [hki, hkj]
    _ = (∑ k : Color, f k) -
          (∑ k : Color, if k = i then f k else 0) -
          (∑ k : Color, if k = j then f k else 0) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = (∑ k : Color, f k) - f i - f j := by simp

/-- Delete three pairwise distinct terms from a finite sum. -/
theorem sum_ite_away_three (f : Color → ℝ) {i j k : Color}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∑ l : Color, if l = i ∨ l = j ∨ l = k then 0 else f l) =
      (∑ l : Color, f l) - f i - f j - f k := by
  calc
    (∑ l : Color, if l = i ∨ l = j ∨ l = k then 0 else f l) =
        ∑ l : Color,
          (f l - (if l = i then f l else 0) -
            (if l = j then f l else 0) -
            (if l = k then f l else 0)) := by
      apply Finset.sum_congr rfl
      intro l _hl
      have hji : j ≠ i := by
        intro hji
        exact hij hji.symm
      have hki : k ≠ i := by
        intro hki
        exact hik hki.symm
      have hkj : k ≠ j := by
        intro hkj
        exact hjk hkj.symm
      by_cases hli : l = i <;> by_cases hlj : l = j <;>
        by_cases hlk : l = k <;>
          simp [hli, hlj, hlk, hij, hji, hik, hki, hjk, hkj]
    _ = (∑ l : Color, f l) -
          (∑ l : Color, if l = i then f l else 0) -
          (∑ l : Color, if l = j then f l else 0) -
          (∑ l : Color, if l = k then f l else 0) := by
      simp only [Finset.sum_sub_distrib]
    _ = (∑ l : Color, f l) - f i - f j - f k := by simp

theorem sum_row_eq_rowSum (h : Color → Color → ℝ)
    (hdiag : ∀ i, h i i = 0) (i : Color) :
    (∑ j : Color, h i j) = rowSum h i := by
  unfold rowSum
  rw [sum_ne_eq_sum_sub]
  simp [hdiag]

theorem sum_column_eq_rowSum (h : Color → Color → ℝ)
    (hsym : ∀ i j, h i j = h j i) (hdiag : ∀ i, h i i = 0)
    (j : Color) :
    (∑ i : Color, h i j) = rowSum h j := by
  calc
    (∑ i : Color, h i j) = ∑ i : Color, h j i := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hsym i j
    _ = rowSum h j := sum_row_eq_rowSum h hdiag j

/-- The ordered sum over pairs meeting `{i,j}` in one color is the sum of
the two row sums, with the tracked entry removed twice. -/
theorem meetingPairSum_eq_rows (h : Color → Color → ℝ)
    (hsym : ∀ i j, h i j = h j i) (hdiag : ∀ i, h i i = 0)
    {i j : Color} (hij : i ≠ j) :
    meetingPairSum i j h = rowSum h i + rowSum h j - 2 * h i j := by
  unfold meetingPairSum
  rw [show
      (∑ k : Color,
        if k = i ∨ k = j then 0 else h k j + h i k) =
        (∑ k : Color, if k = i ∨ k = j then 0 else h k j) +
          (∑ k : Color, if k = i ∨ k = j then 0 else h i k) by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _hk
      by_cases hk : k = i ∨ k = j <;> simp [hk]]
  rw [sum_ite_away_two (fun k ↦ h k j) hij,
    sum_ite_away_two (fun k ↦ h i k) hij,
    sum_column_eq_rowSum h hsym hdiag,
    sum_row_eq_rowSum h hdiag, hdiag, hdiag]
  ring

/-- The ordered sum over pairs disjoint from `{i,j}`. -/
theorem disjointPartnerSum_eq_rows (h : Color → Color → ℝ)
    (hsym : ∀ i j, h i j = h j i) (hdiag : ∀ i, h i i = 0)
    {i j : Color} (hij : i ≠ j) :
    disjointPartnerSum Color i j h =
      total h - 2 * rowSum h i - 2 * rowSum h j + 2 * h i j := by
  have hinner : ∀ k : Color, k ≠ i → k ≠ j →
      (∑ l : Color,
        if l = i ∨ l = j ∨ k = l then 0 else h k l) =
      rowSum h k - h k i - h k j := by
    intro k hki hkj
    rw [show
        (∑ l : Color, if l = i ∨ l = j ∨ k = l then 0 else h k l) =
          (∑ l : Color, if l = i ∨ l = j ∨ l = k then 0 else h k l) by
      apply Finset.sum_congr rfl
      intro l _hl
      by_cases hli : l = i
      · simp [hli]
      by_cases hlj : l = j
      · simp [hlj]
      by_cases hkl : k = l
      · have hleft : l = i ∨ l = j ∨ k = l :=
          Or.inr (Or.inr hkl)
        have hright : l = i ∨ l = j ∨ l = k :=
          Or.inr (Or.inr hkl.symm)
        rw [if_pos hleft, if_pos hright]
      · have hlk : l ≠ k := by
          intro hlk
          exact hkl hlk.symm
        have hleft : ¬ (l = i ∨ l = j ∨ k = l) := by
          intro hleft
          rcases hleft with hli' | hlj' | hkl'
          · exact hli hli'
          · exact hlj hlj'
          · exact hkl hkl'
        have hright : ¬ (l = i ∨ l = j ∨ l = k) := by
          intro hright
          rcases hright with hli' | hlj' | hlk'
          · exact hli hli'
          · exact hlj hlj'
          · exact hlk hlk'
        rw [if_neg hleft, if_neg hright]]
    have hik : i ≠ k := by
      intro hik
      exact hki hik.symm
    have hjk : j ≠ k := by
      intro hjk
      exact hkj hjk.symm
    rw [sum_ite_away_three (fun l ↦ h k l) hij hik hjk,
      sum_row_eq_rowSum h hdiag, hdiag]
    ring
  unfold disjointPartnerSum
  rw [show
      (∑ k : Color, ∑ l : Color,
        if k = i ∨ k = j ∨ l = i ∨ l = j ∨ k = l then 0 else h k l) =
      ∑ k : Color, if k = i ∨ k = j then 0 else
        ∑ l : Color, if l = i ∨ l = j ∨ k = l then 0 else h k l by
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hki : k = i <;> by_cases hkj : k = j
    · simp [hki]
    · simp [hki]
    · simp [hkj]
    · simp [hki, hkj]]
  rw [show
      (∑ k : Color, if k = i ∨ k = j then 0 else
        ∑ l : Color, if l = i ∨ l = j ∨ k = l then 0 else h k l) =
      ∑ k : Color, if k = i ∨ k = j then 0 else
        (rowSum h k - h k i - h k j) by
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hk : k = i ∨ k = j
    · simp [hk]
    · rw [if_neg hk, if_neg hk, hinner k (fun h ↦ hk (Or.inl h))
        (fun h ↦ hk (Or.inr h))]]
  rw [sum_ite_away_two
    (fun k ↦ rowSum h k - h k i - h k j) hij]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    show (∑ k : Color, rowSum h k) = total h by rfl,
    sum_column_eq_rowSum h hsym hdiag,
    sum_column_eq_rowSum h hsym hdiag,
    hdiag, hdiag, hsym j i]
  ring

/-- Squared norm of the vector of off-diagonal row sums. -/
def rowEnergy (h : Color → Color → ℝ) : ℝ :=
  ∑ i : Color, (rowSum h i) ^ 2

theorem meeting_quadratic (h : Color → Color → ℝ)
    (hsym : ∀ i j, h i j = h j i) (hdiag : ∀ i, h i i = 0) :
    (∑ i : Color, ∑ j : Color,
      if i = j then 0 else h i j * meetingPairSum i j h) =
      2 * rowEnergy h - 2 * energy h := by
  simp_rw [show ∀ i j : Color,
      (if i = j then 0 else h i j * meetingPairSum i j h) =
      if i = j then 0 else
        h i j * (rowSum h i + rowSum h j - 2 * h i j) by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · rw [if_neg hij, if_neg hij, meetingPairSum_eq_rows h hsym hdiag hij]]
  unfold rowEnergy energy
  rw [show
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else
          h i j * (rowSum h i + rowSum h j - 2 * h i j)) =
      (∑ i : Color, rowSum h i * rowSum h i) +
        (∑ j : Color, rowSum h j * rowSum h j) -
        2 * (∑ i : Color, ∑ j : Color,
          if i = j then 0 else (h i j) ^ 2) by
    have hfirst :
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else h i j * rowSum h i) =
        ∑ i : Color, rowSum h i * rowSum h i := by
      apply Finset.sum_congr rfl
      intro i _hi
      calc
        (∑ j : Color, if i = j then 0 else h i j * rowSum h i) =
            (∑ j : Color, if i = j then 0 else h i j) * rowSum h i := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _hj
          by_cases hij : i = j <;> simp [hij]
        _ = rowSum h i * rowSum h i := by rfl
    have hsecond :
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else h i j * rowSum h j) =
        ∑ j : Color, rowSum h j * rowSum h j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      calc
        (∑ i : Color, if i = j then 0 else h i j * rowSum h j) =
            (∑ i : Color, if j = i then 0 else h j i) * rowSum h j := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          by_cases hij : i = j
          · subst j
            simp
          · have hji : j ≠ i := by
              intro hji
              exact hij hji.symm
            simp [hij, hji, hsym]
        _ = rowSum h j * rowSum h j := by rfl
    calc
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else
          h i j * (rowSum h i + rowSum h j - 2 * h i j)) =
          (∑ i : Color, ∑ j : Color,
            if i = j then 0 else h i j * rowSum h i) +
          (∑ i : Color, ∑ j : Color,
            if i = j then 0 else h i j * rowSum h j) -
          2 * (∑ i : Color, ∑ j : Color,
            if i = j then 0 else (h i j) ^ 2) := by
        calc
          (∑ i : Color, ∑ j : Color,
            if i = j then 0 else
              h i j * (rowSum h i + rowSum h j - 2 * h i j)) =
              ∑ i : Color, ∑ j : Color,
                ((if i = j then 0 else h i j * rowSum h i) +
                (if i = j then 0 else h i j * rowSum h j) -
                2 * (if i = j then 0 else (h i j) ^ 2)) := by
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
                if i = j then 0 else h i j * rowSum h i) +
              (∑ i : Color, ∑ j : Color,
                if i = j then 0 else h i j * rowSum h j) -
              2 * (∑ i : Color, ∑ j : Color,
                if i = j then 0 else (h i j) ^ 2) := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum]
      _ =
          (∑ i : Color, rowSum h i * rowSum h i) +
          (∑ j : Color, rowSum h j * rowSum h j) -
          2 * (∑ i : Color, ∑ j : Color,
            if i = j then 0 else (h i j) ^ 2) := by
        rw [hfirst, hsecond]]
  simp only [sq]
  ring

theorem disjoint_quadratic (h : Color → Color → ℝ)
    (hsym : ∀ i j, h i j = h j i) (hdiag : ∀ i, h i i = 0) :
    (∑ i : Color, ∑ j : Color,
      if i = j then 0 else h i j * disjointPartnerSum Color i j h) =
      (total h) ^ 2 - 4 * rowEnergy h + 2 * energy h := by
  simp_rw [show ∀ i j : Color,
      (if i = j then 0 else h i j * disjointPartnerSum Color i j h) =
      if i = j then 0 else h i j *
        (total h - 2 * rowSum h i - 2 * rowSum h j + 2 * h i j) by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · rw [if_neg hij, if_neg hij,
        disjointPartnerSum_eq_rows h hsym hdiag hij]]
  have htotal :
      (∑ i : Color, ∑ j : Color, if i = j then 0 else h i j) = total h := rfl
  have hfirst :
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j * rowSum h i) = rowEnergy h := by
    unfold rowEnergy
    apply Finset.sum_congr rfl
    intro i _hi
    calc
      (∑ j : Color, if i = j then 0 else h i j * rowSum h i) =
          (∑ j : Color, if i = j then 0 else h i j) * rowSum h i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hij : i = j <;> simp [hij]
      _ = (rowSum h i) ^ 2 := by
        change rowSum h i * rowSum h i = (rowSum h i) ^ 2
        ring
  have hsecond :
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j * rowSum h j) = rowEnergy h := by
    rw [Finset.sum_comm]
    unfold rowEnergy
    apply Finset.sum_congr rfl
    intro j _hj
    calc
      (∑ i : Color, if i = j then 0 else h i j * rowSum h j) =
          (∑ i : Color, if j = i then 0 else h j i) * rowSum h j := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases hij : i = j
        · subst j
          simp
        · have hji : j ≠ i := by
            intro hji
            exact hij hji.symm
          simp [hij, hji, hsym]
      _ = (rowSum h j) ^ 2 := by
        change rowSum h j * rowSum h j = (rowSum h j) ^ 2
        ring
  have htotalQuadratic :
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j * total h) = (total h) ^ 2 := by
    calc
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j * total h) =
          ∑ i : Color,
            (∑ j : Color, if i = j then 0 else h i j) * total h := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hij : i = j <;> simp [hij]
      _ = (∑ i : Color, ∑ j : Color,
          if i = j then 0 else h i j) * total h := by
        rw [Finset.sum_mul]
      _ = (total h) ^ 2 := by rw [htotal]; ring
  unfold energy
  calc
    (∑ i : Color, ∑ j : Color,
      if i = j then 0 else h i j *
        (total h - 2 * rowSum h i - 2 * rowSum h j + 2 * h i j)) =
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else h i j * total h) -
        2 * (∑ i : Color, ∑ j : Color,
          if i = j then 0 else h i j * rowSum h i) -
        2 * (∑ i : Color, ∑ j : Color,
          if i = j then 0 else h i j * rowSum h j) +
        2 * (∑ i : Color, ∑ j : Color,
          if i = j then 0 else (h i j) ^ 2) := by
      calc
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else h i j *
            (total h - 2 * rowSum h i - 2 * rowSum h j + 2 * h i j)) =
            ∑ i : Color, ∑ j : Color,
              ((if i = j then 0 else h i j * total h) -
              2 * (if i = j then 0 else h i j * rowSum h i) -
              2 * (if i = j then 0 else h i j * rowSum h j) +
              2 * (if i = j then 0 else (h i j) ^ 2)) := by
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
              if i = j then 0 else h i j * total h) -
            2 * (∑ i : Color, ∑ j : Color,
              if i = j then 0 else h i j * rowSum h i) -
            2 * (∑ i : Color, ∑ j : Color,
              if i = j then 0 else h i j * rowSum h j) +
            2 * (∑ i : Color, ∑ j : Color,
              if i = j then 0 else (h i j) ^ 2) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum]
    _ = (total h) ^ 2 - 4 * rowEnergy h +
        2 * (∑ i : Color, ∑ j : Color,
          if i = j then 0 else (h i j) ^ 2) := by
      rw [htotalQuadratic, hfirst, hsecond]
      ring

/-- The vertex projection converts row energy into vertex-part energy. -/
theorem rowEnergy_eq_vertexPart_energy (h : Color → Color → ℝ)
    (htotal : total h = 0) (hcard : 3 ≤ Fintype.card Color)
    (hsym : ∀ i j, h i j = h j i) :
    2 * rowEnergy h =
      ((Fintype.card Color : ℝ) - 2) * energy (vertexPart h) := by
  have hcardReal : (3 : ℝ) ≤ (Fintype.card Color : ℝ) := by
    exact_mod_cast hcard
  have hden : ((Fintype.card Color : ℝ) - 2) ≠ 0 := by
    nlinarith
  have hinner :
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j * vertexPart h i j) =
      2 * ∑ i : Color, rowSum h i * vertexCoefficient h i := by
    rw [show
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else h i j * vertexPart h i j) =
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else h i j * vertexCoefficient h i) +
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else h i j * vertexCoefficient h j) by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, vertexPart]
        ring]
    have hfirst :
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else h i j * vertexCoefficient h i) =
        ∑ i : Color, rowSum h i * vertexCoefficient h i := by
      apply Finset.sum_congr rfl
      intro i _hi
      calc
        (∑ j : Color,
          if i = j then 0 else h i j * vertexCoefficient h i) =
            (∑ j : Color, if i = j then 0 else h i j) *
              vertexCoefficient h i := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _hj
          by_cases hij : i = j <;> simp [hij]
        _ = rowSum h i * vertexCoefficient h i := by rfl
    have hsecond :
        (∑ i : Color, ∑ j : Color,
          if i = j then 0 else h i j * vertexCoefficient h j) =
        ∑ i : Color, rowSum h i * vertexCoefficient h i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      calc
        (∑ i : Color,
          if i = j then 0 else h i j * vertexCoefficient h j) =
            (∑ i : Color, if j = i then 0 else h j i) *
              vertexCoefficient h j := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          by_cases hij : i = j
          · subst j
            simp
          · have hji : j ≠ i := by
              intro hji
              exact hij hji.symm
            simp [hij, hji, hsym]
        _ = rowSum h j * vertexCoefficient h j := by rfl
    rw [hfirst, hsecond]
    ring
  have hprojection :
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j * vertexPart h i j) =
      energy (vertexPart h) := by
    have horth := rowZero_orthogonal_vertexPart h htotal hcard hsym
    unfold rowZeroPart at horth
    calc
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j * vertexPart h i j) =
          (∑ i : Color, ∑ j : Color,
            if i = j then 0 else
              (h i j - vertexPart h i j) * vertexPart h i j) +
            energy (vertexPart h) := by
        unfold energy
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hij : i = j
        · simp [hij]
        · simp [hij]
          ring
      _ = energy (vertexPart h) := by rw [horth, zero_add]
  have hcoeff :
      (∑ i : Color, rowSum h i * vertexCoefficient h i) =
        rowEnergy h / ((Fintype.card Color : ℝ) - 2) := by
    unfold vertexCoefficient rowEnergy
    calc
      (∑ i : Color, rowSum h i *
        (rowSum h i / ((Fintype.card Color : ℝ) - 2))) =
          ∑ i : Color,
            (rowSum h i) ^ 2 / ((Fintype.card Color : ℝ) - 2) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (∑ i : Color, (rowSum h i) ^ 2) /
          ((Fintype.card Color : ℝ) - 2) := by
        rw [← Finset.sum_div]
  rw [hprojection, hcoeff] at hinner
  rw [hinner]
  field_simp [hden]

/-- Exact quadratic form of the averaged two-color operator. -/
theorem averagedPairKernel_quadratic (h : Color → Color → ℝ)
    (htotal : total h = 0) (hcard : 4 ≤ Fintype.card Color)
    (hsym : ∀ i j, h i j = h j i) (hdiag : ∀ i, h i i = 0) :
    (∑ i : Color, ∑ j : Color, if i = j then 0 else h i j *
      (pairP (Fintype.card Color) * h i j +
        pairQ (Fintype.card Color) * meetingPairSum i j h +
        (pairR (Fintype.card Color) / 2) *
          disjointPartnerSum Color i j h)) =
      pairVertexEigenvalue (Fintype.card Color) * energy (vertexPart h) +
        pairRowZeroEigenvalue (Fintype.card Color) * energy (rowZeroPart h) := by
  have hmeet := meeting_quadratic h hsym hdiag
  have hdisjoint := disjoint_quadratic h hsym hdiag
  have hrow := rowEnergy_eq_vertexPart_energy h htotal (by omega) hsym
  have hsplit := energy_eq_vertex_add_rowZero h htotal (by omega) hsym
  have hfactor (c : ℝ) (f : Color → Color → ℝ) :
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j * (c * f i j)) =
      c * (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j * f i j) := by
    calc
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j * (c * f i j)) =
          ∑ i : Color, ∑ j : Color,
            c * (if i = j then 0 else h i j * f i j) := by
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hij : i = j
        · simp [hij]
        · simp [hij]
          ring
      _ = c * (∑ i : Color, ∑ j : Color,
          if i = j then 0 else h i j * f i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
  have hself :
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j * h i j) = energy h := by
    unfold energy
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hij : i = j <;> simp [hij, pow_two]
  have hkernel :
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j *
          (pairP (Fintype.card Color) * h i j +
            pairQ (Fintype.card Color) * meetingPairSum i j h +
            (pairR (Fintype.card Color) / 2) *
              disjointPartnerSum Color i j h)) =
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else
          h i j * (pairP (Fintype.card Color) * h i j)) +
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else
          h i j * (pairQ (Fintype.card Color) * meetingPairSum i j h)) +
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j *
          ((pairR (Fintype.card Color) / 2) *
            disjointPartnerSum Color i j h)) := by
    calc
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j *
          (pairP (Fintype.card Color) * h i j +
            pairQ (Fintype.card Color) * meetingPairSum i j h +
            (pairR (Fintype.card Color) / 2) *
              disjointPartnerSum Color i j h)) =
          ∑ i : Color, ∑ j : Color,
            ((if i = j then 0 else
              h i j * (pairP (Fintype.card Color) * h i j)) +
            (if i = j then 0 else
              h i j * (pairQ (Fintype.card Color) * meetingPairSum i j h)) +
            (if i = j then 0 else h i j *
              ((pairR (Fintype.card Color) / 2) *
                disjointPartnerSum Color i j h))) := by
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
            if i = j then 0 else
              h i j * (pairP (Fintype.card Color) * h i j)) +
          (∑ i : Color, ∑ j : Color,
            if i = j then 0 else h i j *
              (pairQ (Fintype.card Color) * meetingPairSum i j h)) +
          (∑ i : Color, ∑ j : Color,
            if i = j then 0 else h i j *
              ((pairR (Fintype.card Color) / 2) *
                disjointPartnerSum Color i j h)) := by
        simp only [Finset.sum_add_distrib]
  rw [hkernel,
    hfactor (pairP (Fintype.card Color)) h, hself,
    hfactor (pairQ (Fintype.card Color))
      (fun i j ↦ meetingPairSum i j h),
    hfactor (pairR (Fintype.card Color) / 2)
      (fun i j ↦ disjointPartnerSum Color i j h),
    hmeet, hdisjoint, htotal, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    hsplit]
  have hcardReal : (4 : ℝ) ≤ (Fintype.card Color : ℝ) := by
    exact_mod_cast hcard
  have hK : ((Fintype.card Color : ℝ) - 2) ≠ 0 := by
    nlinarith
  have hrow' : rowEnergy h =
      (((Fintype.card Color : ℝ) - 2) / 2) * energy (vertexPart h) := by
    nlinarith
  rw [hrow']
  unfold pairVertexEigenvalue pairRowZeroEigenvalue
  ring

end

end WeightedEdgeColoring.WeightedMomentPairKernelAlgebra
