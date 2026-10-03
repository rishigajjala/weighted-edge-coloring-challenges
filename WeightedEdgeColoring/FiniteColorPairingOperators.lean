import WeightedEdgeColoring.FiniteColorPairingDoubleAverage
import WeightedEdgeColoring.WeightedMomentPairArray

/-!
# Averaging operators attached to a finite color pairing

`singleAverage` averages a one-color list inside every pair.  `pairAverage`
is the conditional expectation of an ordered symmetric two-color array after
independent exchanges inside all pairs.  If the two tracked colors are paired
with each other their unordered product is unchanged; otherwise the four
independent exchange outcomes are averaged.
-/

namespace WeightedEdgeColoring.FiniteColorPairingOperators

open scoped BigOperators
open WeightedEdgeColoring.FiniteColorPairing

noncomputable section

variable {Color : Type*} [Fintype Color] [DecidableEq Color]

def singleAverage (p : Pairing Color) (h : Color → ℝ) (i : Color) : ℝ :=
  (h i + h (partner Color p i)) / 2

def pairAverage (p : Pairing Color) (h : Color → Color → ℝ)
    (i j : Color) : ℝ :=
  if i = j then 0
  else if partner Color p i = j then h i j
  else
    (h i j + h (partner Color p i) j +
      h i (partner Color p j) +
      h (partner Color p i) (partner Color p j)) / 4

/-- Sum of pair-array entries meeting `{i,j}` in exactly one color, written
with ordered representatives. -/
def meetingPairSum (i j : Color) (h : Color → Color → ℝ) : ℝ :=
  ∑ k : Color, if k = i ∨ k = j then 0 else h k j + h i k

theorem singleAverage_partner (p : Pairing Color) (h : Color → ℝ)
    (i : Color) :
    singleAverage p h (partner Color p i) = singleAverage p h i := by
  unfold singleAverage
  rw [partner_partner]
  ring

omit [DecidableEq Color] in
theorem sum_singleAverage (p : Pairing Color) (h : Color → ℝ) :
    ∑ i, singleAverage p h i = ∑ i, h i := by
  unfold singleAverage
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hperm : (∑ i : Color, h (partner Color p i)) = ∑ i, h i := by
    simpa [partner] using Equiv.sum_comp p.1 h
  rw [hperm]
  ring

theorem singleAverage_idempotent (p : Pairing Color) (h : Color → ℝ)
    (i : Color) :
    singleAverage p (singleAverage p h) i = singleAverage p h i := by
  unfold singleAverage
  rw [partner_partner]
  ring

omit [DecidableEq Color] in
theorem sum_sq_singleAverage_eq_inner
    (p : Pairing Color) (h : Color → ℝ) :
    (∑ i, (singleAverage p h i) ^ 2) =
      ∑ i, h i * singleAverage p h i := by
  have hsqperm :
      (∑ i : Color, (h (partner Color p i)) ^ 2) =
        ∑ i : Color, (h i) ^ 2 := by
    simpa [partner] using Equiv.sum_comp p.1 (fun i ↦ (h i) ^ 2)
  unfold singleAverage
  simp_rw [div_pow, add_sq]
  rw [← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hsqperm]
  rw [show
      (∑ i : Color, h i * ((h i + h (partner Color p i)) / 2)) =
        ((∑ i : Color, (h i) ^ 2) +
          ∑ i : Color, h i * h (partner Color p i)) / 2 by
    calc
      (∑ i : Color, h i * ((h i + h (partner Color p i)) / 2)) =
          ∑ i : Color,
            ((h i) ^ 2 + h i * h (partner Color p i)) / 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (∑ i : Color,
            ((h i) ^ 2 + h i * h (partner Color p i))) / 2 := by
        rw [← Finset.sum_div]
      _ = ((∑ i : Color, (h i) ^ 2) +
          ∑ i : Color, h i * h (partner Color p i)) / 2 := by
        rw [Finset.sum_add_distrib]]
  rw [show
      (∑ i : Color, 2 * h i * h (partner Color p i)) =
        2 * ∑ i : Color, h i * h (partner Color p i) by
    calc
      (∑ i : Color, 2 * h i * h (partner Color p i)) =
          ∑ i : Color, 2 * (h i * h (partner Color p i)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = _ := by rw [Finset.mul_sum]]
  ring

/-- The uniform average of the one-color quadratic energy contracts every
zero-sum list by the manuscript eigenvalue, hence by one half. -/
theorem average_sum_sq_singleAverage_eq
    (heven : Even (Fintype.card Color))
    (hcard : 2 ≤ Fintype.card Color)
    (h : Color → ℝ) (hsum : ∑ i, h i = 0) :
    (∑ p : Pairing Color, ∑ i, (singleAverage p h i) ^ 2) /
        (Fintype.card (Pairing Color) : ℝ) =
      WeightedEdgeColoring.WeightedMomentPairingContraction.singleEigenvalue
          (Fintype.card Color) * ∑ i, (h i) ^ 2 := by
  letI : Nonempty (Pairing Color) := nonempty_pairing_of_even_card Color heven
  have hcardReal : (2 : ℝ) ≤ (Fintype.card Color : ℝ) := by
    exact_mod_cast hcard
  have hK1 : ((Fintype.card Color : ℝ) - 1) ≠ 0 := by
    linarith
  simp_rw [sum_sq_singleAverage_eq_inner]
  rw [Finset.sum_comm, Finset.sum_div]
  calc
    (∑ i : Color,
      (∑ p : Pairing Color, h i * singleAverage p h i) /
        (Fintype.card (Pairing Color) : ℝ)) =
        ∑ i : Color, h i *
          ((1 / 2 : ℝ) * h i +
            1 / (2 * ((Fintype.card Color : ℝ) - 1)) *
              ((∑ j : Color, h j) - h i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hpairCard : (Fintype.card (Pairing Color) : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      have havg :
          (∑ p : Pairing Color, singleAverage p h i) /
              (Fintype.card (Pairing Color) : ℝ) =
            (1 / 2 : ℝ) * h i +
              1 / (2 * ((Fintype.card Color : ℝ) - 1)) *
                ((∑ j : Color, h j) - h i) := by
        unfold singleAverage
        rw [← Finset.sum_div, Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        calc
          _ = h i / 2 +
              (((∑ p : Pairing Color, h (partner Color p i)) /
                (Fintype.card (Pairing Color) : ℝ)) / 2) := by
            field_simp
          _ = _ := by
            rw [average_partner Color heven hcard h]
            field_simp [hK1]
      calc
        _ = h i * ((∑ p : Pairing Color, singleAverage p h i) /
            (Fintype.card (Pairing Color) : ℝ)) := by
          rw [← Finset.mul_sum]
          ring
        _ = _ := by rw [havg]
    _ = WeightedEdgeColoring.WeightedMomentPairingContraction.singleEigenvalue
          (Fintype.card Color) * ∑ i, (h i) ^ 2 := by
      have hkernel :=
      WeightedEdgeColoring.WeightedMomentPairingContraction.singleKernel_quadratic_of_sum_zero
        hcard hsum
      rw [show
          (∑ i : Color, h i *
            ((1 / 2 : ℝ) * h i +
              1 / (2 * ((Fintype.card Color : ℝ) - 1)) *
                ((∑ j : Color, h j) - h i))) =
            (1 / 2 : ℝ) * (∑ i : Color, (h i) ^ 2) +
              1 / (2 * ((Fintype.card Color : ℝ) - 1)) *
                ((∑ i : Color, h i) ^ 2 - ∑ i : Color, (h i) ^ 2) by
        calc
          (∑ i : Color, h i *
            ((1 / 2 : ℝ) * h i +
              1 / (2 * ((Fintype.card Color : ℝ) - 1)) *
                ((∑ j : Color, h j) - h i))) =
              ∑ i : Color,
                ((1 / 2 : ℝ) * (h i) ^ 2 +
                  1 / (2 * ((Fintype.card Color : ℝ) - 1)) *
                    (h i * (∑ j : Color, h j) - (h i) ^ 2)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          _ = (1 / 2 : ℝ) * (∑ i : Color, (h i) ^ 2) +
              1 / (2 * ((Fintype.card Color : ℝ) - 1)) *
                (∑ i : Color,
                  (h i * (∑ j : Color, h j) - (h i) ^ 2)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum,
              ← Finset.mul_sum]
          _ = (1 / 2 : ℝ) * (∑ i : Color, (h i) ^ 2) +
              1 / (2 * ((Fintype.card Color : ℝ) - 1)) *
                ((∑ i : Color, h i * (∑ j : Color, h j)) -
                  ∑ i : Color, (h i) ^ 2) := by
            rw [Finset.sum_sub_distrib]
          _ = _ := by
            rw [← Finset.sum_mul]
            ring]
      exact hkernel

theorem average_sum_sq_singleAverage_le_half
    (heven : Even (Fintype.card Color))
    (hcard : 2 ≤ Fintype.card Color)
    (h : Color → ℝ) (hsum : ∑ i, h i = 0) :
    (∑ p : Pairing Color, ∑ i, (singleAverage p h i) ^ 2) /
        (Fintype.card (Pairing Color) : ℝ) ≤
      (∑ i, (h i) ^ 2) / 2 := by
  rw [average_sum_sq_singleAverage_eq heven hcard h hsum]
  simpa [div_eq_mul_inv, mul_comm] using
    (mul_le_mul_of_nonneg_right
      (WeightedEdgeColoring.WeightedMomentPairingContraction.singleEigenvalue_le_half hcard)
      (Fintype.sum_nonneg fun i ↦ sq_nonneg (h i)))

theorem pairAverage_symmetric (p : Pairing Color)
    (h : Color → Color → ℝ) (hsym : ∀ i j, h i j = h j i)
    (i j : Color) : pairAverage p h i j = pairAverage p h j i := by
  unfold pairAverage
  by_cases hij : i = j
  · subst j
    simp
  have hpiff : partner Color p i = j ↔ partner Color p j = i := by
    constructor
    · intro hp
      calc
        partner Color p j = partner Color p (partner Color p i) := by rw [hp]
        _ = i := partner_partner Color p i
    · intro hp
      calc
        partner Color p i = partner Color p (partner Color p j) := by rw [hp]
        _ = j := partner_partner Color p j
  have hji : j ≠ i := by
    intro hji
    exact hij hji.symm
  by_cases hp : partner Color p i = j
  · simp [hij, hji, hp, hpiff.mp hp, hsym]
  · have hp' : partner Color p j ≠ i := fun h ↦ hp (hpiff.mpr h)
    simp [hij, hji, hp, hp', hsym]
    ring

/-- Rewrite the special paired-together case as a correction to the uniform
four-outcome formula. -/
theorem pairAverage_eq_fourAverage_add_correction
    (p : Pairing Color) (h : Color → Color → ℝ)
    (hsym : ∀ i j, h i j = h j i) (hdiag : ∀ i, h i i = 0)
    {i j : Color} (hij : i ≠ j) :
    pairAverage p h i j =
      (h i j + h (partner Color p i) j +
        h i (partner Color p j) +
        h (partner Color p i) (partner Color p j)) / 4 +
      if partner Color p i = j then h i j / 2 else 0 := by
  unfold pairAverage
  rw [if_neg hij]
  by_cases hp : partner Color p i = j
  · have hp' : partner Color p j = i := by
      calc
        partner Color p j = partner Color p (partner Color p i) := by rw [hp]
        _ = i := partner_partner Color p i
    rw [if_pos hp, if_pos hp, hp, hp', hdiag, hdiag, hsym j i]
    ring
  · rw [if_neg hp, if_neg hp]
    ring

/-- Exact averaged coordinate kernel of the pair operator. -/
theorem average_pairAverage
    (heven : Even (Fintype.card Color)) (hcard : 4 ≤ Fintype.card Color)
    (h : Color → Color → ℝ)
    (hsym : ∀ i j, h i j = h j i) (hdiag : ∀ i, h i i = 0)
    {i j : Color} (hij : i ≠ j) :
    (∑ p : Pairing Color, pairAverage p h i j) /
        (Fintype.card (Pairing Color) : ℝ) =
      WeightedEdgeColoring.WeightedMomentPairingContraction.pairP
          (Fintype.card Color) * h i j +
        WeightedEdgeColoring.WeightedMomentPairingContraction.pairQ
          (Fintype.card Color) * meetingPairSum i j h +
        (WeightedEdgeColoring.WeightedMomentPairingContraction.pairR
          (Fintype.card Color) / 2) *
            disjointPartnerSum Color i j h := by
  letI : Nonempty (Pairing Color) := nonempty_pairing_of_even_card Color heven
  have hP : (Fintype.card (Pairing Color) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcardReal : (4 : ℝ) ≤ (Fintype.card Color : ℝ) := by
    exact_mod_cast hcard
  have hK1 : ((Fintype.card Color : ℝ) - 1) ≠ 0 := by
    linarith
  have hpartnerI := average_partner Color heven (by omega : 2 ≤ Fintype.card Color)
    (i := i) (fun k ↦ h k j)
  have hpartnerJ := average_partner Color heven (by omega : 2 ≤ Fintype.card Color)
    (i := j) (fun k ↦ h i k)
  have hdouble := average_partner_partner Color heven hcard hij h
  have hpaired := card_partnerFiber_cast_mul Color hij
  simp_rw [pairAverage_eq_fourAverage_add_correction _ _ hsym hdiag hij]
  rw [Finset.sum_add_distrib, add_div]
  -- Replace each of the four finite averages and the paired-fiber correction.
  have hcorrection :
      (∑ p : Pairing Color,
        if partner Color p i = j then h i j / 2 else 0) /
          (Fintype.card (Pairing Color) : ℝ) =
        h i j / (2 * ((Fintype.card Color : ℝ) - 1)) := by
    rw [show
        (∑ p : Pairing Color,
          if partner Color p i = j then h i j / 2 else 0) =
          ((partnerFiber Color i j).card : ℝ) * (h i j / 2) by
      rw [← Finset.sum_filter]
      simp [partnerFiber]]
    field_simp
    calc
      _ = (((partnerFiber Color i j).card : ℝ) *
            ((Fintype.card Color : ℝ) - 1)) * h i j := by ring
      _ = _ := by rw [hpaired]; ring
  have hmeet :
      (((∑ k : Color, h k j) - h i j) +
        ((∑ k : Color, h i k) - h i j)) = meetingPairSum i j h := by
    let g : Color → ℝ := fun k ↦ h k j + h i k
    have hi : i ∈ (Finset.univ : Finset Color) := Finset.mem_univ i
    have hj : j ∈ (Finset.univ : Finset Color).erase i :=
      Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
    calc
      ((∑ k : Color, h k j) - h i j) +
          ((∑ k : Color, h i k) - h i j) =
        (∑ k : Color, g k) - g i - g j := by
          simp only [g, Finset.sum_add_distrib]
          rw [hdiag i, hdiag j]
          ring
      _ = (∑ k ∈ (Finset.univ : Finset Color).erase i, g k) - g j := by
        rw [← Finset.sum_erase_add (Finset.univ : Finset Color) g hi]
        ring
      _ = ∑ k ∈ ((Finset.univ : Finset Color).erase i).erase j, g k := by
        rw [← Finset.sum_erase_add
          ((Finset.univ : Finset Color).erase i) g hj]
        ring
      _ = meetingPairSum i j h := by
        unfold meetingPairSum
        rw [show ((Finset.univ : Finset Color).erase i).erase j =
            (Finset.univ : Finset Color).filter (fun k ↦ k ≠ i ∧ k ≠ j) by
          ext k
          simp [and_comm]]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k _hk
        by_cases hki : k = i <;> by_cases hkj : k = j <;>
          simp [g, hki, hkj]
  rw [show
      (∑ p : Pairing Color,
        (h i j + h (partner Color p i) j +
          h i (partner Color p j) +
          h (partner Color p i) (partner Color p j)) / 4) /
          (Fintype.card (Pairing Color) : ℝ) =
        (h i j +
          (((∑ k : Color, h k j) - h i j) /
            ((Fintype.card Color : ℝ) - 1)) +
          (((∑ k : Color, h i k) - h i j) /
            ((Fintype.card Color : ℝ) - 1)) +
          (h j i / ((Fintype.card Color : ℝ) - 1) +
            disjointPartnerSum Color i j h /
              (((Fintype.card Color : ℝ) - 1) *
                ((Fintype.card Color : ℝ) - 3)))) / 4 by
      rw [← Finset.sum_div]
      simp only [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc
        _ = (h i j +
            ((∑ p : Pairing Color, h (partner Color p i) j) /
              (Fintype.card (Pairing Color) : ℝ)) +
            ((∑ p : Pairing Color, h i (partner Color p j)) /
              (Fintype.card (Pairing Color) : ℝ)) +
            ((∑ p : Pairing Color,
                h (partner Color p i) (partner Color p j)) /
              (Fintype.card (Pairing Color) : ℝ))) / 4 := by
          field_simp
        _ = _ := by rw [hpartnerI, hpartnerJ, hdouble],
    hcorrection, hsym j i, ← hmeet]
  unfold WeightedEdgeColoring.WeightedMomentPairingContraction.pairP
    WeightedEdgeColoring.WeightedMomentPairingContraction.pairQ
    WeightedEdgeColoring.WeightedMomentPairingContraction.pairR
  field_simp
  ring

end

end WeightedEdgeColoring.FiniteColorPairingOperators
