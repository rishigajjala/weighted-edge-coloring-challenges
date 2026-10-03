import WeightedEdgeColoring.WeightedMomentPairKernelAlgebra

/-!
# Energy contraction of the two-color pairing operator

For a fixed perfect pairing, `pairAverage` is the orthogonal projection onto
the arrays invariant under the legal pair exchanges.  We prove the projection
identity directly by finite reindexing, including the special orbit formed by
two colors paired with each other.  Averaging the identity over all pairings
and using the exact coordinate kernel gives the unconditional factor-one-half
contraction.
-/

namespace WeightedEdgeColoring.FiniteColorPairingPairEnergy

open scoped BigOperators
open WeightedEdgeColoring.FiniteColorPairing
open WeightedEdgeColoring.FiniteColorPairingOperators
open WeightedEdgeColoring.WeightedMomentPairingContraction
open WeightedEdgeColoring.WeightedMomentPairArray
open WeightedEdgeColoring.WeightedMomentPairKernelAlgebra

noncomputable section

variable {Color : Type*} [Fintype Color] [DecidableEq Color]

theorem pairAverage_partner_left (p : Pairing Color)
    (h : Color → Color → ℝ) {i j : Color}
    (hij : i ≠ j) (hpij : partner Color p i ≠ j) :
    pairAverage p h (partner Color p i) j = pairAverage p h i j := by
  unfold pairAverage
  have hpi_ne_j : partner Color p i ≠ j := hpij
  have hppi_ne_j : partner Color p (partner Color p i) ≠ j := by
    intro h
    exact hij ((partner_partner Color p i).symm.trans h)
  rw [partner_partner]
  simp only [if_neg hpi_ne_j, if_neg hppi_ne_j, if_neg hij, if_neg hpij]
  ring

theorem pairAverage_partner_right (p : Pairing Color)
    (h : Color → Color → ℝ) {i j : Color}
    (hij : i ≠ j) (hpij : partner Color p i ≠ j) :
    pairAverage p h i (partner Color p j) = pairAverage p h i j := by
  unfold pairAverage
  have hi_ne_pj : i ≠ partner Color p j := by
    intro hipj
    apply hpij
    calc
      partner Color p i = partner Color p (partner Color p j) := by rw [hipj]
      _ = j := partner_partner Color p j
  have hpi_ne_pj : partner Color p i ≠ partner Color p j := by
    intro h
    exact hij (partner_injective Color p h)
  rw [partner_partner]
  simp only [if_neg hi_ne_pj, if_neg hpi_ne_pj, if_neg hij, if_neg hpij]
  ring

/-- Mask selecting ordered pairs whose two colors lie in different blocks of
the fixed perfect pairing. -/
def unpairedMask (p : Pairing Color) (f : Color → Color → ℝ)
    (i j : Color) : ℝ :=
  if i = j ∨ partner Color p i = j then 0 else f i j

theorem unpaired_pairAverage_eq_four (p : Pairing Color)
    (h : Color → Color → ℝ) {i j : Color}
    (hij : i ≠ j) (hpij : partner Color p i ≠ j) :
    pairAverage p h i j =
      (h i j + h (partner Color p i) j +
        h i (partner Color p j) +
        h (partner Color p i) (partner Color p j)) / 4 := by
  simp [pairAverage, hij, hpij]

theorem sum_unpaired_partner_left (p : Pairing Color)
    (h a : Color → Color → ℝ)
    (hainv : ∀ i j, i ≠ j → partner Color p i ≠ j →
      a (partner Color p i) j = a i j) :
    (∑ i : Color, ∑ j : Color,
      unpairedMask p (fun x y ↦ h (partner Color p x) y * a x y) i j) =
    ∑ i : Color, ∑ j : Color,
      unpairedMask p (fun x y ↦ h x y * a x y) i j := by
  have hreindex := Equiv.sum_comp p.1 (fun i : Color ↦
    ∑ j : Color, unpairedMask p (fun x y ↦ h x y * a x y) i j)
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  unfold unpairedMask
  change
    (if i = j ∨ partner Color p i = j then 0
      else h (partner Color p i) j * a i j) =
    (if partner Color p i = j ∨
        partner Color p (partner Color p i) = j then 0
      else h (partner Color p i) j * a (partner Color p i) j)
  have hpp := partner_partner Color p i
  by_cases hij : i = j
  · subst j
    rw [if_pos (Or.inl rfl), if_pos (Or.inr hpp)]
  by_cases hpij : partner Color p i = j
  · rw [if_pos (Or.inr hpij), if_pos (Or.inl hpij)]
  · have hpi_ne_j : partner Color p i ≠ j := hpij
    have hppi_ne_j : partner Color p (partner Color p i) ≠ j := by
      intro h
      exact hij (hpp.symm.trans h)
    rw [if_neg (not_or_intro hij hpij),
      if_neg (not_or_intro hpi_ne_j hppi_ne_j),
      hainv i j hij hpij]

theorem sum_unpaired_partner_right (p : Pairing Color)
    (h a : Color → Color → ℝ)
    (hainv : ∀ i j, i ≠ j → partner Color p i ≠ j →
      a i (partner Color p j) = a i j) :
    (∑ i : Color, ∑ j : Color,
      unpairedMask p (fun x y ↦ h x (partner Color p y) * a x y) i j) =
    ∑ i : Color, ∑ j : Color,
      unpairedMask p (fun x y ↦ h x y * a x y) i j := by
  apply Finset.sum_congr rfl
  intro i _hi
  have hreindex := Equiv.sum_comp p.1 (fun j : Color ↦
    unpairedMask p (fun x y ↦ h x y * a x y) i j)
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro j _hj
  unfold unpairedMask
  change
    (if i = j ∨ partner Color p i = j then 0
      else h i (partner Color p j) * a i j) =
    (if i = partner Color p j ∨
        partner Color p i = partner Color p j then 0
      else h i (partner Color p j) * a i (partner Color p j))
  have hpp := partner_partner Color p j
  by_cases hij : i = j
  · subst j
    rw [if_pos (Or.inl rfl), if_pos (Or.inr rfl)]
  by_cases hpij : partner Color p i = j
  · have hipj : i = partner Color p j := by
      apply partner_injective Color p
      simpa [hpp] using hpij
    rw [if_pos (Or.inr hpij), if_pos (Or.inl hipj)]
  · have hi_ne_pj : i ≠ partner Color p j := by
      intro hipj
      apply hpij
      calc
        partner Color p i = partner Color p (partner Color p j) := by rw [hipj]
        _ = j := hpp
    have hpi_ne_pj : partner Color p i ≠ partner Color p j := by
      intro h
      exact hij (partner_injective Color p h)
    rw [if_neg (not_or_intro hij hpij),
      if_neg (not_or_intro hi_ne_pj hpi_ne_pj),
      hainv i j hij hpij]

/-- On the different-block part, the four-outcome average is an orthogonal
projection. -/
theorem sum_sq_pairAverage_unpaired_eq_inner (p : Pairing Color)
    (h : Color → Color → ℝ) :
    (∑ i : Color, ∑ j : Color,
      unpairedMask p (fun x y ↦ (pairAverage p h x y) ^ 2) i j) =
    ∑ i : Color, ∑ j : Color,
      unpairedMask p (fun x y ↦ h x y * pairAverage p h x y) i j := by
  let a := pairAverage p h
  have hleft : ∀ i j : Color, i ≠ j → partner Color p i ≠ j →
      a (partner Color p i) j = a i j := by
    intro i j hij hpij
    exact pairAverage_partner_left p h hij hpij
  have hright : ∀ i j : Color, i ≠ j → partner Color p i ≠ j →
      a i (partner Color p j) = a i j := by
    intro i j hij hpij
    exact pairAverage_partner_right p h hij hpij
  have hboth :
      (∑ i : Color, ∑ j : Color,
        unpairedMask p
          (fun x y ↦ h (partner Color p x) (partner Color p y) * a x y)
          i j) =
      ∑ i : Color, ∑ j : Color,
        unpairedMask p (fun x y ↦ h x y * a x y) i j := by
    calc
      (∑ i : Color, ∑ j : Color,
        unpairedMask p
          (fun x y ↦ h (partner Color p x) (partner Color p y) * a x y)
          i j) =
          ∑ i : Color, ∑ j : Color,
            unpairedMask p
              (fun x y ↦ h x (partner Color p y) * a x y) i j :=
        sum_unpaired_partner_left p
          (fun x y ↦ h x (partner Color p y)) a hleft
      _ = _ := sum_unpaired_partner_right p h a hright
  have hleftsum := sum_unpaired_partner_left p h a hleft
  have hrightsum := sum_unpaired_partner_right p h a hright
  symm
  calc
    (∑ i : Color, ∑ j : Color,
      unpairedMask p (fun x y ↦ h x y * a x y) i j) =
      (1 / 4 : ℝ) *
        ((∑ i : Color, ∑ j : Color,
          unpairedMask p (fun x y ↦ h x y * a x y) i j) +
        (∑ i : Color, ∑ j : Color,
          unpairedMask p
            (fun x y ↦ h (partner Color p x) y * a x y) i j) +
        (∑ i : Color, ∑ j : Color,
          unpairedMask p
            (fun x y ↦ h x (partner Color p y) * a x y) i j) +
        (∑ i : Color, ∑ j : Color,
          unpairedMask p
            (fun x y ↦ h (partner Color p x) (partner Color p y) * a x y)
            i j)) := by rw [hleftsum, hrightsum, hboth]; ring
    _ = ∑ i : Color, ∑ j : Color,
        unpairedMask p (fun x y ↦ (a x y) ^ 2) i j := by
      calc
        (1 / 4 : ℝ) *
            ((∑ i : Color, ∑ j : Color,
              unpairedMask p (fun x y ↦ h x y * a x y) i j) +
            (∑ i : Color, ∑ j : Color,
              unpairedMask p
                (fun x y ↦ h (partner Color p x) y * a x y) i j) +
            (∑ i : Color, ∑ j : Color,
              unpairedMask p
                (fun x y ↦ h x (partner Color p y) * a x y) i j) +
            (∑ i : Color, ∑ j : Color,
              unpairedMask p
                (fun x y ↦
                  h (partner Color p x) (partner Color p y) * a x y)
                i j)) =
            (1 / 4 : ℝ) * ∑ i : Color, ∑ j : Color,
              (unpairedMask p (fun x y ↦ h x y * a x y) i j +
                unpairedMask p
                  (fun x y ↦ h (partner Color p x) y * a x y) i j +
                unpairedMask p
                  (fun x y ↦ h x (partner Color p y) * a x y) i j +
                unpairedMask p
                  (fun x y ↦
                    h (partner Color p x) (partner Color p y) * a x y)
                  i j) := by
          simp only [Finset.sum_add_distrib]
        _ = ∑ i : Color, ∑ j : Color,
              (1 / 4 : ℝ) *
                (unpairedMask p (fun x y ↦ h x y * a x y) i j +
                  unpairedMask p
                    (fun x y ↦ h (partner Color p x) y * a x y) i j +
                  unpairedMask p
                    (fun x y ↦ h x (partner Color p y) * a x y) i j +
                  unpairedMask p
                    (fun x y ↦
                      h (partner Color p x) (partner Color p y) * a x y)
                    i j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
        _ = ∑ i : Color, ∑ j : Color,
              unpairedMask p (fun x y ↦ (a x y) ^ 2) i j := by
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro j _hj
          unfold unpairedMask
          by_cases hij : i = j
          · simp [hij]
          · by_cases hpij : partner Color p i = j
            · simp [hpij]
            · simp only [if_neg (not_or_intro hij hpij)]
              have haij : a i j =
                  (h i j + h (partner Color p i) j +
                    h i (partner Color p j) +
                    h (partner Color p i) (partner Color p j)) / 4 := by
                simpa [a] using unpaired_pairAverage_eq_four p h hij hpij
              rw [haij]
              ring

/-- A fixed pairing preserves the total mass of a symmetric off-diagonal
array. -/
theorem total_pairAverage (p : Pairing Color)
    (h : Color → Color → ℝ)
    (hsym : ∀ i j, h i j = h j i) (hdiag : ∀ i, h i i = 0) :
    total (pairAverage p h) = total h := by
  let one : Color → Color → ℝ := fun _ _ ↦ 1
  have honeleft : ∀ i j : Color, i ≠ j → partner Color p i ≠ j →
      one (partner Color p i) j = one i j := by simp [one]
  have honeright : ∀ i j : Color, i ≠ j → partner Color p i ≠ j →
      one i (partner Color p j) = one i j := by simp [one]
  have hleft := sum_unpaired_partner_left p h one honeleft
  have hright := sum_unpaired_partner_right p h one honeright
  have hboth :
      (∑ i : Color, ∑ j : Color,
        unpairedMask p
          (fun x y ↦ h (partner Color p x) (partner Color p y)) i j) =
      ∑ i : Color, ∑ j : Color, unpairedMask p h i j := by
    calc
      (∑ i : Color, ∑ j : Color,
        unpairedMask p
          (fun x y ↦ h (partner Color p x) (partner Color p y)) i j) =
          ∑ i : Color, ∑ j : Color,
            unpairedMask p (fun x y ↦ h x (partner Color p y)) i j := by
        simpa [one] using
          sum_unpaired_partner_left p
            (fun x y ↦ h x (partner Color p y)) one honeleft
      _ = _ := by
        simpa [one] using sum_unpaired_partner_right p h one honeright
  unfold total rowSum
  have hsplitAverage :
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else pairAverage p h i j) =
      (∑ i : Color, ∑ j : Color,
        if partner Color p i = j then h i j else 0) +
      (∑ i : Color, ∑ j : Color,
        unpairedMask p (pairAverage p h) i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    unfold unpairedMask
    by_cases hij : i = j
    · simp [hij, partner_ne]
    · by_cases hpij : partner Color p i = j
      · simp [hij, hpij, pairAverage]
      · simp [hij, hpij]
  have hexpandPoint (i j : Color) :
      unpairedMask p (pairAverage p h) i j =
        (1 / 4 : ℝ) *
          (unpairedMask p h i j +
            unpairedMask p (fun x y ↦ h (partner Color p x) y) i j +
            unpairedMask p (fun x y ↦ h x (partner Color p y)) i j +
            unpairedMask p
              (fun x y ↦ h (partner Color p x) (partner Color p y)) i j) := by
    unfold unpairedMask
    by_cases hij : i = j
    · simp [hij]
    · by_cases hpij : partner Color p i = j
      · simp [hij, hpij]
      · simp only [if_neg (not_or_intro hij hpij)]
        rw [unpaired_pairAverage_eq_four p h hij hpij]
        ring
  have haverageExpand :
      (∑ i : Color, ∑ j : Color,
        unpairedMask p (pairAverage p h) i j) =
      (1 / 4 : ℝ) *
        ((∑ i : Color, ∑ j : Color, unpairedMask p h i j) +
         (∑ i : Color, ∑ j : Color,
            unpairedMask p (fun x y ↦ h (partner Color p x) y) i j) +
         (∑ i : Color, ∑ j : Color,
            unpairedMask p (fun x y ↦ h x (partner Color p y)) i j) +
         (∑ i : Color, ∑ j : Color,
            unpairedMask p
              (fun x y ↦ h (partner Color p x) (partner Color p y))
              i j)) := by
    calc
      (∑ i : Color, ∑ j : Color,
        unpairedMask p (pairAverage p h) i j) =
          ∑ i : Color, ∑ j : Color,
            (1 / 4 : ℝ) *
              (unpairedMask p h i j +
                unpairedMask p (fun x y ↦ h (partner Color p x) y) i j +
                unpairedMask p (fun x y ↦ h x (partner Color p y)) i j +
                unpairedMask p
                  (fun x y ↦ h (partner Color p x) (partner Color p y))
                  i j) := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro j _hj
            exact hexpandPoint i j
      _ = (1 / 4 : ℝ) * ∑ i : Color, ∑ j : Color,
            (unpairedMask p h i j +
              unpairedMask p (fun x y ↦ h (partner Color p x) y) i j +
              unpairedMask p (fun x y ↦ h x (partner Color p y)) i j +
              unpairedMask p
                (fun x y ↦ h (partner Color p x) (partner Color p y))
                i j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hleft' :
      (∑ i : Color, ∑ j : Color,
        unpairedMask p (fun x y ↦ h (partner Color p x) y) i j) =
      ∑ i : Color, ∑ j : Color, unpairedMask p h i j := by
    simpa [one] using hleft
  have hright' :
      (∑ i : Color, ∑ j : Color,
        unpairedMask p (fun x y ↦ h x (partner Color p y)) i j) =
      ∑ i : Color, ∑ j : Color, unpairedMask p h i j := by
    simpa [one] using hright
  have hunpairedAverage :
      (∑ i : Color, ∑ j : Color,
        unpairedMask p (pairAverage p h) i j) =
      ∑ i : Color, ∑ j : Color, unpairedMask p h i j := by
    rw [haverageExpand, hleft', hright', hboth]
    ring
  have hsplitInput :
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j) =
      (∑ i : Color, ∑ j : Color,
        if partner Color p i = j then h i j else 0) +
      (∑ i : Color, ∑ j : Color, unpairedMask p h i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    unfold unpairedMask
    by_cases hij : i = j
    · simp [hij, partner_ne]
    · by_cases hpij : partner Color p i = j <;> simp [hij, hpij]
  rw [hsplitAverage, hunpairedAverage, hsplitInput]

/-- Fixed-pairing projection identity, including the paired-together orbit. -/
theorem energy_pairAverage_eq_inner (p : Pairing Color)
    (h : Color → Color → ℝ)
    (hsym : ∀ i j, h i j = h j i) (hdiag : ∀ i, h i i = 0) :
    energy (pairAverage p h) =
      ∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j * pairAverage p h i j := by
  have hunpaired := sum_sq_pairAverage_unpaired_eq_inner p h
  unfold energy
  have hsplitSquares :
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else (pairAverage p h i j) ^ 2) =
      (∑ i : Color, ∑ j : Color,
        if partner Color p i = j then (h i j) ^ 2 else 0) +
      (∑ i : Color, ∑ j : Color,
        unpairedMask p (fun x y ↦ (pairAverage p h x y) ^ 2) i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    unfold unpairedMask
    by_cases hij : i = j
    · simp [hij, partner_ne]
    · by_cases hpij : partner Color p i = j
      · simp [hij, hpij, pairAverage, pow_two]
      · simp [hij, hpij]
  have hsplitInner :
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j * pairAverage p h i j) =
      (∑ i : Color, ∑ j : Color,
        if partner Color p i = j then (h i j) ^ 2 else 0) +
      (∑ i : Color, ∑ j : Color,
        unpairedMask p (fun x y ↦ h x y * pairAverage p h x y) i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    unfold unpairedMask
    by_cases hij : i = j
    · simp [hij, partner_ne]
    · by_cases hpij : partner Color p i = j
      · simp [hij, hpij, pairAverage, pow_two]
      · simp [hij, hpij]
  calc
    (∑ i : Color, ∑ j : Color,
      if i = j then 0 else (pairAverage p h i j) ^ 2) =
        (∑ i : Color, ∑ j : Color,
          if partner Color p i = j then (h i j) ^ 2 else 0) +
        (∑ i : Color, ∑ j : Color,
          unpairedMask p (fun x y ↦ (pairAverage p h x y) ^ 2) i j) :=
      hsplitSquares
    _ = (∑ i : Color, ∑ j : Color,
          if partner Color p i = j then (h i j) ^ 2 else 0) +
        (∑ i : Color, ∑ j : Color,
          unpairedMask p (fun x y ↦ h x y * pairAverage p h x y) i j) := by
      rw [hunpaired]
    _ = ∑ i : Color, ∑ j : Color,
          if i = j then 0 else h i j * pairAverage p h i j :=
      hsplitInner.symm

/-- Exact energy after averaging over all perfect pairings. -/
theorem average_energy_pairAverage_eq
    (heven : Even (Fintype.card Color)) (hcard : 4 ≤ Fintype.card Color)
    (h : Color → Color → ℝ) (htotal : total h = 0)
    (hsym : ∀ i j, h i j = h j i) (hdiag : ∀ i, h i i = 0) :
    (∑ p : Pairing Color, energy (pairAverage p h)) /
        (Fintype.card (Pairing Color) : ℝ) =
      pairVertexEigenvalue (Fintype.card Color) * energy (vertexPart h) +
        pairRowZeroEigenvalue (Fintype.card Color) * energy (rowZeroPart h) := by
  letI : Nonempty (Pairing Color) := nonempty_pairing_of_even_card Color heven
  have hP : (Fintype.card (Pairing Color) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp_rw [energy_pairAverage_eq_inner _ h hsym hdiag]
  rw [Finset.sum_comm, Finset.sum_div]
  rw [show
      (∑ i : Color,
        (∑ p : Pairing Color, ∑ j : Color,
          if i = j then 0 else h i j * pairAverage p h i j) /
            (Fintype.card (Pairing Color) : ℝ)) =
      ∑ i : Color, ∑ j : Color,
        if i = j then 0 else h i j *
          ((∑ p : Pairing Color, pairAverage p h i j) /
            (Fintype.card (Pairing Color) : ℝ)) by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hij : i = j
    · simp [hij]
    · simp only [if_false, hij]
      rw [← Finset.mul_sum]
      ring]
  simp_rw [show ∀ i j : Color,
      (if i = j then 0 else h i j *
        ((∑ p : Pairing Color, pairAverage p h i j) /
          (Fintype.card (Pairing Color) : ℝ))) =
      if i = j then 0 else h i j *
        (pairP (Fintype.card Color) * h i j +
          pairQ (Fintype.card Color) * meetingPairSum i j h +
          (pairR (Fintype.card Color) / 2) *
            disjointPartnerSum Color i j h) by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · rw [if_neg hij, if_neg hij,
        average_pairAverage heven hcard h hsym hdiag hij]]
  exact averagedPairKernel_quadratic h htotal hcard hsym hdiag

theorem average_energy_pairAverage_le_half
    (heven : Even (Fintype.card Color)) (hcard : 4 ≤ Fintype.card Color)
    (h : Color → Color → ℝ) (htotal : total h = 0)
    (hsym : ∀ i j, h i j = h j i) (hdiag : ∀ i, h i i = 0) :
    (∑ p : Pairing Color, energy (pairAverage p h)) /
        (Fintype.card (Pairing Color) : ℝ) ≤ energy h / 2 := by
  rw [average_energy_pairAverage_eq heven hcard h htotal hsym hdiag]
  exact averagedEnergy_le_half h htotal hcard hsym _ rfl

end

end WeightedEdgeColoring.FiniteColorPairingPairEnergy
