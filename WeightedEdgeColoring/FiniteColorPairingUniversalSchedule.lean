import WeightedEdgeColoring.FiniteColorPairingPairEnergy

/-!
# A universal deterministic schedule of color pairings

The graph may have arbitrarily many vertices, so a schedule cannot be chosen
by a union bound over vertex states.  Instead this file evolves, in parallel,
an arbitrary finite tuple of zero-sum one-color vectors and symmetric
zero-total off-diagonal arrays.  The sum of their Hilbert--Schmidt energies
contracts in uniform average.  Iterating the finite averaging argument gives
one deterministic schedule which works for the whole tuple; taking the tuple
of centered coordinate bases produces the universal operator schedule.
-/

namespace WeightedEdgeColoring.FiniteColorPairingUniversalSchedule

open scoped BigOperators
open WeightedEdgeColoring.FiniteColorPairing
open WeightedEdgeColoring.FiniteColorPairingOperators
open WeightedEdgeColoring.FiniteColorPairingPairEnergy
open WeightedEdgeColoring.WeightedMomentPairArray
open WeightedEdgeColoring.WeightedMomentPairingContraction

noncomputable section

variable {Color SingleIndex PairIndex : Type*}
variable [Fintype Color] [DecidableEq Color]
variable [Fintype SingleIndex] [Fintype PairIndex]

/-- A finite family of states on which one pairing schedule must act
simultaneously. -/
structure UniversalState where
  single : SingleIndex → Color → ℝ
  pair : PairIndex → Color → Color → ℝ
  single_sum_zero : ∀ a, ∑ i, single a i = 0
  pair_symmetric : ∀ a i j, pair a i j = pair a j i
  pair_diagonal : ∀ a i, pair a i i = 0
  pair_total_zero : ∀ a, total (pair a) = 0

def universalEnergy (x : UniversalState (Color := Color)
    (SingleIndex := SingleIndex) (PairIndex := PairIndex)) : ℝ :=
  (∑ a : SingleIndex, ∑ i : Color, (x.single a i) ^ 2) +
    ∑ a : PairIndex, energy (x.pair a)

theorem universalEnergy_nonneg
    (x : UniversalState (Color := Color)
      (SingleIndex := SingleIndex) (PairIndex := PairIndex)) :
    0 ≤ universalEnergy x := by
  unfold universalEnergy
  apply add_nonneg
  · exact Finset.sum_nonneg (fun a _ha ↦
      Finset.sum_nonneg (fun i _hi ↦ sq_nonneg (x.single a i)))
  · exact Finset.sum_nonneg (fun a _ha ↦ energy_nonneg (x.pair a))

def universalStep (p : Pairing Color)
    (x : UniversalState (Color := Color)
      (SingleIndex := SingleIndex) (PairIndex := PairIndex)) :
    UniversalState (Color := Color)
      (SingleIndex := SingleIndex) (PairIndex := PairIndex) where
  single a := singleAverage p (x.single a)
  pair a := pairAverage p (x.pair a)
  single_sum_zero a := by
    rw [sum_singleAverage, x.single_sum_zero]
  pair_symmetric a i j :=
    pairAverage_symmetric p (x.pair a) (x.pair_symmetric a) i j
  pair_diagonal a i := by simp [pairAverage]
  pair_total_zero a := by
    rw [total_pairAverage p (x.pair a) (x.pair_symmetric a)
      (x.pair_diagonal a), x.pair_total_zero]

/-- The same random pairing contracts the total energy of every member of
the tuple on average. -/
theorem average_universalEnergy_universalStep_le_half
    (heven : Even (Fintype.card Color)) (hcard : 4 ≤ Fintype.card Color)
    (x : UniversalState (Color := Color)
      (SingleIndex := SingleIndex) (PairIndex := PairIndex)) :
    (∑ p : Pairing Color, universalEnergy (universalStep p x)) /
        (Fintype.card (Pairing Color) : ℝ) ≤
      universalEnergy x / 2 := by
  letI : Nonempty (Pairing Color) := nonempty_pairing_of_even_card Color heven
  have hP : (0 : ℝ) < Fintype.card (Pairing Color) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Pairing Color))
  have hsingle :
      (∑ a : SingleIndex,
        ((∑ p : Pairing Color, ∑ i : Color,
            (singleAverage p (x.single a) i) ^ 2) /
          (Fintype.card (Pairing Color) : ℝ))) ≤
      ∑ a : SingleIndex, (∑ i : Color, (x.single a i) ^ 2) / 2 := by
    apply Finset.sum_le_sum
    intro a _ha
    exact average_sum_sq_singleAverage_le_half heven (by omega)
      (x.single a) (x.single_sum_zero a)
  have hpair :
      (∑ a : PairIndex,
        ((∑ p : Pairing Color, energy (pairAverage p (x.pair a))) /
          (Fintype.card (Pairing Color) : ℝ))) ≤
      ∑ a : PairIndex, energy (x.pair a) / 2 := by
    apply Finset.sum_le_sum
    intro a _ha
    exact average_energy_pairAverage_le_half heven hcard
      (x.pair a) (x.pair_total_zero a) (x.pair_symmetric a)
      (x.pair_diagonal a)
  unfold universalEnergy universalStep
  rw [show
      (∑ p : Pairing Color,
        ((∑ a : SingleIndex, ∑ i : Color,
            (singleAverage p (x.single a) i) ^ 2) +
          ∑ a : PairIndex, energy (pairAverage p (x.pair a)))) /
            (Fintype.card (Pairing Color) : ℝ) =
      (∑ a : SingleIndex,
        ((∑ p : Pairing Color, ∑ i : Color,
            (singleAverage p (x.single a) i) ^ 2) /
          (Fintype.card (Pairing Color) : ℝ))) +
      (∑ a : PairIndex,
        ((∑ p : Pairing Color, energy (pairAverage p (x.pair a))) /
          (Fintype.card (Pairing Color) : ℝ))) by
    rw [Finset.sum_add_distrib, add_div]
    congr 1
    · rw [Finset.sum_comm]
      simp only [Finset.sum_div]
    · rw [Finset.sum_comm]
      simp only [Finset.sum_div]]
  calc
    (∑ a : SingleIndex,
        (∑ p : Pairing Color, ∑ i : Color,
          (singleAverage p (x.single a) i) ^ 2) /
            (Fintype.card (Pairing Color) : ℝ)) +
      ∑ a : PairIndex,
        (∑ p : Pairing Color, energy (pairAverage p (x.pair a))) /
          (Fintype.card (Pairing Color) : ℝ) ≤
        (∑ a : SingleIndex, (∑ i : Color, (x.single a i) ^ 2) / 2) +
          ∑ a : PairIndex, energy (x.pair a) / 2 :=
      add_le_add hsingle hpair
    _ = ((∑ a : SingleIndex, ∑ i : Color, (x.single a i) ^ 2) +
          ∑ a : PairIndex, energy (x.pair a)) / 2 := by
      rw [← Finset.sum_div, ← Finset.sum_div]
      ring

/-- A deterministic length-`s` schedule contracts the entire finite tuple by
`2^{-s}`.  The conclusion is universal once `x` is chosen to contain the
centered coordinate bases. -/
theorem exists_universalPairingSchedule
    (heven : Even (Fintype.card Color)) (hcard : 4 ≤ Fintype.card Color)
    (s : ℕ)
    (x : UniversalState (Color := Color)
      (SingleIndex := SingleIndex) (PairIndex := PairIndex)) :
    ∃ schedule : List (Pairing Color),
      schedule.length = s ∧
      universalEnergy
          (applyChoiceList universalStep schedule x) ≤
        (1 / 2 : ℝ) ^ s * universalEnergy x := by
  letI : Nonempty (Pairing Color) := nonempty_pairing_of_even_card Color heven
  exact exists_choiceList_contracts universalEnergy universalStep
    (average_universalEnergy_universalStep_le_half heven hcard) s x

/-! ## Centered coordinate bases -/

/-- Ordered distinct pairs.  Using both orientations avoids choosing an
order on the color type; the reconstruction coefficient is `h a b / 2`. -/
abbrev PairCoordinate (Color : Type*) [DecidableEq Color] :=
  {ab : Color × Color // ab.1 ≠ ab.2}

theorem sum_pairCoordinate_eq_sum_ne (f : Color → Color → ℝ) :
    (∑ ab : PairCoordinate Color, f ab.1.1 ab.1.2) =
      ∑ a : Color, ∑ b : Color, if a ≠ b then f a b else 0 := by
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun ab : Color × Color ↦ ab.1 ≠ ab.2))
    (by intro ab; simp)
    (fun ab : Color × Color ↦ f ab.1 ab.2)]
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]

def singleCenteredBasis (a i : Color) : ℝ :=
  (if i = a then 1 else 0) - 1 / Fintype.card Color

def offDiagonalOne (i j : Color) : ℝ := if i = j then 0 else 1

def pairAtom (ab : PairCoordinate Color) (i j : Color) : ℝ :=
  if (i = ab.1.1 ∧ j = ab.1.2) ∨
      (i = ab.1.2 ∧ j = ab.1.1) then 1 else 0

def pairCenteredBasis (ab : PairCoordinate Color) (i j : Color) : ℝ :=
  pairAtom ab i j -
    (2 / ((Fintype.card Color : ℝ) *
      ((Fintype.card Color : ℝ) - 1))) * offDiagonalOne i j

private theorem sum_pair_indicator (a b : Color) (r : ℝ) :
    (∑ i : Color, ∑ j : Color,
      if i = a ∧ j = b then r else 0) = r := by
  rw [show
      (∑ i : Color, ∑ j : Color,
        if i = a ∧ j = b then r else 0) =
        ∑ i : Color, if i = a then r else 0 by
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hia : i = a
    · subst i
      simp
    · simp [hia]]
  simp

theorem sum_singleCenteredBasis (a : Color)
    (hcard : 1 ≤ Fintype.card Color) :
    ∑ i : Color, singleCenteredBasis a i = 0 := by
  have hcardReal : (1 : ℝ) ≤ (Fintype.card Color : ℝ) := by
    exact_mod_cast hcard
  have hK : (Fintype.card Color : ℝ) ≠ 0 := by nlinarith
  unfold singleCenteredBasis
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem offDiagonalOne_symmetric (i j : Color) :
    offDiagonalOne i j = offDiagonalOne j i := by
  unfold offDiagonalOne
  by_cases hij : i = j
  · subst j
    rfl
  · rw [if_neg hij, if_neg (Ne.symm hij)]

theorem pairAtom_symmetric (ab : PairCoordinate Color) (i j : Color) :
    pairAtom ab i j = pairAtom ab j i := by
  unfold pairAtom
  have hiff :
      ((i = ab.1.1 ∧ j = ab.1.2) ∨
          (i = ab.1.2 ∧ j = ab.1.1)) ↔
        ((j = ab.1.1 ∧ i = ab.1.2) ∨
          (j = ab.1.2 ∧ i = ab.1.1)) := by
    tauto
  by_cases hcase :
      (i = ab.1.1 ∧ j = ab.1.2) ∨
        (i = ab.1.2 ∧ j = ab.1.1)
  · rw [if_pos hcase, if_pos (hiff.mp hcase)]
  · rw [if_neg hcase, if_neg (fun h ↦ hcase (hiff.mpr h))]

theorem pairCenteredBasis_symmetric (ab : PairCoordinate Color) (i j : Color) :
    pairCenteredBasis ab i j = pairCenteredBasis ab j i := by
  unfold pairCenteredBasis
  rw [pairAtom_symmetric, offDiagonalOne_symmetric]

theorem pairCenteredBasis_diagonal (ab : PairCoordinate Color) (i : Color) :
    pairCenteredBasis ab i i = 0 := by
  unfold pairCenteredBasis pairAtom offDiagonalOne
  have hnot : ¬ ((i = ab.1.1 ∧ i = ab.1.2) ∨
      (i = ab.1.2 ∧ i = ab.1.1)) := by
    rintro (⟨hia, hib⟩ | ⟨hib, hia⟩)
    · exact ab.2 (hia.symm.trans hib)
    · exact ab.2 (hia.symm.trans hib)
  rw [if_neg hnot, if_pos rfl]
  ring

theorem total_offDiagonalOne :
    total (offDiagonalOne : Color → Color → ℝ) =
      (Fintype.card Color : ℝ) * ((Fintype.card Color : ℝ) - 1) := by
  unfold total rowSum offDiagonalOne
  rw [show
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else (if i = j then 0 else 1)) =
      ∑ i : Color, ((Fintype.card Color : ℝ) - 1) by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [show
        (∑ j : Color,
          if i = j then 0 else (if i = j then 0 else 1)) =
        ∑ j : Color, if i = j then 0 else (1 : ℝ) by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hij : i = j <;> simp [hij]]
    rw [sum_ne_eq_sum_sub (fun _j : Color ↦ (1 : ℝ)) i]
    simp]
  simp <;> ring

theorem total_pairAtom (ab : PairCoordinate Color) :
    total (pairAtom ab) = 2 := by
  unfold total rowSum pairAtom
  rw [show
      (∑ i : Color, ∑ j : Color,
        if i = j then 0
        else if (i = ab.1.1 ∧ j = ab.1.2) ∨
            (i = ab.1.2 ∧ j = ab.1.1) then 1 else 0) =
      (∑ i : Color, ∑ j : Color,
        ((if i = ab.1.1 ∧ j = ab.1.2 then (1 : ℝ) else 0) +
          if i = ab.1.2 ∧ j = ab.1.1 then (1 : ℝ) else 0)) by
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hfirst : i = ab.1.1 ∧ j = ab.1.2
    · rcases hfirst with ⟨rfl, rfl⟩
      simp [ab.2]
    · by_cases hsecond : i = ab.1.2 ∧ j = ab.1.1
      · rcases hsecond with ⟨rfl, rfl⟩
        simp [Ne.symm ab.2]
      · simp [hfirst, hsecond]]
  simp_rw [Finset.sum_add_distrib]
  rw [sum_pair_indicator, sum_pair_indicator]
  norm_num

theorem total_pairCenteredBasis (ab : PairCoordinate Color)
    (hcard : 2 ≤ Fintype.card Color) :
    total (pairCenteredBasis ab) = 0 := by
  have hcardReal : (2 : ℝ) ≤ (Fintype.card Color : ℝ) := by
    exact_mod_cast hcard
  have hden : (Fintype.card Color : ℝ) *
      ((Fintype.card Color : ℝ) - 1) ≠ 0 := by
    exact ne_of_gt (mul_pos (by linarith) (by linarith))
  have hK1 : (Fintype.card Color : ℝ) - 1 ≠ 0 := by
    linarith
  unfold total rowSum pairCenteredBasis
  rw [show
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else
          pairAtom ab i j -
            2 / ((Fintype.card Color : ℝ) *
              ((Fintype.card Color : ℝ) - 1)) * offDiagonalOne i j) =
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else pairAtom ab i j) -
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else
          2 / ((Fintype.card Color : ℝ) *
            ((Fintype.card Color : ℝ) - 1)) * offDiagonalOne i j) by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hij : i = j <;> simp [hij],
    show
      (∑ i : Color, ∑ j : Color, if i = j then 0 else pairAtom ab i j) =
        total (pairAtom ab) by rfl,
    show
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else
          2 / ((Fintype.card Color : ℝ) *
              ((Fintype.card Color : ℝ) - 1)) * offDiagonalOne i j) =
        2 / ((Fintype.card Color : ℝ) *
              ((Fintype.card Color : ℝ) - 1)) *
          total (offDiagonalOne : Color → Color → ℝ) by
      unfold total rowSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hij : i = j <;> simp [hij],
    total_pairAtom, total_offDiagonalOne]
  field_simp [hden, hK1]
  ring

def centeredBasisState (hcard : 4 ≤ Fintype.card Color) :
    UniversalState (Color := Color) (SingleIndex := Color)
      (PairIndex := PairCoordinate Color) where
  single := singleCenteredBasis
  pair := pairCenteredBasis
  single_sum_zero a := sum_singleCenteredBasis a (by omega)
  pair_symmetric := pairCenteredBasis_symmetric
  pair_diagonal := pairCenteredBasis_diagonal
  pair_total_zero ab := total_pairCenteredBasis ab (by omega)

theorem sum_sq_singleCenteredBasis (hcard : 1 ≤ Fintype.card Color)
    (a : Color) :
    (∑ i : Color, (singleCenteredBasis a i) ^ 2) =
      1 - 1 / Fintype.card Color := by
  have hcardReal : (1 : ℝ) ≤ (Fintype.card Color : ℝ) := by
    exact_mod_cast hcard
  have hK : (Fintype.card Color : ℝ) ≠ 0 := by nlinarith
  let u : ℝ := 1 / Fintype.card Color
  rw [show
      (∑ i : Color, (singleCenteredBasis a i) ^ 2) =
      ∑ i : Color, (u ^ 2 + if i = a then 1 - 2 * u else 0) by
    apply Finset.sum_congr rfl
    intro i _hi
    unfold singleCenteredBasis
    by_cases hia : i = a <;> simp [hia, u] <;> ring]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [u]
  field_simp
  ring

theorem energy_pairCenteredBasis (hcard : 2 ≤ Fintype.card Color)
    (ab : PairCoordinate Color) :
    energy (pairCenteredBasis ab) =
      2 - 4 / ((Fintype.card Color : ℝ) *
        ((Fintype.card Color : ℝ) - 1)) := by
  let N : ℝ := (Fintype.card Color : ℝ) *
    ((Fintype.card Color : ℝ) - 1)
  let u : ℝ := 2 / N
  have hcardReal : (2 : ℝ) ≤ (Fintype.card Color : ℝ) := by
    exact_mod_cast hcard
  have hN : N ≠ 0 := by
    dsimp [N]
    exact ne_of_gt (mul_pos (by linarith) (by linarith))
  unfold energy
  rw [show
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else (pairCenteredBasis ab i j) ^ 2) =
      u ^ 2 * total (offDiagonalOne : Color → Color → ℝ) +
        (1 - 2 * u) * total (pairAtom ab) by
    unfold total rowSum
    calc
      (∑ i : Color, ∑ j : Color,
        if i = j then 0 else (pairCenteredBasis ab i j) ^ 2) =
          ∑ i : Color, ∑ j : Color,
            (u ^ 2 * (if i = j then 0 else offDiagonalOne i j) +
              (1 - 2 * u) * (if i = j then 0 else pairAtom ab i j)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        unfold pairCenteredBasis pairAtom offDiagonalOne
        by_cases hij : i = j
        · simp [hij, ab.2]
        · by_cases hatom :
            (i = ab.1.1 ∧ j = ab.1.2) ∨
              (i = ab.1.2 ∧ j = ab.1.1)
          · simp [hij, hatom, u]
            ring
          · simp [hij, hatom, u]
            ring
      _ = _ := by
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum]]
  rw [total_offDiagonalOne, total_pairAtom]
  simp only [u, N]
  field_simp
  ring

/-- Exact initial Hilbert--Schmidt size of the centered basis tuple. -/
theorem universalEnergy_centeredBasisState
    (hcard : 4 ≤ Fintype.card Color) :
    universalEnergy (centeredBasisState hcard) =
      2 * (Fintype.card Color : ℝ) ^ 2 -
        (Fintype.card Color : ℝ) - 5 := by
  unfold universalEnergy centeredBasisState
  simp_rw [sum_sq_singleCenteredBasis (by omega : 1 ≤ Fintype.card Color)]
  simp_rw [energy_pairCenteredBasis (by omega : 2 ≤ Fintype.card Color)]
  have hcardReal : (4 : ℝ) ≤ (Fintype.card Color : ℝ) := by
    exact_mod_cast hcard
  have hK : (Fintype.card Color : ℝ) ≠ 0 := by nlinarith
  have hK1 : ((Fintype.card Color : ℝ) - 1) ≠ 0 := by nlinarith
  rw [show
      (∑ _a : Color, (1 - 1 / (Fintype.card Color : ℝ))) =
        (Fintype.card Color : ℝ) *
          (1 - 1 / (Fintype.card Color : ℝ)) by
    simp
    ring]
  rw [show
      (∑ _ab : PairCoordinate Color,
        (2 - 4 / ((Fintype.card Color : ℝ) *
          ((Fintype.card Color : ℝ) - 1)))) =
        ((Fintype.card Color : ℝ) *
          ((Fintype.card Color : ℝ) - 1)) *
        (2 - 4 / ((Fintype.card Color : ℝ) *
          ((Fintype.card Color : ℝ) - 1))) by
    change
      (∑ ab : PairCoordinate Color,
        (fun _a _b : Color ↦
          2 - 4 / ((Fintype.card Color : ℝ) *
            ((Fintype.card Color : ℝ) - 1))) ab.1.1 ab.1.2) = _
    rw [show
        (∑ ab : PairCoordinate Color,
          (fun _a _b : Color ↦
            2 - 4 / ((Fintype.card Color : ℝ) *
              ((Fintype.card Color : ℝ) - 1))) ab.1.1 ab.1.2) =
          ∑ a : Color, ∑ b : Color, if a ≠ b then
            2 - 4 / ((Fintype.card Color : ℝ) *
              ((Fintype.card Color : ℝ) - 1)) else 0 by
      exact sum_pairCoordinate_eq_sum_ne
        (f := fun _a _b ↦
          2 - 4 / ((Fintype.card Color : ℝ) *
            ((Fintype.card Color : ℝ) - 1)))]
    calc
      (∑ a : Color, ∑ b : Color,
        if a ≠ b then
          2 - 4 / ((Fintype.card Color : ℝ) *
            ((Fintype.card Color : ℝ) - 1)) else 0) =
        ∑ a : Color,
          ((Fintype.card Color : ℝ) - 1) *
            (2 - 4 / ((Fintype.card Color : ℝ) *
              ((Fintype.card Color : ℝ) - 1))) := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [show
            (∑ b : Color,
              if a ≠ b then
                2 - 4 / ((Fintype.card Color : ℝ) *
                  ((Fintype.card Color : ℝ) - 1)) else 0) =
            (∑ b : Color,
              if a = b then 0 else
                (2 - 4 / ((Fintype.card Color : ℝ) *
                  ((Fintype.card Color : ℝ) - 1)))) by
          apply Finset.sum_congr rfl
          intro b _hb
          by_cases hab : a = b <;> simp [hab]]
        rw [sum_ne_eq_sum_sub]
        simp
        ring
      _ = _ := by simp; ring]
  field_simp
  ring

theorem universalEnergy_centeredBasisState_le_two_sq
    (hcard : 4 ≤ Fintype.card Color) :
    universalEnergy (centeredBasisState hcard) ≤
      2 * (Fintype.card Color : ℝ) ^ 2 := by
  rw [universalEnergy_centeredBasisState hcard]
  have hcardReal : (0 : ℝ) ≤ (Fintype.card Color : ℝ) := by positivity
  linarith

def applySingleSchedule (schedule : List (Pairing Color))
    (h : Color → ℝ) : Color → ℝ :=
  applyChoiceList (fun p g ↦ singleAverage p g) schedule h

def applyPairSchedule (schedule : List (Pairing Color))
    (h : Color → Color → ℝ) : Color → Color → ℝ :=
  applyChoiceList (fun p g ↦ pairAverage p g) schedule h

theorem applyUniversalSchedule_single
    (schedule : List (Pairing Color))
    (x : UniversalState (Color := Color)
      (SingleIndex := SingleIndex) (PairIndex := PairIndex))
    (a : SingleIndex) :
    (applyChoiceList universalStep schedule x).single a =
      applySingleSchedule schedule (x.single a) := by
  induction schedule generalizing x with
  | nil => rfl
  | cons p schedule ih =>
      change
        (applyChoiceList universalStep schedule (universalStep p x)).single a =
          applySingleSchedule schedule ((universalStep p x).single a)
      exact ih (universalStep p x)

theorem applyUniversalSchedule_pair
    (schedule : List (Pairing Color))
    (x : UniversalState (Color := Color)
      (SingleIndex := SingleIndex) (PairIndex := PairIndex))
    (a : PairIndex) :
    (applyChoiceList universalStep schedule x).pair a =
      applyPairSchedule schedule (x.pair a) := by
  induction schedule generalizing x with
  | nil => rfl
  | cons p schedule ih =>
      change
        (applyChoiceList universalStep schedule (universalStep p x)).pair a =
          applyPairSchedule schedule ((universalStep p x).pair a)
      exact ih (universalStep p x)

theorem singleAverage_sum (p : Pairing Color)
    (coeff : SingleIndex → ℝ) (h : SingleIndex → Color → ℝ) (i : Color) :
    singleAverage p (fun c ↦ ∑ a, coeff a * h a c) i =
      ∑ a, coeff a * singleAverage p (h a) i := by
  unfold singleAverage
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

theorem pairAverage_sum (p : Pairing Color)
    (coeff : PairIndex → ℝ) (h : PairIndex → Color → Color → ℝ)
    (i j : Color) :
    pairAverage p (fun c d ↦ ∑ a, coeff a * h a c d) i j =
      ∑ a, coeff a * pairAverage p (h a) i j := by
  unfold pairAverage
  by_cases hij : i = j
  · simp only [if_pos hij, mul_zero, Finset.sum_const_zero]
  · simp only [if_neg hij]
    by_cases hpij : partner Color p i = j
    · simp only [if_pos hpij]
    · simp only [if_neg hpij]
      repeat' rw [← Finset.sum_add_distrib]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _ha
      ring

theorem applySingleSchedule_sum (schedule : List (Pairing Color))
    (coeff : SingleIndex → ℝ) (h : SingleIndex → Color → ℝ) (i : Color) :
    applySingleSchedule schedule (fun c ↦ ∑ a, coeff a * h a c) i =
      ∑ a, coeff a * applySingleSchedule schedule (h a) i := by
  induction schedule generalizing h with
  | nil => rfl
  | cons p schedule ih =>
      change
        applySingleSchedule schedule
            (singleAverage p (fun c ↦ ∑ a, coeff a * h a c)) i =
          ∑ a, coeff a *
            applySingleSchedule schedule (singleAverage p (h a)) i
      have hstep :
          singleAverage p (fun c ↦ ∑ a, coeff a * h a c) =
            fun c ↦ ∑ a, coeff a * singleAverage p (h a) c := by
        funext c
        exact singleAverage_sum p coeff h c
      calc
        applySingleSchedule schedule
            (singleAverage p (fun c ↦ ∑ a, coeff a * h a c)) i =
          applySingleSchedule schedule
            (fun c ↦ ∑ a, coeff a * singleAverage p (h a) c) i := by
              exact congrArg (fun g ↦ applySingleSchedule schedule g i) hstep
        _ = _ := ih (fun a ↦ singleAverage p (h a))

theorem applyPairSchedule_sum (schedule : List (Pairing Color))
    (coeff : PairIndex → ℝ) (h : PairIndex → Color → Color → ℝ)
    (i j : Color) :
    applyPairSchedule schedule (fun c d ↦ ∑ a, coeff a * h a c d) i j =
      ∑ a, coeff a * applyPairSchedule schedule (h a) i j := by
  induction schedule generalizing h with
  | nil => rfl
  | cons p schedule ih =>
      change
        applyPairSchedule schedule
            (pairAverage p (fun c d ↦ ∑ a, coeff a * h a c d)) i j =
          ∑ a, coeff a *
            applyPairSchedule schedule (pairAverage p (h a)) i j
      have hstep :
          pairAverage p (fun c d ↦ ∑ a, coeff a * h a c d) =
            fun c d ↦ ∑ a, coeff a * pairAverage p (h a) c d := by
        funext c d
        exact pairAverage_sum p coeff h c d
      calc
        applyPairSchedule schedule
            (pairAverage p (fun c d ↦ ∑ a, coeff a * h a c d)) i j =
          applyPairSchedule schedule
            (fun c d ↦ ∑ a, coeff a * pairAverage p (h a) c d) i j := by
              exact congrArg (fun g ↦ applyPairSchedule schedule g i j) hstep
        _ = _ := ih (fun a ↦ pairAverage p (h a))

theorem single_eq_sum_centeredBasis (h : Color → ℝ)
    (hsum : ∑ i, h i = 0) (i : Color) :
    h i = ∑ a : Color, h a * singleCenteredBasis a i := by
  unfold singleCenteredBasis
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [show (∑ a : Color, h a * (if i = a then 1 else 0)) = h i by simp,
    ← Finset.sum_mul, hsum]
  ring

theorem pair_eq_sum_centeredBasis (h : Color → Color → ℝ)
    (hsym : ∀ i j, h i j = h j i) (hdiag : ∀ i, h i i = 0)
    (htotal : total h = 0) (i j : Color) :
    h i j = ∑ ab : PairCoordinate Color,
      (h ab.1.1 ab.1.2 / 2) * pairCenteredBasis ab i j := by
  by_cases hij : i = j
  · subst j
    simp [hdiag, pairCenteredBasis_diagonal]
  have hcoeff :
      (∑ ab : PairCoordinate Color, h ab.1.1 ab.1.2 / 2) = 0 := by
    rw [← Finset.sum_div]
    have hsubtype :
        (∑ ab : PairCoordinate Color, h ab.1.1 ab.1.2) = total h := by
      unfold total rowSum
      rw [sum_pairCoordinate_eq_sum_ne]
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases hab : a = b <;> simp [hab, hdiag]
    rw [hsubtype, htotal]
    simp
  unfold pairCenteredBasis
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [show
      (∑ ab : PairCoordinate Color,
        h ab.1.1 ab.1.2 / 2 * pairAtom ab i j) =
        h i j by
    rw [show
        (∑ ab : PairCoordinate Color,
          h ab.1.1 ab.1.2 / 2 * pairAtom ab i j) =
          h i j / 2 + h j i / 2 by
      unfold pairAtom
      rw [show
          (∑ ab : PairCoordinate Color,
            h ab.1.1 ab.1.2 / 2 *
              (if (i = ab.1.1 ∧ j = ab.1.2) ∨
                (i = ab.1.2 ∧ j = ab.1.1) then 1 else 0)) =
            ∑ a : Color, ∑ b : Color, if a ≠ b then
              h a b / 2 *
                (if (i = a ∧ j = b) ∨ (i = b ∧ j = a) then 1 else 0)
              else 0 by
        exact sum_pairCoordinate_eq_sum_ne
          (f := fun a b ↦ h a b / 2 *
            (if (i = a ∧ j = b) ∨ (i = b ∧ j = a) then 1 else 0))]
      rw [show
          (∑ a : Color, ∑ b : Color, if a ≠ b then
            h a b / 2 *
              (if (i = a ∧ j = b) ∨ (i = b ∧ j = a) then 1 else 0)
            else 0) =
            (∑ a : Color, ∑ b : Color,
              ((if a = i ∧ b = j then h i j / 2 else 0) +
                if a = j ∧ b = i then h j i / 2 else 0)) by
        apply Finset.sum_congr rfl
        intro a _ha
        apply Finset.sum_congr rfl
        intro b _hb
        by_cases hfirst : a = i ∧ b = j
        · rcases hfirst with ⟨rfl, rfl⟩
          simp [hij]
        · by_cases hsecond : a = j ∧ b = i
          · rcases hsecond with ⟨rfl, rfl⟩
            simp [Ne.symm hij]
          · have hfirst' : ¬ (i = a ∧ j = b) := by
              simpa [eq_comm] using hfirst
            have hsecond' : ¬ (i = b ∧ j = a) := by
              rintro ⟨hib, hja⟩
              exact hsecond ⟨hja.symm, hib.symm⟩
            simp [hfirst, hsecond, hfirst', hsecond']]
      simp_rw [Finset.sum_add_distrib]
      rw [sum_pair_indicator, sum_pair_indicator]]
    rw [hsym j i]
    ring,
    ← Finset.sum_mul, hcoeff]
  ring

/-- Universal schedule with an explicit Hilbert--Schmidt error certificate.
The single and pair coordinate images in the conclusion are controlled by
one common nonnegative number. -/
theorem exists_centeredBasisSchedule
    (heven : Even (Fintype.card Color)) (hcard : 4 ≤ Fintype.card Color)
    (s : ℕ) :
    ∃ schedule : List (Pairing Color),
      schedule.length = s ∧
      universalEnergy
          (applyChoiceList universalStep schedule
            (centeredBasisState hcard)) ≤
        (1 / 2 : ℝ) ^ s * universalEnergy (centeredBasisState hcard) :=
  exists_universalPairingSchedule heven hcard s (centeredBasisState hcard)

theorem sum_mul_sq_le (x y : SingleIndex → ℝ) :
    (∑ a, x a * y a) ^ 2 ≤
      (∑ a, (x a) ^ 2) * ∑ a, (y a) ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    (s := Finset.univ)
    (r := fun a ↦ x a * y a)
    (f := fun a ↦ (x a) ^ 2)
    (g := fun a ↦ (y a) ^ 2)
  · intro a _ha
    positivity
  · intro a _ha
    positivity
  · intro a _ha
    ring

theorem applySingleSchedule_sq_le_universalEnergy
    (hcard : 4 ≤ Fintype.card Color)
    (schedule : List (Pairing Color)) (h : Color → ℝ)
    (hsum : ∑ i, h i = 0) (i : Color) :
    (applySingleSchedule schedule h i) ^ 2 ≤
      (∑ a : Color, (h a) ^ 2) *
        universalEnergy
          (applyChoiceList universalStep schedule
            (centeredBasisState hcard)) := by
  have hreconstruct :
      applySingleSchedule schedule h i =
        ∑ a : Color, h a *
          applySingleSchedule schedule (singleCenteredBasis a) i := by
    have hdecomp : h = fun c ↦
        ∑ a : Color, h a * singleCenteredBasis a c := by
      funext c
      exact single_eq_sum_centeredBasis h hsum c
    calc
      applySingleSchedule schedule h i =
          applySingleSchedule schedule
            (fun c ↦ ∑ a : Color, h a * singleCenteredBasis a c) i := by
        exact congrArg (fun g ↦ applySingleSchedule schedule g i) hdecomp
      _ = _ := applySingleSchedule_sum schedule h singleCenteredBasis i
  rw [hreconstruct]
  calc
    (∑ a : Color, h a *
        applySingleSchedule schedule (singleCenteredBasis a) i) ^ 2 ≤
      (∑ a : Color, (h a) ^ 2) *
        ∑ a : Color,
          (applySingleSchedule schedule (singleCenteredBasis a) i) ^ 2 :=
      sum_mul_sq_le h
        (fun a ↦ applySingleSchedule schedule (singleCenteredBasis a) i)
    _ ≤ (∑ a : Color, (h a) ^ 2) *
        universalEnergy
          (applyChoiceList universalStep schedule
            (centeredBasisState hcard)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold universalEnergy
      have hcoordinate :
          (∑ a : Color,
            (applySingleSchedule schedule (singleCenteredBasis a) i) ^ 2) ≤
          ∑ a : Color, ∑ j : Color,
            ((applyChoiceList universalStep schedule
              (centeredBasisState hcard)).single a j) ^ 2 := by
        apply Finset.sum_le_sum
        intro a _ha
        rw [applyUniversalSchedule_single]
        exact Finset.single_le_sum (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i)
      exact hcoordinate.trans (le_add_of_nonneg_right
        (Finset.sum_nonneg (fun a _ha ↦ energy_nonneg _)))

theorem applyPairSchedule_sq_le_universalEnergy
    (hcard : 4 ≤ Fintype.card Color)
    (schedule : List (Pairing Color)) (h : Color → Color → ℝ)
    (hsym : ∀ i j, h i j = h j i) (hdiag : ∀ i, h i i = 0)
    (htotal : total h = 0) (i j : Color) :
    (applyPairSchedule schedule h i j) ^ 2 ≤
      (energy h / 4) *
        universalEnergy
          (applyChoiceList universalStep schedule
            (centeredBasisState hcard)) := by
  have hreconstruct :
      applyPairSchedule schedule h i j =
        ∑ ab : PairCoordinate Color, (h ab.1.1 ab.1.2 / 2) *
          applyPairSchedule schedule (pairCenteredBasis ab) i j := by
    have hdecomp : h = fun c d ↦
        ∑ ab : PairCoordinate Color,
          (h ab.1.1 ab.1.2 / 2) * pairCenteredBasis ab c d := by
      funext c d
      exact pair_eq_sum_centeredBasis h hsym hdiag htotal c d
    calc
      applyPairSchedule schedule h i j =
          applyPairSchedule schedule
            (fun c d ↦ ∑ ab : PairCoordinate Color,
              (h ab.1.1 ab.1.2 / 2) * pairCenteredBasis ab c d) i j := by
        exact congrArg (fun g ↦ applyPairSchedule schedule g i j) hdecomp
      _ = _ := applyPairSchedule_sum schedule
        (fun ab : PairCoordinate Color ↦ h ab.1.1 ab.1.2 / 2)
        pairCenteredBasis i j
  rw [hreconstruct]
  calc
    (∑ ab : PairCoordinate Color, (h ab.1.1 ab.1.2 / 2) *
        applyPairSchedule schedule (pairCenteredBasis ab) i j) ^ 2 ≤
      (∑ ab : PairCoordinate Color, (h ab.1.1 ab.1.2 / 2) ^ 2) *
        ∑ ab : PairCoordinate Color,
          (applyPairSchedule schedule (pairCenteredBasis ab) i j) ^ 2 :=
      sum_mul_sq_le
        (fun ab : PairCoordinate Color ↦ h ab.1.1 ab.1.2 / 2)
        (fun ab ↦ applyPairSchedule schedule (pairCenteredBasis ab) i j)
    _ = (energy h / 4) *
        ∑ ab : PairCoordinate Color,
          (applyPairSchedule schedule (pairCenteredBasis ab) i j) ^ 2 := by
      congr 1
      rw [show
          (∑ ab : PairCoordinate Color,
            (h ab.1.1 ab.1.2 / 2) ^ 2) =
            energy h / 4 by
        have hsubtype :
            (∑ ab : PairCoordinate Color,
              (h ab.1.1 ab.1.2) ^ 2) = energy h := by
          unfold energy
          rw [show
              (∑ ab : PairCoordinate Color,
                (h ab.1.1 ab.1.2) ^ 2) =
                ∑ a : Color, ∑ b : Color,
                  if a ≠ b then (h a b) ^ 2 else 0 by
            exact sum_pairCoordinate_eq_sum_ne
              (f := fun a b ↦ (h a b) ^ 2)]
          apply Finset.sum_congr rfl
          intro a _ha
          apply Finset.sum_congr rfl
          intro b _hb
          by_cases hab : a = b <;> simp [hab]
        calc
          (∑ ab : PairCoordinate Color,
              (h ab.1.1 ab.1.2 / 2) ^ 2) =
              (∑ ab : PairCoordinate Color,
                (h ab.1.1 ab.1.2) ^ 2) / 4 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro ab _hab
            ring
          _ = energy h / 4 := by rw [hsubtype]]
    _ ≤ (energy h / 4) *
        universalEnergy
          (applyChoiceList universalStep schedule
            (centeredBasisState hcard)) := by
      apply mul_le_mul_of_nonneg_left _
      · exact div_nonneg (energy_nonneg h) (by norm_num)
      unfold universalEnergy
      have hcoordinate :
          (∑ ab : PairCoordinate Color,
            (applyPairSchedule schedule (pairCenteredBasis ab) i j) ^ 2) ≤
          ∑ ab : PairCoordinate Color,
            energy ((applyChoiceList universalStep schedule
              (centeredBasisState hcard)).pair ab) := by
        apply Finset.sum_le_sum
        intro ab _hab
        change
          (applyPairSchedule schedule
            ((centeredBasisState hcard).pair ab) i j) ^ 2 ≤
          energy ((applyChoiceList universalStep schedule
            (centeredBasisState hcard)).pair ab)
        rw [← applyUniversalSchedule_pair schedule
          (centeredBasisState hcard) ab]
        let y := applyChoiceList universalStep schedule
          (centeredBasisState hcard)
        by_cases hij : i = j
        · subst j
          rw [y.pair_diagonal ab i]
          simpa [y] using energy_nonneg (y.pair ab)
        · unfold energy
          calc
            (y.pair ab i j) ^ 2 =
                (if i = j then 0 else (y.pair ab i j) ^ 2) := by simp [hij]
            _ ≤ ∑ j' : Color,
                if i = j' then 0 else (y.pair ab i j') ^ 2 :=
              Finset.single_le_sum (s := Finset.univ)
                (f := fun j' : Color ↦
                  if i = j' then (0 : ℝ) else (y.pair ab i j') ^ 2)
                (fun j' _hj' ↦ by
                  change 0 ≤ if i = j' then (0 : ℝ) else
                    (y.pair ab i j') ^ 2
                  by_cases hij' : i = j'
                  · simp [hij']
                  · simpa [hij'] using sq_nonneg (y.pair ab i j'))
                (Finset.mem_univ j)
            _ ≤ ∑ i' : Color, ∑ j' : Color,
                if i' = j' then 0 else (y.pair ab i' j') ^ 2 :=
              Finset.single_le_sum (s := Finset.univ)
                (f := fun i' : Color ↦ ∑ j' : Color,
                  if i' = j' then (0 : ℝ) else (y.pair ab i' j') ^ 2)
                (fun i' _hi' ↦
                  Finset.sum_nonneg (fun j' _hj' ↦ by
                    by_cases hi'j' : i' = j'
                    · simp [hi'j']
                    · simpa [hi'j'] using sq_nonneg (y.pair ab i' j')))
                (Finset.mem_univ i)
      exact hcoordinate.trans (le_add_of_nonneg_left
        (Finset.sum_nonneg (fun a _ha ↦
          Finset.sum_nonneg (fun c _hc ↦ sq_nonneg _))))

/-- One length-`s` pairing schedule has an operator certificate valid for
every later graph vertex state.  The only dimension loss is the explicit
Hilbert--Schmidt energy of the centered coordinate bases. -/
theorem exists_universalOperatorSchedule
    (heven : Even (Fintype.card Color)) (hcard : 4 ≤ Fintype.card Color)
    (s : ℕ) :
    ∃ schedule : List (Pairing Color),
      schedule.length = s ∧
      (∀ (h : Color → ℝ), (∑ i, h i = 0) → ∀ i,
        (applySingleSchedule schedule h i) ^ 2 ≤
          (∑ a, (h a) ^ 2) *
            ((1 / 2 : ℝ) ^ s *
              universalEnergy (centeredBasisState hcard))) ∧
      ∀ (h : Color → Color → ℝ),
        (∀ i j, h i j = h j i) → (∀ i, h i i = 0) → total h = 0 →
        ∀ i j,
          (applyPairSchedule schedule h i j) ^ 2 ≤
            (energy h / 4) *
              ((1 / 2 : ℝ) ^ s *
                universalEnergy (centeredBasisState hcard)) := by
  rcases exists_centeredBasisSchedule heven hcard s with
    ⟨schedule, hlength, henergy⟩
  refine ⟨schedule, hlength, ?_, ?_⟩
  · intro h hsum i
    exact (applySingleSchedule_sq_le_universalEnergy
      hcard schedule h hsum i).trans
      (mul_le_mul_of_nonneg_left henergy (by positivity))
  · intro h hsym hdiag htotal i j
    exact (applyPairSchedule_sq_le_universalEnergy
      hcard schedule h hsym hdiag htotal i j).trans
      (mul_le_mul_of_nonneg_left henergy (by
        exact div_nonneg (energy_nonneg h) (by norm_num)))

/-- Polynomial-dimension form of the universal certificate.  The common
operator loss is at most `2 * K^2 * 2^{-s}`. -/
theorem exists_universalOperatorSchedule_two_sq
    (heven : Even (Fintype.card Color)) (hcard : 4 ≤ Fintype.card Color)
    (s : ℕ) :
    ∃ schedule : List (Pairing Color),
      schedule.length = s ∧
      (∀ (h : Color → ℝ), (∑ i, h i = 0) → ∀ i,
        (applySingleSchedule schedule h i) ^ 2 ≤
          (∑ a, (h a) ^ 2) *
            ((1 / 2 : ℝ) ^ s *
              (2 * (Fintype.card Color : ℝ) ^ 2))) ∧
      ∀ (h : Color → Color → ℝ),
        (∀ i j, h i j = h j i) → (∀ i, h i i = 0) → total h = 0 →
        ∀ i j,
          (applyPairSchedule schedule h i j) ^ 2 ≤
            (energy h / 4) *
              ((1 / 2 : ℝ) ^ s *
                (2 * (Fintype.card Color : ℝ) ^ 2)) := by
  rcases exists_universalOperatorSchedule heven hcard s with
    ⟨schedule, hlength, hsingle, hpair⟩
  refine ⟨schedule, hlength, ?_, ?_⟩
  · intro h hsum i
    exact (hsingle h hsum i).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (universalEnergy_centeredBasisState_le_two_sq hcard)
          (by positivity)) (by positivity))
  · intro h hsym hdiag htotal i j
    exact (hpair h hsym hdiag htotal i j).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (universalEnergy_centeredBasisState_le_two_sq hcard)
          (by positivity))
        (div_nonneg (energy_nonneg h) (by norm_num)))

end

end WeightedEdgeColoring.FiniteColorPairingUniversalSchedule
