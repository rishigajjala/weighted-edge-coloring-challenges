import WeightedEdgeColoring.FiniteColorPairingUniversalSchedule

/-!
# Robustness of a universal pairing schedule

The component-coin selector realizes each ideal pairing stage with a uniform
coordinate error.  Pair averages are contractions in the sup norm, so these
errors add only linearly with the number of stages.  In the graph application
the one-color error is `delta1` and the sequential two-block construction
gives pair-coordinate error `2 * delta2` per stage.
-/

namespace WeightedEdgeColoring.FiniteColorPairingScheduleRobust

open WeightedEdgeColoring.FiniteColorPairing
open WeightedEdgeColoring.FiniteColorPairingOperators
open WeightedEdgeColoring.FiniteColorPairingUniversalSchedule

noncomputable section

variable {Color : Type*} [Fintype Color] [DecidableEq Color]

omit [Fintype Color] [DecidableEq Color] in
theorem singleAverage_sup_nonexpansive (p : Pairing Color)
    {x y : Color → ℝ} {eta : ℝ}
    (hxy : ∀ i, |x i - y i| ≤ eta) (i : Color) :
    |singleAverage p x i - singleAverage p y i| ≤ eta := by
  unfold singleAverage
  rw [show
      (x i + x (partner Color p i)) / 2 -
        (y i + y (partner Color p i)) / 2 =
      ((x i - y i) +
        (x (partner Color p i) - y (partner Color p i))) / 2 by ring]
  calc
    |((x i - y i) +
        (x (partner Color p i) - y (partner Color p i))) / 2| ≤
      (|x i - y i| +
        |x (partner Color p i) - y (partner Color p i)|) / 2 := by
        rw [abs_div]
        norm_num
        exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    _ ≤ eta := by linarith [hxy i, hxy (partner Color p i)]

omit [Fintype Color] in
theorem pairAverage_sup_nonexpansive (p : Pairing Color)
    {x y : Color → Color → ℝ} {eta : ℝ} (heta : 0 ≤ eta)
    (hxy : ∀ i j, |x i j - y i j| ≤ eta) (i j : Color) :
    |pairAverage p x i j - pairAverage p y i j| ≤ eta := by
  by_cases hij : i = j
  · simp [pairAverage, hij, heta]
  by_cases hpij : partner Color p i = j
  · simp only [pairAverage, hij, hpij, if_false, if_true]
    exact hxy i j
  simp only [pairAverage, hij, hpij, if_false]
  rw [show
      (x i j + x (partner Color p i) j +
          x i (partner Color p j) +
          x (partner Color p i) (partner Color p j)) / 4 -
        (y i j + y (partner Color p i) j +
          y i (partner Color p j) +
          y (partner Color p i) (partner Color p j)) / 4 =
      ((x i j - y i j) +
        (x (partner Color p i) j - y (partner Color p i) j) +
        (x i (partner Color p j) - y i (partner Color p j)) +
        (x (partner Color p i) (partner Color p j) -
          y (partner Color p i) (partner Color p j))) / 4 by ring]
  calc
    |_ / 4| ≤
      (|x i j - y i j| +
        |x (partner Color p i) j - y (partner Color p i) j| +
        |x i (partner Color p j) - y i (partner Color p j)| +
        |x (partner Color p i) (partner Color p j) -
          y (partner Color p i) (partner Color p j)|) / 4 := by
      rw [abs_div]
      norm_num
      apply div_le_div_of_nonneg_right _ (by norm_num)
      linarith [abs_add_le (x i j - y i j)
          (x (partner Color p i) j - y (partner Color p i) j),
        abs_add_le
          ((x i j - y i j) +
            (x (partner Color p i) j - y (partner Color p i) j))
          (x i (partner Color p j) - y i (partner Color p j)),
        abs_add_le
          ((x i j - y i j) +
            (x (partner Color p i) j - y (partner Color p i) j) +
            (x i (partner Color p j) - y i (partner Color p j)))
          (x (partner Color p i) (partner Color p j) -
            y (partner Color p i) (partner Color p j))]
    _ ≤ eta := by
      linarith [hxy i j, hxy (partner Color p i) j,
        hxy i (partner Color p j),
        hxy (partner Color p i) (partner Color p j)]

omit [Fintype Color] [DecidableEq Color] in
theorem applySingleSchedule_sup_nonexpansive
    (schedule : List (Pairing Color)) {x y : Color → ℝ} {eta : ℝ}
    (hxy : ∀ i, |x i - y i| ≤ eta) (i : Color) :
    |applySingleSchedule schedule x i - applySingleSchedule schedule y i| ≤ eta := by
  induction schedule generalizing x y with
  | nil => exact hxy i
  | cons p schedule ih =>
      exact ih (singleAverage_sup_nonexpansive p hxy)

omit [Fintype Color] in
theorem applyPairSchedule_sup_nonexpansive
    (schedule : List (Pairing Color)) {x y : Color → Color → ℝ} {eta : ℝ}
    (heta : 0 ≤ eta) (hxy : ∀ i j, |x i j - y i j| ≤ eta)
    (i j : Color) :
    |applyPairSchedule schedule x i j - applyPairSchedule schedule y i j| ≤ eta := by
  induction schedule generalizing x y with
  | nil => exact hxy i j
  | cons p schedule ih =>
      exact ih (pairAverage_sup_nonexpansive p heta hxy)

/-- An approximate one-color orbit of a pairing schedule. -/
inductive SingleApproxOrbit (eta : ℝ) :
    List (Pairing Color) → (Color → ℝ) → (Color → ℝ) → Prop
  | nil (x) : SingleApproxOrbit eta [] x x
  | cons (p) (schedule) (x next final)
      (hstep : ∀ i, |next i - singleAverage p x i| ≤ eta)
      (htail : SingleApproxOrbit eta schedule next final) :
      SingleApproxOrbit eta (p :: schedule) x final

/-- An approximate pair-array orbit of a pairing schedule. -/
inductive PairApproxOrbit (eta : ℝ) :
    List (Pairing Color) →
      (Color → Color → ℝ) → (Color → Color → ℝ) → Prop
  | nil (x) : PairApproxOrbit eta [] x x
  | cons (p) (schedule) (x next final)
      (hstep : ∀ i j, |next i j - pairAverage p x i j| ≤ eta)
      (htail : PairApproxOrbit eta schedule next final) :
      PairApproxOrbit eta (p :: schedule) x final

omit [Fintype Color] [DecidableEq Color] in
theorem SingleApproxOrbit.error_le_length_mul
    {eta : ℝ} {schedule : List (Pairing Color)}
    {x final : Color → ℝ} (horbit : SingleApproxOrbit eta schedule x final)
    (i : Color) :
    |final i - applySingleSchedule schedule x i| ≤ schedule.length * eta := by
  induction horbit with
  | nil x =>
      simp [applySingleSchedule,
        WeightedEdgeColoring.WeightedMomentPairingContraction.applyChoiceList]
  | cons p schedule x next final hstep htail ih =>
      have hprop := applySingleSchedule_sup_nonexpansive schedule hstep i
      calc
        |final i - applySingleSchedule (p :: schedule) x i| ≤
            |final i - applySingleSchedule schedule next i| +
              |applySingleSchedule schedule next i -
                applySingleSchedule schedule (singleAverage p x) i| := by
          simpa [applySingleSchedule] using
            (abs_sub_le (final i)
              (applySingleSchedule schedule next i)
              (applySingleSchedule schedule (singleAverage p x) i))
        _ ≤ schedule.length * eta + eta := add_le_add ih hprop
        _ = (p :: schedule).length * eta := by simp; ring

omit [Fintype Color] in
theorem PairApproxOrbit.error_le_length_mul
    {eta : ℝ} (heta : 0 ≤ eta) {schedule : List (Pairing Color)}
    {x final : Color → Color → ℝ}
    (horbit : PairApproxOrbit eta schedule x final) (i j : Color) :
    |final i j - applyPairSchedule schedule x i j| ≤
      schedule.length * eta := by
  induction horbit with
  | nil x =>
      simp [applyPairSchedule,
        WeightedEdgeColoring.WeightedMomentPairingContraction.applyChoiceList]
  | cons p schedule x next final hstep htail ih =>
      have hprop := applyPairSchedule_sup_nonexpansive schedule heta hstep i j
      calc
        |final i j - applyPairSchedule (p :: schedule) x i j| ≤
            |final i j - applyPairSchedule schedule next i j| +
              |applyPairSchedule schedule next i j -
                applyPairSchedule schedule (pairAverage p x) i j| := by
          simpa [applyPairSchedule] using
            (abs_sub_le (final i j)
              (applyPairSchedule schedule next i j)
              (applyPairSchedule schedule (pairAverage p x) i j))
        _ ≤ schedule.length * eta + eta := add_le_add ih hprop
        _ = (p :: schedule).length * eta := by simp; ring

omit [Fintype Color] in
/-- The sequential-pair selector supplies `2 * delta2` error per complete
pairing stage, hence at most `2*s*delta2` after `s` stages. -/
theorem PairApproxOrbit.error_le_two_mul_length_mul
    {delta2 : ℝ} (hdelta2 : 0 ≤ delta2)
    {schedule : List (Pairing Color)}
    {x final : Color → Color → ℝ}
    (horbit : PairApproxOrbit (2 * delta2) schedule x final) (i j : Color) :
    |final i j - applyPairSchedule schedule x i j| ≤
      2 * schedule.length * delta2 := by
  have h := horbit.error_le_length_mul (mul_nonneg (by norm_num) hdelta2) i j
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

end

end WeightedEdgeColoring.FiniteColorPairingScheduleRobust
