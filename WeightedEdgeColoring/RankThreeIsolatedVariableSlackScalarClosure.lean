import WeightedEdgeColoring.RankThreeIsolatedVariableSlackRound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Closed scalar choices for the variable-slack isolated round

The earlier non-isolated round used `4 log (d+1)` as its event exponent.
That exponent does not pay the quartic lower-row incidence budget after
passing to the raw-sample-then-isolate construction.  Here we use

`z(d) = 8 log (d+1)`

and choose the quadratic-moment order in base two.  The definition of the
moment order is deliberately exact: it makes the comparison between
`2*(1/2)^k` and `exp(-z)` a one-line ceiling argument and avoids any decimal
estimate for `log 2`.
-/

namespace WeightedEdgeColoring

open SharpFixedSlackNumeric

/-- The row exponent used by the isolated variable-slack round. -/
noncomputable def isolatedVariableZ (d : ℕ) : ℝ :=
  8 * Real.log ((d : ℝ) + 1)

/-- The least base-two moment which pays the row weight `exp(-z)`. -/
noncomputable def isolatedVariableMoment (d : ℕ) : ℕ :=
  Nat.ceil ((isolatedVariableZ d + Real.log 2) / Real.log 2)

/-- A real upper envelope for the ceiling in `isolatedVariableMoment`. -/
noncomputable def isolatedVariableMomentUpper (d : ℕ) : ℝ :=
  (isolatedVariableZ d + Real.log 2) / Real.log 2 + 1

theorem isolatedVariableZ_pos (d : ℕ) (hd : 0 < d) :
    0 < isolatedVariableZ d := by
  unfold isolatedVariableZ
  have hx : (1 : ℝ) < (d : ℝ) + 1 := by
    exact_mod_cast Nat.succ_lt_succ hd
  exact mul_pos (by norm_num) (Real.log_pos hx)

theorem isolatedVariableMoment_pos (d : ℕ) (hd : 0 < d) :
    0 < isolatedVariableMoment d := by
  apply Nat.ceil_pos.mpr
  have hz := isolatedVariableZ_pos d hd
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem isolatedVariableMoment_cast_le (d : ℕ) (hd : 0 < d) :
    (isolatedVariableMoment d : ℝ) ≤ isolatedVariableMomentUpper d := by
  unfold isolatedVariableMoment isolatedVariableMomentUpper
  have hz := isolatedVariableZ_pos d hd
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem isolatedVariableMoment_threshold_le (d : ℕ) :
    (isolatedVariableZ d + Real.log 2) / Real.log 2 ≤
      isolatedVariableMoment d := by
  unfold isolatedVariableMoment
  exact Nat.le_ceil _

/-- The exact base-two moment pays every collision and isolation-loss event. -/
theorem isolatedVariable_collisionWeight_le (d : ℕ) :
    collisionWeight (isolatedVariableMoment d) ≤
      exponentialRowWeight (isolatedVariableZ d) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hbase1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hpow := Real.rpow_le_rpow_of_exponent_ge hbase0 hbase1
    (isolatedVariableMoment_threshold_le d)
  rw [Real.rpow_natCast] at hpow
  calc
    collisionWeight (isolatedVariableMoment d) =
        2 * (1 / 2 : ℝ) ^ isolatedVariableMoment d := rfl
    _ ≤ 2 * (1 / 2 : ℝ) ^
          ((isolatedVariableZ d + Real.log 2) / Real.log 2) := by
      gcongr
    _ = exponentialRowWeight (isolatedVariableZ d) := by
      rw [Real.rpow_def_of_pos hbase0]
      rw [show Real.log (1 / 2 : ℝ) = -Real.log 2 by
        rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
          (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
        ring]
      unfold exponentialRowWeight
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [← Real.exp_add]
      congr 1
      rw [Real.log_exp]
      field_simp [hlog2.ne']
      ring

/-- The real moment envelope is nonnegative. -/
theorem isolatedVariableMomentUpper_nonneg (d : ℕ) :
    0 ≤ isolatedVariableMomentUpper d := by
  unfold isolatedVariableMomentUpper isolatedVariableZ
  have hlogd : 0 ≤ Real.log ((d : ℝ) + 1) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-! ## The quartic Harris products -/

/-- The corrected row weight is exactly an inverse eighth power. -/
theorem isolatedVariable_exponentialRowWeight_eq (d : ℕ) :
    exponentialRowWeight (isolatedVariableZ d) =
      1 / (((d : ℝ) + 1) ^ 8) := by
  have hx : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  unfold exponentialRowWeight isolatedVariableZ
  rw [show -(8 * Real.log ((d : ℝ) + 1)) =
      (8 : ℕ) * (-Real.log ((d : ℝ) + 1)) by norm_num]
  rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log hx]
  simp [div_eq_mul_inv]

/-- Any quartic incidence budget with coefficient at most `150` is paid by
the inverse-eighth-power row weight once `d ≥ 5`. -/
theorem isolatedVariable_product_of_budget
    (d budget : ℕ) (hd : 5 ≤ d)
    (hbudget : (budget : ℝ) ≤ 150 * (d : ℝ) ^ 4) :
    exponentialRowWeight (isolatedVariableZ d) * budget ≤ 1 / 2 := by
  rw [isolatedVariable_exponentialRowWeight_eq]
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hpow4 : (625 : ℝ) ≤ (d : ℝ) ^ 4 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hdR 4
    norm_num at hp ⊢
    exact hp
  have hself : 300 * (d : ℝ) ^ 4 ≤ (d : ℝ) ^ 8 := by
    calc
      300 * (d : ℝ) ^ 4 ≤ (d : ℝ) ^ 4 * (d : ℝ) ^ 4 := by
        gcongr
        linarith
      _ = (d : ℝ) ^ 8 := by ring
  have hden : (d : ℝ) ^ 8 ≤ ((d : ℝ) + 1) ^ 8 := by
    exact pow_le_pow_left₀ hd0 (by linarith) 8
  have hdenpos : 0 < ((d : ℝ) + 1) ^ 8 := by positivity
  calc
    1 / (((d : ℝ) + 1) ^ 8) * (budget : ℝ) ≤
        1 / (((d : ℝ) + 1) ^ 8) *
          (150 * (d : ℝ) ^ 4) := by gcongr
    _ ≤ 1 / 2 := by
      rw [one_div, inv_mul_eq_div]
      apply (div_le_iff₀ hdenpos).2
      nlinarith [hself.trans hden]

theorem isolatedVariable_rowWeight_le_half (d : ℕ) (hd : 1 ≤ d) :
    exponentialRowWeight (isolatedVariableZ d) ≤ 1 / 2 := by
  rw [isolatedVariable_exponentialRowWeight_eq]
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (2 : ℝ) ≤ ((d : ℝ) + 1) ^ 8 := by
    have hbase : (2 : ℝ) ≤ (d : ℝ) + 1 := by linarith
    calc
      (2 : ℝ) ≤ 2 ^ 8 := by norm_num
      _ ≤ ((d : ℝ) + 1) ^ 8 := pow_le_pow_left₀ (by norm_num) hbase 8
  exact (div_le_iff₀ (by positivity : 0 < ((d : ℝ) + 1) ^ 8)).2 (by
    nlinarith)

theorem isolatedVariable_upperNeighborBudget_le
    (d : ℕ) (hd : 1 ≤ d) :
    (increasingNeighborBudget (upperSupportBudget d) 2 d : ℝ) ≤
      20 * (d : ℝ) ^ 3 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  simp only [increasingNeighborBudget, upperSupportBudget]
  push_cast
  have haux : 0 ≤ (d : ℝ) ^ 2 * ((d : ℝ) - 1) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hdR)
  nlinarith

theorem isolatedVariable_slotNeighborBudget_le
    (d : ℕ) (hd : 1 ≤ d) :
    (increasingNeighborBudget (slotSupportBudget d) 2 d : ℝ) ≤
      30 * (d : ℝ) ^ 3 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  simp only [increasingNeighborBudget, slotSupportBudget]
  push_cast
  have haux : 0 ≤ (d : ℝ) ^ 2 * ((d : ℝ) - 1) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hdR)
  nlinarith

theorem isolatedVariable_slotConflictNeighborBudget_le
    (d : ℕ) (hd : 1 ≤ d) :
    (increasingNeighborBudget
        (RankThreeOptionSystem.isolatedConflictSupportBudget
          (slotSupportBudget d) d) 2 d : ℝ) ≤
      120 * (d : ℝ) ^ 4 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  simp only [increasingNeighborBudget, slotSupportBudget,
    RankThreeOptionSystem.isolatedConflictSupportBudget]
  push_cast
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have h3 : 3 * (d : ℝ) + 1 ≤ 4 * d := by linarith
  have h10 : 2 + 8 * (d : ℝ) ≤ 10 * d := by linarith
  have hfirst : (d : ℝ) * (d + 2 * d) = 3 * d ^ 2 := by ring
  calc
    ((d : ℝ) * (d + 2 * d)) * (3 * d + 1) * (2 + 8 * d) ≤
        (3 * d ^ 2) * (3 * d + 1) * (2 + 8 * d) := by rw [hfirst]
    _ ≤ (3 * d ^ 2) * (4 * d) * (2 + 8 * d) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity)
    _ ≤ (3 * d ^ 2) * (4 * d) * (10 * d) := by
      exact mul_le_mul_of_nonneg_left h10 (by positivity)
    _ = 120 * d ^ 4 := by ring

theorem isolatedVariable_groupConflictNeighborBudget_le
    (d K : ℕ) (hd : 1 ≤ d) (hK : K ≤ d) :
    (increasingNeighborBudget
        (RankThreeOptionSystem.isolatedConflictSupportBudget
          (groupSupportBudget (2 * K) d) d) 2 d : ℝ) ≤
      80 * (d : ℝ) ^ 4 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hKR : (K : ℝ) ≤ d := by exact_mod_cast hK
  simp only [increasingNeighborBudget, groupSupportBudget,
    RankThreeOptionSystem.isolatedConflictSupportBudget]
  push_cast
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have h3 : 3 * (d : ℝ) + 1 ≤ 4 * d := by linarith
  have h10 : 2 + 8 * (d : ℝ) ≤ 10 * d := by linarith
  have hKfactor : (2 * (K : ℝ)) * d ≤ (2 * d) * d := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hKR (by norm_num)) (by positivity)
  calc
    ((2 * (K : ℝ)) * d) * (3 * d + 1) * (2 + 8 * d) ≤
        ((2 * d) * d) * (3 * d + 1) * (2 + 8 * d) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKfactor (by positivity)) (by positivity)
    _ ≤ ((2 * d) * d) * (4 * d) * (2 + 8 * d) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity)
    _ ≤ ((2 * d) * d) * (4 * d) * (10 * d) := by
      exact mul_le_mul_of_nonneg_left h10 (by positivity)
    _ = 80 * d ^ 4 := by ring

theorem isolatedVariable_slotLowerNeighborBudget_le
    (d : ℕ) (hd : 1 ≤ d) :
    (RankThreeOptionSystem.isolatedLowerNeighborBudget
        (slotSupportBudget d) 2 d : ℝ) ≤
      150 * (d : ℝ) ^ 4 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  simp only [RankThreeOptionSystem.isolatedLowerNeighborBudget,
    slotSupportBudget]
  push_cast
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have h3 : 3 * (d : ℝ) + 1 ≤ 4 * d := by linarith
  have h10 : 2 + 8 * (d : ℝ) ≤ 10 * d := by linarith
  have hprod : (3 * (d : ℝ) + 1) * (2 + 8 * d) ≤
      (4 * d) * (10 * d) :=
    mul_le_mul h3 h10 (by positivity) (by positivity)
  have hinner :
      2 * (d : ℝ) + ((3 * d + 1) * (2 + 8 * d) + 8 * d) ≤
        50 * (d : ℝ) ^ 2 := by
    calc
      2 * (d : ℝ) + ((3 * d + 1) * (2 + 8 * d) + 8 * d) ≤
          2 * d + ((4 * d) * (10 * d) + 8 * d) := by gcongr
      _ = 10 * d + 40 * d ^ 2 := by ring
      _ ≤ 50 * d ^ 2 := by
        have hten : (0 : ℝ) ≤ 10 * (d : ℝ) := by positivity
        have : 0 ≤ 10 * (d : ℝ) * (d - 1) :=
          mul_nonneg hten (sub_nonneg.mpr hdR)
        nlinarith
  have hfirst : (d : ℝ) * (d + 2 * d) = 3 * d ^ 2 := by ring
  calc
    (d : ℝ) * (d + 2 * d) *
        (2 * d + ((3 * d + 1) * (2 + 8 * d) + 8 * d)) ≤
      (3 * d ^ 2) *
        (2 * d + ((3 * d + 1) * (2 + 8 * d) + 8 * d)) := by rw [hfirst]
    _ ≤ (3 * d ^ 2) * (50 * d ^ 2) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 150 * d ^ 4 := by ring

theorem isolatedVariable_groupLowerNeighborBudget_le
    (d K : ℕ) (hd : 1 ≤ d) (hK : K ≤ d) :
    (RankThreeOptionSystem.isolatedLowerNeighborBudget
        (groupSupportBudget (2 * K) d) 2 d : ℝ) ≤
      100 * (d : ℝ) ^ 4 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hKR : (K : ℝ) ≤ d := by exact_mod_cast hK
  simp only [RankThreeOptionSystem.isolatedLowerNeighborBudget,
    groupSupportBudget]
  push_cast
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hinner :
      2 * (d : ℝ) + ((3 * d + 1) * (2 + 8 * d) + 8 * d) ≤
      50 * d ^ 2 := by
    have h3 : 3 * (d : ℝ) + 1 ≤ 4 * d := by linarith
    have h10 : 2 + 8 * (d : ℝ) ≤ 10 * d := by linarith
    have hprod : (3 * (d : ℝ) + 1) * (2 + 8 * d) ≤
        (4 * d) * (10 * d) :=
      mul_le_mul h3 h10 (by positivity) (by positivity)
    calc
      2 * (d : ℝ) + ((3 * d + 1) * (2 + 8 * d) + 8 * d) ≤
          2 * d + ((4 * d) * (10 * d) + 8 * d) := by gcongr
      _ = 10 * d + 40 * d ^ 2 := by ring
      _ ≤ 50 * d ^ 2 := by
        have hten : (0 : ℝ) ≤ 10 * (d : ℝ) := by positivity
        have hdiff : 0 ≤ 10 * (d : ℝ) * (d - 1) :=
          mul_nonneg hten (sub_nonneg.mpr hdR)
        nlinarith
  have hKfactor : (2 * (K : ℝ)) * d ≤ 2 * d ^ 2 := by
    have htwo : (0 : ℝ) ≤ 2 := by norm_num
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hKR htwo)
      (by positivity : (0 : ℝ) ≤ d)
    convert h using 1 <;> ring
  calc
    ((2 * (K : ℝ)) * d) *
        (2 * d + ((3 * d + 1) * (2 + 8 * d) + 8 * d)) ≤
      (2 * d ^ 2) *
        (2 * d + ((3 * d + 1) * (2 + 8 * d) + 8 * d)) :=
      mul_le_mul_of_nonneg_right hKfactor (by positivity)
    _ ≤ (2 * d ^ 2) * (50 * d ^ 2) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 100 * d ^ 4 := by ring

/-- All four half-product hypotheses of the isolated uniform round follow
from `d ≥ 5` and `K ≤ d`. -/
theorem isolatedVariable_all_product_bounds
    (d K : ℕ) (hd : 5 ≤ d) (hK : K ≤ d) :
    exponentialRowWeight (isolatedVariableZ d) *
        (increasingNeighborBudget (upperSupportBudget d) 2 d : ℝ) ≤ 1 / 2 ∧
    exponentialRowWeight (isolatedVariableZ d) *
        (increasingNeighborBudget
          (RankThreeOptionSystem.isolatedConflictSupportBudget
            (groupSupportBudget (2 * K) d) d) 2 d : ℝ) ≤ 1 / 2 ∧
    exponentialRowWeight (isolatedVariableZ d) *
        (increasingNeighborBudget
          (RankThreeOptionSystem.isolatedConflictSupportBudget
            (slotSupportBudget d) d) 2 d : ℝ) ≤ 1 / 2 ∧
    exponentialRowWeight (isolatedVariableZ d) *
        (increasingNeighborBudget (slotSupportBudget d) 2 d : ℝ) ≤ 1 / 2 := by
  have hd1 : 1 ≤ d := by omega
  refine ⟨isolatedVariable_product_of_budget d _ hd
      ((isolatedVariable_upperNeighborBudget_le d hd1).trans ?_), ?_⟩
  · have hd0 : (0 : ℝ) ≤ d := by positivity
    have hd4 : (d : ℝ) ^ 3 ≤ d ^ 4 := by
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      have := mul_nonneg (show 0 ≤ (d : ℝ) ^ 3 by positivity)
        (sub_nonneg.mpr hdR)
      nlinarith
    calc
      20 * (d : ℝ) ^ 3 ≤ 150 * (d : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ 150 * (d : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_left hd4 (by norm_num)
  refine ⟨isolatedVariable_product_of_budget d _ hd
      ((isolatedVariable_groupConflictNeighborBudget_le d K hd1 hK).trans
        (mul_le_mul_of_nonneg_right (by norm_num : (80 : ℝ) ≤ 150)
          (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 4))), ?_⟩
  refine ⟨isolatedVariable_product_of_budget d _ hd
      ((isolatedVariable_slotConflictNeighborBudget_le d hd1).trans
        (mul_le_mul_of_nonneg_right (by norm_num : (120 : ℝ) ≤ 150)
          (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 4))), ?_⟩
  apply isolatedVariable_product_of_budget d _ hd
  exact (isolatedVariable_slotNeighborBudget_le d hd1).trans (by
    have hd4 : (d : ℝ) ^ 3 ≤ d ^ 4 := by
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      have := mul_nonneg (show 0 ≤ (d : ℝ) ^ 3 by positivity)
        (sub_nonneg.mpr hdR)
      nlinarith
    calc
      30 * (d : ℝ) ^ 3 ≤ 150 * (d : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ 150 * (d : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_left hd4 (by norm_num))

theorem isolatedVariable_lower_corrections_le_one
    (d K : ℕ) (hd : 5 ≤ d) (hK : K ≤ d) :
    2 * exponentialRowWeight (isolatedVariableZ d) *
        (RankThreeOptionSystem.isolatedLowerNeighborBudget
          (groupSupportBudget (2 * K) d) 2 d : ℝ) ≤ 1 ∧
    2 * exponentialRowWeight (isolatedVariableZ d) *
        (RankThreeOptionSystem.isolatedLowerNeighborBudget
          (slotSupportBudget d) 2 d : ℝ) ≤ 1 := by
  have hd1 : 1 ≤ d := by omega
  have hgroupBudget := isolatedVariable_groupLowerNeighborBudget_le d K hd1 hK
  have hslotBudget := isolatedVariable_slotLowerNeighborBudget_le d hd1
  have hgroupProduct := isolatedVariable_product_of_budget d _ hd
    (hgroupBudget.trans (by
      have : (0 : ℝ) ≤ d ^ 4 := by positivity
      nlinarith))
  have hslotProduct := isolatedVariable_product_of_budget d _ hd hslotBudget
  constructor <;> nlinarith

/-! ## Closed Chernoff-rate lower bounds -/

/-- The endpoint-group Chernoff coefficient has a uniform quadratic gap.
The loose factor `1/4` is enough for the block-size choice and follows from
the third-order exponential remainder on `[0,1/2]`. -/
theorem groupChernoffCoefficient_le_neg_sq_quarter
    {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    x * (1 - x) + (Real.exp (-x) - 1) ≤ -(x ^ 2) / 4 := by
  have habs : |-x| ≤ (1 : ℝ) := by
    rw [abs_neg, abs_of_nonneg hx0]
    linarith
  have h := Real.exp_bound (x := -x) habs (n := 3) (by norm_num)
  have hu := (abs_le.mp h).2
  norm_num [Finset.sum_range_succ, abs_of_nonneg hx0] at hu
  have hcubic : 2 * x ^ 3 / 9 ≤ x ^ 2 / 4 := by
    have := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hxhalf)
    nlinarith
  nlinarith

theorem variableSlack_groupRate_lower
    {alpha gamma delta : ℝ} {d lambda m : ℕ}
    (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma)
    (hd : 0 < d) (hlambda : 0 < lambda)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    delta ^ 2 * variableSlackA alpha gamma lambda * m / 64 ≤
      -(((delta / 2) * (1 - delta / 2) +
          (Real.exp (-(delta / 2)) - 1)) *
        (variableSlackRho alpha gamma d lambda * (m * d : ℕ))) := by
  have hcoef := groupChernoffCoefficient_le_neg_sq_quarter
    (show 0 ≤ delta / 2 by positivity) (by linarith)
  have ha : 0 ≤ variableSlackA alpha gamma lambda := by
    unfold variableSlackA
    positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmass :
      variableSlackRho alpha gamma d lambda * ((m * d : ℕ) : ℝ) =
        variableSlackA alpha gamma lambda * m := by
    unfold variableSlackRho
    push_cast
    field_simp [hdR.ne']
  rw [hmass]
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hcoef' : delta ^ 2 / 64 ≤
      -((delta / 2) * (1 - delta / 2) +
        (Real.exp (-(delta / 2)) - 1)) := by
    nlinarith [hcoef]
  have hmul := mul_le_mul_of_nonneg_right hcoef'
    (mul_nonneg ha hm0)
  convert hmul using 1 <;> ring

theorem variableSlackSlotMean_upper
    {alpha gamma : ℝ} {d S lambda : ℕ}
    (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma)
    (hd : 0 < d) (hlambda : 0 < lambda) (hS : S ≤ d) :
    variableSlackSlotMean alpha gamma d S lambda ≤
      2 * variableSlackA alpha gamma lambda * d / (3 * lambda : ℕ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlambdaR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have ha : 0 ≤ variableSlackA alpha gamma lambda := by
    unfold variableSlackA
    positivity
  have hnat : S * (d + S - 3 * lambda) ≤ 2 * d * d := by
    calc
      S * (d + S - 3 * lambda) ≤ S * (d + S) :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ d * (d + d) := Nat.mul_le_mul hS (Nat.add_le_add_left hS d)
      _ = 2 * d * d := by ring
  have hreal : (((S * (d + S - 3 * lambda) : ℕ) : ℝ)) ≤
      2 * (d : ℝ) * d := by exact_mod_cast hnat
  unfold variableSlackSlotMean variableSlackRho
  have hquot :
      (((S * (d + S - 3 * lambda) : ℕ) : ℝ) /
          ((3 * lambda : ℕ) : ℝ)) ≤
        (2 * (d : ℝ) * d) / (3 * lambda : ℕ) := by
    exact div_le_div_of_nonneg_right hreal (by positivity)
  calc
    (variableSlackA alpha gamma lambda / (d : ℝ)) *
        (((S * (d + S - 3 * lambda) : ℕ) : ℝ) /
          ((3 * lambda : ℕ) : ℝ)) ≤
      (variableSlackA alpha gamma lambda / (d : ℝ)) *
        ((2 * (d : ℝ) * d) / (3 * lambda : ℕ)) := by
          gcongr
    _ = 2 * variableSlackA alpha gamma lambda * d /
        (3 * lambda : ℕ) := by
      push_cast
      field_simp [hdR.ne', hlambdaR.ne']

theorem variableSlackJobMean_upper
    {alpha gamma : ℝ} {d S lambda : ℕ}
    (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma)
    (hd : 0 < d) (hlambda : 0 < lambda) (hS : S ≤ d) :
    variableSlackJobMean alpha gamma d S lambda ≤
      variableSlackA alpha gamma lambda * d / lambda := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlambdaR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have ha : 0 ≤ variableSlackA alpha gamma lambda := by
    unfold variableSlackA
    positivity
  have hSR : (S : ℝ) ≤ d := by exact_mod_cast hS
  have hmean : variableSlackJobMean alpha gamma d S lambda =
      variableSlackA alpha gamma lambda * S / lambda := by
    unfold variableSlackJobMean variableSlackRho
    field_simp [hdR.ne', hlambdaR.ne']
  rw [hmean]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hSR ha) hlambdaR.le

theorem variableSlack_slotQuadraticRate_lower
    {alpha gamma : ℝ} {d S lambda : ℕ}
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hd : 0 < d) (hlambda : 0 < lambda) (hS : S ≤ d)
    (hmean : 0 < variableSlackSlotMean alpha gamma d S lambda)
    (hgap : variableSlackEta alpha gamma lambda * d /
        (6 * lambda : ℕ) ≤ variableSlackSlotGap alpha gamma d S lambda) :
    variableSlackEta alpha gamma lambda ^ 2 * d /
        (96 * variableSlackA alpha gamma lambda * lambda) ≤
      variableSlackSlotGap alpha gamma d S lambda ^ 2 /
        (4 * variableSlackSlotMean alpha gamma d S lambda) := by
  have ha := variableSlackA_pos halpha hgamma hlambda
  have heta := variableSlackEta_pos halpha hgamma hlambda
  have hlambdaR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hgap0 : 0 ≤ variableSlackSlotGap alpha gamma d S lambda :=
    (div_nonneg (mul_nonneg heta.le hdR.le) (by positivity)).trans hgap
  have hmeanUpper := variableSlackSlotMean_upper halpha.le hgamma.le hd
    hlambda hS
  have hgapSq :
      (variableSlackEta alpha gamma lambda * d /
        (6 * lambda : ℕ)) ^ 2 ≤
          variableSlackSlotGap alpha gamma d S lambda ^ 2 :=
    (sq_le_sq₀ (div_nonneg
      (mul_nonneg heta.le hdR.le) (by positivity)) hgap0).2 hgap
  have hdenUpper :
      4 * variableSlackSlotMean alpha gamma d S lambda ≤
        4 * (2 * variableSlackA alpha gamma lambda * d /
          (3 * lambda : ℕ)) := by nlinarith
  calc
    variableSlackEta alpha gamma lambda ^ 2 * d /
          (96 * variableSlackA alpha gamma lambda * lambda) =
        (variableSlackEta alpha gamma lambda * d /
            (6 * lambda : ℕ)) ^ 2 /
          (4 * (2 * variableSlackA alpha gamma lambda * d /
            (3 * lambda : ℕ))) := by
      push_cast
      field_simp [ha.ne', heta.ne', hlambdaR.ne', hdR.ne']
      ring
    _ ≤ (variableSlackEta alpha gamma lambda * d /
            (6 * lambda : ℕ)) ^ 2 /
          (4 * variableSlackSlotMean alpha gamma d S lambda) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _)
        (mul_pos (by norm_num) hmean) hdenUpper
    _ ≤ variableSlackSlotGap alpha gamma d S lambda ^ 2 /
          (4 * variableSlackSlotMean alpha gamma d S lambda) := by
      exact div_le_div_of_nonneg_right hgapSq (by positivity)

theorem variableSlack_jobQuadraticRate_lower
    {alpha gamma : ℝ} {d S lambda : ℕ}
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hd : 0 < d) (hlambda : 0 < lambda) (hS : S ≤ d)
    (hmean : 0 < variableSlackJobMean alpha gamma d S lambda)
    (hgap : variableSlackEta alpha gamma lambda * d /
        (2 * lambda : ℕ) ≤ variableSlackJobGap alpha gamma d S lambda) :
    variableSlackEta alpha gamma lambda ^ 2 * d /
        (16 * variableSlackA alpha gamma lambda * lambda) ≤
      variableSlackJobGap alpha gamma d S lambda ^ 2 /
        (4 * variableSlackJobMean alpha gamma d S lambda) := by
  have ha := variableSlackA_pos halpha hgamma hlambda
  have heta := variableSlackEta_pos halpha hgamma hlambda
  have hlambdaR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hgap0 : 0 ≤ variableSlackJobGap alpha gamma d S lambda :=
    (div_nonneg (mul_nonneg heta.le hdR.le) (by positivity)).trans hgap
  have hmeanUpper := variableSlackJobMean_upper halpha.le hgamma.le hd
    hlambda hS
  have hgapSq :
      (variableSlackEta alpha gamma lambda * d /
        (2 * lambda : ℕ)) ^ 2 ≤
          variableSlackJobGap alpha gamma d S lambda ^ 2 :=
    (sq_le_sq₀ (div_nonneg
      (mul_nonneg heta.le hdR.le) (by positivity)) hgap0).2 hgap
  have hdenUpper :
      4 * variableSlackJobMean alpha gamma d S lambda ≤
        4 * (variableSlackA alpha gamma lambda * d / lambda) := by nlinarith
  calc
    variableSlackEta alpha gamma lambda ^ 2 * d /
          (16 * variableSlackA alpha gamma lambda * lambda) =
        (variableSlackEta alpha gamma lambda * d /
            (2 * lambda : ℕ)) ^ 2 /
          (4 * (variableSlackA alpha gamma lambda * d / lambda)) := by
      push_cast
      field_simp [ha.ne', heta.ne', hlambdaR.ne', hdR.ne']
      ring
    _ ≤ (variableSlackEta alpha gamma lambda * d /
            (2 * lambda : ℕ)) ^ 2 /
          (4 * variableSlackJobMean alpha gamma d S lambda) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _)
        (mul_pos (by norm_num) hmean) hdenUpper
    _ ≤ variableSlackJobGap alpha gamma d S lambda ^ 2 /
          (4 * variableSlackJobMean alpha gamma d S lambda) := by
      exact div_le_div_of_nonneg_right hgapSq (by positivity)

/-- On the padded slot degree, the elementary positivity and tilt-range
hypotheses needed by the Chernoff lemmas follow from the same local scale
condition used for the lower slot gap. -/
theorem variableSlack_padded_mean_and_gap_shape
    {alpha gamma : ℝ} {d S lambda : ℕ}
    (halpha : 0 < alpha) (hgamma0 : 0 < gamma)
    (hgammaHalf : gamma ≤ 1 / 2)
    (hlambda : 0 < lambda)
    (hSupper : (S : ℝ) ≤ (1 - gamma) * d)
    (hSlower : (1 - gamma) * d - 1 ≤ (S : ℝ))
    (hscale : 1000 * ((lambda : ℝ) + 1) ≤ gamma * d) :
    0 < variableSlackSlotMean alpha gamma d S lambda ∧
      variableSlackSlotGap alpha gamma d S lambda ≤
        2 * variableSlackSlotMean alpha gamma d S lambda ∧
      0 < variableSlackJobMean alpha gamma d S lambda ∧
      variableSlackJobGap alpha gamma d S lambda ≤
        2 * variableSlackJobMean alpha gamma d S lambda := by
  have hlambdaR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have hlambda1 : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
  have hgamma1 : gamma ≤ 1 := hgammaHalf.trans (by norm_num)
  have hdLarge : (2000 : ℝ) * (lambda + 1) ≤ d := by
    nlinarith
  have hdR : (0 : ℝ) < d := by nlinarith
  have hSposR : (0 : ℝ) < S := by
    nlinarith
  have hSpos : 0 < S := by exact_mod_cast hSposR
  have hthreeLt : 3 * lambda < d := by
    have hreal : ((3 * lambda : ℕ) : ℝ) < d := by
      push_cast
      nlinarith
    exact_mod_cast hreal
  have hinner : 0 < d + S - 3 * lambda := by
    exact Nat.sub_pos_of_lt (hthreeLt.trans_le (Nat.le_add_right d S))
  have ha := variableSlackA_pos halpha hgamma0 hlambda
  have heta := variableSlackEta_pos halpha hgamma0 hlambda
  have hslotMean : 0 < variableSlackSlotMean alpha gamma d S lambda := by
    unfold variableSlackSlotMean variableSlackRho
    positivity
  have hslotTarget0 : 0 ≤ variableSlackSlotTarget alpha gamma d lambda := by
    have hcoef : 0 ≤
        variableSlackA alpha gamma lambda * (2 - gamma) * (1 - gamma) -
          variableSlackEta alpha gamma lambda := by
      unfold variableSlackEta
      have h1 : (1 / 2 : ℝ) ≤ 1 - gamma := by linarith
      have h2 : (3 / 2 : ℝ) ≤ 2 - gamma := by linarith
      have hprod : (3 / 4 : ℝ) ≤ (2 - gamma) * (1 - gamma) := by
        nlinarith [mul_le_mul h2 h1 (by norm_num : 0 ≤ (1 / 2 : ℝ))
          (by linarith : 0 ≤ 2 - gamma)]
      have hsmall : gamma / 64 ≤ (3 / 4 : ℝ) := by linarith
      have hbracket : 0 ≤ (2 - gamma) * (1 - gamma) - gamma / 64 := by
        linarith
      nlinarith [mul_nonneg ha.le hbracket]
    unfold variableSlackSlotTarget
    positivity
  have hslotGap2 : variableSlackSlotGap alpha gamma d S lambda ≤
      2 * variableSlackSlotMean alpha gamma d S lambda := by
    unfold variableSlackSlotGap
    nlinarith
  have hjobMeanEq : variableSlackJobMean alpha gamma d S lambda =
      variableSlackA alpha gamma lambda * S / lambda := by
    unfold variableSlackJobMean variableSlackRho
    field_simp [hdR.ne', hlambdaR.ne']
  have hjobMean : 0 < variableSlackJobMean alpha gamma d S lambda := by
    rw [hjobMeanEq]
    positivity
  have htargetLe : variableSlackJobTarget alpha gamma d lambda ≤
      3 * variableSlackJobMean alpha gamma d S lambda := by
    rw [hjobMeanEq]
    unfold variableSlackJobTarget variableSlackEta
    apply (div_le_iff₀ (by positivity : 0 < ((2 * lambda : ℕ) : ℝ))).2
    push_cast
    have hfactor : 0 ≤ 1 - gamma := by linarith
    have hscaledLower := mul_le_mul_of_nonneg_left hSlower ha.le
    field_simp [hlambdaR.ne'] at hscaledLower ⊢
    nlinarith [mul_nonneg ha.le hfactor]
  have hjobGap2 : variableSlackJobGap alpha gamma d S lambda ≤
      2 * variableSlackJobMean alpha gamma d S lambda := by
    unfold variableSlackJobGap
    linarith
  exact ⟨hslotMean, hslotGap2, hjobMean, hjobGap2⟩

/-! ## Expanded scale formulas -/

theorem variableSlack_groupScale_formula
    {alpha gamma delta : ℝ} {lambda K : ℕ} (hlambda : 0 < lambda) :
    delta ^ 2 * variableSlackA alpha gamma lambda * K / 64 =
      delta ^ 2 * alpha * gamma * K / (64 * lambda) := by
  unfold variableSlackA
  push_cast
  field_simp [show (lambda : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hlambda)]

theorem variableSlack_slotRate_formula
    {alpha gamma : ℝ} {d lambda : ℕ}
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (hlambda : 0 < lambda) :
    variableSlackEta alpha gamma lambda ^ 2 * d /
        (96 * variableSlackA alpha gamma lambda * lambda) =
      alpha * gamma ^ 3 * d / (393216 * (lambda : ℝ) ^ 2) := by
  have hlambdaR : (lambda : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hlambda)
  unfold variableSlackEta variableSlackA
  push_cast
  field_simp [hlambdaR, halpha.ne', hgamma.ne']
  ring

theorem variableSlack_jobRate_formula
    {alpha gamma : ℝ} {d lambda : ℕ}
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (hlambda : 0 < lambda) :
    variableSlackEta alpha gamma lambda ^ 2 * d /
        (16 * variableSlackA alpha gamma lambda * lambda) =
      alpha * gamma ^ 3 * d / (65536 * (lambda : ℝ) ^ 2) := by
  have hlambdaR : (lambda : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hlambda)
  unfold variableSlackEta variableSlackA
  push_cast
  field_simp [hlambdaR, halpha.ne', hgamma.ne']
  ring

/-! ## Isolation-moment arithmetic with the corrected moment -/

/-- A square-ratio bound for the corrected moment implies the full
quadratic isolation envelope.  This is the moment-parametric version of
`variableSlack_isolationBudget_of_square_ratio`. -/
theorem variableSlack_isolationBudget_of_corrected_square_ratio
    (alpha gamma beta0 : ℝ) (d lambda : ℕ)
    (hd : 0 < d) (hlambda : 0 < lambda)
    (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma) (hbeta0 : 0 ≤ beta0)
    (hratio : (lambda : ℝ) ^ 2 * isolatedVariableMomentUpper d ^ 2 ≤
      beta0 * d)
    (hfixed :
      18 * (alpha * gamma) ^ 2 +
          (72 * (alpha * gamma) + 24) * beta0 ≤
        alpha * gamma ^ 2 / 64) :
    18 * variableSlackA alpha gamma lambda ^ 2 * d +
        72 * variableSlackA alpha gamma lambda *
          isolatedVariableMoment d * lambda +
        24 * isolatedVariableMoment d ^ 2 * lambda ≤
      variableSlackEta alpha gamma lambda * d := by
  have hlambdaR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have hkU := isolatedVariableMoment_cast_le d hd
  have hk0 : (0 : ℝ) ≤ isolatedVariableMoment d := by positivity
  have hU0 := isolatedVariableMomentUpper_nonneg d
  have hkSq : ((isolatedVariableMoment d : ℕ) : ℝ) ^ 2 ≤
      isolatedVariableMomentUpper d ^ 2 :=
    pow_le_pow_left₀ hk0 hkU 2
  have hratioK : (lambda : ℝ) ^ 2 *
      (isolatedVariableMoment d : ℝ) ^ 2 ≤ beta0 * d := by
    exact (mul_le_mul_of_nonneg_left hkSq (sq_nonneg (lambda : ℝ))).trans
      hratio
  have hlinearK : (lambda : ℝ) ^ 2 *
      (isolatedVariableMoment d : ℝ) ≤ beta0 * d := by
    have hk1 : (1 : ℝ) ≤ isolatedVariableMoment d := by
      exact_mod_cast isolatedVariableMoment_pos d hd
    have hk_le_sq : (isolatedVariableMoment d : ℝ) ≤
        (isolatedVariableMoment d : ℝ) ^ 2 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hk_le_sq
      (sq_nonneg (lambda : ℝ))).trans hratioK
  have hlambda1 : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
  have hlinearOne : (lambda : ℝ) *
      (isolatedVariableMoment d : ℝ) ≤ beta0 * d := by
    have hk0' : (0 : ℝ) ≤ isolatedVariableMoment d := by positivity
    have hlambdaSq : (lambda : ℝ) ≤ (lambda : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((lambda : ℝ) - 1)]
    exact (mul_le_mul_of_nonneg_right hlambdaSq hk0').trans hlinearK
  have hdivide :
      18 * ((alpha * gamma) / (lambda : ℝ)) ^ 2 * d +
          72 * ((alpha * gamma) / (lambda : ℝ)) *
            (isolatedVariableMoment d : ℝ) * lambda +
          24 * (isolatedVariableMoment d : ℝ) ^ 2 * lambda ≤
        ((alpha * gamma ^ 2 / 64) / (lambda : ℝ)) * d := by
    have hfixedD := mul_le_mul_of_nonneg_right hfixed
      (show (0 : ℝ) ≤ d by positivity)
    have hfirst :
        18 * ((alpha * gamma) / (lambda : ℝ)) ^ 2 * d ≤
          (18 * (alpha * gamma) ^ 2 / (lambda : ℝ)) * d := by
      have hsquare : (lambda : ℝ) ≤ lambda ^ 2 := by nlinarith
      have hnum : 0 ≤ 18 * (alpha * gamma) ^ 2 := by positivity
      have hdiv := div_le_div_of_nonneg_left hnum hlambdaR hsquare
      calc
        18 * ((alpha * gamma) / (lambda : ℝ)) ^ 2 * d =
            (18 * (alpha * gamma) ^ 2 / (lambda : ℝ) ^ 2) * d := by ring
        _ ≤ (18 * (alpha * gamma) ^ 2 / (lambda : ℝ)) * d :=
          mul_le_mul_of_nonneg_right hdiv (by positivity)
    have hlin :
        72 * ((alpha * gamma) / (lambda : ℝ)) *
            (isolatedVariableMoment d : ℝ) * lambda ≤
          ((72 * (alpha * gamma)) * beta0 / (lambda : ℝ)) * d := by
      have hag0 : 0 ≤ alpha * gamma := mul_nonneg halpha hgamma
      rw [show ((72 * (alpha * gamma)) * beta0 / (lambda : ℝ)) * d =
        ((72 * (alpha * gamma)) * beta0 * d) / (lambda : ℝ) by ring]
      apply (le_div_iff₀ hlambdaR).2
      calc
        72 * ((alpha * gamma) / (lambda : ℝ)) *
              (isolatedVariableMoment d : ℝ) * lambda * lambda =
            72 * (alpha * gamma) *
              ((lambda : ℝ) * isolatedVariableMoment d) := by
          field_simp [hlambdaR.ne']
        _ ≤ 72 * (alpha * gamma) * (beta0 * d) := by gcongr
        _ = (72 * (alpha * gamma) * beta0) * d := by ring
    have hquad :
        24 * (isolatedVariableMoment d : ℝ) ^ 2 * lambda ≤
          (24 * beta0 / (lambda : ℝ)) * d := by
      rw [show (24 * beta0 / (lambda : ℝ)) * d =
        (24 * beta0 * d) / (lambda : ℝ) by ring]
      apply (le_div_iff₀ hlambdaR).2
      calc
        24 * (isolatedVariableMoment d : ℝ) ^ 2 * lambda * lambda =
            24 * ((lambda : ℝ) ^ 2 *
              (isolatedVariableMoment d : ℝ) ^ 2) := by ring
        _ ≤ 24 * (beta0 * d) := by gcongr
        _ = (24 * beta0) * d := by ring
    calc
      _ ≤ ((18 * (alpha * gamma) ^ 2 +
          (72 * (alpha * gamma) + 24) * beta0) /
            (lambda : ℝ)) * d := by
          calc
            _ ≤ (18 * (alpha * gamma) ^ 2 / (lambda : ℝ)) * d +
                ((72 * (alpha * gamma)) * beta0 / (lambda : ℝ)) * d +
                (24 * beta0 / (lambda : ℝ)) * d :=
              add_le_add (add_le_add hfirst hlin) hquad
            _ = _ := by ring
      _ ≤ ((alpha * gamma ^ 2 / 64) / (lambda : ℝ)) * d := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hfixed hlambdaR.le)
          (by positivity)
  convert hdivide using 1 <;>
    simp only [variableSlackA, variableSlackEta] <;>
    push_cast <;> ring

end WeightedEdgeColoring
