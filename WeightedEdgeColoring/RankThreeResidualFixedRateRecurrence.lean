import WeightedEdgeColoring.RankThreeResidualFixedRateBudgets

/-!
# Integer recurrence for the fixed-rate residual round

This file records the rounding bookkeeping for repeated fixed-rate rounds.
The slot cap loses half of the floored slot budget, while the surviving job
degree pays the ceiled job budget.  Once the slot budget is at least two, a
coarse factor `640` absorbs both rounding errors.
-/

namespace WeightedEdgeColoring

/-- Slot caps obtained by repeatedly applying the natural fixed-rate update. -/
noncomputable def fixedRateSlotCap (lambda S0 : ℕ) : ℕ → ℕ
  | 0 => S0
  | t + 1 => fixedRateNextSlotBound lambda (fixedRateSlotCap lambda S0 t)

/-- Guaranteed surviving job degree under the natural fixed-rate loss. -/
noncomputable def fixedRateJobFloor (lambda d0 S0 : ℕ) : ℕ → ℕ
  | 0 => d0
  | t + 1 => fixedRateJobFloor lambda d0 S0 t -
      fixedRateJobBudget lambda (fixedRateSlotCap lambda S0 t)

@[simp] theorem fixedRateSlotCap_zero (lambda S0 : ℕ) :
    fixedRateSlotCap lambda S0 0 = S0 := rfl

@[simp] theorem fixedRateSlotCap_succ (lambda S0 t : ℕ) :
    fixedRateSlotCap lambda S0 (t + 1) =
      fixedRateNextSlotBound lambda (fixedRateSlotCap lambda S0 t) := rfl

@[simp] theorem fixedRateJobFloor_zero (lambda d0 S0 : ℕ) :
    fixedRateJobFloor lambda d0 S0 0 = d0 := rfl

@[simp] theorem fixedRateJobFloor_succ (lambda d0 S0 t : ℕ) :
    fixedRateJobFloor lambda d0 S0 (t + 1) =
      fixedRateJobFloor lambda d0 S0 t -
        fixedRateJobBudget lambda (fixedRateSlotCap lambda S0 t) := rfl

theorem fixedRateSlotCap_succ_le (lambda S0 t : ℕ) :
    fixedRateSlotCap lambda S0 (t + 1) ≤ fixedRateSlotCap lambda S0 t := by
  rw [fixedRateSlotCap_succ]
  exact fixedRateNextSlotBound_le _ _

theorem fixedRateSlotCap_antitone (lambda S0 : ℕ) :
    Antitone (fixedRateSlotCap lambda S0) :=
  antitone_nat_of_succ_le (fixedRateSlotCap_succ_le lambda S0)

theorem fixedRateSlotCap_le_initial (lambda S0 t : ℕ) :
    fixedRateSlotCap lambda S0 t ≤ S0 :=
  fixedRateSlotCap_antitone lambda S0 (Nat.zero_le t)

theorem fixedRateJobFloor_succ_le (lambda d0 S0 t : ℕ) :
    fixedRateJobFloor lambda d0 S0 (t + 1) ≤
      fixedRateJobFloor lambda d0 S0 t := by
  simp

theorem fixedRateJobFloor_antitone (lambda d0 S0 : ℕ) :
    Antitone (fixedRateJobFloor lambda d0 S0) :=
  antitone_nat_of_succ_le (fixedRateJobFloor_succ_le lambda d0 S0)

/-- The ideal job budget is exactly 160 times the ideal (undivided) slot
budget. -/
theorem fixedRate_job_real_eq_160_mul_slot_real (lambda S : ℕ) :
    8 * fixedRateKappa * (S : ℝ) / (lambda : ℝ) =
      160 * (fixedRateKappa * (S : ℝ) / (20 * (lambda : ℝ))) := by
  ring

/-- If the floored slot budget is at least two, factor `640` absorbs the
floor, the later division by two, and the ceiling in the job budget. -/
theorem fixedRateJobBudget_le_640_mul_halfSlotBudget
    (lambda S : ℕ) (hslot : 2 ≤ fixedRateSlotBudget lambda S) :
    fixedRateJobBudget lambda S ≤
      640 * (fixedRateSlotBudget lambda S / 2) := by
  let B := fixedRateSlotBudget lambda S
  let U := fixedRateJobBudget lambda S
  have hx := fixedRateSlotBudget_lt_cast_add_one lambda S
  have hU := fixedRateJobBudget_cast_lt_add_one lambda S
  have hreal : (U : ℝ) < ((160 * B + 161 : ℕ) : ℝ) := by
    dsimp only [U, B]
    rw [fixedRate_job_real_eq_160_mul_slot_real] at hU
    push_cast
    nlinarith
  have hnat : U < 160 * B + 161 := by
    exact_mod_cast hreal
  dsimp only [U, B] at hnat hslot ⊢
  omega

/-- Exact size of one slot-cap drop. -/
theorem fixedRateSlotCap_drop (lambda S0 t : ℕ) :
    fixedRateSlotCap lambda S0 t - fixedRateSlotCap lambda S0 (t + 1) =
      fixedRateSlotBudget lambda (fixedRateSlotCap lambda S0 t) / 2 := by
  rw [fixedRateSlotCap_succ, fixedRateNextSlotBound]
  have hq : fixedRateSlotBudget lambda (fixedRateSlotCap lambda S0 t) / 2 ≤
      fixedRateSlotCap lambda S0 t := by
    by_cases hlambda : lambda = 0
    · simp [fixedRateSlotBudget, hlambda]
    · exact (Nat.div_le_self _ _).trans
        (fixedRateSlotBudget_le_slotBound lambda _ (Nat.pos_of_ne_zero hlambda))
  omega

/-- Up to any round in which every slot budget is at least two, total job
loss is at most `640` times the total drop of the slot cap.  This formulation
with truncated subtraction remains true even if a formal job floor reaches
zero. -/
theorem fixedRate_affine_invariant
    (lambda d0 S0 n : ℕ)
    (hlarge : ∀ t < n,
      2 ≤ fixedRateSlotBudget lambda (fixedRateSlotCap lambda S0 t)) :
    d0 - 640 * (S0 - fixedRateSlotCap lambda S0 n) ≤
      fixedRateJobFloor lambda d0 S0 n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hlarge' : ∀ t < n,
          2 ≤ fixedRateSlotBudget lambda (fixedRateSlotCap lambda S0 t) := by
        intro t ht
        exact hlarge t (by omega)
      have hinv := ih hlarge'
      have hratio := fixedRateJobBudget_le_640_mul_halfSlotBudget
        lambda (fixedRateSlotCap lambda S0 n) (hlarge n (by omega))
      have hcap := fixedRateSlotCap_le_initial lambda S0 n
      have hq : fixedRateSlotBudget lambda (fixedRateSlotCap lambda S0 n) / 2 ≤
          fixedRateSlotCap lambda S0 n := by
        rw [← fixedRateSlotCap_drop lambda S0 n]
        omega
      rw [fixedRateJobFloor_succ, fixedRateSlotCap_succ,
        fixedRateNextSlotBound]
      omega

/-- A small initial slot-to-job ratio keeps every job floor at least half
of the reference job scale. -/
theorem fixedRate_job_half_of_small_initial_slot
    (lambda J d0 S0 n : ℕ)
    (hd0 : J ≤ d0) (hsmall : 1280 * S0 ≤ J)
    (hlarge : ∀ t < n,
      2 ≤ fixedRateSlotBudget lambda (fixedRateSlotCap lambda S0 t)) :
    J ≤ 2 * fixedRateJobFloor lambda d0 S0 n := by
  have hinv := fixedRate_affine_invariant lambda d0 S0 n hlarge
  have hcap := fixedRateSlotCap_le_initial lambda S0 n
  omega

/-- Under a strict initial scale separation, the next job budget is smaller
than the current guaranteed degree. -/
theorem fixedRate_jobBudget_lt_jobFloor
    (lambda J d0 S0 t : ℕ)
    (hd0 : J ≤ d0) (hsmall : 1280 * S0 < J)
    (hlarge : ∀ i ≤ t,
      2 ≤ fixedRateSlotBudget lambda (fixedRateSlotCap lambda S0 i)) :
    fixedRateJobBudget lambda (fixedRateSlotCap lambda S0 t) <
      fixedRateJobFloor lambda d0 S0 t := by
  have hlarge' : ∀ i < t,
      2 ≤ fixedRateSlotBudget lambda (fixedRateSlotCap lambda S0 i) := by
    intro i hi
    exact hlarge i (by omega)
  have hhalf := fixedRate_job_half_of_small_initial_slot
    lambda J d0 S0 t hd0 hsmall.le hlarge'
  have hratio := fixedRateJobBudget_le_640_mul_halfSlotBudget
    lambda (fixedRateSlotCap lambda S0 t) (hlarge t le_rfl)
  have hq : fixedRateSlotBudget lambda (fixedRateSlotCap lambda S0 t) / 2 ≤
      fixedRateSlotCap lambda S0 t := by
    rw [← fixedRateSlotCap_drop lambda S0 t]
    omega
  have hcap := fixedRateSlotCap_le_initial lambda S0 t
  omega

/-- Consequently the next formal job floor is positive. -/
theorem fixedRateJobFloor_succ_pos
    (lambda J d0 S0 t : ℕ)
    (hd0 : J ≤ d0) (hsmall : 1280 * S0 < J)
    (hlarge : ∀ i ≤ t,
      2 ≤ fixedRateSlotBudget lambda (fixedRateSlotCap lambda S0 i)) :
    0 < fixedRateJobFloor lambda d0 S0 (t + 1) := by
  rw [fixedRateJobFloor_succ]
  exact Nat.sub_pos_of_lt
    (fixedRate_jobBudget_lt_jobFloor lambda J d0 S0 t hd0 hsmall hlarge)

end WeightedEdgeColoring
