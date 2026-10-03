import WeightedEdgeColoring.RankThreeResidualFixedRateRecurrence

/-!
# A finite stopping round for the slot-cap recurrence

As long as the natural slot budget is at least two, every round decreases the
integer slot cap by at least one.  Hence the recurrence reaches any prescribed
lower target in finitely many rounds.  Choosing the first such round also
records all hypotheses that hold strictly above the target.
-/

namespace WeightedEdgeColoring

theorem fixedRateSlotCap_strict_decrease
    (lambda S0 t : ℕ)
    (hlambda : 0 < lambda)
    (hbudget : 2 ≤ fixedRateSlotBudget lambda
      (fixedRateSlotCap lambda S0 t)) :
    fixedRateSlotCap lambda S0 (t + 1) <
      fixedRateSlotCap lambda S0 t := by
  have hb := fixedRateSlotBudget_le_slotBound lambda
    (fixedRateSlotCap lambda S0 t) hlambda
  rw [fixedRateSlotCap_succ, fixedRateNextSlotBound]
  have hhalf : 1 ≤
      fixedRateSlotBudget lambda (fixedRateSlotCap lambda S0 t) / 2 := by
    omega
  omega

/-- If every cap above `target` has a nontrivial slot budget, the recurrence
eventually reaches `target`. -/
theorem exists_fixedRateSlotCap_le
    (lambda S0 target : ℕ)
    (hlambda : 0 < lambda)
    (hbudget : ∀ S, target < S → S ≤ S0 →
      2 ≤ fixedRateSlotBudget lambda S) :
    ∃ n, fixedRateSlotCap lambda S0 n ≤ target := by
  by_contra hnone
  push Not at hnone
  have hdec : ∀ t,
      fixedRateSlotCap lambda S0 (t + 1) <
        fixedRateSlotCap lambda S0 t := by
    intro t
    apply fixedRateSlotCap_strict_decrease lambda S0 t hlambda
    exact hbudget _ (hnone t)
      (fixedRateSlotCap_le_initial lambda S0 t)
  have hbound : ∀ n,
      fixedRateSlotCap lambda S0 n + n ≤ S0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hd := hdec n
        omega
  have := hbound (S0 + 1)
  omega

/-- The first round at which the slot cap is at most `target`. -/
noncomputable def fixedRateStoppingRound
    (lambda S0 target : ℕ)
    (hlambda : 0 < lambda)
    (hbudget : ∀ S, target < S → S ≤ S0 →
      2 ≤ fixedRateSlotBudget lambda S) : ℕ :=
  Nat.find (exists_fixedRateSlotCap_le lambda S0 target hlambda hbudget)

theorem fixedRateSlotCap_stopping_le
    (lambda S0 target : ℕ)
    (hlambda : 0 < lambda)
    (hbudget : ∀ S, target < S → S ≤ S0 →
      2 ≤ fixedRateSlotBudget lambda S) :
    fixedRateSlotCap lambda S0
      (fixedRateStoppingRound lambda S0 target hlambda hbudget) ≤ target := by
  exact Nat.find_spec
    (exists_fixedRateSlotCap_le lambda S0 target hlambda hbudget)

theorem fixedRateSlotCap_before_stopping_gt
    (lambda S0 target : ℕ)
    (hlambda : 0 < lambda)
    (hbudget : ∀ S, target < S → S ≤ S0 →
      2 ≤ fixedRateSlotBudget lambda S)
    {t : ℕ} (ht : t <
      fixedRateStoppingRound lambda S0 target hlambda hbudget) :
    target < fixedRateSlotCap lambda S0 t := by
  have hnot := Nat.find_min
    (exists_fixedRateSlotCap_le lambda S0 target hlambda hbudget) ht
  omega

/-- At every round before the stopping round, the slot budget is at least
two. -/
theorem fixedRateSlotBudget_before_stopping
    (lambda S0 target : ℕ)
    (hlambda : 0 < lambda)
    (hbudget : ∀ S, target < S → S ≤ S0 →
      2 ≤ fixedRateSlotBudget lambda S)
    {t : ℕ} (ht : t <
      fixedRateStoppingRound lambda S0 target hlambda hbudget) :
    2 ≤ fixedRateSlotBudget lambda (fixedRateSlotCap lambda S0 t) := by
  exact hbudget _
    (fixedRateSlotCap_before_stopping_gt lambda S0 target hlambda hbudget ht)
    (fixedRateSlotCap_le_initial lambda S0 t)

/-- A bundled first-crossing index, useful when the proof does not need the
definition of the stopping round itself. -/
theorem exists_fixedRate_first_crossing
    (lambda S0 target : ℕ)
    (hlambda : 0 < lambda)
    (hbudget : ∀ S, target < S → S ≤ S0 →
      2 ≤ fixedRateSlotBudget lambda S) :
    ∃ n,
      fixedRateSlotCap lambda S0 n ≤ target ∧
      (∀ t < n, target < fixedRateSlotCap lambda S0 t) ∧
      (∀ t < n,
        2 ≤ fixedRateSlotBudget lambda (fixedRateSlotCap lambda S0 t)) := by
  let n := fixedRateStoppingRound lambda S0 target hlambda hbudget
  refine ⟨n, fixedRateSlotCap_stopping_le lambda S0 target hlambda hbudget,
    ?_, ?_⟩
  · intro t ht
    exact fixedRateSlotCap_before_stopping_gt lambda S0 target hlambda hbudget ht
  · intro t ht
    exact fixedRateSlotBudget_before_stopping lambda S0 target hlambda hbudget ht

end WeightedEdgeColoring
