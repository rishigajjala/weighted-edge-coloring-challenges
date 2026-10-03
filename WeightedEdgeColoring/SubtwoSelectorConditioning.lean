import WeightedEdgeColoring.FiniteCategoricalSelection

/-!
# Conditioning finite source laws on locally good states

This is the probability step needed before two-sided mixed candidate selection.
It conditions each source law separately, keeps the selected states good,
and controls every bounded nonnegative row expectation without asserting that
the original exact edge marginals survive conditioning.
-/

namespace WeightedEdgeColoring.FiniteCategoricalSelection

open scoped BigOperators

variable {State : Type*} [Fintype State]
variable (good : State → Prop) [DecidablePred good]

def goodMass (prob : State → ℝ) : ℝ :=
  ∑ a, if good a then prob a else 0

noncomputable def conditionedProb (prob : State → ℝ) (a : State) : ℝ :=
  if good a then prob a / goodMass good prob else 0

theorem goodMass_nonneg
    (prob : State → ℝ) (hprob0 : ∀ a, 0 ≤ prob a) :
    0 ≤ goodMass good prob := by
  unfold goodMass
  apply Finset.sum_nonneg
  intro a _
  split
  · exact hprob0 a
  · exact le_rfl

theorem goodMass_le_one
    (prob : State → ℝ) (hprob0 : ∀ a, 0 ≤ prob a)
    (hprobSum : ∑ a, prob a = 1) :
    goodMass good prob ≤ 1 := by
  rw [← hprobSum]
  unfold goodMass
  apply Finset.sum_le_sum
  intro a _
  split
  · exact le_rfl
  · exact hprob0 a

theorem goodMass_pos
    (prob : State → ℝ) (eta : ℝ) (heta : eta < 1)
    (hgood : 1 - eta ≤ goodMass good prob) :
    0 < goodMass good prob := by
  linarith

theorem conditionedProb_nonneg
    (prob : State → ℝ) (hprob0 : ∀ a, 0 ≤ prob a)
    (hMass : 0 ≤ goodMass good prob) :
    ∀ a, 0 ≤ conditionedProb good prob a := by
  intro a
  unfold conditionedProb
  split
  · exact div_nonneg (hprob0 a) hMass
  · exact le_rfl

theorem conditionedProb_sum_one
    (prob : State → ℝ) (hMass : 0 < goodMass good prob) :
    ∑ a, conditionedProb good prob a = 1 := by
  calc
    (∑ a, conditionedProb good prob a) =
        ∑ a, (if good a then prob a else 0) / goodMass good prob := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : good a <;> simp [conditionedProb, ha]
    _ = goodMass good prob / goodMass good prob := by
      rw [← Finset.sum_div]
      rfl
    _ = 1 := div_self (ne_of_gt hMass)

theorem conditionedProb_good
    (prob : State → ℝ) (a : State)
    (hpos : 0 < conditionedProb good prob a) : good a := by
  by_contra hbad
  simp [conditionedProb, hbad] at hpos

theorem conditionalExpectation_upper
    (prob f : State → ℝ) (eta : ℝ) (heta : eta < 1)
    (hprob0 : ∀ a, 0 ≤ prob a)
    (hf0 : ∀ a, 0 ≤ f a)
    (hgood : 1 - eta ≤ goodMass good prob) :
    (∑ a, conditionedProb good prob a * f a) ≤
      (∑ a, prob a * f a) / (1 - eta) := by
  have hMass := goodMass_pos good prob eta heta hgood
  have hden : 0 < 1 - eta := by linarith
  have hnum0 : 0 ≤ ∑ a, prob a * f a :=
    Finset.sum_nonneg (fun a _ ↦ mul_nonneg (hprob0 a) (hf0 a))
  have hselected :
      (∑ a, if good a then prob a * f a else 0) ≤
        ∑ a, prob a * f a := by
    apply Finset.sum_le_sum
    intro a _
    split
    · exact le_rfl
    · exact mul_nonneg (hprob0 a) (hf0 a)
  have heq : (∑ a, conditionedProb good prob a * f a) =
      (∑ a, if good a then prob a * f a else 0) /
        goodMass good prob := by
    calc
      (∑ a, conditionedProb good prob a * f a) =
          ∑ a, (if good a then prob a * f a else 0) /
            goodMass good prob := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : good a
        · simp [conditionedProb, ha, div_mul_eq_mul_div]
        · simp [conditionedProb, ha]
      _ = _ := by rw [← Finset.sum_div]
  rw [heq]
  exact (div_le_div_of_nonneg_right hselected hMass.le).trans
    (div_le_div_of_nonneg_left hnum0 hden hgood)

/-- Conditioning loses at most `cap * eta` of an original bounded row
expectation.  The lower bound deliberately retains the original, unconditioned
edge marginal; no exact marginal equality is assumed after conditioning. -/
theorem conditionalExpectation_lower
    (prob f : State → ℝ) (cap eta : ℝ)
    (heta : eta < 1) (hcap0 : 0 ≤ cap)
    (hprob0 : ∀ a, 0 ≤ prob a)
    (hprobSum : ∑ a, prob a = 1)
    (hf0 : ∀ a, 0 ≤ f a)
    (hfCap : ∀ a, f a ≤ cap)
    (hgood : 1 - eta ≤ goodMass good prob) :
    (∑ a, prob a * f a) - cap * eta ≤
      ∑ a, conditionedProb good prob a * f a := by
  have hMass := goodMass_pos good prob eta heta hgood
  have hMass1 := goodMass_le_one good prob hprob0 hprobSum
  let G := ∑ a, if good a then prob a * f a else 0
  let B := ∑ a, if good a then 0 else prob a * f a
  let badMass := ∑ a, if good a then 0 else prob a
  have hpartition : G + B = ∑ a, prob a * f a := by
    dsimp [G, B]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : good a <;> simp [ha]
  have hmassPartition : goodMass good prob + badMass = 1 := by
    rw [← hprobSum]
    dsimp [goodMass, badMass]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : good a <;> simp [ha]
  have hbad : B ≤ cap * badMass := by
    dsimp [B, badMass]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : good a
    · simp [ha]
    · simp only [if_neg ha, mul_comm cap]
      exact mul_le_mul_of_nonneg_left (hfCap a) (hprob0 a)
  have hbadMass : badMass ≤ eta := by
    linarith
  have hB : B ≤ cap * eta :=
    hbad.trans (mul_le_mul_of_nonneg_left hbadMass hcap0)
  have hG0 : 0 ≤ G := by
    dsimp [G]
    apply Finset.sum_nonneg
    intro a _
    split
    · exact mul_nonneg (hprob0 a) (hf0 a)
    · exact le_rfl
  have hGE : (∑ a, prob a * f a) - cap * eta ≤ G := by
    linarith
  have heq : (∑ a, conditionedProb good prob a * f a) =
      G / goodMass good prob := by
    calc
      (∑ a, conditionedProb good prob a * f a) =
          ∑ a, (if good a then prob a * f a else 0) /
            goodMass good prob := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : good a
        · simp [conditionedProb, ha, div_mul_eq_mul_div]
        · simp [conditionedProb, ha]
      _ = _ := by rw [← Finset.sum_div]
  rw [heq]
  exact hGE.trans ((le_div_iff₀ hMass).2 (by
    nlinarith [mul_nonneg hG0 (sub_nonneg.mpr hMass1)]))

end WeightedEdgeColoring.FiniteCategoricalSelection
