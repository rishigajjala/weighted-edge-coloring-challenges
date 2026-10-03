import WeightedEdgeColoring.FiniteBernoulliChernoff
import WeightedEdgeColoring.FiniteProductCylinder

/-!
# Finite categorical-product selection

Each finite source independently chooses one state.  This file proves the
normalization and Chernoff estimate for the resulting categorical product
mass, then gives simultaneous row-selection corollaries by a union bound and
by the finite lopsided local lemma.

The local-lemma theorem states its division-free conditioning hypothesis
explicitly.  A separate support lemma proves that a row overload event only
depends on sources that can contribute to that row.  Thus a later application
only has to turn disjoint source supports into the stated conditioning bound.
-/

namespace WeightedEdgeColoring.FiniteCategoricalSelection

open scoped BigOperators

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- Product mass of a complete choice of one state per source. -/
def categoricalMass (prob : Source → State → ℝ) (choice : Source → State) : ℝ :=
  ∏ s, prob s (choice s)

/-- Load placed on one row by a complete categorical choice. -/
def rowLoad (use : Source → State → Row → ℝ)
    (r : Row) (choice : Source → State) : ℝ :=
  ∑ s, use s (choice s) r

/-- Fractional mean load of one row. -/
def rowMean (prob : Source → State → ℝ)
    (use : Source → State → Row → ℝ) (r : Row) : ℝ :=
  ∑ s, ∑ a, prob s a * use s a r

/-- Choices whose load on a row is at least its forbidden threshold. -/
noncomputable def badRow (use : Source → State → Row → ℝ)
    (threshold : Row → ℝ) (r : Row) : Finset (Source → State) :=
  Finset.univ.filter fun choice ↦ threshold r ≤ rowLoad use r choice

/-- Sources that can make a nonzero contribution to a row. -/
noncomputable def rowSupport (use : Source → State → Row → ℝ) (r : Row) : Finset Source :=
  Finset.univ.filter fun s ↦ ∃ a, use s a r ≠ 0

/-- An event is determined by the choices on a specified source set. -/
def DependsOn (K : Finset Source) (event : Finset (Source → State)) : Prop :=
  ∀ x y, (∀ s ∈ K, x s = y s) → (x ∈ event ↔ y ∈ event)

theorem categoricalMass_nonneg (prob : Source → State → ℝ)
    (hprob0 : ∀ s a, 0 ≤ prob s a) (choice : Source → State) :
    0 ≤ categoricalMass prob choice := by
  exact Finset.prod_nonneg fun s _ ↦ hprob0 s (choice s)

theorem sum_categoricalMass (prob : Source → State → ℝ)
    (hprobSum : ∀ s, ∑ a, prob s a = 1) :
    ∑ choice : Source → State, categoricalMass prob choice = 1 := by
  unfold categoricalMass
  rw [← Fintype.prod_sum]
  simp [hprobSum]

private theorem exp_mul_le_secant {lambda a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.exp (lambda * a) ≤ 1 + a * (Real.exp lambda - 1) := by
  have hconvex := convexOn_exp.2 (Set.mem_univ lambda) (Set.mem_univ 0)
    ha0 (sub_nonneg.mpr ha1) (by ring : a + (1 - a) = 1)
  have hconvex' : Real.exp (lambda * a) ≤
      a * Real.exp lambda + (1 - a) := by
    simpa [smul_eq_mul, mul_comm] using hconvex
  linarith

private theorem categorical_mgf_exact
    (prob : Source → State → ℝ) (use : Source → State → Row → ℝ)
    (r : Row) (lambda : ℝ) :
    (∑ choice : Source → State,
        categoricalMass prob choice * Real.exp (lambda * rowLoad use r choice)) =
      ∏ s, ∑ a, prob s a * Real.exp (lambda * use s a r) := by
  classical
  unfold categoricalMass rowLoad
  simp only [Finset.mul_sum, Real.exp_sum]
  calc
    (∑ choice : Source → State,
        (∏ s, prob s (choice s)) *
          ∏ s, Real.exp (lambda * use s (choice s) r)) =
        ∑ choice : Source → State,
          ∏ s, prob s (choice s) * Real.exp (lambda * use s (choice s) r) := by
      apply Finset.sum_congr rfl
      intro choice _
      rw [Finset.prod_mul_distrib]
    _ = _ := (Fintype.prod_sum
      (fun s a ↦ prob s a * Real.exp (lambda * use s a r))).symm

/-- Categorical-product exponential-moment estimate. -/
theorem categorical_mgf_le
    (prob : Source → State → ℝ) (use : Source → State → Row → ℝ)
    (r : Row) (lambda : ℝ)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huse1 : ∀ s a r, use s a r ≤ 1) :
    (∑ choice : Source → State,
        categoricalMass prob choice * Real.exp (lambda * rowLoad use r choice)) ≤
      Real.exp ((Real.exp lambda - 1) * rowMean prob use r) := by
  rw [categorical_mgf_exact]
  calc
    (∏ s, ∑ a, prob s a * Real.exp (lambda * use s a r)) ≤
        ∏ s, Real.exp ((Real.exp lambda - 1) *
          ∑ a, prob s a * use s a r) := by
      apply Finset.prod_le_prod
      · intro s _
        exact Finset.sum_nonneg fun a _ ↦
          mul_nonneg (hprob0 s a) (Real.exp_pos _).le
      · intro s _
        calc
          (∑ a, prob s a * Real.exp (lambda * use s a r)) ≤
              ∑ a, prob s a *
                (1 + use s a r * (Real.exp lambda - 1)) := by
            apply Finset.sum_le_sum
            intro a _
            exact mul_le_mul_of_nonneg_left
              (exp_mul_le_secant (huse0 s a r) (huse1 s a r))
              (hprob0 s a)
          _ = 1 + (Real.exp lambda - 1) *
                ∑ a, prob s a * use s a r := by
            calc
              (∑ a, prob s a *
                  (1 + use s a r * (Real.exp lambda - 1))) =
                  ∑ a, (prob s a +
                    (Real.exp lambda - 1) * (prob s a * use s a r)) := by
                apply Finset.sum_congr rfl
                intro a _
                ring
              _ = (∑ a, prob s a) +
                    ∑ a, (Real.exp lambda - 1) *
                      (prob s a * use s a r) := Finset.sum_add_distrib
              _ = 1 + (Real.exp lambda - 1) *
                    ∑ a, prob s a * use s a r := by
                rw [hprobSum, Finset.mul_sum]
          _ ≤ Real.exp ((Real.exp lambda - 1) *
                ∑ a, prob s a * use s a r) := by
            simpa [add_comm] using Real.add_one_le_exp
              ((Real.exp lambda - 1) * ∑ a, prob s a * use s a r)
    _ = Real.exp ((Real.exp lambda - 1) * rowMean prob use r) := by
      rw [← Real.exp_sum]
      congr 1
      simp [rowMean, Finset.mul_sum]

/-- Chernoff upper tail for a categorical product. -/
theorem categorical_badRow_mass_le
    (prob : Source → State → ℝ) (use : Source → State → Row → ℝ)
    (threshold : Row → ℝ) (r : Row) (lambda : ℝ)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huse1 : ∀ s a r, use s a r ≤ 1)
    (hlambda : 0 ≤ lambda) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (categoricalMass prob)
        (badRow use threshold r) ≤
      Real.exp (-lambda * threshold r +
        (Real.exp lambda - 1) * rowMean prob use r) := by
  change WeightedEdgeColoring.FiniteLocalLemma.eventMass (categoricalMass prob)
      (WeightedEdgeColoring.FiniteBernoulliChernoff.upperTail
        (rowLoad use r) (threshold r)) ≤ _
  calc
    _ ≤ Real.exp (-lambda * threshold r) *
        ∑ choice, categoricalMass prob choice *
          Real.exp (lambda * rowLoad use r choice) :=
      WeightedEdgeColoring.FiniteBernoulliChernoff.exponential_markov _ _ _ _
        (categoricalMass_nonneg prob hprob0) hlambda
    _ ≤ Real.exp (-lambda * threshold r) *
        Real.exp ((Real.exp lambda - 1) * rowMean prob use r) :=
      mul_le_mul_of_nonneg_left
        (categorical_mgf_le prob use r lambda hprob0 hprobSum huse0 huse1)
        (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

/-- The overload event for a row only depends on its source support. -/
theorem badRow_dependsOn_rowSupport
    (use : Source → State → Row → ℝ) (threshold : Row → ℝ) (r : Row) :
    DependsOn (rowSupport use r) (badRow use threshold r) := by
  intro x y hxy
  have hload : rowLoad use r x = rowLoad use r y := by
    unfold rowLoad
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : s ∈ rowSupport use r
    · rw [hxy s hs]
    · have hall : ∀ a, use s a r = 0 := by
        intro a
        by_contra ha
        apply hs
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, ⟨a, ha⟩⟩
      rw [hall (x s), hall (y s)]
  simp [badRow, hload]

/-- Simultaneous categorical selection by the finite union bound. -/
theorem exists_choice_rowLoad_lt_of_sum_chernoff_lt_one
    (prob : Source → State → ℝ) (use : Source → State → Row → ℝ)
    (threshold lambda : Row → ℝ)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huse1 : ∀ s a r, use s a r ≤ 1)
    (hlambda : ∀ r, 0 ≤ lambda r)
    (hsmall : (∑ r, Real.exp (-lambda r * threshold r +
      (Real.exp (lambda r) - 1) * rowMean prob use r)) < 1) :
    ∃ choice : Source → State, ∀ r, rowLoad use r choice < threshold r := by
  obtain ⟨choice, hchoice⟩ :=
    WeightedEdgeColoring.FiniteLocalLemma.exists_avoids_of_sum_bounds_lt_one
      (categoricalMass_nonneg prob hprob0)
      (sum_categoricalMass prob hprobSum)
      (badRow use threshold)
      (fun r ↦ Real.exp (-lambda r * threshold r +
        (Real.exp (lambda r) - 1) * rowMean prob use r))
      (fun r ↦ categorical_badRow_mass_le prob use threshold r (lambda r)
        hprob0 hprobSum huse0 huse1 (hlambda r)) hsmall
  refine ⟨choice, ?_⟩
  intro r
  simpa [badRow, rowLoad, not_le] using hchoice r

/-- Symmetric lopsided-LLL categorical selection.  The final hypothesis is
the exact division-free conditional estimate; support splitting can be used
to establish it when non-neighbour events use disjoint source coordinates. -/
theorem exists_choice_rowLoad_lt_of_lopsided_local_lemma
    (prob : Source → State → ℝ) (use : Source → State → Row → ℝ)
    (threshold : Row → ℝ) (neighbor : Row → Finset Row)
    (lambda : Row → ℝ) (p x : ℝ) (d : ℕ)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huse1 : ∀ s a r, use s a r ≤ 1)
    (hlambda : ∀ r, 0 ≤ lambda r)
    (hdegree : ∀ r, (neighbor r).card ≤ d)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hnumeric : p ≤ x * (1 - x) ^ d)
    (hchernoff : ∀ r, Real.exp (-lambda r * threshold r +
      (Real.exp (lambda r) - 1) * rowMean prob use r) ≤ p)
    (hindependent : ∀ (r : Row) (T : Finset Row),
      T ⊆ Finset.univ \ insert r (neighbor r) →
      WeightedEdgeColoring.FiniteProductCylinder.IndependentEvents (categoricalMass prob)
        (badRow use threshold r)
        (WeightedEdgeColoring.FiniteLocalLemma.avoid (badRow use threshold) T)) :
    ∃ choice : Source → State, ∀ r, rowLoad use r choice < threshold r := by
  have hpositive :=
    WeightedEdgeColoring.FiniteProductCylinder.symmetric_lopsided_local_lemma_of_independent
    (categoricalMass prob) (badRow use threshold) neighbor p x d
    (categoricalMass_nonneg prob hprob0)
    (sum_categoricalMass prob hprobSum) hdegree hx0 hx1 hnumeric
    (fun r ↦ (categorical_badRow_mass_le prob use threshold r (lambda r)
      hprob0 hprobSum huse0 huse1 (hlambda r)).trans (hchernoff r))
    hindependent
  have hnonempty :
      (WeightedEdgeColoring.FiniteLocalLemma.avoid (badRow use threshold)
        Finset.univ).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hpositive
    simp [WeightedEdgeColoring.FiniteLocalLemma.eventMass] at hpositive
  obtain ⟨choice, hchoice⟩ := hnonempty
  refine ⟨choice, ?_⟩
  intro r
  have hall := hchoice
  simp only [WeightedEdgeColoring.FiniteLocalLemma.avoid, Finset.mem_filter,
    Finset.mem_univ, true_and] at hall
  have hav := hall r trivial
  simpa [badRow, rowLoad, not_le] using hav

end WeightedEdgeColoring.FiniteCategoricalSelection
