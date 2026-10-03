import WeightedEdgeColoring.FiniteCategoricalSelection
import Mathlib.Analysis.Complex.Exponential

/-!
# A finite categorical Bernstein bound

This file turns the exponential-moment estimate for independent finite
categorical choices into a centered upper-tail bound.  The proof is entirely
finite: probability is represented by the product mass already used by the
finite local-lemma files.
-/

namespace WeightedEdgeColoring.FiniteCategoricalSelection

open scoped BigOperators

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- On the interval `[0,1]`, the exponential remainder is at most the square. -/
theorem exp_sub_one_sub_id_le_sq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 - x ≤ x ^ 2 := by
  have habs : |x| ≤ 1 := by simpa [abs_of_nonneg hx0] using hx1
  exact le_trans (le_abs_self (Real.exp x - 1 - x))
    (Real.abs_exp_sub_one_sub_id_le habs)

/-- Centered categorical Bernstein bound.  Every individual contribution is
in `[0,1]`; `M` is any positive upper bound on the row mean.  For
`0 ≤ t ≤ 2M`, the upper tail above `mean + t` has mass at most
`exp (-t²/(4M))`.

The constant is deliberately elementary.  It follows from
`exp λ - 1 - λ ≤ λ²` for `0 ≤ λ ≤ 1` and avoids any measure-theoretic
probability interface. -/
theorem categorical_centered_upperTail_mass_le
    (prob : Source → State → ℝ) (use : Source → State → Row → ℝ)
    (r : Row) (M t : ℝ)
    (hprob0 : ∀ s a, 0 ≤ prob s a)
    (hprobSum : ∀ s, ∑ a, prob s a = 1)
    (huse0 : ∀ s a r, 0 ≤ use s a r)
    (huse1 : ∀ s a r, use s a r ≤ 1)
    (hmeanM : rowMean prob use r ≤ M)
    (hM : 0 < M) (ht0 : 0 ≤ t) (htM : t ≤ 2 * M) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (categoricalMass prob)
        (badRow use (fun _ ↦ rowMean prob use r + t) r) ≤
      Real.exp (-(t ^ 2) / (4 * M)) := by
  let lambda : ℝ := t / (2 * M)
  have hmean0 : 0 ≤ rowMean prob use r := by
    unfold rowMean
    exact Finset.sum_nonneg fun s _ ↦
      Finset.sum_nonneg fun a _ ↦ mul_nonneg (hprob0 s a) (huse0 s a r)
  have hM0 : 0 ≤ M := hM.le
  have hden : 0 < 2 * M := mul_pos (by norm_num) hM
  have hlambda0 : 0 ≤ lambda := div_nonneg ht0 hden.le
  have hlambda1 : lambda ≤ 1 := by
    unfold lambda
    exact (div_le_one hden).2 htM
  have hrem0 : 0 ≤ Real.exp lambda - 1 - lambda := by
    linarith [Real.add_one_le_exp lambda]
  have hrem : Real.exp lambda - 1 - lambda ≤ lambda ^ 2 :=
    exp_sub_one_sub_id_le_sq hlambda0 hlambda1
  calc
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (categoricalMass prob)
        (badRow use (fun _ ↦ rowMean prob use r + t) r) ≤
        Real.exp (-lambda * (rowMean prob use r + t) +
          (Real.exp lambda - 1) * rowMean prob use r) :=
      categorical_badRow_mass_le prob use
        (fun _ ↦ rowMean prob use r + t) r lambda
        hprob0 hprobSum huse0 huse1 hlambda0
    _ ≤ Real.exp (-lambda * t + lambda ^ 2 * M) := by
      apply Real.exp_le_exp.mpr
      calc
        -lambda * (rowMean prob use r + t) +
            (Real.exp lambda - 1) * rowMean prob use r =
            -lambda * t +
              (Real.exp lambda - 1 - lambda) * rowMean prob use r := by ring
        _ ≤ -lambda * t +
              (Real.exp lambda - 1 - lambda) * M := by
          gcongr
        _ ≤ -lambda * t + lambda ^ 2 * M := by
          gcongr
    _ = Real.exp (-(t ^ 2) / (4 * M)) := by
      congr 1
      unfold lambda
      field_simp
      ring

end WeightedEdgeColoring.FiniteCategoricalSelection
