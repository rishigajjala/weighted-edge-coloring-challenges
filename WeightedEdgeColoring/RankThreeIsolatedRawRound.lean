import WeightedEdgeColoring.RankThreeIsolatedRawHarris
import WeightedEdgeColoring.RankThreeIsolatedRowTransfer

/-!
# Turning a raw Harris outcome into an isolated nibble round

This module joins the two independent parts of the isolated-raw argument.
The Harris lemma chooses a raw Bernoulli set with lower and upper linear-row
bounds and with a small quadratic isolation loss in every lower row.  Keeping
only isolated options gives a partial matching.  The quadratic margin pays
for everything deleted by isolation, while nonnegative upper rows can only
decrease.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliHarris
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w x y

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  {LowerRow : Type x} {UpperRow : Type y}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [Fintype LowerRow] [Fintype UpperRow]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  [DecidableEq LowerRow] [DecidableEq UpperRow]
  (H : RankThreeOptionSystem Job Slot Option)

/-- The inside-support sum used by the cylinder event is exactly the global
row sum, since every coordinate omitted from the support has coefficient
zero. -/
theorem weightedSum_linearRowSupport_eq_global_raw
    (weight : LowerRow → Option → ℝ) (r : LowerRow)
    (S : Finset Option) :
    weightedSum
        (fun o : Inside (linearRowSupport weight r) ↦ weight r o)
        (splitEquiv (linearRowSupport weight r) S).1 =
      weightedSum (weight r) S := by
  rw [weightedSum_splitEquiv_inside]
  unfold linearRowSupport weightedSum
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro o _ho
  by_cases hz : weight r o = 0 <;> simp [hz]

/-- Exact isolated-raw Harris round.  Pair conflicts are absent from the
local lemma.  Instead, one increasing quadratic event per lower row bounds
the amount removed by the final deterministic isolation step. -/
theorem exists_isolated_with_lower_and_upper_rows_harris
    (q : Option → ℝ)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (target lossThreshold lowerLambda : LowerRow → ℝ)
    (upperThreshold upperLambda : UpperRow → ℝ)
    (x : IsolatedRawBadIndex LowerRow UpperRow LowerRow → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hlower0 : ∀ r o, 0 ≤ lowerWeight r o)
    (hlower1 : ∀ r o, lowerWeight r o ≤ 1)
    (hupper0 : ∀ r o, 0 ≤ upperWeight r o)
    (hupper1 : ∀ r o, upperWeight r o ≤ 1)
    (hlowerLambda : ∀ r, 0 ≤ lowerLambda r)
    (hupperLambda : ∀ r, 0 ≤ upperLambda r)
    (hx0 : ∀ b, 0 ≤ x b) (hx1 : ∀ b, x b < 1)
    (hlower : ∀ r,
      Real.exp (lowerLambda r * (target r + lossThreshold r) +
        (Real.exp (-lowerLambda r) - 1) *
          linearRowMean q lowerWeight r) ≤
        x (Sum.inl (Sum.inr (Sum.inl r))) *
          ∏ b ∈ directNibbleExtraNeighbor
            (emptyOptionMap : Fin 0 → Option) emptyOptionMap
            lowerWeight upperWeight
            (fun s ↦ H.isolatedRowConflictSupport lowerWeight s)
            (Sum.inl (Sum.inr (Sum.inl r))), (1 - x b))
    (hupper : ∀ r,
      Real.exp (-upperLambda r * upperThreshold r +
        (Real.exp (upperLambda r) - 1) *
          linearRowMean q upperWeight r) ≤
        x (Sum.inl (Sum.inr (Sum.inr r))) *
          ∏ b ∈ directNibbleExtraNeighbor
            (emptyOptionMap : Fin 0 → Option) emptyOptionMap
            lowerWeight upperWeight
            (fun s ↦ H.isolatedRowConflictSupport lowerWeight s)
            (Sum.inl (Sum.inr (Sum.inr r))), (1 - x b))
    (hloss : ∀ r,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q
            (H.isolatedRowConflictSupport lowerWeight r)))
          (H.isolatedRowConflictLocalBad lowerWeight r (lossThreshold r)) ≤
        x (Sum.inr r) *
          ∏ b ∈ directNibbleExtraNeighbor
            (emptyOptionMap : Fin 0 → Option) emptyOptionMap
            lowerWeight upperWeight
            (fun s ↦ H.isolatedRowConflictSupport lowerWeight s)
            (Sum.inr r), (1 - x b)) :
    ∃ A : Finset Option,
      H.IsPartialMatching A ∧
      (∀ r, target r < weightedSum (lowerWeight r) A) ∧
      (∀ r, weightedSum (upperWeight r) A < upperThreshold r) := by
  have hextraIncreasing : ∀ r,
      IsIncreasing
        (H.isolatedRowConflictLocalBad lowerWeight r (lossThreshold r)) :=
    fun r ↦ H.isolatedRowConflictLocalBad_isIncreasing
      lowerWeight hlower0 r (lossThreshold r)
  rcases exists_raw_with_extra_increasing_harris
      q lowerWeight upperWeight
      (fun r ↦ target r + lossThreshold r) lowerLambda
      upperThreshold upperLambda
      (fun r ↦ H.isolatedRowConflictSupport lowerWeight r)
      (fun r ↦ H.isolatedRowConflictLocalBad
        lowerWeight r (lossThreshold r))
      hextraIncreasing x hq0 hq1 hlower0 hlower1 hupper0 hupper1
      hlowerLambda hupperLambda hx0 hx1 hlower hupper hloss with
    ⟨S, hrawLower, hrawUpper, hgoodLoss⟩
  refine ⟨H.isolatedOptions S, H.isolatedOptions_isPartialMatching S, ?_, ?_⟩
  · intro r
    apply H.target_lt_isolated_weightedSum_of_raw_and_not_localBad
      lowerWeight hlower0 r S (target r) (lossThreshold r)
    · rw [← weightedSum_linearRowSupport_eq_global_raw lowerWeight r S]
      exact hrawLower r
    · exact hgoodLoss r
  · intro r
    apply (H.isolated_weightedSum_le_raw (upperWeight r)
      (hupper0 r) S).trans_lt
    rw [← weightedSum_linearRowSupport_eq_global_raw upperWeight r S]
    exact hrawUpper r

end WeightedEdgeColoring.RankThreeOptionSystem
