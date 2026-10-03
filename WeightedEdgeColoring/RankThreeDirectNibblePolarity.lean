import WeightedEdgeColoring.RankThreeDirectNibbleLLL
import WeightedEdgeColoring.FiniteBernoulliMonotoneLopsided
import WeightedEdgeColoring.FiniteBernoulliTailMonotone
import WeightedEdgeColoring.FiniteBernoulliCylinderMonotone

/-!
# Polarity of the direct-nibble bad events

Conflict-pair events and upper-tail rows are increasing.  Coverage
lower-tail rows are decreasing.  This file packages those facts for the
support-refined monotone local lemma.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliHarris
open WeightedEdgeColoring.FiniteBernoulliMonotoneLopsided
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w x y z

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  {Conflict : Type x} {LowerRow : Type y} {UpperRow : Type z}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [Fintype Conflict] [Fintype LowerRow] [Fintype UpperRow]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  [DecidableEq Conflict] [DecidableEq LowerRow] [DecidableEq UpperRow]

/-- `true` for conflict and upper-tail events, `false` for lower tails. -/
def directNibblePolarity :
    DirectNibbleBadIndex Conflict LowerRow UpperRow → Bool
  | Sum.inl _ => true
  | Sum.inr (Sum.inl _) => false
  | Sum.inr (Sum.inr _) => true

theorem conflictPairLocalBad_isIncreasing
    (left right : Conflict → Option) (hne : ∀ c, left c ≠ right c)
    (c : Conflict) :
    IsIncreasing (conflictPairLocalBad left right hne c) := by
  intro S hS T hST
  simp only [conflictPairLocalBad, Finset.mem_filter, Finset.mem_univ,
    true_and] at hS ⊢
  exact ⟨hST hS.1, hST hS.2⟩

/-- Every local direct-nibble event has its declared polarity. -/
theorem directNibbleLocalBad_hasPolarity
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (lowerThreshold : LowerRow → ℝ)
    (upperThreshold : UpperRow → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (hlower0 : ∀ r o, 0 ≤ lowerWeight r o)
    (hupper0 : ∀ r o, 0 ≤ upperWeight r o)
    (b : DirectNibbleBadIndex Conflict LowerRow UpperRow) :
    HasPolarity (directNibblePolarity b)
      (directNibbleLocalBad left right lowerWeight upperWeight
        lowerThreshold upperThreshold hne b) := by
  rcases b with c | r
  · change IsIncreasing (conflictPairLocalBad left right hne c)
    exact conflictPairLocalBad_isIncreasing left right hne c
  · rcases r with r | r
    · change IsDecreasing
        (lowerTail
          (weightedSum
            (fun o : Inside (linearRowSupport lowerWeight r) ↦ lowerWeight r o))
          (lowerThreshold r))
      exact WeightedEdgeColoring.FiniteBernoulliTailMonotone.lowerTail_weightedSum_isDecreasing
        (fun o : Inside (linearRowSupport lowerWeight r) ↦ lowerWeight r o)
        (lowerThreshold r) (fun o ↦ hlower0 r o)
    · change IsIncreasing
        (upperTail
          (weightedSum
            (fun o : Inside (linearRowSupport upperWeight r) ↦ upperWeight r o))
          (upperThreshold r))
      exact WeightedEdgeColoring.FiniteBernoulliTailMonotone.upperTail_weightedSum_isIncreasing
        (fun o : Inside (linearRowSupport upperWeight r) ↦ upperWeight r o)
        (upperThreshold r) (fun o ↦ hupper0 r o)

/-- After lifting to the global Bernoulli space, direct-nibble events retain
their declared polarity. -/
theorem directNibbleGlobalBad_hasPolarity
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (lowerThreshold : LowerRow → ℝ)
    (upperThreshold : UpperRow → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (hlower0 : ∀ r o, 0 ≤ lowerWeight r o)
    (hupper0 : ∀ r o, 0 ≤ upperWeight r o)
    (b : DirectNibbleBadIndex Conflict LowerRow UpperRow) :
    HasPolarity (directNibblePolarity b)
      (insideCylinder
        (directNibbleSupport left right lowerWeight upperWeight b)
        (directNibbleLocalBad left right lowerWeight upperWeight
          lowerThreshold upperThreshold hne b)) := by
  have hlocal := directNibbleLocalBad_hasPolarity left right lowerWeight
    upperWeight lowerThreshold upperThreshold hne hlower0 hupper0 b
  cases hp : directNibblePolarity b
  · have hdec : IsDecreasing
        (directNibbleLocalBad left right lowerWeight upperWeight
          lowerThreshold upperThreshold hne b) := by
      simpa [HasPolarity, hp] using hlocal
    simpa [HasPolarity, hp] using
      (WeightedEdgeColoring.FiniteBernoulliCylinderMonotone.insideCylinder_isDecreasing
        (directNibbleSupport left right lowerWeight upperWeight b)
        (directNibbleLocalBad left right lowerWeight upperWeight
          lowerThreshold upperThreshold hne b) hdec)
  · have hinc : IsIncreasing
        (directNibbleLocalBad left right lowerWeight upperWeight
          lowerThreshold upperThreshold hne b) := by
      simpa [HasPolarity, hp] using hlocal
    simpa [HasPolarity, hp] using
      (WeightedEdgeColoring.FiniteBernoulliCylinderMonotone.insideCylinder_isIncreasing
        (directNibbleSupport left right lowerWeight upperWeight b)
        (directNibbleLocalBad left right lowerWeight upperWeight
          lowerThreshold upperThreshold hne b) hinc)

end WeightedEdgeColoring.RankThreeOptionSystem
