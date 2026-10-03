import WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
import WeightedEdgeColoring.FinitePartialResamplingTreeWeights
import WeightedEdgeColoring.FinitePartialResamplingCoarseCriterion

/-!
# A finite numerical budget for coarse witness trees

The per-root tree estimate can be summed over the finite label type.  Its
right-hand side is the total coarse charge `M`.  The natural number
`floor M + 1` is strictly larger than `M` and is positive, so it has exactly
the two numerical properties required as a horizon in the finite witness
counting lemma.

This file proves only these finite sums and inequalities.  It makes no claim
that a resampling history or a witness map exists.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingTreeBudget

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential
open WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
open WeightedEdgeColoring.FinitePartialResamplingTreeWeights
open WeightedEdgeColoring.FinitePartialResamplingCoarseCriterion

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- Sum of the coarse charges over the finite witness-label type. -/
noncomputable def coarseMuTotal
    (q : Row → PartialAssignment Source State → ℝ)
    (lambda : Source → State → ℝ) : ℝ :=
  ∑ root : Label Source State Row, coarseMu q lambda root

/-- Sum, over all possible root labels, of the proper-tree weights at one
finite depth. -/
noncomputable def coarseDepthTreeBudget
    (q : Row → PartialAssignment Source State → ℝ)
    (p : Source → State → ℝ) (depth : Nat) : ℝ :=
  ∑ root : Label Source State Row,
    totalProperTreeWeight
      (ProperChildren (Source := Source) (State := State) (Row := Row))
      (fun a : Label Source State Row ↦
        q a.1 a.2 * partialLambdaProduct p a.2)
      depth root

/-- The full finite-depth tree budget is bounded by the sum of the coarse
charges. -/
theorem coarseDepthTreeBudget_le_coarseMuTotal
    {q : Row → PartialAssignment Source State → ℝ}
    {p lambda : Source → State → ℝ}
    (hq : ∀ r Y, 0 ≤ q r Y) (hp : ∀ i j, 0 ≤ p i j)
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (hscale : ∀ i j, lambda i j = lambdaTotal lambda i * p i j)
    (hself : ∀ r, coarseSelfCharge q lambda r < 1)
    (hsource : ∀ i,
      (∑ r, coarseSourceCharge q lambda r i /
        (1 - coarseSelfCharge q lambda r)) ≤ lambdaTotal lambda i - 1)
    (depth : Nat) :
    coarseDepthTreeBudget q p depth ≤ coarseMuTotal q lambda := by
  unfold coarseDepthTreeBudget coarseMuTotal
  exact Finset.sum_le_sum fun root _hroot ↦
    totalProperTreeWeight_coarse_le hq hp hlambda hscale hself hsource
      depth root

/-- The total coarse charge is nonnegative. -/
theorem coarseMuTotal_nonneg
    {q : Row → PartialAssignment Source State → ℝ}
    {lambda : Source → State → ℝ}
    (hq : ∀ r Y, 0 ≤ q r Y)
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (hself : ∀ r, coarseSelfCharge q lambda r < 1) :
    0 ≤ coarseMuTotal q lambda := by
  unfold coarseMuTotal
  exact Finset.sum_nonneg fun root _hroot ↦
    coarseMu_nonneg hq hlambda hself root

/-- The strict natural budget attached to a real finite total. -/
noncomputable def strictFloorBudget (M : ℝ) : Nat :=
  Nat.floor M + 1

/-- `floor M + 1` is strictly larger than `M` and is a positive natural
number.  The nonnegativity assumption records the range in which this budget
is used, although the two conclusions themselves hold for every real `M`. -/
theorem strictFloorBudget_spec (M : ℝ) (_hM : 0 ≤ M) :
    M < (strictFloorBudget M : ℝ) ∧ 0 < strictFloorBudget M := by
  constructor
  · unfold strictFloorBudget
    simpa using (Nat.lt_floor_add_one M)
  · simp [strictFloorBudget]

/-- Natural witness horizon obtained from the total coarse charge. -/
noncomputable def coarseWitnessHorizon
    (q : Row → PartialAssignment Source State → ℝ)
    (lambda : Source → State → ℝ) : Nat :=
  strictFloorBudget (coarseMuTotal q lambda)

/-- The total coarse charge is strictly below its natural witness horizon,
and that horizon is positive. -/
theorem coarseWitnessHorizon_spec
    {q : Row → PartialAssignment Source State → ℝ}
    {lambda : Source → State → ℝ}
    (hq : ∀ r Y, 0 ≤ q r Y)
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (hself : ∀ r, coarseSelfCharge q lambda r < 1) :
    coarseMuTotal q lambda < (coarseWitnessHorizon q lambda : ℝ) ∧
      0 < coarseWitnessHorizon q lambda := by
  unfold coarseWitnessHorizon
  exact strictFloorBudget_spec (coarseMuTotal q lambda)
    (coarseMuTotal_nonneg hq hlambda hself)

/-- Exact numerical inputs for finite witness counting: the complete
depth-`depth` proper-tree budget is below a positive natural horizon. -/
theorem coarseDepthTreeBudget_lt_horizon_and_pos
    {q : Row → PartialAssignment Source State → ℝ}
    {p lambda : Source → State → ℝ}
    (hq : ∀ r Y, 0 ≤ q r Y) (hp : ∀ i j, 0 ≤ p i j)
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (hscale : ∀ i j, lambda i j = lambdaTotal lambda i * p i j)
    (hself : ∀ r, coarseSelfCharge q lambda r < 1)
    (hsource : ∀ i,
      (∑ r, coarseSourceCharge q lambda r i /
        (1 - coarseSelfCharge q lambda r)) ≤ lambdaTotal lambda i - 1)
    (depth : Nat) :
    coarseDepthTreeBudget q p depth <
        (coarseWitnessHorizon q lambda : ℝ) ∧
      0 < coarseWitnessHorizon q lambda := by
  have htree := coarseDepthTreeBudget_le_coarseMuTotal hq hp hlambda
    hscale hself hsource depth
  have hhorizon := coarseWitnessHorizon_spec hq hlambda hself
  exact ⟨htree.trans_lt hhorizon.1, hhorizon.2⟩

end WeightedEdgeColoring.FinitePartialResamplingTreeBudget
