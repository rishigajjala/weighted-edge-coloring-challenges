import WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
import WeightedEdgeColoring.FinitePartialResamplingTreeWeights

/-!
# The coarse charge criterion controls every finite witness-tree depth

This file joins the finite neighbor-polynomial calculation to the generic
finite-depth rooted-tree bound.  For the coarse conflict relation, the local
child-set sum in the tree theorem is exactly `neighborPolynomial`.  The
already proved root-weight inequality therefore supplies the local
hypothesis of the tree induction with no additional assumption.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingCoarseCriterion

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential
open WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
open WeightedEdgeColoring.FinitePartialResamplingTreeWeights

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- The child-set product used by the generic tree theorem is the monomial
used in the coarse neighbor polynomial. -/
theorem properChildrenProductSum_eq_neighborPolynomial
    (mu : Label Source State Row → ℝ)
    (root : Label Source State Row) :
    (∑ childset : Finset (Label Source State Row),
      if ProperChildren root childset then
        ∏ child : ↥childset, mu child.1
      else 0) =
        neighborPolynomial mu root := by
  classical
  unfold neighborPolynomial properChildFinsets
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro childset _hchildset
  by_cases hproper : ProperChildren root childset
  · simp only [hproper, if_true]
    unfold childMonomial
    simpa using (Finset.prod_coe_sort childset mu)
  · simp [hproper]

/-- A product of nonnegative categorical masses over a partial assignment is
nonnegative. -/
theorem partialLambdaProduct_nonneg
    {p : Source → State → ℝ} (hp : ∀ i j, 0 ≤ p i j)
    (Y : PartialAssignment Source State) :
    0 ≤ partialLambdaProduct p Y := by
  unfold partialLambdaProduct partialProduct
  apply Finset.prod_nonneg
  intro i _hi
  cases hYi : Y i with
  | none => simp [hYi]
  | some j => simpa [hYi] using hp i j

/-- The root factor used in the coarse tree expansion is nonnegative. -/
theorem coarseRootBase_nonneg
    {q : Row → PartialAssignment Source State → ℝ}
    {p : Source → State → ℝ}
    (hq : ∀ r Y, 0 ≤ q r Y) (hp : ∀ i j, 0 ≤ p i j)
    (root : Label Source State Row) :
    0 ≤ q root.1 root.2 * partialLambdaProduct p root.2 := by
  exact mul_nonneg (hq root.1 root.2)
    (partialLambdaProduct_nonneg hp root.2)

/-- Every finite-depth total of proper coarse witness trees is bounded by the
standard coarse charge. -/
theorem totalProperTreeWeight_coarse_le
    {q : Row → PartialAssignment Source State → ℝ}
    {p lambda : Source → State → ℝ}
    (hq : ∀ r Y, 0 ≤ q r Y) (hp : ∀ i j, 0 ≤ p i j)
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (hscale : ∀ i j, lambda i j = lambdaTotal lambda i * p i j)
    (hself : ∀ r, coarseSelfCharge q lambda r < 1)
    (hsource : ∀ i,
      (∑ r, coarseSourceCharge q lambda r i /
        (1 - coarseSelfCharge q lambda r)) ≤ lambdaTotal lambda i - 1)
    (depth : Nat) (root : Label Source State Row) :
    totalProperTreeWeight
        (ProperChildren (Source := Source) (State := State) (Row := Row))
        (fun a : Label Source State Row ↦
          q a.1 a.2 * partialLambdaProduct p a.2)
        depth root ≤
      coarseMu q lambda root := by
  refine totalProperTreeWeight_le_mu
    (ProperChildren (Source := Source) (State := State) (Row := Row))
    (base := fun a : Label Source State Row ↦
      q a.1 a.2 * partialLambdaProduct p a.2)
    (mu := coarseMu q lambda) ?_ ?_ ?_ depth root
  · exact coarseRootBase_nonneg hq hp
  · exact coarseMu_nonneg hq hlambda hself
  · intro a
    rw [properChildrenProductSum_eq_neighborPolynomial]
    exact rootWeight_mul_neighborPolynomial_le_coarseMu
      hq hp hlambda hscale hself hsource a

end WeightedEdgeColoring.FinitePartialResamplingCoarseCriterion
