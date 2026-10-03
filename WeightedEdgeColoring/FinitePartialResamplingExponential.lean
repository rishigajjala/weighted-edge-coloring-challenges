import WeightedEdgeColoring.FiniteCategoricalBernstein

/-!
# Exponential fractional hitting weights for assignment packing

This file develops the elementary finite-product part of a partial-resampling
proof for categorical packing constraints.  A partial assignment chooses
either no state or one state at every source.  Giving a nonempty partial
assignment `Y` the (uncapped) weight

`prod_{(i,j) in Y} (exp (theta * a i j) - 1) / (exp (theta * b) - 1)`

has two useful features.

* If a complete assignment has row load at least `b`, the weights of its
  nonempty compatible partial assignments sum to at least one.
* Under an inflated fractional assignment `lambda`, both the total charge and
  the charge through one source factor into finite products.  Convexity of the
  exponential then bounds them by the physical row and column masses.

These facts replace the fixed-cardinality elementary-symmetric-polynomial
construction in Harris--Srinivasan.  They are purely finite and make no
probabilistic or algorithmic assumption.  The separate witness-tree theorem
needed to turn the charges into a simultaneous integral assignment is not
asserted here.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingExponential

open scoped BigOperators

variable {Source State : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]

/-- A partial categorical assignment selects zero or one state at each source. -/
abbrev PartialAssignment (Source State : Type*) := Source → Option State

/-- The empty partial assignment. -/
def emptyPartial : PartialAssignment Source State := fun _ ↦ none

/-- Product of local terms over a partial assignment. -/
def partialProduct (term : Source → State → ℝ)
    (Y : PartialAssignment Source State) : ℝ :=
  ∏ i, match Y i with
    | none => 1
    | some j => term i j

/-- A partial assignment is compatible with a complete assignment when every
state mentioned by the partial assignment is the current state. -/
def Compatible (Y : PartialAssignment Source State) (z : Source → State) : Prop :=
  ∀ i j, Y i = some j → z i = j

instance compatibleDecidable (Y : PartialAssignment Source State)
    (z : Source → State) : Decidable (Compatible Y z) := by
  unfold Compatible
  infer_instance

/-- The exponential local factor used in the hitting weight. -/
noncomputable def expKernel (theta : ℝ) (a : Source → State → ℝ)
    (i : Source) (j : State) : ℝ :=
  Real.exp (theta * a i j) - 1

/-- Uncapped exponential hitting weight.  The empty partial assignment has
weight zero.  Allowing a weight above one is harmless: the partial-resampling
selection normalizes all eligible weights, and every proof only needs
nonnegativity and total eligible weight at least one. -/
noncomputable def expHittingWeight (theta threshold : ℝ)
    (a : Source → State → ℝ) (Y : PartialAssignment Source State) : ℝ :=
  if Y = emptyPartial then 0
  else partialProduct (expKernel theta a) Y /
    (Real.exp (theta * threshold) - 1)

/-- Product of the `lambda`-mass and the exponential kernel on a partial
assignment. -/
noncomputable def expChargeProduct (theta : ℝ)
    (a lambda : Source → State → ℝ)
    (Y : PartialAssignment Source State) : ℝ :=
  partialProduct (fun i j ↦ lambda i j * expKernel theta a i j) Y

/-- Product of an arbitrary categorical mass vector over a partial
assignment. -/
def partialLambdaProduct (lambda : Source → State → ℝ)
    (Y : PartialAssignment Source State) : ℝ :=
  partialProduct lambda Y

/-- Self charge of one threshold row. -/
noncomputable def expSelfCharge (theta threshold : ℝ)
    (a lambda : Source → State → ℝ) : ℝ :=
  ∑ Y : PartialAssignment Source State,
    expHittingWeight theta threshold a Y * partialLambdaProduct lambda Y

/-- Charge of one threshold row through one source. -/
noncomputable def expSourceCharge (theta threshold : ℝ)
    (a lambda : Source → State → ℝ) (i : Source) : ℝ :=
  ∑ Y : PartialAssignment Source State,
    if Y i = none then 0
    else expHittingWeight theta threshold a Y * partialLambdaProduct lambda Y

/-- Weighted mean of one row under a categorical mass vector. -/
def weightedMean (lambda a : Source → State → ℝ) : ℝ :=
  ∑ i, ∑ j, lambda i j * a i j

/-- The part of a row mean carried by one source. -/
def sourceMean (lambda a : Source → State → ℝ) (i : Source) : ℝ :=
  ∑ j, lambda i j * a i j

/-- Sum of the local factors over one optional coordinate. -/
@[simp] theorem sum_optionTerm (term : Source → State → ℝ) (i : Source) :
    (∑ o : Option State, match o with
      | none => 1
      | some j => term i j) = 1 + ∑ j, term i j := by
  rw [Fintype.sum_option]

/-- Finite product expansion over all partial assignments. -/
theorem sum_partialProduct (term : Source → State → ℝ) :
    (∑ Y : PartialAssignment Source State, partialProduct term Y) =
      ∏ i, (1 + ∑ j, term i j) := by
  unfold partialProduct
  calc
    (∑ Y : Source → Option State,
        ∏ i, match Y i with
          | none => 1
          | some j => term i j) =
        ∏ i, ∑ o : Option State, match o with
          | none => 1
          | some j => term i j :=
      (Fintype.prod_sum (ι := Source) (κ := fun _ ↦ Option State)
        (R := ℝ) (fun i o ↦ match o with
          | none => 1
          | some j => term i j)).symm
    _ = ∏ i, (1 + ∑ j, term i j) := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact sum_optionTerm term i

@[simp] theorem partialProduct_empty (term : Source → State → ℝ) :
    partialProduct term (emptyPartial : PartialAssignment Source State) = 1 := by
  simp [partialProduct, emptyPartial]

/-- Removing the empty partial assignment subtracts exactly one from the
finite product expansion. -/
theorem sum_partialProduct_ne_empty (term : Source → State → ℝ) :
    (∑ Y : PartialAssignment Source State,
        if Y = emptyPartial then 0 else partialProduct term Y) =
      (∏ i, (1 + ∑ j, term i j)) - 1 := by
  classical
  let e : PartialAssignment Source State := emptyPartial
  have he : e ∈ (Finset.univ : Finset (PartialAssignment Source State)) :=
    Finset.mem_univ _
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset (PartialAssignment Source State)))
    (f := partialProduct term) he
  rw [sum_partialProduct] at hsplit
  rw [partialProduct_empty] at hsplit
  calc
    (∑ Y : PartialAssignment Source State,
        if Y = emptyPartial then 0 else partialProduct term Y) =
        ∑ Y ∈ (Finset.univ.erase e), partialProduct term Y := by
          have hzero : (if e = emptyPartial then 0 else partialProduct term e) = 0 := by
            simp [e]
          rw [← Finset.sum_erase (s := Finset.univ)
            (f := fun Y ↦ if Y = emptyPartial then 0 else partialProduct term Y) hzero]
          apply Finset.sum_congr rfl
          intro Y hY
          have hne : Y ≠ e := Finset.ne_of_mem_erase hY
          simp [e] at hne
          simp [hne]
    _ = (∏ i, (1 + ∑ j, term i j)) - 1 := by linarith

/-- Local terms which retain only partial assignments compatible with `z`. -/
def compatibleTerm (z : Source → State) (term : Source → State → ℝ)
    (i : Source) (o : Option State) : ℝ :=
  match o with
  | none => 1
  | some j => if z i = j then term i j else 0

theorem partialProduct_compatibleTerm
    (z : Source → State) (term : Source → State → ℝ)
    (Y : PartialAssignment Source State) :
    (∏ i, compatibleTerm z term i (Y i)) =
      if Compatible Y z then partialProduct term Y else 0 := by
  classical
  by_cases hcompat : Compatible Y z
  · rw [if_pos hcompat]
    unfold partialProduct compatibleTerm
    apply Finset.prod_congr rfl
    intro i _hi
    cases hYi : Y i with
    | none => simp
    | some j =>
        have hz : z i = j := hcompat i j hYi
        simp [hYi, hz]
  · rw [if_neg hcompat]
    have hfailure : ∃ i j, Y i = some j ∧ z i ≠ j := by
      simpa [Compatible] using hcompat
    obtain ⟨i, j, hYi, hz⟩ := hfailure
    have hi : i ∈ (Finset.univ : Finset Source) := Finset.mem_univ _
    apply Finset.prod_eq_zero hi
    simp [compatibleTerm, hYi, hz]

/-- Exact expansion over partial assignments compatible with one complete
assignment. -/
theorem sum_compatible_partialProduct
    (z : Source → State) (term : Source → State → ℝ) :
    (∑ Y : PartialAssignment Source State,
        if Compatible Y z then partialProduct term Y else 0) =
      ∏ i, (1 + term i (z i)) := by
  classical
  calc
    (∑ Y : PartialAssignment Source State,
        if Compatible Y z then partialProduct term Y else 0) =
        ∑ Y : PartialAssignment Source State,
          ∏ i, compatibleTerm z term i (Y i) := by
            apply Finset.sum_congr rfl
            intro Y _hY
            exact (partialProduct_compatibleTerm z term Y).symm
    _ = ∏ i, ∑ o : Option State, compatibleTerm z term i o :=
      (Fintype.prod_sum (ι := Source) (κ := fun _ ↦ Option State)
        (R := ℝ) (compatibleTerm z term)).symm
    _ = ∏ i, (1 + term i (z i)) := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [Fintype.sum_option]
      simp [compatibleTerm]

/-- Exact compatible expansion after deleting the empty partial assignment. -/
theorem sum_compatible_partialProduct_ne_empty
    (z : Source → State) (term : Source → State → ℝ) :
    (∑ Y : PartialAssignment Source State,
        if Y = emptyPartial then 0
        else if Compatible Y z then partialProduct term Y else 0) =
      (∏ i, (1 + term i (z i))) - 1 := by
  classical
  let f : PartialAssignment Source State → ℝ := fun Y ↦
    if Compatible Y z then partialProduct term Y else 0
  have hsum : (∑ Y, f Y) = ∏ i, (1 + term i (z i)) := by
    simpa [f] using sum_compatible_partialProduct z term
  have hempty : f (emptyPartial : PartialAssignment Source State) = 1 := by
    simp [f, Compatible, emptyPartial]
  let e : PartialAssignment Source State := emptyPartial
  have he : e ∈ (Finset.univ : Finset (PartialAssignment Source State)) :=
    Finset.mem_univ _
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset (PartialAssignment Source State)))
    (f := f) he
  rw [hsum, hempty] at hsplit
  calc
    (∑ Y : PartialAssignment Source State,
        if Y = emptyPartial then 0
        else if Compatible Y z then partialProduct term Y else 0) =
        ∑ Y ∈ (Finset.univ.erase e), f Y := by
          have hzero : (if e = emptyPartial then 0 else f e) = 0 := by simp [e]
          rw [← Finset.sum_erase (s := Finset.univ)
            (f := fun Y ↦ if Y = emptyPartial then 0 else f Y) hzero]
          apply Finset.sum_congr rfl
          intro Y hY
          have hne : Y ≠ e := Finset.ne_of_mem_erase hY
          simp [e] at hne
          simp [hne, f]
    _ = (∏ i, (1 + term i (z i))) - 1 := by linarith

/-- The exponential kernel is nonnegative for nonnegative parameter and
coefficient. -/
theorem expKernel_nonneg {theta : ℝ} {a : Source → State → ℝ}
    (htheta : 0 ≤ theta) (ha : ∀ i j, 0 ≤ a i j) (i : Source) (j : State) :
    0 ≤ expKernel theta a i j := by
  unfold expKernel
  exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg htheta (ha i j)))

/-- Secant-line bound for the exponential kernel on `[0,1]`. -/
theorem expKernel_le_scale_mul {theta : ℝ} {a : Source → State → ℝ}
    (ha0 : ∀ i j, 0 ≤ a i j) (ha1 : ∀ i j, a i j ≤ 1)
    (i : Source) (j : State) :
    expKernel theta a i j ≤ (Real.exp theta - 1) * a i j := by
  have hconvex := convexOn_exp.2 (Set.mem_univ theta) (Set.mem_univ 0)
    (ha0 i j) (sub_nonneg.mpr (ha1 i j)) (by ring : a i j + (1 - a i j) = 1)
  have hconvex' : Real.exp (theta * a i j) ≤
      a i j * Real.exp theta + (1 - a i j) := by
    simpa [smul_eq_mul, mul_comm] using hconvex
  unfold expKernel
  nlinarith

/-- Product identity behind the exponential hitting property. -/
theorem compatible_expKernel_product
    (theta : ℝ) (a : Source → State → ℝ) (z : Source → State) :
    (∏ i, (1 + expKernel theta a i (z i))) =
      Real.exp (theta * ∑ i, a i (z i)) := by
  calc
    (∏ i, (1 + expKernel theta a i (z i))) =
        ∏ i, Real.exp (theta * a i (z i)) := by
          apply Finset.prod_congr rfl
          intro i _hi
          unfold expKernel
          ring
    _ = Real.exp (∑ i, theta * a i (z i)) := by rw [← Real.exp_sum]
    _ = Real.exp (theta * ∑ i, a i (z i)) := by rw [Finset.mul_sum]

/-- Exact total compatible nonempty kernel mass. -/
theorem sum_compatible_expKernel_ne_empty
    (theta : ℝ) (a : Source → State → ℝ) (z : Source → State) :
    (∑ Y : PartialAssignment Source State,
        if Y = emptyPartial then 0
        else if Compatible Y z then partialProduct (expKernel theta a) Y else 0) =
      Real.exp (theta * ∑ i, a i (z i)) - 1 := by
  rw [sum_compatible_partialProduct_ne_empty,
    compatible_expKernel_product]

/-- The uncapped exponential weights form a fractional hitting set for a
threshold row. -/
theorem sum_expHittingWeight_compatible_ge_one
    {theta threshold : ℝ} {a : Source → State → ℝ} (z : Source → State)
    (htheta : 0 < theta) (hthreshold : 0 < threshold)
    (hbad : threshold ≤ ∑ i, a i (z i)) :
    1 ≤ ∑ Y : PartialAssignment Source State,
      if Compatible Y z then expHittingWeight theta threshold a Y else 0 := by
  classical
  have hden : 0 < Real.exp (theta * threshold) - 1 := by
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos htheta hthreshold))
  have hexp : Real.exp (theta * threshold) ≤
      Real.exp (theta * ∑ i, a i (z i)) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbad htheta.le)
  rw [show (∑ Y : PartialAssignment Source State,
      if Compatible Y z then expHittingWeight theta threshold a Y else 0) =
      (Real.exp (theta * ∑ i, a i (z i)) - 1) /
        (Real.exp (theta * threshold) - 1) by
    calc
      (∑ Y : PartialAssignment Source State,
          if Compatible Y z then expHittingWeight theta threshold a Y else 0) =
          (∑ Y : PartialAssignment Source State,
            if Y = emptyPartial then 0
            else if Compatible Y z then partialProduct (expKernel theta a) Y else 0) /
              (Real.exp (theta * threshold) - 1) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro Y _hY
            by_cases hcompat : Compatible Y z
            · by_cases hempty : Y = emptyPartial
              · simp [hcompat, hempty, expHittingWeight]
              · simp [hcompat, hempty, expHittingWeight]
            · simp [hcompat, expHittingWeight]
      _ = (Real.exp (theta * ∑ i, a i (z i)) - 1) /
          (Real.exp (theta * threshold) - 1) := by
            rw [sum_compatible_expKernel_ne_empty]]
  exact (le_div_iff₀ hden).2 (by linarith)

/-- Exact finite product for the unnormalized charge mass. -/
theorem sum_expChargeProduct
    (theta : ℝ) (a lambda : Source → State → ℝ) :
    (∑ Y : PartialAssignment Source State,
        expChargeProduct theta a lambda Y) =
      ∏ i, (1 + ∑ j, lambda i j * expKernel theta a i j) := by
  exact sum_partialProduct _

/-- Products distribute pointwise over the local kernel. -/
theorem partialLambdaProduct_mul_kernel
    (theta : ℝ) (a lambda : Source → State → ℝ)
    (Y : PartialAssignment Source State) :
    partialLambdaProduct lambda Y * partialProduct (expKernel theta a) Y =
      expChargeProduct theta a lambda Y := by
  unfold partialLambdaProduct expChargeProduct partialProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  cases Y i <;> simp

/-- A source-marked product keeps precisely the partial assignments that
mention that source. -/
theorem sum_expChargeProduct_usesSource
    (theta : ℝ) (a lambda : Source → State → ℝ) (i0 : Source) :
    (∑ Y : PartialAssignment Source State,
        if Y i0 = none then 0 else expChargeProduct theta a lambda Y) =
      (∑ j, lambda i0 j * expKernel theta a i0 j) *
        ∏ i ∈ (Finset.univ.erase i0),
          (1 + ∑ j, lambda i j * expKernel theta a i j) := by
  let marked : Source → Option State → ℝ := fun i o ↦
    if i = i0 then
      match o with
      | none => 0
      | some j => lambda i j * expKernel theta a i j
    else
      match o with
      | none => 1
      | some j => lambda i j * expKernel theta a i j
  have hpoint : ∀ Y : PartialAssignment Source State,
      (∏ i, marked i (Y i)) =
        if Y i0 = none then 0 else expChargeProduct theta a lambda Y := by
    intro Y
    by_cases hnone : Y i0 = none
    · rw [if_pos hnone]
      apply Finset.prod_eq_zero (Finset.mem_univ i0)
      simp [marked, hnone]
    · rw [if_neg hnone]
      unfold expChargeProduct partialProduct
      apply Finset.prod_congr rfl
      intro i _hi
      by_cases hii : i = i0
      · subst i
        cases hY : Y i0 with
        | none => exact (hnone hY).elim
        | some j => simp [marked, hY]
      · simp [marked, hii]
  calc
    (∑ Y : PartialAssignment Source State,
        if Y i0 = none then 0 else expChargeProduct theta a lambda Y) =
        ∑ Y : PartialAssignment Source State, ∏ i, marked i (Y i) := by
          apply Finset.sum_congr rfl
          intro Y _hY
          exact (hpoint Y).symm
    _ = ∏ i, ∑ o : Option State, marked i o :=
      (Fintype.prod_sum (ι := Source) (κ := fun _ ↦ Option State)
        (R := ℝ) marked).symm
    _ = (∑ j, lambda i0 j * expKernel theta a i0 j) *
        ∏ i ∈ (Finset.univ.erase i0),
          (1 + ∑ j, lambda i j * expKernel theta a i j) := by
      rw [← Finset.mul_prod_erase (s := Finset.univ)
        (f := fun i ↦ ∑ o : Option State, marked i o) (Finset.mem_univ i0)]
      congr 1
      · rw [Fintype.sum_option]
        simp [marked]
      · apply Finset.prod_congr rfl
        intro i hi
        have hii : i ≠ i0 := Finset.ne_of_mem_erase hi
        rw [Fintype.sum_option]
        simp [marked, hii]

/-- Every local charge factor is bounded by its physical mean times the
common exponential scale. -/
theorem localKernelMean_le
    {theta : ℝ} {a lambda : Source → State → ℝ}
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (ha0 : ∀ i j, 0 ≤ a i j) (ha1 : ∀ i j, a i j ≤ 1)
    (i : Source) :
    (∑ j, lambda i j * expKernel theta a i j) ≤
      (Real.exp theta - 1) * sourceMean lambda a i := by
  unfold sourceMean
  calc
    (∑ j, lambda i j * expKernel theta a i j) ≤
        ∑ j, lambda i j * ((Real.exp theta - 1) * a i j) := by
          apply Finset.sum_le_sum
          intro j _hj
          exact mul_le_mul_of_nonneg_left
            (expKernel_le_scale_mul ha0 ha1 i j) (hlambda i j)
    _ = (Real.exp theta - 1) * ∑ j, lambda i j * a i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

/-- The total exponential-kernel mean is bounded by the row mean. -/
theorem totalKernelMean_le
    {theta : ℝ} {a lambda : Source → State → ℝ}
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (ha0 : ∀ i j, 0 ≤ a i j) (ha1 : ∀ i j, a i j ≤ 1) :
    (∑ i, ∑ j, lambda i j * expKernel theta a i j) ≤
      (Real.exp theta - 1) * weightedMean lambda a := by
  unfold weightedMean
  calc
    (∑ i, ∑ j, lambda i j * expKernel theta a i j) ≤
        ∑ i, (Real.exp theta - 1) * ∑ j, lambda i j * a i j := by
          exact Finset.sum_le_sum fun i _hi ↦
            localKernelMean_le hlambda ha0 ha1 i
    _ = (Real.exp theta - 1) * ∑ i, ∑ j, lambda i j * a i j := by
      rw [Finset.mul_sum]

/-- Product of `1 + local charge` is at most the exponential of the total
local charge. -/
theorem prod_one_add_localKernel_le_exp
    {theta : ℝ} {a lambda : Source → State → ℝ}
    (htheta : 0 ≤ theta) (hlambda : ∀ i j, 0 ≤ lambda i j)
    (ha0 : ∀ i j, 0 ≤ a i j) :
    (∏ i, (1 + ∑ j, lambda i j * expKernel theta a i j)) ≤
      Real.exp (∑ i, ∑ j, lambda i j * expKernel theta a i j) := by
  calc
    (∏ i, (1 + ∑ j, lambda i j * expKernel theta a i j)) ≤
        ∏ i, Real.exp (∑ j, lambda i j * expKernel theta a i j) := by
          apply Finset.prod_le_prod
          · intro i _hi
            have hlocal : 0 ≤ ∑ j, lambda i j * expKernel theta a i j :=
              Finset.sum_nonneg fun j _hj ↦
                mul_nonneg (hlambda i j) (expKernel_nonneg htheta ha0 i j)
            linarith
          · intro i _hi
            simpa [add_comm] using
              (Real.add_one_le_exp (∑ j, lambda i j * expKernel theta a i j))
    _ = Real.exp (∑ i, ∑ j, lambda i j * expKernel theta a i j) := by
      rw [← Real.exp_sum]

/-- Total charge bound for one row, before deleting the empty partial
assignment.  This slightly weaker form is convenient and sufficient for the
partial-resampling criterion. -/
theorem total_expCharge_le
    {theta : ℝ} {a lambda : Source → State → ℝ}
    (htheta : 0 ≤ theta) (hlambda : ∀ i j, 0 ≤ lambda i j)
    (ha0 : ∀ i j, 0 ≤ a i j) (ha1 : ∀ i j, a i j ≤ 1) :
    (∑ Y : PartialAssignment Source State,
        expChargeProduct theta a lambda Y) ≤
      Real.exp ((Real.exp theta - 1) * weightedMean lambda a) := by
  rw [sum_expChargeProduct]
  exact (prod_one_add_localKernel_le_exp htheta hlambda ha0).trans
    (Real.exp_le_exp.mpr (totalKernelMean_le hlambda ha0 ha1))

/-- Charge through one fixed source.  The bound is linear in that source's
physical row mass; this is the feature that later converts a column-sum bound
into a count-independent theorem. -/
theorem source_expCharge_le
    {theta : ℝ} {a lambda : Source → State → ℝ}
    (i0 : Source)
    (htheta : 0 ≤ theta) (hlambda : ∀ i j, 0 ≤ lambda i j)
    (ha0 : ∀ i j, 0 ≤ a i j) (ha1 : ∀ i j, a i j ≤ 1) :
    (∑ Y : PartialAssignment Source State,
        if Y i0 = none then 0 else expChargeProduct theta a lambda Y) ≤
      ((Real.exp theta - 1) * sourceMean lambda a i0) *
        Real.exp ((Real.exp theta - 1) * weightedMean lambda a) := by
  let ell : Source → ℝ := fun i ↦
    ∑ j, lambda i j * expKernel theta a i j
  have hexact :
      (∑ Y : PartialAssignment Source State,
          if Y i0 = none then 0 else expChargeProduct theta a lambda Y) =
        ell i0 * ∏ i ∈ (Finset.univ.erase i0), (1 + ell i) := by
    simpa [ell] using sum_expChargeProduct_usesSource theta a lambda i0
  have hlocal0 : ∀ i, 0 ≤ ell i := by
    intro i
    exact Finset.sum_nonneg fun j _hj ↦
      mul_nonneg (hlambda i j) (expKernel_nonneg htheta ha0 i j)
  have hprod :
      (∏ i ∈ (Finset.univ.erase i0), (1 + ell i)) ≤
        Real.exp (∑ i, ell i) := by
    calc
      (∏ i ∈ (Finset.univ.erase i0), (1 + ell i)) ≤
          ∏ i ∈ (Finset.univ.erase i0), Real.exp (ell i) := by
            apply Finset.prod_le_prod
            · intro i _hi
              linarith [hlocal0 i]
            · intro i _hi
              simpa [add_comm] using (Real.add_one_le_exp (ell i))
      _ = Real.exp (∑ i ∈ (Finset.univ.erase i0), ell i) := by
        rw [← Real.exp_sum]
      _ ≤ Real.exp (∑ i, ell i) := by
        apply Real.exp_le_exp.mpr
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun _ _ ↦ Finset.mem_univ _)
          (fun i _ _ ↦ hlocal0 i)
  have hlocalUpper : ell i0 ≤
      (Real.exp theta - 1) * sourceMean lambda a i0 :=
    localKernelMean_le hlambda ha0 ha1 i0
  have htotalUpper : (∑ i, ell i) ≤
      (Real.exp theta - 1) * weightedMean lambda a :=
    totalKernelMean_le hlambda ha0 ha1
  calc
    (∑ Y : PartialAssignment Source State,
        if Y i0 = none then 0 else expChargeProduct theta a lambda Y) =
        ell i0 * ∏ i ∈ (Finset.univ.erase i0), (1 + ell i) := hexact
    _ ≤
        ell i0 * Real.exp (∑ i, ell i) :=
      mul_le_mul_of_nonneg_left hprod (hlocal0 i0)
    _ ≤ ((Real.exp theta - 1) * sourceMean lambda a i0) *
        Real.exp (∑ i, ell i) := by
      exact mul_le_mul_of_nonneg_right hlocalUpper (Real.exp_pos _).le
    _ ≤ ((Real.exp theta - 1) * sourceMean lambda a i0) *
        Real.exp ((Real.exp theta - 1) * weightedMean lambda a) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htotalUpper)
      exact (hlocal0 i0).trans hlocalUpper

/-- The normalized self charge is bounded by the unnormalized exponential
product divided by the hitting denominator. -/
theorem expSelfCharge_le
    {theta threshold : ℝ} {a lambda : Source → State → ℝ}
    (htheta : 0 < theta) (hthreshold : 0 < threshold)
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (ha0 : ∀ i j, 0 ≤ a i j) (ha1 : ∀ i j, a i j ≤ 1) :
    expSelfCharge theta threshold a lambda ≤
      Real.exp ((Real.exp theta - 1) * weightedMean lambda a) /
        (Real.exp (theta * threshold) - 1) := by
  have hden : 0 < Real.exp (theta * threshold) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos htheta hthreshold))
  have hterm : ∀ Y : PartialAssignment Source State,
      expHittingWeight theta threshold a Y * partialLambdaProduct lambda Y ≤
        expChargeProduct theta a lambda Y /
          (Real.exp (theta * threshold) - 1) := by
    intro Y
    by_cases hempty : Y = emptyPartial
    · subst Y
      simp [expHittingWeight, emptyPartial, partialLambdaProduct,
        partialProduct, expChargeProduct, hden.le]
    · rw [show expHittingWeight theta threshold a Y =
          partialProduct (expKernel theta a) Y /
            (Real.exp (theta * threshold) - 1) by
        simp [expHittingWeight, hempty]]
      rw [div_mul_eq_mul_div,
        mul_comm (partialProduct (expKernel theta a) Y)
          (partialLambdaProduct lambda Y),
        partialLambdaProduct_mul_kernel]
  unfold expSelfCharge
  calc
    (∑ Y : PartialAssignment Source State,
        expHittingWeight theta threshold a Y * partialLambdaProduct lambda Y) ≤
        ∑ Y : PartialAssignment Source State,
          expChargeProduct theta a lambda Y /
            (Real.exp (theta * threshold) - 1) :=
      Finset.sum_le_sum fun Y _hY ↦ hterm Y
    _ = (∑ Y : PartialAssignment Source State,
          expChargeProduct theta a lambda Y) /
            (Real.exp (theta * threshold) - 1) := by rw [Finset.sum_div]
    _ ≤ Real.exp ((Real.exp theta - 1) * weightedMean lambda a) /
        (Real.exp (theta * threshold) - 1) := by
      exact div_le_div_of_nonneg_right
        (total_expCharge_le htheta.le hlambda ha0 ha1) hden.le

/-- The normalized charge through a source inherits the linear source-mass
bound. -/
theorem expSourceCharge_le
    {theta threshold : ℝ} {a lambda : Source → State → ℝ}
    (i : Source)
    (htheta : 0 < theta) (hthreshold : 0 < threshold)
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (ha0 : ∀ i j, 0 ≤ a i j) (ha1 : ∀ i j, a i j ≤ 1) :
    expSourceCharge theta threshold a lambda i ≤
      (((Real.exp theta - 1) * sourceMean lambda a i) *
        Real.exp ((Real.exp theta - 1) * weightedMean lambda a)) /
          (Real.exp (theta * threshold) - 1) := by
  have hden : 0 < Real.exp (theta * threshold) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos htheta hthreshold))
  have hexact : expSourceCharge theta threshold a lambda i =
      (∑ Y : PartialAssignment Source State,
          if Y i = none then 0 else expChargeProduct theta a lambda Y) /
        (Real.exp (theta * threshold) - 1) := by
    unfold expSourceCharge
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro Y _hY
    by_cases hnone : Y i = none
    · simp [hnone]
    · have hne : Y ≠ emptyPartial := by
        intro hY
        subst Y
        exact hnone rfl
      rw [if_neg hnone, if_neg hnone]
      rw [show expHittingWeight theta threshold a Y =
          partialProduct (expKernel theta a) Y /
            (Real.exp (theta * threshold) - 1) by
        simp [expHittingWeight, hne]]
      rw [div_mul_eq_mul_div,
        mul_comm (partialProduct (expKernel theta a) Y)
          (partialLambdaProduct lambda Y),
        partialLambdaProduct_mul_kernel]
  rw [hexact]
  exact div_le_div_of_nonneg_right
    (source_expCharge_le i htheta.le hlambda ha0 ha1) hden.le

end WeightedEdgeColoring.FinitePartialResamplingExponential
