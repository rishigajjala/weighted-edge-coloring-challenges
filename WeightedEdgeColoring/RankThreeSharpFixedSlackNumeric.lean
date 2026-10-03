import WeightedEdgeColoring.RankThreeResidualHarrisExponential

/-!
# Small scalar lemmas for the sharp fixed-slack round

This file deliberately contains no eventual-asymptotic theorem.  It turns
transparent tail estimates and linear or exponential product-cost estimates
into the numerical hypotheses of
`exists_sharpFixedSlackRound_harris_extra`.  Pair, upper, and collision
products use a half bound; the much larger lower-row product keeps its full
exponential scale.

The intended asymptotic substitution is

* `rho = a / d`, `pairX = 2 * rho^2`, `cap = 4 * rho^2`;
* `lowerX = upperX = exp (-z)`;
* `collisionX = 2 * (1/2)^k`.

All estimates which say that these quantities dominate one another remain
explicit hypotheses.  This keeps the reusable algebra independent of a
particular choice such as `lambda = ceil (log d)^2`.
-/

namespace WeightedEdgeColoring.SharpFixedSlackNumeric

open scoped BigOperators

/-- The three neighbor budgets occurring in the concrete sharp round. -/
def pairNeighborBudget (R D : ℕ) : ℕ := 2 * (R + 8 * D)

def lowerNeighborBudget (support D : ℕ) : ℕ := support * (16 * D)

def increasingNeighborBudget (support R D : ℕ) : ℕ :=
  support * (R + 8 * D)

/-- Uniform-degree support budgets used by the graph-specific wrapper. -/
def groupSupportBudget (K D : ℕ) : ℕ := K * D

def slotSupportBudget (D : ℕ) : ℕ := D * (D + 2 * D)

def upperSupportBudget (D : ℕ) : ℕ := 2 * D * D

/-- Bernoulli's inequality in the exact form used for every Harris
neighbor product. -/
theorem half_le_one_sub_pow_of_mul_le_half
    (x : ℝ) (n : ℕ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hmul : x * (n : ℝ) ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ (1 - x) ^ n := by
  have hbern : 1 + (n : ℝ) * (-x) ≤ (1 - x) ^ n := by
    have h := one_add_mul_le_pow (a := -x) (n := n) (by linarith)
    simpa only [sub_eq_add_neg] using h
  calc
    (1 / 2 : ℝ) ≤ 1 - x * (n : ℝ) := by linarith
    _ = 1 + (n : ℝ) * (-x) := by ring
    _ ≤ (1 - x) ^ n := hbern

/-- It is enough to check the product cost at any upper bound for the
actual exponent. -/
theorem half_le_one_sub_pow_of_le
    (x : ℝ) (n N : ℕ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hn : n ≤ N) (hmul : x * (N : ℝ) ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ (1 - x) ^ n := by
  apply half_le_one_sub_pow_of_mul_le_half x n hx0 hx1
  apply (mul_le_mul_of_nonneg_left ?_ hx0).trans hmul
  exact_mod_cast hn

/-- Exponential version of the product estimate.  Unlike the half-product
form, this remains useful when `x*N` grows, as it does for lower rows. -/
theorem exp_neg_two_mul_le_one_sub_pow_of_le
    (x : ℝ) (n N : ℕ) (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hn : n ≤ N) :
    Real.exp (-2 * x * (N : ℝ)) ≤ (1 - x) ^ n := by
  calc
    Real.exp (-2 * x * (N : ℝ)) ≤ (1 - x) ^ N :=
      WeightedEdgeColoring.exp_neg_two_mul_nat_le_one_sub_pow x N hx0 hxhalf
    _ ≤ (1 - x) ^ n :=
      pow_le_pow_of_le_one (sub_nonneg.mpr (hxhalf.trans (by norm_num)))
        (sub_le_self 1 hx0) hn

/-- Generic half-product conversion. -/
theorem tail_le_weight_mul_one_sub_pow_of_half
    (tail eventX neighborX : ℝ) (n N : ℕ)
    (hevent0 : 0 ≤ eventX)
    (hneighbor0 : 0 ≤ neighborX) (hneighbor1 : neighborX ≤ 1)
    (hn : n ≤ N)
    (htail : tail ≤ eventX / 2)
    (hcost : neighborX * (N : ℝ) ≤ 1 / 2) :
    tail ≤ eventX * (1 - neighborX) ^ n := by
  calc
    tail ≤ eventX / 2 := htail
    _ = eventX * (1 / 2) := by ring
    _ ≤ eventX * (1 - neighborX) ^ n :=
      mul_le_mul_of_nonneg_left
        (half_le_one_sub_pow_of_le neighborX n N hneighbor0 hneighbor1
          hn hcost) hevent0

/-- Exponential-product conversion with no small-total-cost assumption. -/
theorem tail_le_weight_mul_one_sub_pow_of_exp
    (tail eventX neighborX : ℝ) (n N : ℕ)
    (hevent0 : 0 ≤ eventX)
    (hneighbor0 : 0 ≤ neighborX) (hneighborHalf : neighborX ≤ 1 / 2)
    (hn : n ≤ N)
    (htail : tail ≤ eventX * Real.exp (-2 * neighborX * (N : ℝ))) :
    tail ≤ eventX * (1 - neighborX) ^ n := by
  exact htail.trans (mul_le_mul_of_nonneg_left
    (exp_neg_two_mul_le_one_sub_pow_of_le neighborX n N
      hneighbor0 hneighborHalf hn) hevent0)

/-- If the row weight is `exp (-z)`, a single exponent budget proves the
event-weight times product inequality. -/
theorem tail_le_exp_mul_one_sub_pow_of_exp_budget
    (tail z neighborX : ℝ) (n N : ℕ)
    (hneighbor0 : 0 ≤ neighborX) (hneighborHalf : neighborX ≤ 1 / 2)
    (hn : n ≤ N)
    (htail : tail ≤ Real.exp (-(z + 2 * neighborX * (N : ℝ)))) :
    tail ≤ Real.exp (-z) * (1 - neighborX) ^ n := by
  apply tail_le_weight_mul_one_sub_pow_of_exp tail (Real.exp (-z))
    neighborX n N (Real.exp_pos _).le hneighbor0 hneighborHalf hn
  calc
    tail ≤ Real.exp (-(z + 2 * neighborX * (N : ℝ))) := htail
    _ = Real.exp (-z) * Real.exp (-2 * neighborX * (N : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Pair-event numerical hypothesis.  Pair events pay only `lowerX`. -/
theorem pairNumeric_of_half
    (pairMass pairX lowerX : ℝ) (n R D : ℕ)
    (hpairX0 : 0 ≤ pairX)
    (hlowerX0 : 0 ≤ lowerX) (hlowerX1 : lowerX ≤ 1)
    (hn : n ≤ pairNeighborBudget R D)
    (htail : pairMass ≤ pairX / 2)
    (hcost : lowerX * (pairNeighborBudget R D : ℝ) ≤ 1 / 2) :
    pairMass ≤ pairX * (1 - lowerX) ^ n := by
  exact tail_le_weight_mul_one_sub_pow_of_half
    pairMass pairX lowerX n (pairNeighborBudget R D)
    hpairX0 hlowerX0 hlowerX1 hn htail hcost

/-- Lower-row numerical hypothesis.  Lower events pay the common cap on
pair, upper, and collision weights. -/
theorem lowerNumeric_of_half
    (tail lowerX cap : ℝ) (n support D : ℕ)
    (hlowerX0 : 0 ≤ lowerX)
    (hcap0 : 0 ≤ cap) (hcap1 : cap ≤ 1)
    (hn : n ≤ lowerNeighborBudget support D)
    (htail : tail ≤ lowerX / 2)
    (hcost : cap * (lowerNeighborBudget support D : ℝ) ≤ 1 / 2) :
    tail ≤ lowerX * (1 - cap) ^ n := by
  exact tail_le_weight_mul_one_sub_pow_of_half
    tail lowerX cap n (lowerNeighborBudget support D)
    hlowerX0 hcap0 hcap1 hn htail hcost

/-- Exponential form of the lower-row hypothesis.  This is the form used
when `cap` is of order `a^2/d^2` and the lower neighbor budget is of order
`d^3`. -/
theorem lowerNumeric_of_exp
    (tail lowerX cap : ℝ) (n support D : ℕ)
    (hlowerX0 : 0 ≤ lowerX)
    (hcap0 : 0 ≤ cap) (hcapHalf : cap ≤ 1 / 2)
    (hn : n ≤ lowerNeighborBudget support D)
    (htail : tail ≤ lowerX * Real.exp
      (-2 * cap * (lowerNeighborBudget support D : ℝ))) :
    tail ≤ lowerX * (1 - cap) ^ n := by
  exact tail_le_weight_mul_one_sub_pow_of_exp
    tail lowerX cap n (lowerNeighborBudget support D)
    hlowerX0 hcap0 hcapHalf hn htail

/-- The same lower-row conversion with `lowerX = exp (-z)`. -/
theorem lowerNumeric_of_exp_budget
    (tail z cap : ℝ) (n support D : ℕ)
    (hcap0 : 0 ≤ cap) (hcapHalf : cap ≤ 1 / 2)
    (hn : n ≤ lowerNeighborBudget support D)
    (htail : tail ≤ Real.exp
      (-(z + 2 * cap * (lowerNeighborBudget support D : ℝ)))) :
    tail ≤ Real.exp (-z) * (1 - cap) ^ n := by
  exact tail_le_exp_mul_one_sub_pow_of_exp_budget tail z cap n
    (lowerNeighborBudget support D) hcap0 hcapHalf hn htail

/-- Upper-row numerical hypothesis.  Upper events pay only `lowerX`. -/
theorem upperNumeric_of_half
    (tail upperX lowerX : ℝ) (n support R D : ℕ)
    (hupperX0 : 0 ≤ upperX)
    (hlowerX0 : 0 ≤ lowerX) (hlowerX1 : lowerX ≤ 1)
    (hn : n ≤ increasingNeighborBudget support R D)
    (htail : tail ≤ upperX / 2)
    (hcost : lowerX * (increasingNeighborBudget support R D : ℝ) ≤ 1 / 2) :
    tail ≤ upperX * (1 - lowerX) ^ n := by
  exact tail_le_weight_mul_one_sub_pow_of_half
    tail upperX lowerX n (increasingNeighborBudget support R D)
    hupperX0 hlowerX0 hlowerX1 hn htail hcost

/-- Collision-event numerical hypothesis.  Collision events have the same
polarity and product cost as upper rows. -/
theorem collisionNumeric_of_half
    (tail collisionX lowerX : ℝ) (n support R D : ℕ)
    (hcollisionX0 : 0 ≤ collisionX)
    (hlowerX0 : 0 ≤ lowerX) (hlowerX1 : lowerX ≤ 1)
    (hn : n ≤ increasingNeighborBudget support R D)
    (htail : tail ≤ collisionX / 2)
    (hcost : lowerX * (increasingNeighborBudget support R D : ℝ) ≤ 1 / 2) :
    tail ≤ collisionX * (1 - lowerX) ^ n := by
  exact tail_le_weight_mul_one_sub_pow_of_half
    tail collisionX lowerX n (increasingNeighborBudget support R D)
    hcollisionX0 hlowerX0 hlowerX1 hn htail hcost

/-! ## The intended four weights -/

def pairWeight (rho : ℝ) : ℝ := 2 * rho ^ 2

def increasingCap (rho : ℝ) : ℝ := 4 * rho ^ 2

noncomputable def exponentialRowWeight (z : ℝ) : ℝ := Real.exp (-z)

noncomputable def collisionWeight (k : ℕ) : ℝ := 2 * (1 / 2 : ℝ) ^ k

theorem sq_eq_pairWeight_div_two (rho : ℝ) :
    rho ^ 2 = pairWeight rho / 2 := by
  simp [pairWeight]

theorem pairWeight_nonneg (rho : ℝ) : 0 ≤ pairWeight rho := by
  unfold pairWeight
  positivity

theorem pairWeight_le_increasingCap (rho : ℝ) :
    pairWeight rho ≤ increasingCap rho := by
  simp only [pairWeight, increasingCap]
  nlinarith [sq_nonneg rho]

theorem increasingCap_nonneg (rho : ℝ) : 0 ≤ increasingCap rho := by
  unfold increasingCap
  positivity

theorem increasingCap_le_half (rho : ℝ) (h : rho ^ 2 ≤ 1 / 8) :
    increasingCap rho ≤ 1 / 2 := by
  dsimp [increasingCap]
  linarith

theorem exponentialRowWeight_pos (z : ℝ) :
    0 < exponentialRowWeight z := Real.exp_pos _

theorem exponentialRowWeight_nonneg (z : ℝ) :
    0 ≤ exponentialRowWeight z := (exponentialRowWeight_pos z).le

theorem exponentialRowWeight_le_one (z : ℝ) (hz : 0 ≤ z) :
    exponentialRowWeight z ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)

theorem collisionWeight_nonneg (k : ℕ) : 0 ≤ collisionWeight k := by
  unfold collisionWeight
  positivity

theorem half_pow_eq_collisionWeight_div_two (k : ℕ) :
    (1 / 2 : ℝ) ^ k = collisionWeight k / 2 := by
  simp [collisionWeight]

end WeightedEdgeColoring.SharpFixedSlackNumeric
