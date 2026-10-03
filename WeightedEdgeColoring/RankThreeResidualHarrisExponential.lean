import WeightedEdgeColoring.RankThreeResidualHarrisBridge

/-!
# Exponential lower bounds for local-lemma products

For `0 ≤ x ≤ 1/2`, the elementary estimate

`exp (-2*x*n) ≤ (1-x)^n`

keeps the full exponential scale of the local-lemma neighbor product.  This
is stronger than replacing the product by a fixed constant and is the form
needed when coverage groups have logarithmic size.
-/

namespace WeightedEdgeColoring

/-- On `[0,1/2]`, `exp(-2x)` lies below `1-x`. -/
theorem exp_neg_two_mul_le_one_sub
    (x : ℝ) (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hlinear : (1 : ℝ) ≤ (1 - x) * (1 + 2 * x) := by
    nlinarith
  have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * x)
  have hx1 : x ≤ 1 := hxhalf.trans (by norm_num)
  have hone : (1 : ℝ) ≤ (1 - x) * Real.exp (2 * x) := by
    calc
      (1 : ℝ) ≤ (1 - x) * (1 + 2 * x) := hlinear
      _ ≤ (1 - x) * Real.exp (2 * x) :=
        mul_le_mul_of_nonneg_left hexp (sub_nonneg.mpr hx1)
  rw [show -2 * x = -(2 * x) by ring, Real.exp_neg, inv_eq_one_div]
  exact (div_le_iff₀ (Real.exp_pos (2 * x))).2 hone

/-- Power form of `exp_neg_two_mul_le_one_sub`. -/
theorem exp_neg_two_mul_nat_le_one_sub_pow
    (x : ℝ) (n : ℕ) (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.exp (-2 * x * (n : ℝ)) ≤ (1 - x) ^ n := by
  have hbase := exp_neg_two_mul_le_one_sub x hx0 hxhalf
  have hpow : (Real.exp (-2 * x)) ^ n ≤ (1 - x) ^ n :=
    pow_le_pow_left₀ (Real.exp_pos (-2 * x)).le hbase n
  calc
    Real.exp (-2 * x * (n : ℝ)) = (Real.exp (-2 * x)) ^ n := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ (1 - x) ^ n := hpow

end WeightedEdgeColoring

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Exponential-product form of the uniform residual Harris round.  It
replaces each `(1-x)^n` premise by the stronger but easier-to-balance term
`exp(-2*x*n)`, valid while the LLL weights are at most one half. -/
theorem exists_oneRound_residual_harris_uniform_exp
    (rho : ℝ) (members : Group → Finset Job)
    (lambda : ℕ) (hlambda : 0 < lambda)
    (jobBudget : Job → ℕ) (slotBudget : Slot → ℕ)
    (upperLambda : ResidualDeleteRow Job Slot → ℝ)
    (D R K m : ℕ) (pairX rowX cap delta : ℝ)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hmembers : ∀ g, (members g).card ≤ K)
    (hgroupSupportLower : ∀ g,
      m ≤ (linearRowSupport
        (H.jobGroupCoverageWeight members) g).card)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (hdelta0 : 0 ≤ delta)
    (hcoefficient :
      delta * (1 - delta) + (Real.exp (-delta) - 1) ≤ 0)
    (hupperLambda : ∀ r, 0 ≤ upperLambda r)
    (hpairX0 : 0 ≤ pairX) (hrowX0 : 0 ≤ rowX)
    (hpairXcap : pairX ≤ cap) (hrowXcap : rowX ≤ cap)
    (hcapHalf : cap ≤ 1 / 2)
    (hpairNumeric : rho * rho ≤
      pairX * Real.exp (-2 * rowX * ((2 * R : ℕ) : ℝ)))
    (hlowerNumeric :
      Real.exp
        ((delta * (1 - delta) + (Real.exp (-delta) - 1)) *
          (rho * (m : ℝ))) ≤
        rowX * Real.exp
          (-2 * cap * ((((K * D) * (14 * D) : ℕ)) : ℝ)))
    (hupperNumeric : ∀ r,
      Real.exp (-upperLambda r *
          residualDeleteThreshold lambda jobBudget slotBudget r +
        (Real.exp (upperLambda r) - 1) *
          (rho * (3 * D * D : ℕ))) ≤
        rowX * Real.exp
          (-2 * rowX * ((((3 * D * D) * R : ℕ)) : ℝ))) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ g, (1 - delta) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.jobGroupCoverageWeight members) g <
        ∑ o ∈ S, H.jobGroupCoverageWeight members g o) ∧
      (∀ j, ¬ H.Covers S j →
        H.residualJobDegree ∅ j ≤ H.residualJobDegree S j + jobBudget j) ∧
      (∀ s, (∀ p ∈ S, s ∉ H.slots p) →
        H.residualSlotDegree ∅ s ≤
          H.residualSlotDegree S s + slotBudget s) := by
  have hcap0 : 0 ≤ cap := hpairX0.trans hpairXcap
  have hrowHalf : rowX ≤ 1 / 2 := hrowXcap.trans hcapHalf
  have hcap1 : cap < 1 := hcapHalf.trans_lt (by norm_num)
  apply H.exists_oneRound_residual_harris_uniform rho members lambda hlambda
    jobBudget slotBudget upperLambda D R K m pairX rowX cap delta
    hrho0 hrho1 hjobDegree hslotDegree hjobSlot hslotPair hmembers
    hgroupSupportLower hgroupIncidence hdelta0 hcoefficient hupperLambda
    hpairX0 hrowX0 hpairXcap hrowXcap hcap1
  · apply hpairNumeric.trans
    apply mul_le_mul_of_nonneg_left _ hpairX0
    exact WeightedEdgeColoring.exp_neg_two_mul_nat_le_one_sub_pow rowX (2 * R)
      hrowX0 hrowHalf
  · apply hlowerNumeric.trans
    apply mul_le_mul_of_nonneg_left _ hrowX0
    exact WeightedEdgeColoring.exp_neg_two_mul_nat_le_one_sub_pow cap
      ((K * D) * (14 * D)) hcap0 hcapHalf
  · intro r
    apply (hupperNumeric r).trans
    apply mul_le_mul_of_nonneg_left _ hrowX0
    exact WeightedEdgeColoring.exp_neg_two_mul_nat_le_one_sub_pow rowX
      ((3 * D * D) * R) hrowX0 hrowHalf

end WeightedEdgeColoring.RankThreeOptionSystem
