import WeightedEdgeColoring.RankThreeResidualHarrisHalf

/-!
# Explicit parameters for the residual Harris round

This file records a rational bound for the lower-tail coefficient at
`delta = 1/2`.  The proof uses only `1+x <= exp x`: applying it four times
at `x = 1/8` gives `8/5 <= exp (1/2)`, hence
`exp (-1/2) <= 5/8`.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators

/-- Four copies of the elementary lower bound at `1/8` give a rational
lower bound on `exp (1/2)`. -/
theorem eight_fifths_le_exp_one_half :
    (8 / 5 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
  have hbase : (9 / 8 : ℝ) ≤ Real.exp (1 / 8 : ℝ) := by
    have h := Real.add_one_le_exp (1 / 8 : ℝ)
    norm_num at h ⊢
    exact h
  have hpow : (9 / 8 : ℝ) ^ 4 ≤ (Real.exp (1 / 8 : ℝ)) ^ 4 := by
    exact pow_le_pow_left₀ (by norm_num) hbase 4
  have hrat : (8 / 5 : ℝ) ≤ (9 / 8 : ℝ) ^ 4 := by
    norm_num
  calc
    (8 / 5 : ℝ) ≤ (9 / 8 : ℝ) ^ 4 := hrat
    _ ≤ (Real.exp (1 / 8 : ℝ)) ^ 4 := hpow
    _ = Real.exp (1 / 2 : ℝ) := by
      rw [← Real.exp_nat_mul]
      norm_num

/-- Rational upper bound on `exp (-1/2)`. -/
theorem exp_neg_one_half_le_five_eighths :
    Real.exp (-(1 / 2 : ℝ)) ≤ 5 / 8 := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos (1 / 2 : ℝ))).2
  calc
    (1 : ℝ) = (5 / 8) * (8 / 5) := by norm_num
    _ ≤ (5 / 8) * Real.exp (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left eight_fifths_le_exp_one_half (by norm_num)

/-- At `delta = 1/2`, the lower-tail Chernoff coefficient is at most
`-1/8`. -/
theorem half_lowerTail_coefficient_le_neg_one_eighth :
    (1 / 2 : ℝ) * (1 - 1 / 2) +
        (Real.exp (-(1 / 2 : ℝ)) - 1) ≤ -(1 / 8 : ℝ) := by
  have h := exp_neg_one_half_le_five_eighths
  norm_num at h ⊢
  linarith

/-- In particular, the coefficient required by the Harris theorem is
nonpositive at `delta = 1/2`. -/
theorem half_lowerTail_coefficient_nonpos :
    (1 / 2 : ℝ) * (1 - 1 / 2) +
        (Real.exp (-(1 / 2 : ℝ)) - 1) ≤ 0 := by
  exact half_lowerTail_coefficient_le_neg_one_eighth.trans (by norm_num)

/-- Multiplying the fixed coefficient bound by a nonnegative mean preserves
the inequality. -/
theorem half_lowerTail_exponent_le (mu : ℝ) (hmu : 0 ≤ mu) :
    ((1 / 2 : ℝ) * (1 - 1 / 2) +
        (Real.exp (-(1 / 2 : ℝ)) - 1)) * mu ≤
      -(1 / 8 : ℝ) * mu := by
  exact mul_le_mul_of_nonneg_right
    half_lowerTail_coefficient_le_neg_one_eighth hmu

/-- Kernel-checked exponential tail comparison used by the half round. -/
theorem half_lowerTail_exp_le (mu : ℝ) (hmu : 0 ≤ mu) :
    Real.exp (((1 / 2 : ℝ) * (1 - 1 / 2) +
        (Real.exp (-(1 / 2 : ℝ)) - 1)) * mu) ≤
      Real.exp (-(1 / 8 : ℝ) * mu) := by
  exact Real.exp_le_exp.mpr (half_lowerTail_exponent_le mu hmu)

/-! ## A fixed upper-tail parameter -/

/-- A small rational upper bound for Euler's number, derived from Mathlib's
finite exponential-series remainder bound. -/
theorem exp_one_lt_three : Real.exp 1 < 3 := by
  have h := Real.exp_bound' (x := (1 : ℝ)) (n := 4)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-- At Chernoff parameter one, a threshold at least four times the mean
forces an exponent of at most `-2*mu`. -/
theorem upperTail_lambda_one_exp_le (mu t : ℝ)
    (hmu : 0 ≤ mu) (ht : 4 * mu ≤ t) :
    Real.exp (-t + (Real.exp 1 - 1) * mu) ≤
      Real.exp (-2 * mu) := by
  apply Real.exp_le_exp.mpr
  have he : Real.exp 1 - 1 ≤ 2 := by
    linarith [exp_one_lt_three]
  have hmul : (Real.exp 1 - 1) * mu ≤ 2 * mu :=
    mul_le_mul_of_nonneg_right he hmu
  linarith

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

/-- The half-product residual Harris theorem at `delta = 1/2`.  Its lower
tail input is the simpler rational estimate `exp (-rho*m/8) <= rowX/2`.
The proof only supplies the explicit coefficient lemmas above to the generic
half theorem. -/
theorem exists_oneRound_residual_harris_uniform_half_delta_one_half
    (rho : ℝ) (members : Group → Finset Job)
    (lambda : ℕ) (hlambda : 0 < lambda)
    (jobBudget : Job → ℕ) (slotBudget : Slot → ℕ)
    (upperLambda : ResidualDeleteRow Job Slot → ℝ)
    (D R K m : ℕ) (pairX rowX cap : ℝ)
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
    (hupperLambda : ∀ r, 0 ≤ upperLambda r)
    (hpairX0 : 0 ≤ pairX) (hrowX0 : 0 ≤ rowX)
    (hpairXcap : pairX ≤ cap) (hrowXcap : rowX ≤ cap)
    (hcap1 : cap < 1)
    (hpairTail : rho * rho ≤ pairX / 2)
    (hlowerTail :
      Real.exp (-(1 / 8 : ℝ) * (rho * (m : ℝ))) ≤ rowX / 2)
    (hupperTail : ∀ r,
      Real.exp (-upperLambda r *
          residualDeleteThreshold lambda jobBudget slotBudget r +
        (Real.exp (upperLambda r) - 1) *
          (rho * (3 * D * D : ℕ))) ≤ rowX / 2)
    (hpairCost : rowX * (2 * R : ℕ) ≤ 1 / 2)
    (hlowerCost : cap * (((K * D) * (14 * D) : ℕ) : ℝ) ≤ 1 / 2)
    (hupperCost : rowX * (((3 * D * D) * R : ℕ) : ℝ) ≤ 1 / 2) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ g, (1 / 2 : ℝ) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.jobGroupCoverageWeight members) g <
        ∑ o ∈ S, H.jobGroupCoverageWeight members g o) ∧
      (∀ j, ¬ H.Covers S j →
        H.residualJobDegree ∅ j ≤ H.residualJobDegree S j + jobBudget j) ∧
      (∀ s, (∀ p ∈ S, s ∉ H.slots p) →
        H.residualSlotDegree ∅ s ≤
          H.residualSlotDegree S s + slotBudget s) := by
  have hmu : 0 ≤ rho * (m : ℝ) :=
    mul_nonneg hrho0 (Nat.cast_nonneg m)
  have hlowerTail' :
      Real.exp
        (((1 / 2 : ℝ) * (1 - 1 / 2) +
          (Real.exp (-(1 / 2 : ℝ)) - 1)) *
            (rho * (m : ℝ))) ≤ rowX / 2 :=
    (half_lowerTail_exp_le (rho * (m : ℝ)) hmu).trans hlowerTail
  have hresult := H.exists_oneRound_residual_harris_uniform_half
    rho members lambda hlambda jobBudget slotBudget upperLambda
    D R K m pairX rowX cap (1 / 2 : ℝ)
    hrho0 hrho1 hjobDegree hslotDegree hjobSlot hslotPair hmembers
    hgroupSupportLower hgroupIncidence (by norm_num)
    half_lowerTail_coefficient_nonpos hupperLambda
    hpairX0 hrowX0 hpairXcap hrowXcap hcap1
    hpairTail hlowerTail' hupperTail hpairCost hlowerCost hupperCost
  norm_num at hresult ⊢
  exact hresult

/-- Fully explicit half-product round with upper Chernoff parameter one.
Every normalized residual threshold is at least four times the common upper
mean bound `rho * 3D²`; the single remaining upper-tail check is then
`exp (-2 * rho * 3D²) <= rowX/2`. -/
theorem exists_oneRound_residual_harris_uniform_explicit
    (rho : ℝ) (members : Group → Finset Job)
    (lambda : ℕ) (hlambda : 0 < lambda)
    (jobBudget : Job → ℕ) (slotBudget : Slot → ℕ)
    (D R K m : ℕ) (pairX rowX cap : ℝ)
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
    (hpairX0 : 0 ≤ pairX) (hrowX0 : 0 ≤ rowX)
    (hpairXcap : pairX ≤ cap) (hrowXcap : rowX ≤ cap)
    (hcap1 : cap < 1)
    (hpairTail : rho * rho ≤ pairX / 2)
    (hlowerTail :
      Real.exp (-(1 / 8 : ℝ) * (rho * (m : ℝ))) ≤ rowX / 2)
    (hthreshold : ∀ r : ResidualDeleteRow Job Slot,
      4 * (rho * (3 * D * D : ℕ)) ≤
        residualDeleteThreshold lambda jobBudget slotBudget r)
    (hupperTail :
      Real.exp (-2 * (rho * (3 * D * D : ℕ))) ≤ rowX / 2)
    (hpairCost : rowX * (2 * R : ℕ) ≤ 1 / 2)
    (hlowerCost : cap * (((K * D) * (14 * D) : ℕ) : ℝ) ≤ 1 / 2)
    (hupperCost : rowX * (((3 * D * D) * R : ℕ) : ℝ) ≤ 1 / 2) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ g, (1 / 2 : ℝ) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.jobGroupCoverageWeight members) g <
        ∑ o ∈ S, H.jobGroupCoverageWeight members g o) ∧
      (∀ j, ¬ H.Covers S j →
        H.residualJobDegree ∅ j ≤ H.residualJobDegree S j + jobBudget j) ∧
      (∀ s, (∀ p ∈ S, s ∉ H.slots p) →
        H.residualSlotDegree ∅ s ≤
          H.residualSlotDegree S s + slotBudget s) := by
  have hmu : 0 ≤ rho * (3 * D * D : ℕ) :=
    mul_nonneg hrho0 (Nat.cast_nonneg (3 * D * D))
  apply H.exists_oneRound_residual_harris_uniform_half_delta_one_half
    rho members lambda hlambda jobBudget slotBudget (fun _ ↦ 1)
    D R K m pairX rowX cap hrho0 hrho1 hjobDegree hslotDegree
    hjobSlot hslotPair hmembers hgroupSupportLower hgroupIncidence
    (fun _ ↦ by norm_num) hpairX0 hrowX0 hpairXcap hrowXcap hcap1
    hpairTail hlowerTail
  · intro r
    have h := upperTail_lambda_one_exp_le
      (rho * (3 * D * D : ℕ))
      (residualDeleteThreshold lambda jobBudget slotBudget r)
      hmu (hthreshold r)
    have h' :
        Real.exp (-(1 : ℝ) *
            residualDeleteThreshold lambda jobBudget slotBudget r +
          (Real.exp (1 : ℝ) - 1) * (rho * (3 * D * D : ℕ))) ≤
          Real.exp (-2 * (rho * (3 * D * D : ℕ))) := by
      simpa using h
    exact h'.trans hupperTail
  · exact hpairCost
  · exact hlowerCost
  · exact hupperCost

end WeightedEdgeColoring.RankThreeOptionSystem
