import WeightedEdgeColoring.RankThreeResidualHarrisBridge

/-!
# A half-product specialization of the residual Harris round

The abstract local-lemma inequalities contain factors `(1 - x)^d`.  For
parameter selection it is convenient to replace each such factor by `1/2`.
Bernoulli's inequality shows that this is valid whenever `d*x ≤ 1/2`.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

/-- A convenient consequence of Bernoulli's inequality: if the total linear
loss `n*x` is at most one half, then the product `(1-x)^n` is at least one
half. -/
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

/-- Uniform residual Harris round with every local-lemma neighbor product
replaced by the lower bound `1/2`.  Thus the only probability estimates one
has to prove are `tail ≤ eventWeight/2`; the three linear hypotheses certify
the corresponding product bounds. -/
theorem exists_oneRound_residual_harris_uniform_half
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
    (hcap1 : cap < 1)
    (hpairTail : rho * rho ≤ pairX / 2)
    (hlowerTail :
      Real.exp
        ((delta * (1 - delta) + (Real.exp (-delta) - 1)) *
          (rho * (m : ℝ))) ≤ rowX / 2)
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
  have hcap1' : cap ≤ 1 := hcap1.le
  have hrowX1 : rowX ≤ 1 := hrowXcap.trans hcap1'
  have hpairPow : (1 / 2 : ℝ) ≤ (1 - rowX) ^ (2 * R) := by
    apply half_le_one_sub_pow_of_mul_le_half rowX (2 * R) hrowX0 hrowX1
    exact_mod_cast hpairCost
  have hlowerPow : (1 / 2 : ℝ) ≤
      (1 - cap) ^ ((K * D) * (14 * D)) := by
    exact half_le_one_sub_pow_of_mul_le_half cap ((K * D) * (14 * D))
      hcap0 hcap1' hlowerCost
  have hupperPow : (1 / 2 : ℝ) ≤
      (1 - rowX) ^ ((3 * D * D) * R) := by
    exact half_le_one_sub_pow_of_mul_le_half rowX ((3 * D * D) * R)
      hrowX0 hrowX1 hupperCost
  apply H.exists_oneRound_residual_harris_uniform rho members lambda hlambda
    jobBudget slotBudget upperLambda D R K m pairX rowX cap delta
    hrho0 hrho1 hjobDegree hslotDegree hjobSlot hslotPair hmembers
    hgroupSupportLower hgroupIncidence hdelta0 hcoefficient hupperLambda
    hpairX0 hrowX0 hpairXcap hrowXcap hcap1
  · calc
      rho * rho ≤ pairX / 2 := hpairTail
      _ = pairX * (1 / 2) := by ring
      _ ≤ pairX * (1 - rowX) ^ (2 * R) :=
        mul_le_mul_of_nonneg_left hpairPow hpairX0
  · calc
      Real.exp
          ((delta * (1 - delta) + (Real.exp (-delta) - 1)) *
            (rho * (m : ℝ))) ≤ rowX / 2 := hlowerTail
      _ = rowX * (1 / 2) := by ring
      _ ≤ rowX * (1 - cap) ^ ((K * D) * (14 * D)) :=
        mul_le_mul_of_nonneg_left hlowerPow hrowX0
  · intro r
    calc
      Real.exp (-upperLambda r *
          residualDeleteThreshold lambda jobBudget slotBudget r +
        (Real.exp (upperLambda r) - 1) *
          (rho * (3 * D * D : ℕ))) ≤ rowX / 2 := hupperTail r
      _ = rowX * (1 / 2) := by ring
      _ ≤ rowX * (1 - rowX) ^ ((3 * D * D) * R) :=
        mul_le_mul_of_nonneg_left hupperPow hrowX0

end WeightedEdgeColoring.RankThreeOptionSystem
