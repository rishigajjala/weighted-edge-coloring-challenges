import WeightedEdgeColoring.RankThreeGroupCoverageBridge
import WeightedEdgeColoring.WeightedGroupCoverage

/-!
# Weighted output of job-group coverage

This file converts the covered-job count supplied by a Harris round into a
covered-weight estimate for groups of comparable job weights.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Generic count-to-weight conversion.  If a group has at most `K` jobs,
its positive weights vary by at most a factor `kappa`, and more than `c`
members are covered, then the covered weight is more than the
`c/(K*kappa)` fraction of the whole group weight. -/
theorem coveredGroupWeight_gt_of_count_gt_generic
    (members : Group → Finset Job) (weight : Job → ℝ) (a : Group → ℝ)
    (S : Finset Option) (K : ℕ) (c kappa : ℝ)
    (hK : 0 < K) (hc0 : 0 ≤ c) (hkappa : 0 < kappa)
    (ha : ∀ g, 0 < a g)
    (hmembers : ∀ g, (members g).card ≤ K)
    (hlower : ∀ g j, j ∈ members g → a g ≤ weight j)
    (hupper : ∀ g j, j ∈ members g → weight j ≤ kappa * a g)
    (hcount : ∀ g, c < (H.coveredGroupJobs members g S).card) :
    ∀ g,
      ((c / (K : ℝ)) / kappa) *
          (∑ j ∈ members g, weight j) <
        ∑ j ∈ H.coveredGroupJobs members g S, weight j := by
  intro g
  let theta : ℝ := c / (K : ℝ)
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have htheta0 : 0 ≤ theta := div_nonneg hc0 hKreal.le
  have hcard : ((members g).card : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hmembers g
  have hfraction : theta * ((members g).card : ℝ) ≤ c := by
    calc
      theta * ((members g).card : ℝ) ≤ theta * (K : ℝ) :=
        mul_le_mul_of_nonneg_left hcard htheta0
      _ = c := by
        dsimp [theta]
        field_simp
  have hcount' :
      theta * ((members g).card : ℝ) <
        ((H.coveredGroupJobs members g S).card : ℝ) :=
    hfraction.trans_lt (hcount g)
  apply WeightedEdgeColoring.mul_sum_lt_sum_of_nearEqual_and_card
    weight (members g) (H.coveredGroupJobs members g S)
    (a g) kappa theta (ha g) hkappa htheta0
  · intro j hj
    exact hlower g j (Finset.mem_filter.mp hj).1
  · exact hupper g
  · exact hcount'

/-- A count guarantee based on the minimum group size `k` and minimum job
degree `d` implies a proportional weighted guarantee for every group of at
most `K` jobs whose weights vary by at most `kappa`. -/
theorem coveredGroupWeight_gt_of_count_gt
    (members : Group → Finset Job) (weight : Job → ℝ) (a : Group → ℝ)
    (S : Finset Option) (K k d : ℕ) (rho delta kappa : ℝ)
    (hK : 0 < K) (hrho0 : 0 ≤ rho) (hdelta1 : delta ≤ 1)
    (hkappa : 0 < kappa) (ha : ∀ g, 0 < a g)
    (hmembers : ∀ g, (members g).card ≤ K)
    (hlower : ∀ g j, j ∈ members g → a g ≤ weight j)
    (hupper : ∀ g j, j ∈ members g → weight j ≤ kappa * a g)
    (hcount : ∀ g,
      (1 - delta) * rho * ((k * d : ℕ) : ℝ) <
        (H.coveredGroupJobs members g S).card) :
    ∀ g,
      ((((1 - delta) * rho * ((k * d : ℕ) : ℝ)) / (K : ℝ)) / kappa) *
          (∑ j ∈ members g, weight j) <
        ∑ j ∈ H.coveredGroupJobs members g S, weight j := by
  intro g
  let theta : ℝ :=
    ((1 - delta) * rho * ((k * d : ℕ) : ℝ)) / (K : ℝ)
  have hbase0 : 0 ≤ (1 - delta) * rho * ((k * d : ℕ) : ℝ) := by
    exact mul_nonneg (mul_nonneg (by linarith) hrho0) (Nat.cast_nonneg _)
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have htheta0 : 0 ≤ theta := div_nonneg hbase0 hKreal.le
  have hcard : ((members g).card : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hmembers g
  have hfraction :
      theta * ((members g).card : ℝ) ≤
        (1 - delta) * rho * ((k * d : ℕ) : ℝ) := by
    calc
      theta * ((members g).card : ℝ) ≤ theta * (K : ℝ) :=
        mul_le_mul_of_nonneg_left hcard htheta0
      _ = (1 - delta) * rho * ((k * d : ℕ) : ℝ) := by
        dsimp [theta]
        field_simp
  have hcount' :
      theta * ((members g).card : ℝ) <
        ((H.coveredGroupJobs members g S).card : ℝ) :=
    hfraction.trans_lt (hcount g)
  apply WeightedEdgeColoring.mul_sum_lt_sum_of_nearEqual_and_card
    weight (members g) (H.coveredGroupJobs members g S)
    (a g) kappa theta (ha g) hkappa htheta0
  · intro j hj
    exact hlower g j (Finset.mem_filter.mp hj).1
  · exact hupper g
  · exact hcount'

end WeightedEdgeColoring.RankThreeOptionSystem
