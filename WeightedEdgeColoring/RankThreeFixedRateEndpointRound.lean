import WeightedEdgeColoring.RankThreeResidualFixedRateBudgets
import WeightedEdgeColoring.RankThreeEndpointGroupRound

/-!
# A fixed-rate round on dyadic endpoint groups

This file combines the numeric fixed-rate local-lemma package with the
dyadic endpoint groups of a weighted simple graph.  One partial matching
covers a fixed fraction of every retained endpoint block, decreases every
active unused slot by the natural slot budget, and protects every uncovered
job up to the natural job budget.  The count guarantee is also summed at
each graph vertex to give a weighted gain, with the discarded small-block
weight shown explicitly.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace RankThreeOptionSystem

universe u v w

variable (G : WeightedSimpleGraph.{u})
  {Slot : Type v} {Option : Type w}
  [Fintype Slot] [Fintype Option]
  [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem G.E Slot Option)

/-- The common count scale in a fixed-rate endpoint-group round. -/
noncomputable def fixedRateEndpointEta
    (lambda J K dJob S : ℕ) : ℝ :=
  activeSlotUniformLowerMean
    (fixedRateRho lambda J) (K * dJob) dJob
      (fixedRateSlotThreshold S) lambda

/-- The fraction of retained active star weight gained in one round.  The
factor `16` is the product of the half-mean count threshold and the factor
`8` in the dyadic count-to-weight conversion. -/
noncomputable def fixedRateEndpointTheta
    (lambda J K dJob S : ℕ) : ℝ :=
  fixedRateEndpointEta lambda J K dJob S / (16 * (K : ℝ))

theorem fixedRateEndpointEta_nonneg
    (lambda J K dJob S : ℕ) :
    0 ≤ fixedRateEndpointEta lambda J K dJob S := by
  exact activeSlotUniformLowerMean_nonneg
    (fixedRateRho lambda J) (K * dJob) dJob
      (fixedRateSlotThreshold S) lambda
      (fixedRateRho_nonneg lambda J)

/-- A complete fixed-rate round for the retained dyadic endpoint blocks.

The hypotheses are precisely the degree, codegree, block-size, and scalar
scale conditions used by the one-round local-lemma theorem.  Besides the
global next-slot cap, the conclusion retains the sharper raw deletion
inequality on every active unused slot.
-/
theorem exists_fixedRate_endpointRound
    {β : ℝ} {L K : ℕ}
    (D : G.ActiveEndpointDyadicGrouping H.activeJobs β L K)
    (lambda J S dJob : ℕ)
    (hK : 0 < K) (hlambda : 0 < lambda) (hJ : 0 < J)
    (hSJ : S ≤ J) (h2J : 2 ≤ J) (h2KS : 2 * K ≤ S)
    (hgroupSize : S ≤ 10 * lambda * K)
    (hjobHalf : J ≤ 2 * dJob) (hcodegreeScale : 6 * lambda ≤ J)
    (hjobDegreeLower : ∀ o, dJob ≤ (H.fiber (H.owner o)).card)
    (hjobDegreeUpper : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegreeUpper : ∀ s, H.slotDegree s ≤ S)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hscale : Real.exp
      (-(fixedRateKappa * fixedRateScale lambda S / 320)) ≤
        fixedRateLLLWeight lambda J) :
    ∃ A : Finset Option,
      H.IsPartialMatching A ∧
      (∀ g : G.ActiveEndpointDyadicLargeGroup D,
        fixedRateEndpointEta lambda J K dJob S / 2 <
          (H.coveredGroupJobs
            G.activeEndpointDyadicLargeMembers g A).card) ∧
      (∀ vtx,
        fixedRateEndpointTheta lambda J K dJob S *
            ((∑ e ∈ G.activeStarEdgeSet H.activeJobs vtx, G.weight e) -
              (((L + 1) * (K - 1) : ℕ) : ℝ)) ≤
          ∑ e ∈ (G.activeStarEdgeSet H.activeJobs vtx).filter (H.Covers A),
            G.weight e) ∧
      (∀ s : H.ActiveSlot (fixedRateSlotThreshold S),
        (∀ p ∈ A, s.1 ∉ H.slots p) →
          2 * H.residualSlotDegree A s.1 + fixedRateSlotBudget lambda S ≤
            2 * H.residualSlotDegree ∅ s.1) ∧
      (∀ s, H.residualSlotDegree A s ≤
        fixedRateNextSlotBound lambda S) ∧
      (∀ j, ¬ H.Covers A j →
        H.residualJobDegree ∅ j ≤ H.residualJobDegree A j +
          fixedRateJobBudget lambda S) := by
  have hstruct := H.endpointDyadicLarge_structural G
    (D := D) hjobDegreeLower
  rcases hstruct with ⟨_hactive, hcards, hsupport, hincidence⟩
  have hnumeric := fixedRate_activeSlot_numeric_package
    lambda J S 2 (2 * K) K (K * dJob) dJob
      (fixedRateSlotThreshold S)
      hlambda hJ hSJ h2J h2KS hgroupSize hjobHalf
      (by simp [fixedRateSlotThreshold]; omega)
      hcodegreeScale le_rfl hscale
  rcases hnumeric with ⟨hpairNumeric, hlowerNumeric, hupperNumeric⟩
  have hrho0 := fixedRateRho_nonneg lambda J
  have hrho1 : fixedRateRho lambda J ≤ 1 :=
    (fixedRateRho_le_half lambda J hlambda hJ).trans (by norm_num)
  have hweight0 := fixedRateLLLWeight_nonneg lambda J
  have hweightHalf := fixedRateLLLWeight_le_half lambda J hlambda hJ
  have hlowerThreshold :
      ∀ s : H.ActiveSlot (fixedRateSlotThreshold S),
        (fixedRateSlotBudget lambda S : ℝ) / (3 * lambda : ℕ) ≤
          activeSlotUniformLowerMean
            (fixedRateRho lambda J) (K * dJob) dJob
              (fixedRateSlotThreshold S) lambda / 2 := by
    intro _s
    exact fixedRate_lowerSlotBudget_threshold
      lambda J S K (K * dJob) dJob hlambda hJ hgroupSize hjobHalf
      hcodegreeScale le_rfl
  have hupperThreshold : ∀ _j : G.E,
      4 * (fixedRateRho lambda J *
        ((J : ℝ) * (S : ℝ) / (lambda : ℝ))) ≤
          (fixedRateJobBudget lambda S : ℝ) / (2 * lambda : ℕ) := by
    intro _j
    exact fixedRate_upperJobBudget_threshold lambda J S hlambda hJ
  rcases H.exists_oneRound_activeSlot_uniform_exponential
      (fixedRateRho lambda J) G.activeEndpointDyadicLargeMembers
      lambda hlambda
      (fun _ ↦ fixedRateSlotBudget lambda S)
      (fun _ ↦ fixedRateJobBudget lambda S)
      J S dJob (fixedRateSlotThreshold S) 2 (2 * K) (K * dJob)
      (fixedRateLLLWeight lambda J) (fixedRateLLLWeight lambda J)
      (fixedRateLLLWeight lambda J)
      hrho0 hrho1 hjobDegreeLower hjobDegreeUpper hslotDegreeUpper
      hjobSlot hslotPair (fun g ↦ (hcards g).2.2) hsupport hincidence
      hweight0 hweight0 le_rfl le_rfl hweightHalf
      hlowerThreshold hupperThreshold hpairNumeric hlowerNumeric hupperNumeric with
    ⟨A, hA, hgroup, hslotShrink, hjob⟩
  have hcount : ∀ g : G.ActiveEndpointDyadicLargeGroup D,
      fixedRateEndpointEta lambda J K dJob S / 2 <
        (H.coveredGroupJobs
          G.activeEndpointDyadicLargeMembers g A).card := by
    simpa [fixedRateEndpointEta] using hgroup
  have hc0 : 0 ≤ fixedRateEndpointEta lambda J K dJob S / 2 :=
    div_nonneg (fixedRateEndpointEta_nonneg lambda J K dJob S) (by norm_num)
  have hgainRaw :=
    H.endpointDyadic_coveredActiveIncidentWeight_ge_defaultFloor
      G hK hc0 A hcount
  have htheta :
      fixedRateEndpointTheta lambda J K dJob S =
        (fixedRateEndpointEta lambda J K dJob S / 2) /
          (8 * (K : ℝ)) := by
    simp only [fixedRateEndpointTheta]
    ring
  have hgain : ∀ vtx,
      fixedRateEndpointTheta lambda J K dJob S *
          ((∑ e ∈ G.activeStarEdgeSet H.activeJobs vtx, G.weight e) -
            (((L + 1) * (K - 1) : ℕ) : ℝ)) ≤
        ∑ e ∈ (G.activeStarEdgeSet H.activeJobs vtx).filter (H.Covers A),
          G.weight e := by
    intro vtx
    rw [htheta]
    exact hgainRaw vtx
  have hslotNext : ∀ s, H.residualSlotDegree A s ≤
      fixedRateNextSlotBound lambda S :=
    H.residualSlotDegree_le_of_active_shrink A
      (fixedRateSlotThreshold S) (fixedRateSlotBudget lambda S)
      S (fixedRateNextSlotBound lambda S) hslotDegreeUpper
      (fixedRateSlotThreshold_le_next_add_one lambda S hlambda)
      (fixedRate_two_mul_slotBound_le_next_add_budget lambda S hlambda)
      hslotShrink
  exact ⟨A, hA, hcount, hgain, hslotShrink, hslotNext, hjob⟩

end RankThreeOptionSystem
end WeightedEdgeColoring
