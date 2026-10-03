import WeightedEdgeColoring.RankThreeResidualActiveIteration
import WeightedEdgeColoring.RankThreeFixedRateEndpointRound
import WeightedEdgeColoring.RankThreeResidualBlockParameters
import WeightedEdgeColoring.RankThreeResidualMonotonicity

/-!
# Iterating the fixed-rate endpoint round

This file supplies the concrete one-round input to the abstract active
residual iteration.  At round `t` the active stars are split into dyadic
blocks of the canonical size `fixedRateBlockSize lambda (slotCap t)`.  The
fixed-rate endpoint theorem is then applied to the current residual option
system.

The hypotheses deliberately leave the two integer recurrences abstract.
They say exactly that the proposed next job floor pays the rounded job
budget and that the proposed next slot cap is at least the canonical next
cap.  Thus no unproved asymptotic recurrence estimate is hidden here.
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

/-! ## The concrete finite iteration -/

/-- Iterate the fixed-rate dyadic endpoint round for `steps` rounds.

The result retains the exact affine recurrence, including the discarded
small-block floor in each round.  Later asymptotic estimates can therefore
choose their stopping time and bound this recurrence without changing the
finite combinatorial proof. -/
theorem exists_fixedRate_endpointIteration
    {β : ℝ} (L steps lambda J : ℕ)
    (d slotCap : ℕ → ℕ)
    (hβ : 0 < β)
    (hdyadicCover : 1 ≤ dyadicScale β L)
    (hweightLower : ∀ e, β ≤ G.weight e)
    (hlambda : 0 < lambda) (hJ : 0 < J) (h2J : 2 ≤ J)
    (hcodegreeScale : 6 * lambda ≤ J)
    (hjobNext : ∀ t < steps,
      d (t + 1) ≤ d t - fixedRateJobBudget lambda (slotCap t))
    (hjobPositive : ∀ t < steps,
      fixedRateJobBudget lambda (slotCap t) < d t)
    (hslotNext : ∀ t < steps,
      fixedRateNextSlotBound lambda (slotCap t) ≤ slotCap (t + 1))
    (hslotScale : ∀ t < steps, 10 * lambda ≤ slotCap t)
    (hslotJob : ∀ t < steps, slotCap t ≤ J)
    (hjobHalf : ∀ t < steps, J ≤ 2 * d t)
    (hscale : ∀ t < steps, Real.exp
      (-(fixedRateKappa * fixedRateScale lambda (slotCap t) / 320)) ≤
        fixedRateLLLWeight lambda J)
    (hlower0 : ∀ o, d 0 ≤ (H.fiber (H.owner o)).card)
    (hjobUpper0 : ∀ j, (H.fiber j).card ≤ J)
    (hslotUpper0 : ∀ s, H.slotDegree s ≤ slotCap 0)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda) :
    ∃ M : Finset Option,
      H.IsPartialMatching M ∧
      (H.residualSystem M).activeJobs =
        (H.activeJobs.filter fun j ↦ ¬ H.Covers M j) ∧
      (∀ o : H.ResidualOption M,
        d steps ≤ ((H.residualSystem M).fiber
          ((H.residualSystem M).owner o)).card) ∧
      (∀ s, (H.residualSystem M).slotDegree s ≤ slotCap steps) ∧
      ∀ vtx,
        G.residualActiveStarWeight H M vtx ≤
          activeStarAffineBound
            (fun _ ↦ fixedRateCoverageRate lambda)
            (fun t ↦
              ((((L + 1) *
                (fixedRateBlockSize lambda (slotCap t) - 1) : ℕ) : ℝ)))
            (G.residualActiveStarWeight H ∅ vtx) steps := by
  let K : ℕ → ℕ := fun t ↦ fixedRateBlockSize lambda (slotCap t)
  let floor : ℕ → ℝ := fun t ↦
    ((((L + 1) * (K t - 1) : ℕ) : ℝ))
  have htheta0 : ∀ t < steps, 0 ≤ fixedRateCoverageRate lambda := by
    intro _t _ht
    exact fixedRateCoverageRate_nonneg lambda
  have htheta1 : ∀ t < steps, fixedRateCoverageRate lambda ≤ 1 := by
    intro _t _ht
    exact fixedRateCoverageRate_le_one lambda hlambda
  have hthreshold : ∀ t < steps,
      fixedRateSlotThreshold (slotCap t) ≤ slotCap (t + 1) + 1 := by
    intro t ht
    exact (fixedRateSlotThreshold_le_next_add_one
      lambda (slotCap t) hlambda).trans
        (Nat.add_le_add_right (hslotNext t ht) 1)
  have hslotArithmetic : ∀ t < steps,
      2 * slotCap t ≤ 2 * slotCap (t + 1) +
        fixedRateSlotBudget lambda (slotCap t) := by
    intro t ht
    calc
      2 * slotCap t ≤
          2 * fixedRateNextSlotBound lambda (slotCap t) +
            fixedRateSlotBudget lambda (slotCap t) :=
        fixedRate_two_mul_slotBound_le_next_add_budget
          lambda (slotCap t) hlambda
      _ ≤ 2 * slotCap (t + 1) +
            fixedRateSlotBudget lambda (slotCap t) := by
        have hnext := hslotNext t ht
        omega
  apply H.exists_iterated_active_residual_rounds G steps d slotCap
    (fun t ↦ fixedRateJobBudget lambda (slotCap t))
    (fun t ↦ fixedRateSlotThreshold (slotCap t))
    (fun t ↦ fixedRateSlotBudget lambda (slotCap t))
    (fun _ ↦ fixedRateCoverageRate lambda) floor
    htheta0 htheta1 hjobNext hjobPositive hthreshold hslotArithmetic
    hlower0 hslotUpper0
  intro t ht M hM hlowerM hupperM
  let R := H.residualSystem M
  have hSpos : 0 < slotCap t := by
    have := hslotScale t ht
    omega
  have hKpos : 0 < K t := by
    exact fixedRateBlockSize_pos lambda (slotCap t) hlambda hSpos
  have hwindow := fixedRateBlockSize_window
    lambda (slotCap t) hlambda (hslotScale t ht)
  obtain ⟨hgroupSize, hKupper, h2K⟩ := hwindow
  let D : G.ActiveEndpointDyadicGrouping R.activeJobs β L (K t) :=
    Classical.choice (G.exists_activeEndpointDyadicGrouping
      R.activeJobs β L (K t) hβ hdyadicCover
      (fun e _he ↦ hweightLower e) hKpos)
  have hjobUpperR : ∀ j, (R.fiber j).card ≤ J := by
    intro j
    exact (H.residualSystem_fiber_card_le_original M j).trans
      (hjobUpper0 j)
  have hjobSlotR : ∀ j s, R.jobSlotCodegree j s ≤ lambda := by
    intro j s
    exact (H.residualSystem_jobSlotCodegree_le_original M j s).trans
      (hjobSlot j s)
  have hslotPairR : ∀ s q, s ≠ q → R.slotPairCodegree s q ≤ lambda := by
    intro s q hsq
    exact (H.residualSystem_slotPairCodegree_le_original M s q).trans
      (hslotPair s q hsq)
  rcases R.exists_fixedRate_endpointRound G D
      lambda J (slotCap t) (d t)
      hKpos hlambda hJ (hslotJob t ht) h2J h2K hgroupSize
      (hjobHalf t ht) hcodegreeScale hlowerM hjobUpperR hupperM
      hjobSlotR hslotPairR (hscale t ht) with
    ⟨A, hA, _hcount, hgainExact, hslotShrink, _hslotExact, hjobA⟩
  refine ⟨A, hA, hjobA, hslotShrink, ?_⟩
  intro vtx
  let X : ℝ := G.residualActiveStarWeight H M vtx - floor t
  have hgainExact' :
      fixedRateEndpointTheta lambda J (K t) (d t) (slotCap t) * X ≤
        ∑ e ∈ (G.activeStarEdgeSet R.activeJobs vtx).filter (R.Covers A),
          G.weight e := by
    simpa [R, X, floor, WeightedSimpleGraph.residualActiveStarWeight,
      Nat.cast_mul] using hgainExact vtx
  have hthetaLe :
      fixedRateCoverageRate lambda ≤
        fixedRateEndpointTheta lambda J (K t) (d t) (slotCap t) := by
    simpa [fixedRateEndpointTheta, fixedRateEndpointEta, K] using
      fixedRateCoverageRate_le_activeSlot_fraction
        lambda J (slotCap t) (K t) ((K t) * d t) (d t)
          (fixedRateSlotThreshold (slotCap t))
        hlambda hJ hKpos hgroupSize hKupper (hjobHalf t ht)
        (by simp [fixedRateSlotThreshold]; omega) hcodegreeScale le_rfl
  by_cases hX : 0 ≤ X
  · exact (mul_le_mul_of_nonneg_right hthetaLe hX).trans hgainExact'
  · have hthetaNonneg := fixedRateCoverageRate_nonneg lambda
    have hleft : fixedRateCoverageRate lambda * X ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hthetaNonneg (le_of_not_ge hX)
    exact hleft.trans (Finset.sum_nonneg fun e _he ↦ G.weight_nonneg e)

end RankThreeOptionSystem
end WeightedEdgeColoring
