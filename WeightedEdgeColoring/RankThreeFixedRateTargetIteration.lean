import WeightedEdgeColoring.RankThreeFixedRateNaturalIteration
import WeightedEdgeColoring.RankThreeResidualFixedRateStopping

/-!
# Stopping the fixed-rate endpoint iteration at a target slot cap

This theorem chooses the first round whose slot cap reaches a prescribed
target.  If the target is at most an `epsilon^2` fraction of the initial cap,
the comparison between slot decay and weight decay turns the geometric term
into `epsilon` times the initial active-star weight.
-/

namespace WeightedEdgeColoring
namespace RankThreeOptionSystem

universe u v w

variable (G : WeightedSimpleGraph.{u})
  {Slot : Type v} {Option : Type w}
  [Fintype Slot] [Fintype Option]
  [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem G.E Slot Option)

theorem exists_fixedRate_endpointIteration_to_target
    {β : ℝ} (L lambda J d0 S0 target : ℕ) (epsilon : ℝ)
    (hβ : 0 < β)
    (hdyadicCover : 1 ≤ dyadicScale β L)
    (hweightLower : ∀ e, β ≤ G.weight e)
    (hlambda : 0 < lambda) (hJ : 0 < J) (h2J : 2 ≤ J)
    (hS0 : 0 < S0)
    (hcodegreeScale : 6 * lambda ≤ J)
    (hd0 : J ≤ d0) (hsmall : 1280 * S0 < J)
    (hepsilon : 0 ≤ epsilon)
    (htarget : (target : ℝ) ≤ epsilon ^ 2 * (S0 : ℝ))
    (htargetScale : 10 * lambda ≤ target + 1)
    (hbudgetRange : ∀ S, target < S → S ≤ S0 →
      2 ≤ fixedRateSlotBudget lambda S)
    (hscaleRange : ∀ S, target < S → S ≤ S0 → Real.exp
      (-(fixedRateKappa * fixedRateScale lambda S / 320)) ≤
        fixedRateLLLWeight lambda J)
    (hlower0 : ∀ o, d0 ≤ (H.fiber (H.owner o)).card)
    (hjobUpper0 : ∀ j, (H.fiber j).card ≤ J)
    (hslotUpper0 : ∀ s, H.slotDegree s ≤ S0)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda) :
    ∃ (steps : ℕ) (M : Finset Option),
      fixedRateSlotCap lambda S0 steps ≤ target ∧
      H.IsPartialMatching M ∧
      (H.residualSystem M).activeJobs =
        (H.activeJobs.filter fun j ↦ ¬ H.Covers M j) ∧
      (∀ o : H.ResidualOption M,
        fixedRateJobFloor lambda d0 S0 steps ≤
          ((H.residualSystem M).fiber
            ((H.residualSystem M).owner o)).card) ∧
      (∀ s, (H.residualSystem M).slotDegree s ≤
        fixedRateSlotCap lambda S0 steps) ∧
      ∀ vtx,
        G.residualActiveStarWeight H M vtx ≤
          epsilon * G.residualActiveStarWeight H ∅ vtx +
            ((((L + 1) *
              (fixedRateBlockSize lambda S0 - 1) : ℕ) : ℝ)) := by
  rcases exists_fixedRate_first_crossing lambda S0 target hlambda
      hbudgetRange with ⟨steps, hcap, habove, hlarge⟩
  have hslotScale : ∀ t < steps,
      10 * lambda ≤ fixedRateSlotCap lambda S0 t := by
    intro t ht
    have := habove t ht
    omega
  have hscale : ∀ t < steps, Real.exp
      (-(fixedRateKappa *
          fixedRateScale lambda (fixedRateSlotCap lambda S0 t) / 320)) ≤
        fixedRateLLLWeight lambda J := by
    intro t ht
    exact hscaleRange _ (habove t ht)
      (fixedRateSlotCap_le_initial lambda S0 t)
  rcases H.exists_fixedRate_naturalEndpointIteration G
      L steps lambda J d0 S0 hβ hdyadicCover hweightLower
      hlambda hJ h2J hcodegreeScale hd0 hsmall hlarge hslotScale hscale
      hlower0 hjobUpper0 hslotUpper0 hjobSlot hslotPair with
    ⟨M, hM, hactiveM, hlowerM, hslotM, hweightM⟩
  have hcapReal : (fixedRateSlotCap lambda S0 steps : ℝ) ≤
      epsilon ^ 2 * (S0 : ℝ) := by
    have hcapCast : (fixedRateSlotCap lambda S0 steps : ℝ) ≤
        (target : ℝ) := by exact_mod_cast hcap
    exact hcapCast.trans htarget
  have hfactor := fixedRateCoverageRetention_pow_le_of_slotCap
    lambda S0 steps epsilon hlambda hS0 hepsilon hcapReal
  refine ⟨steps, M, hcap, hM, hactiveM, hlowerM, hslotM, ?_⟩
  intro vtx
  have hweight0 : 0 ≤ G.residualActiveStarWeight H ∅ vtx := by
    apply Finset.sum_nonneg
    intro e _he
    exact G.weight_nonneg e
  calc
    G.residualActiveStarWeight H M vtx ≤
        fixedRateCoverageRetention lambda ^ steps *
            G.residualActiveStarWeight H ∅ vtx +
          ((((L + 1) *
            (fixedRateBlockSize lambda S0 - 1) : ℕ) : ℝ)) :=
      hweightM vtx
    _ ≤ epsilon * G.residualActiveStarWeight H ∅ vtx +
          ((((L + 1) *
            (fixedRateBlockSize lambda S0 - 1) : ℕ) : ℝ)) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hfactor hweight0) le_rfl

end RankThreeOptionSystem
end WeightedEdgeColoring
