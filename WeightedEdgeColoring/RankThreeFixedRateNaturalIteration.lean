import WeightedEdgeColoring.RankThreeFixedRateEndpointIteration
import WeightedEdgeColoring.RankThreeResidualFixedRateRecurrence
import WeightedEdgeColoring.RankThreeResidualFixedRateDecay

/-!
# Fixed-rate endpoint iteration with the natural integer recurrences

This file substitutes the actual rounded slot-cap and job-floor sequences
into the finite endpoint iteration.  It also bounds every round's dyadic
remainder by the initial one, so the final active-star estimate has one
geometric term and one additive floor.
-/

namespace WeightedEdgeColoring
namespace RankThreeOptionSystem

universe u v w

variable (G : WeightedSimpleGraph.{u})
  {Slot : Type v} {Option : Type w}
  [Fintype Slot] [Fintype Option]
  [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem G.E Slot Option)

/-- The fixed-rate endpoint iteration with its canonical natural sequences. -/
theorem exists_fixedRate_naturalEndpointIteration
    {β : ℝ} (L steps lambda J d0 S0 : ℕ)
    (hβ : 0 < β)
    (hdyadicCover : 1 ≤ dyadicScale β L)
    (hweightLower : ∀ e, β ≤ G.weight e)
    (hlambda : 0 < lambda) (hJ : 0 < J) (h2J : 2 ≤ J)
    (hcodegreeScale : 6 * lambda ≤ J)
    (hd0 : J ≤ d0) (hsmall : 1280 * S0 < J)
    (hlarge : ∀ t < steps,
      2 ≤ fixedRateSlotBudget lambda (fixedRateSlotCap lambda S0 t))
    (hslotScale : ∀ t < steps,
      10 * lambda ≤ fixedRateSlotCap lambda S0 t)
    (hscale : ∀ t < steps, Real.exp
      (-(fixedRateKappa *
          fixedRateScale lambda (fixedRateSlotCap lambda S0 t) / 320)) ≤
        fixedRateLLLWeight lambda J)
    (hlower0 : ∀ o, d0 ≤ (H.fiber (H.owner o)).card)
    (hjobUpper0 : ∀ j, (H.fiber j).card ≤ J)
    (hslotUpper0 : ∀ s, H.slotDegree s ≤ S0)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda) :
    ∃ M : Finset Option,
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
          fixedRateCoverageRetention lambda ^ steps *
              G.residualActiveStarWeight H ∅ vtx +
            ((((L + 1) *
              (fixedRateBlockSize lambda S0 - 1) : ℕ) : ℝ)) := by
  let d : ℕ → ℕ := fixedRateJobFloor lambda d0 S0
  let slotCap : ℕ → ℕ := fixedRateSlotCap lambda S0
  have hjobNext : ∀ t < steps,
      d (t + 1) ≤ d t - fixedRateJobBudget lambda (slotCap t) := by
    intro t _ht
    rfl
  have hjobPositive : ∀ t < steps,
      fixedRateJobBudget lambda (slotCap t) < d t := by
    intro t ht
    apply fixedRate_jobBudget_lt_jobFloor lambda J d0 S0 t hd0 hsmall
    intro i hi
    exact hlarge i (lt_of_le_of_lt hi ht)
  have hslotNext : ∀ t < steps,
      fixedRateNextSlotBound lambda (slotCap t) ≤ slotCap (t + 1) := by
    intro t _ht
    exact le_rfl
  have hslotJob : ∀ t < steps, slotCap t ≤ J := by
    intro t _ht
    exact (fixedRateSlotCap_le_initial lambda S0 t).trans
      (by omega : S0 ≤ J)
  have hjobHalf : ∀ t < steps, J ≤ 2 * d t := by
    intro t ht
    apply fixedRate_job_half_of_small_initial_slot
      lambda J d0 S0 t hd0 hsmall.le
    intro i hi
    exact hlarge i (hi.trans ht)
  rcases H.exists_fixedRate_endpointIteration G L steps lambda J d slotCap
      hβ hdyadicCover hweightLower hlambda hJ h2J hcodegreeScale
      hjobNext hjobPositive hslotNext hslotScale hslotJob hjobHalf hscale
      hlower0 hjobUpper0 hslotUpper0 hjobSlot hslotPair with
    ⟨M, hM, hactiveM, hlowerM, hslotM, hweightM⟩
  refine ⟨M, hM, hactiveM, hlowerM, hslotM, ?_⟩
  intro vtx
  let floor : ℕ → ℝ := fun t ↦
    ((((L + 1) *
      (fixedRateBlockSize lambda (slotCap t) - 1) : ℕ) : ℝ))
  let F : ℝ := ((((L + 1) *
    (fixedRateBlockSize lambda S0 - 1) : ℕ) : ℝ))
  have hfloor0 : 0 ≤ F := by positivity
  have hfloor : ∀ t, floor t ≤ F := by
    intro t
    have hcap : slotCap t ≤ S0 :=
      fixedRateSlotCap_le_initial lambda S0 t
    have hK := fixedRateBlockSize_mono lambda hcap
    dsimp only [floor, F, slotCap]
    exact_mod_cast Nat.mul_le_mul_left (L + 1) (Nat.sub_le_sub_right hK 1)
  have haffine := activeStarAffineBound_const_le
    (fixedRateCoverageRate lambda) floor
    (G.residualActiveStarWeight H ∅ vtx) F
    (fixedRateCoverageRate_nonneg lambda)
    (fixedRateCoverageRate_le_one lambda hlambda) hfloor0 hfloor steps
  calc
    G.residualActiveStarWeight H M vtx ≤
        activeStarAffineBound
          (fun _ ↦ fixedRateCoverageRate lambda) floor
          (G.residualActiveStarWeight H ∅ vtx) steps := by
      simpa [floor, slotCap] using hweightM vtx
    _ ≤ fixedRateCoverageRetention lambda ^ steps *
          G.residualActiveStarWeight H ∅ vtx + F := by
      simpa [fixedRateCoverageRetention] using haffine

end RankThreeOptionSystem
end WeightedEdgeColoring
