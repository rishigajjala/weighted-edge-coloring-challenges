import WeightedEdgeColoring.RankThreeIsolatedVariableSlackClosedRound
import WeightedEdgeColoring.RankThreeOriginalTypeIsolatedEndpointIteration

/-!
# Corrected variable-slack endpoint step

This is the original-type regular-extension adapter for the corrected
isolated scalar package.  Unlike the older constructor, the collision
moment used by the round and by the square-codegree estimate is definitionally
the same `isolatedVariableMoment d`.
-/

namespace WeightedEdgeColoring
namespace RankThreeOptionSystem

open scoped BigOperators
open SharpFixedSlackNumeric

universe u v w

variable (G : WeightedSimpleGraph.{u})
  {Slot : Type v} {Option : Type w}
  [Fintype Slot] [Fintype Option]
  [DecidableEq Slot] [DecidableEq Option]
  {H : RankThreeOptionSystem G.E Slot Option}

namespace OriginalIterationState

set_option maxHeartbeats 800000 in
noncomputable def EndpointNaturalIsolatedSharpStepData.ofVariableSlackClosed
    {beta alpha gamma delta : ℝ} {L K d S lambda : ℕ}
    (X : OriginalIterationState H)
    (Dg : G.ActiveEndpointDyadicGrouping X.activeJobs beta L K)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (hgamma0 : 0 < gamma) (hgammaHalf : gamma ≤ 1 / 2)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hd : 5 ≤ d) (hSd : S ≤ d) (hK : 0 < K) (hKd : K ≤ d)
    (hlambda : 0 < lambda)
    (hS : S = fixedSlackPaddedSlotTarget gamma d)
    (hscale : 1000 * ((lambda : ℝ) + 1) ≤ gamma * d)
    (hgroupScale : isolatedVariableZ d + 1 ≤
        delta ^ 2 * variableSlackA alpha gamma lambda * K / 64)
    (hslotScale : isolatedVariableZ d + 1 ≤
        variableSlackEta alpha gamma lambda ^ 2 * d /
          (96 * variableSlackA alpha gamma lambda * lambda))
    (hjobScale : isolatedVariableZ d + Real.log 2 ≤
      variableSlackEta alpha gamma lambda ^ 2 * d /
        (16 * variableSlackA alpha gamma lambda * lambda))
    (hblock : 128 * (lambda : ℝ) *
        (isolatedVariableMoment d : ℝ) ^ 2 ≤
      delta * alpha * gamma * K)
    (haSmall : variableSlackA alpha gamma lambda ≤ delta / 96)
    (hsquare : (lambda : ℝ) ^ 2 *
        isolatedVariableMomentUpper d ^ 2 ≤
      variableSlackBeta0 alpha gamma * d) :
    EndpointNaturalIsolatedSharpStepData G X Dg d S lambda
      (variableSlackA alpha gamma lambda) gamma
      (variableSlackEta alpha gamma lambda)
      (2 * variableSlackEta alpha gamma lambda)
      (variableSlackEta alpha gamma lambda) delta (by omega) hSd := by
  refine ⟨?_⟩
  intro trim htrim htwo hslot hjobSlot hslotPair
  let B := (X.activeSystem).inducedOnOptions trim
  let Q := B.cyclicRegularization hSd htwo
  let E : IsRegularExtension B Q d S (max lambda 1) :=
    CyclicRegularization.regularExtension (by omega) hSd htwo htrim hslot
      hjobSlot hslotPair
  have hmax : max lambda 1 = lambda := Nat.max_eq_left hlambda
  have htwoQ : ∀ o, (Q.slots o).card = 2 := by
    intro o
    rcases o with ot | dk
    · simpa [Q, B, cyclicRegularization, cyclicSlots] using htwo ot.1
    · simp [Q, B, cyclicRegularization, cyclicSlots]
  let members := activeEndpointMembers G X Dg
  have hmembers : ∀ g,
      ((E.liftedOldMembers members) g).card ≤ 2 * K := by
    intro g
    simp only [IsRegularExtension.liftedOldMembers, Finset.card_map]
    rw [activeEndpointMembers_card G X Dg g]
    exact (G.activeEndpointDyadicLarge_card_between g).2.trans (by omega)
  have hsupport : ∀ g, K * d ≤
      (linearRowSupport
        (Q.jobGroupCoverageWeight (E.liftedOldMembers members)) g).card := by
    intro g
    rw [E.linearRowSupport_liftedOldMembers_card]
    rw [B.jobGroupCoverage_support_card_eq_sum]
    calc
      K * d ≤ (members g).card * d := by
        apply Nat.mul_le_mul_right
        dsimp [members]
        rw [activeEndpointMembers_card G X Dg g]
        exact (G.activeEndpointDyadicLarge_card_between g).1
      _ = ∑ _j ∈ members g, d := by simp
      _ = ∑ j ∈ members g, (B.fiber j).card := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [htrim j]
  have hincidence : ∀ j,
      ((Finset.univ : Finset (G.ActiveEndpointDyadicLargeGroup Dg)).filter
        (fun g ↦ j ∈ E.liftedOldMembers members g)).card ≤ 2 :=
    E.liftedOldMembers_incidence_le members 2
      (activeEndpointMembers_incidence_le_two G X Dg)
  have hSgap : (S : ℝ) ≤ (1 - gamma) * d := by
    subst S
    apply Nat.floor_le
    exact mul_nonneg (by linarith [hgammaHalf]) (by positivity)
  have hSlower : (1 - gamma) * d - 1 ≤ (S : ℝ) := by
    subst S
    exact (fixedSlackPaddedSlotTarget_lower gamma d).le
  have hscaleMax :
      1000 * (((max lambda 1 : ℕ) : ℝ) + 1) ≤ gamma * d := by
    simpa only [hmax] using hscale
  have hgroupScaleMax : isolatedVariableZ d + 1 ≤
      delta ^ 2 * variableSlackA alpha gamma (max lambda 1) * K / 64 := by
    simpa only [hmax] using hgroupScale
  have hslotScaleMax : isolatedVariableZ d + 1 ≤
      variableSlackEta alpha gamma (max lambda 1) ^ 2 * d /
        (96 * variableSlackA alpha gamma (max lambda 1) * (max lambda 1)) := by
    simpa only [hmax] using hslotScale
  have hjobScaleMax : isolatedVariableZ d + Real.log 2 ≤
      variableSlackEta alpha gamma (max lambda 1) ^ 2 * d /
        (16 * variableSlackA alpha gamma (max lambda 1) * (max lambda 1)) := by
    simpa only [hmax] using hjobScale
  have hblockMax : 128 * ((max lambda 1 : ℕ) : ℝ) *
      (isolatedVariableMoment d : ℝ) ^ 2 ≤
        delta * alpha * gamma * K := by
    simpa only [hmax] using hblock
  have haSmallMax : variableSlackA alpha gamma (max lambda 1) ≤
      delta / 96 := by
    simpa only [hmax] using haSmall
  have hsquareMax : ((max lambda 1 : ℕ) : ℝ) ^ 2 *
      isolatedVariableMomentUpper d ^ 2 ≤
        variableSlackBeta0 alpha gamma * d := by
    simpa only [hmax] using hsquare
  subst S
  have hround := Q.exists_isolatedVariableSlackRound_closed
    (E.liftedOldMembers members) alpha gamma delta (max lambda 1) d
    (fixedSlackPaddedSlotTarget gamma d) K halpha halphaSmall hgamma0
    hgammaHalf hdelta0 hdelta1 hd (by omega) hK hKd hSgap hSlower hscaleMax
    htwoQ E.jobDegree_eq E.slotDegree_eq E.jobSlotCodegree_le
    E.slotPairCodegree_le hmembers hsupport hincidence hgroupScaleMax
    hslotScaleMax hjobScaleMax hblockMax haSmallMax hsquareMax
  rcases hround with ⟨M, hmatching, hgroup, hjobResidual, hslotResidual⟩
  refine ⟨M, hmatching, ?_, ?_, ?_⟩
  · intro g
    simpa [hmax, variableSlackRho, Nat.cast_mul] using hgroup g
  · intro j hj
    simpa only [hmax] using hjobResidual j hj
  · intro s hs
    have h := hslotResidual s hs
    simp only [hmax] at h
    convert h using 1 <;> ring

end OriginalIterationState
end RankThreeOptionSystem
end WeightedEdgeColoring
