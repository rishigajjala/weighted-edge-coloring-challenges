import WeightedEdgeColoring.RankThreeOriginalTypeEndpointIteration
import WeightedEdgeColoring.RankThreeOriginalTypeIsolatedSharpStep
import WeightedEdgeColoring.RankThreeIsolatedVariableSlackRound

/-!
# Endpoint iteration driven by isolated sharp rounds

This is the dependent endpoint-block iteration with the pair-event round
replaced by the raw-sample-then-isolate round.  The trace and its active-star
recurrence are unchanged.
-/

open scoped BigOperators
open WeightedEdgeColoring.SharpFixedSlackNumeric

namespace WeightedEdgeColoring
namespace RankThreeOptionSystem

universe u v w

variable (G : WeightedSimpleGraph.{u})
  {Slot : Type v} {Option : Type w}
  [Fintype Slot] [Fintype Option]
  [DecidableEq Slot] [DecidableEq Option]
  {H : RankThreeOptionSystem G.E Slot Option}

namespace OriginalIterationState

/-- Per-round input for the isolated endpoint iteration.  The conclusion
of `numeric` is exactly the regular-extension round consumed by
`exists_activeIsolatedSharpRound`. -/
structure EndpointNaturalIsolatedSharpStepData
    {beta : ℝ} {L K : ℕ}
    (X : OriginalIterationState H)
    (D : G.ActiveEndpointDyadicGrouping X.activeJobs beta L K)
    (d S lambda : ℕ)
    (a gamma etaJob etaLoad etaCollision delta : ℝ)
    (hd : 0 < d) (hSd : S ≤ d) where
  numeric : ∀
    (trim : Finset (X.system.ActiveJobOption X.activeJobs))
    (htrim : ∀ j,
      ((((X.activeSystem).inducedOnOptions trim).fiber j).card) = d)
    (htwo : ∀ o : KeptOption trim,
      ((((X.activeSystem).inducedOnOptions trim).slots o).card) = 2)
    (hslot : ∀ s,
      ((X.activeSystem).inducedOnOptions trim).slotDegree s ≤ S)
    (hjobSlot : ∀ j s,
      ((X.activeSystem).inducedOnOptions trim).jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t →
      ((X.activeSystem).inducedOnOptions trim).slotPairCodegree s t ≤ lambda),
    let B := (X.activeSystem).inducedOnOptions trim
    let Q := B.cyclicRegularization hSd htwo
    let E : IsRegularExtension B Q d S (max lambda 1) :=
      CyclicRegularization.regularExtension hd hSd htwo htrim hslot
        hjobSlot hslotPair
    ∃ M : Finset (B.CyclicOption d S),
      Q.IsPartialMatching M ∧
      (∀ g, (1 - delta) * (a / (d : ℝ)) * (K * d) <
        ∑ q ∈ M, Q.jobGroupCoverageWeight
          (E.liftedOldMembers (activeEndpointMembers G X D)) g q) ∧
      (∀ j, ¬ Q.Covers M j →
        (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d ≤
          Q.residualJobDegree M j) ∧
      (∀ s, (∀ q ∈ M, s ∉ Q.slots q) →
        (Q.residualSlotDegree M s : ℝ) ≤
          (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
            etaLoad + etaCollision) * d)

set_option maxHeartbeats 800000 in
/-- Build the endpoint step data from the concrete isolated scalar
inequalities.  All option-system bounds are supplied by cyclic
regularization and the endpoint grouping. -/
noncomputable def EndpointNaturalIsolatedSharpStepData.ofSharpConcrete
    {beta : ℝ} {L K d S lambda : ℕ}
    (X : OriginalIterationState H)
    (Dg : G.ActiveEndpointDyadicGrouping X.activeJobs beta L K)
    (hd : 0 < d) (hSd : S ≤ d)
    (hKpos : 0 < K) (hlambda : 0 < lambda)
    (hS : S = fixedSlackPaddedSlotTarget sharpConcreteGamma d)
    (hscale : 1000 * max lambda 1 ≤ d)
    (hrowHalf : exponentialRowWeight (sharpConcreteZ d) ≤ 1 / 2)
    (hcollisionRow : collisionWeight (sharpConcreteMomentOrder d) ≤
      exponentialRowWeight (sharpConcreteZ d))
    (hgroupRate : sharpConcreteZ d +
        2 * exponentialRowWeight (sharpConcreteZ d) *
          (isolatedLowerNeighborBudget
            (groupSupportBudget (2 * K) d) 2 d : ℝ) ≤
      -(((sharpConcreteDelta / 2) * (1 - sharpConcreteDelta / 2) +
          (Real.exp (-(sharpConcreteDelta / 2)) - 1)) *
        (sharpConcreteRho d (max lambda 1) * (K * d : ℕ))))
    (hslotRate : sharpConcreteZ d +
        2 * exponentialRowWeight (sharpConcreteZ d) *
          (isolatedLowerNeighborBudget (slotSupportBudget d) 2 d : ℝ) ≤
      sharpConcreteSlotGap d S (max lambda 1) ^ 2 /
        (4 * sharpConcreteSlotMean d S (max lambda 1)))
    (hupperRate : sharpConcreteZ d + Real.log 2 ≤
      sharpConcreteJobGap d S (max lambda 1) ^ 2 /
        (4 * sharpConcreteJobMean d S (max lambda 1)))
    (hupperProduct : exponentialRowWeight (sharpConcreteZ d) *
      (increasingNeighborBudget (upperSupportBudget d) 2 d : ℝ) ≤ 1 / 2)
    (hgroupLossProduct : exponentialRowWeight (sharpConcreteZ d) *
      (increasingNeighborBudget
        (isolatedConflictSupportBudget (groupSupportBudget (2 * K) d) d)
          2 d : ℝ) ≤ 1 / 2)
    (hslotLossProduct : exponentialRowWeight (sharpConcreteZ d) *
      (increasingNeighborBudget
        (isolatedConflictSupportBudget (slotSupportBudget d) d) 2 d : ℝ) ≤
        1 / 2)
    (hcollisionProduct : exponentialRowWeight (sharpConcreteZ d) *
      (increasingNeighborBudget (slotSupportBudget d) 2 d : ℝ) ≤ 1 / 2)
    (hblock : sharpEndpointBlockFactor * max lambda 1 *
      sharpConcreteMomentOrder d ^ 2 ≤ K)
    (hsquare : ((max lambda 1 : ℕ) : ℝ) ^ 2 *
        sharpConcreteMomentUpper d ^ 2 ≤ sharpIsolationBeta0 * d) :
    EndpointNaturalIsolatedSharpStepData G X Dg d S lambda
      (sharpScaledA lambda) sharpConcreteGamma
      (sharpScaledEta lambda) (2 * sharpScaledEta lambda)
      (sharpScaledEta lambda) sharpConcreteDelta hd hSd := by
  have hmax : max lambda 1 = lambda := Nat.max_eq_left hlambda
  refine ⟨?_⟩
  intro trim htrim htwo hslot hjobSlot hslotPair
  let B := (X.activeSystem).inducedOnOptions trim
  let Q := B.cyclicRegularization hSd htwo
  let E : IsRegularExtension B Q d S (max lambda 1) :=
    CyclicRegularization.regularExtension hd hSd htwo htrim hslot
      hjobSlot hslotPair
  have hell : 0 < max lambda 1 := by omega
  have htwoQ : ∀ o, (Q.slots o).card = 2 := by
    intro o
    rcases o with ot | dk
    · simpa [Q, B, cyclicRegularization, cyclicSlots] using htwo ot.1
    · simp [Q, B, cyclicRegularization, cyclicSlots]
  have hjobQ : ∀ j, (Q.fiber j).card = d := E.jobDegree_eq
  have hslotQ : ∀ s, Q.slotDegree s = S := E.slotDegree_eq
  let members := activeEndpointMembers G X Dg
  have hmembersOld : ∀ g, (members g).card ≤ 2 * K := by
    intro g
    rw [show (members g).card =
      (G.activeEndpointDyadicLargeMembers g).card by
        exact activeEndpointMembers_card G X Dg g]
    exact (G.activeEndpointDyadicLarge_card_between g).2.trans (by omega)
  have hmembers : ∀ g, ((E.liftedOldMembers members) g).card ≤ 2 * K := by
    intro g
    simpa [IsRegularExtension.liftedOldMembers] using hmembersOld g
  have hsupportOld : ∀ g,
      K * d ≤ (linearRowSupport (B.jobGroupCoverageWeight members) g).card := by
    intro g
    rw [B.jobGroupCoverage_support_card_eq_sum members g]
    calc
      K * d ≤ (members g).card * d := by
        apply Nat.mul_le_mul_right d
        rw [show (members g).card =
          (G.activeEndpointDyadicLargeMembers g).card by
            exact activeEndpointMembers_card G X Dg g]
        exact (G.activeEndpointDyadicLarge_card_between g).1
      _ = ∑ _j ∈ members g, d := by simp
      _ = ∑ j ∈ members g, (B.fiber j).card := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [htrim j]
  have hsupport : ∀ g,
      K * d ≤ (linearRowSupport
        (Q.jobGroupCoverageWeight (E.liftedOldMembers members)) g).card := by
    intro g
    rw [E.linearRowSupport_liftedOldMembers_card members g]
    exact hsupportOld g
  have hincidenceOld : ∀ j,
      ((Finset.univ : Finset (G.ActiveEndpointDyadicLargeGroup Dg)).filter
        (fun g ↦ j ∈ members g)).card ≤ 2 := by
    exact activeEndpointMembers_incidence_le_two G X Dg
  have hincidence : ∀ j,
      ((Finset.univ : Finset (G.ActiveEndpointDyadicLargeGroup Dg)).filter
        (fun g ↦ j ∈ E.liftedOldMembers members g)).card ≤ 2 :=
    E.liftedOldMembers_incidence_le members 2 hincidenceOld
  have hgroupLoss := sharpScaled_groupLossEnvelope_of_blockScale
    d (max lambda 1) K (sharpConcreteMomentOrder d) hd hell
    (sharpConcreteMomentOrder_pos d hd) hblock
  have hIsolation := sharpScaled_isolationBudget_of_square_ratio
    d (max lambda 1) hd hell hsquare
  subst S
  simpa only [members, Nat.cast_mul] using
    Q.exists_isolatedSharpFixedSlackRound_sharpConcretePadded
      (E.liftedOldMembers members) lambda d 2 (2 * K) (K * d)
      hd hlambda (Nat.mul_pos hKpos hd) (by simpa [hmax] using hscale)
      htwoQ hjobQ hslotQ
      (by simpa [hmax] using E.jobSlotCodegree_le)
      (by simpa [hmax] using E.slotPairCodegree_le) hmembers hsupport hincidence
      hrowHalf hcollisionRow (by simpa [hmax] using hgroupRate)
      (by simpa [hmax] using hslotRate)
      (by simpa [hmax] using hupperRate) hupperProduct
      (by simpa [hmax] using hgroupLoss) hgroupLossProduct hslotLossProduct
      hcollisionProduct (by simpa [hmax] using hIsolation)

set_option maxHeartbeats 800000 in
/-- Variable-slack constructor for the endpoint step.  It is the analogue
of `ofSharpConcrete`, but its maintained gap is the application parameter
`gamma` and its proposal is `alpha*gamma/lambda`. -/
noncomputable def EndpointNaturalIsolatedSharpStepData.ofVariableSlack
    {beta alpha gamma delta z : ℝ} {L K d S lambda k : ℕ}
    (X : OriginalIterationState H)
    (Dg : G.ActiveEndpointDyadicGrouping X.activeJobs beta L K)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (hgamma0 : 0 < gamma) (hgammaHalf : gamma ≤ 1 / 2)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hd : 0 < d) (hSd : S ≤ d) (hKpos : 0 < K)
    (hlambda : 0 < lambda) (hk : 0 < k)
    (hkEq : k = sharpConcreteMomentOrder d)
    (hS : S = fixedSlackPaddedSlotTarget gamma d)
    (hslotMean : 0 < variableSlackSlotMean alpha gamma d S lambda)
    (hslotGap0 : 0 ≤ variableSlackSlotGap alpha gamma d S lambda)
    (hslotGap2 : variableSlackSlotGap alpha gamma d S lambda ≤
      2 * variableSlackSlotMean alpha gamma d S lambda)
    (hjobMean : 0 < variableSlackJobMean alpha gamma d S lambda)
    (hjobGap0 : 0 ≤ variableSlackJobGap alpha gamma d S lambda)
    (hjobGap2 : variableSlackJobGap alpha gamma d S lambda ≤
      2 * variableSlackJobMean alpha gamma d S lambda)
    (hrowHalf : exponentialRowWeight z ≤ 1 / 2)
    (hcollisionRow : collisionWeight k ≤ exponentialRowWeight z)
    (hgroupRate : z + 2 * exponentialRowWeight z *
        (isolatedLowerNeighborBudget
          (groupSupportBudget (2 * K) d) 2 d : ℝ) ≤
      -(((delta / 2) * (1 - delta / 2) +
          (Real.exp (-(delta / 2)) - 1)) *
        (variableSlackRho alpha gamma d lambda * (K * d : ℕ))))
    (hslotRate : z + 2 * exponentialRowWeight z *
        (isolatedLowerNeighborBudget (slotSupportBudget d) 2 d : ℝ) ≤
      variableSlackSlotGap alpha gamma d S lambda ^ 2 /
        (4 * variableSlackSlotMean alpha gamma d S lambda))
    (hupperRate : z + Real.log 2 ≤
      variableSlackJobGap alpha gamma d S lambda ^ 2 /
        (4 * variableSlackJobMean alpha gamma d S lambda))
    (hupperProduct : exponentialRowWeight z *
      (increasingNeighborBudget (upperSupportBudget d) 2 d : ℝ) ≤ 1 / 2)
    (hgroupLossProduct : exponentialRowWeight z *
      (increasingNeighborBudget
        (isolatedConflictSupportBudget (groupSupportBudget (2 * K) d) d)
          2 d : ℝ) ≤ 1 / 2)
    (hslotLossProduct : exponentialRowWeight z *
      (increasingNeighborBudget
        (isolatedConflictSupportBudget (slotSupportBudget d) d) 2 d : ℝ) ≤
        1 / 2)
    (hcollisionProduct : exponentialRowWeight z *
      (increasingNeighborBudget (slotSupportBudget d) 2 d : ℝ) ≤ 1 / 2)
    (hblock : 128 * (lambda : ℝ) * (k : ℝ) ^ 2 ≤
      delta * alpha * gamma * K)
    (haSmall : variableSlackA alpha gamma lambda ≤ delta / 96)
    (hsquare : (lambda : ℝ) ^ 2 * sharpConcreteMomentUpper d ^ 2 ≤
      variableSlackBeta0 alpha gamma * d) :
    EndpointNaturalIsolatedSharpStepData G X Dg d S lambda
      (variableSlackA alpha gamma lambda) gamma
      (variableSlackEta alpha gamma lambda)
      (2 * variableSlackEta alpha gamma lambda)
      (variableSlackEta alpha gamma lambda) delta hd hSd := by
  refine ⟨?_⟩
  intro trim htrim htwo hslot hjobSlot hslotPair
  let B := (X.activeSystem).inducedOnOptions trim
  let Q := B.cyclicRegularization hSd htwo
  let E : IsRegularExtension B Q d S (max lambda 1) :=
    CyclicRegularization.regularExtension hd hSd htwo htrim hslot
      hjobSlot hslotPair
  have hmax : max lambda 1 = lambda := Nat.max_eq_left hlambda
  have htwoQ : ∀ o, (Q.slots o).card = 2 := by
    intro o
    rcases o with ot | dk
    · simpa [Q, B, cyclicRegularization, cyclicSlots] using htwo ot.1
    · simp [Q, B, cyclicRegularization, cyclicSlots]
  have hmembers : ∀ g,
      ((E.liftedOldMembers (activeEndpointMembers G X Dg)) g).card ≤
        2 * K := by
    intro g
    simp only [IsRegularExtension.liftedOldMembers, Finset.card_map]
    rw [activeEndpointMembers_card G X Dg g]
    exact (G.activeEndpointDyadicLarge_card_between g).2.trans (by omega)
  have hsupport : ∀ g, K * d ≤
      (linearRowSupport (Q.jobGroupCoverageWeight
        (E.liftedOldMembers (activeEndpointMembers G X Dg))) g).card := by
    intro g
    rw [E.linearRowSupport_liftedOldMembers_card]
    rw [B.jobGroupCoverage_support_card_eq_sum]
    calc
      K * d ≤ (activeEndpointMembers G X Dg g).card * d := by
        apply Nat.mul_le_mul_right
        rw [activeEndpointMembers_card G X Dg g]
        exact (G.activeEndpointDyadicLarge_card_between g).1
      _ = ∑ _j ∈ activeEndpointMembers G X Dg g, d := by simp
      _ = ∑ j ∈ activeEndpointMembers G X Dg g, (B.fiber j).card := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [htrim j]
  have hincidence : ∀ j,
      ((Finset.univ : Finset (G.ActiveEndpointDyadicLargeGroup Dg)).filter
        (fun g ↦ j ∈ E.liftedOldMembers
          (activeEndpointMembers G X Dg) g)).card ≤ 2 :=
    E.liftedOldMembers_incidence_le (activeEndpointMembers G X Dg) 2
      (activeEndpointMembers_incidence_le_two G X Dg)
  have hgroupLoss := variableSlack_groupLossEnvelope_of_blockScale
    alpha gamma delta d lambda K k hd hlambda hk
      halpha hgamma0 hdelta0 hdelta1 haSmall hblock
  have hIsolation := variableSlack_isolationBudget_of_square_ratio
    alpha gamma (variableSlackBeta0 alpha gamma) d lambda hd hlambda
    halpha.le hgamma0.le (by unfold variableSlackBeta0; positivity)
    hsquare (variableSlack_fixed_isolation_budget
      halpha halphaSmall hgamma0 (hgammaHalf.trans (by norm_num)))
  have hIsolationK :
      18 * variableSlackA alpha gamma lambda ^ 2 * d +
          72 * variableSlackA alpha gamma lambda * k * lambda +
          24 * k ^ 2 * lambda ≤
        variableSlackEta alpha gamma lambda * d := by
    simpa only [hkEq] using hIsolation
  have hSgap : (S : ℝ) ≤ (1 - gamma) * d := by
    subst S
    apply Nat.floor_le
    exact mul_nonneg (by linarith [hgammaHalf]) (by positivity)
  simpa only [variableSlackRho, Nat.cast_mul] using
    Q.exists_isolatedVariableSlackRound
      (E.liftedOldMembers (activeEndpointMembers G X Dg))
      alpha gamma delta z lambda d S 2 (2 * K) (K * d) k
      halpha halphaSmall hgamma0 hgammaHalf hdelta0 hdelta1 hd
      hlambda (Nat.mul_pos hKpos hd) hSgap htwoQ E.jobDegree_eq
      E.slotDegree_eq (by simpa [hmax] using E.jobSlotCodegree_le)
      (by simpa [hmax] using E.slotPairCodegree_le) hmembers
      hsupport hincidence hslotMean hslotGap0 hslotGap2 hjobMean
      hjobGap0 hjobGap2 hrowHalf hcollisionRow hgroupRate hslotRate
      hupperRate hupperProduct hgroupLoss hgroupLossProduct
      hslotLossProduct hcollisionProduct hIsolationK

set_option maxHeartbeats 1600000 in
/-- Natural endpoint iteration using isolated rounds. -/
theorem exists_endpointNaturalIsolatedSharpIteration
    {beta : ℝ}
    (initial : OriginalIterationState H)
    (steps d0 S0 lambda L K : ℕ)
    (a gamma etaJob etaLoad etaCollision delta : ℝ)
    (hbeta : 0 < beta)
    (hdyadicCover : 1 ≤ dyadicScale beta L)
    (hweightLower : ∀ e, beta ≤ G.weight e)
    (hK : 0 < K) (hlambda : 0 < lambda)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hdelta1 : delta ≤ 1) (ha0 : 0 ≤ a)
    (htheta1 : (1 - delta) * a / 8 ≤ 1)
    (hjobRate0 : 0 ≤ WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob)
    (hslotRate0 : 0 ≤
      WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
        etaLoad + etaCollision)
    (herror : (1 - gamma) * etaJob + etaLoad + etaCollision ≤
      a * gamma * (1 - gamma))
    (hgap0 : (S0 : ℝ) ≤ (1 - gamma) * d0)
    (hmargin : ∀ n < steps, 1 - gamma ≤
      (a * gamma * (1 - gamma) -
        ((1 - gamma) * etaJob + etaLoad + etaCollision)) *
          naturalSharpJobScale d0 a gamma etaJob n)
    (hpositive : ∀ n < steps,
      0 < naturalSharpJobScale d0 a gamma etaJob n)
    (hnextPositive : ∀ n < steps,
      0 < (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) *
        naturalSharpJobScale d0 a gamma etaJob n)
    (htwo : ∀ o, (H.slots o).card = 2)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hdegree0 : ∀ j, (initial.system.fiber j).Nonempty →
      d0 ≤ (initial.system.fiber j).card)
    (hslot0 : ∀ s, initial.system.slotDegree s ≤ S0)
    (data : ∀ n (hn : n < steps) (X : OriginalIterationState H)
      (D : G.ActiveEndpointDyadicGrouping X.activeJobs beta L K),
      EndpointNaturalIsolatedSharpStepData G X D
        (naturalSharpJobScale d0 a gamma etaJob n)
        (fixedSlackPaddedSlotTarget gamma
          (naturalSharpJobScale d0 a gamma etaJob n))
        lambda a gamma etaJob etaLoad etaCollision delta
        (hpositive n hn)
        (fixedSlackPaddedSlotTarget_le gamma
          (naturalSharpJobScale d0 a gamma etaJob n) hgamma0 hgamma1)) :
    ∃ final : OriginalIterationState H,
      EndpointSharpTrace G beta a delta L K steps initial final ∧
      (∀ j, (final.system.fiber j).Nonempty →
        naturalSharpJobScale d0 a gamma etaJob steps ≤
          (final.system.fiber j).card) ∧
      (∀ s, final.system.slotDegree s ≤
        naturalSharpSlotCap S0 d0 a gamma etaJob etaLoad etaCollision steps) ∧
      ∀ vtx,
        stateActiveStarWeight G final vtx ≤
          (1 - (1 - delta) * a / 8) ^ steps *
              stateActiveStarWeight G initial vtx +
            (((L + 1) * (K - 1) : ℕ) : ℝ) := by
  let d : ℕ → ℕ := naturalSharpJobScale d0 a gamma etaJob
  let cap : ℕ → ℕ :=
    naturalSharpSlotCap S0 d0 a gamma etaJob etaLoad etaCollision
  have hgap : ∀ n, n ≤ steps →
      (cap n : ℝ) ≤ (1 - gamma) * d n := by
    intro n hn
    induction n with
    | zero => exact hgap0
    | succ n ih =>
        exact naturalSharp_rounding_preserves_gap
          (naturalSharpJobScale d0 a gamma etaJob n)
          a gamma etaJob etaLoad etaCollision hgamma0 hgamma1
          hjobRate0 hslotRate0 (hmargin n (Nat.lt_of_succ_le hn))
  have hiter : ∀ n, n ≤ steps →
      ∃ X : OriginalIterationState H,
        EndpointSharpTrace G beta a delta L K n initial X ∧
        (∀ j, (X.system.fiber j).Nonempty →
          d n ≤ (X.system.fiber j).card) ∧
        (∀ s, X.system.slotDegree s ≤ cap n) := by
    intro n hn
    induction n with
    | zero =>
        exact ⟨initial, EndpointSharpTrace.zero initial, hdegree0, hslot0⟩
    | succ n ih =>
        have hnlt : n < steps := Nat.lt_of_succ_le hn
        rcases ih (Nat.le_of_succ_le hn) with
          ⟨X, htrace, hdegreeX, hslotX⟩
        let D : G.ActiveEndpointDyadicGrouping X.activeJobs beta L K :=
          Classical.choice (G.exists_activeEndpointDyadicGrouping
            X.activeJobs beta L K hbeta hdyadicCover
            (fun e _he ↦ hweightLower e) hK)
        let members := activeEndpointMembers G X D
        have hmembers : ∀ g, (members g).card ≤ 2 * K := by
          intro g
          rw [show (members g).card =
            (G.activeEndpointDyadicLargeMembers g).card by
              exact activeEndpointMembers_card G X D g]
          exact (G.activeEndpointDyadicLarge_card_between g).2.trans (by omega)
        have hgroupSize : ∀ g, K * d n ≤ (members g).card * d n := by
          intro g
          apply Nat.mul_le_mul_right (d n)
          rw [show (members g).card =
            (G.activeEndpointDyadicLargeMembers g).card by
              exact activeEndpointMembers_card G X D g]
          exact (G.activeEndpointDyadicLarge_card_between g).1
        have htwoX : ∀ o : KeptOption X.keep,
            (X.system.slots o).card = 2 := fun o ↦ htwo o.1
        have hjobSlotX : ∀ j s,
            X.system.jobSlotCodegree j s ≤ lambda := by
          intro j s
          exact (H.inducedOnOptions_jobSlotCodegree_le X.keep j s).trans
            (hjobSlot j s)
        have hslotPairX : ∀ s t, s ≠ t →
            X.system.slotPairCodegree s t ≤ lambda := by
          intro s t hst
          exact (H.inducedOnOptions_slotPairCodegree_le X.keep s t).trans
            (hslotPair s t hst)
        have hslotCap0 : 0 ≤
            (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
              etaLoad + etaCollision) * d n :=
          mul_nonneg hslotRate0 (Nat.cast_nonneg _)
        have hcapPad : cap n ≤ fixedSlackPaddedSlotTarget gamma (d n) :=
          nat_le_fixedSlackPaddedSlotTarget gamma (d n) (cap n)
            hgamma1 (hgap n (Nat.le_of_lt hnlt))
        have hslotPad : ∀ s,
            X.system.slotDegree s ≤ fixedSlackPaddedSlotTarget gamma (d n) :=
          fun s ↦ (hslotX s).trans hcapPad
        let stepData := data n hnlt X D
        have hnumeric := stepData.numeric
        dsimp only [d, members] at hnumeric
        have hround := exists_activeIsolatedSharpRound X (d n)
            (fixedSlackPaddedSlotTarget gamma (d n)) lambda (2 * K)
            (K * d n) a gamma etaJob etaLoad etaCollision delta
            (hpositive n hnlt)
            (fixedSlackPaddedSlotTarget_le gamma (d n) hgamma0 hgamma1)
            hdegreeX htwoX hslotPad hjobSlotX hslotPairX
            (Nat.floor_le
              (mul_nonneg (sub_nonneg.mpr hgamma1) (Nat.cast_nonneg _)))
            hgamma1 herror hslotCap0 members hmembers hgroupSize
            (by simpa only [Nat.cast_mul] using hnumeric)
        rcases hround with
          ⟨W, hgood⟩
        let Y := W.result
        have hdegreeY : ∀ j, (Y.system.fiber j).Nonempty →
            d (n + 1) ≤ (Y.system.fiber j).card := by
          intro j hj
          have hlower := hgood.originalKeep_nonempty_fiber_lower j (by
            simpa [Y, OriginalIterationState.system] using hj)
          have harg : 0 ≤
              (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d n :=
            mul_nonneg hjobRate0 (Nat.cast_nonneg _)
          have hreal : ((d (n + 1) : ℕ) : ℝ) ≤
              ((H.inducedOnOptions W.originalKeep).fiber j).card :=
            (Nat.floor_le harg).trans hlower
          have hnat : d (n + 1) ≤
              ((H.inducedOnOptions W.originalKeep).fiber j).card := by
            exact_mod_cast hreal
          simpa [Y, OriginalIterationState.system] using hnat
        have hslotY : ∀ s, Y.system.slotDegree s ≤ cap (n + 1) := by
          intro s
          have hreal := hgood.originalKeep_slotDegree s
          have harg : 0 ≤
              (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
                etaLoad + etaCollision) * d n :=
            mul_nonneg hslotRate0 (Nat.cast_nonneg _)
          have hnat :
              (H.inducedOnOptions W.originalKeep).slotDegree s ≤
                ⌊(WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
                    etaLoad + etaCollision) * d n⌋₊ :=
            (Nat.le_floor_iff harg).mpr hreal
          simpa [Y, OriginalIterationState.system, cap, d,
            naturalSharpSlotCap] using hnat
        have htraceY : EndpointSharpTrace G beta a delta L K (n + 1)
            initial Y := by
          exact EndpointSharpTrace.succ htrace D W
            (hgood.result_activeJobs (hnextPositive n hnlt))
            (hgood.endpointBlock_count G X D W (hpositive n hnlt)) rfl
        exact ⟨Y, htraceY, hdegreeY, hslotY⟩
  rcases hiter steps le_rfl with ⟨final, htrace, hdegree, hslot⟩
  have hweight := htrace.stateActiveStarWeight_le G hK
    hdelta1 ha0 htheta1
  exact ⟨final, htrace, hdegree, hslot, hweight⟩

/-- Fixed-constant multiple-round partial rounding.  Every combinatorial,
recurrence, and endpoint-weight conclusion is closed; the sole remaining
per-round input is the concrete isolated scalar record `data`. -/
theorem exists_endpointSharpConcreteIsolatedIteration
    {beta : ℝ}
    (initial : OriginalIterationState H)
    (steps d0 S0 lambda L K : ℕ)
    (hbeta : 0 < beta)
    (hdyadicCover : 1 ≤ dyadicScale beta L)
    (hweightLower : ∀ e, beta ≤ G.weight e)
    (hK : 0 < K) (hlambda : 0 < lambda)
    (hgap0 : (S0 : ℝ) ≤ (1 - sharpConcreteGamma) * d0)
    (hmargin : ∀ n < steps, 1 - sharpConcreteGamma ≤
      (sharpScaledA lambda * sharpConcreteGamma *
          (1 - sharpConcreteGamma) -
        ((1 - sharpConcreteGamma) * sharpScaledEta lambda +
          2 * sharpScaledEta lambda + sharpScaledEta lambda)) *
        naturalSharpJobScale d0 (sharpScaledA lambda)
          sharpConcreteGamma (sharpScaledEta lambda) n)
    (hpositive : ∀ n < steps,
      0 < naturalSharpJobScale d0 (sharpScaledA lambda)
        sharpConcreteGamma (sharpScaledEta lambda) n)
    (hnextPositive : ∀ n < steps,
      0 < (WeightedEdgeColoring.fixedSlackJobRetention (sharpScaledA lambda)
          sharpConcreteGamma - sharpScaledEta lambda) *
        naturalSharpJobScale d0 (sharpScaledA lambda)
          sharpConcreteGamma (sharpScaledEta lambda) n)
    (htwo : ∀ o, (H.slots o).card = 2)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hdegree0 : ∀ j, (initial.system.fiber j).Nonempty →
      d0 ≤ (initial.system.fiber j).card)
    (hslot0 : ∀ s, initial.system.slotDegree s ≤ S0)
    (data : ∀ n (hn : n < steps) (X : OriginalIterationState H)
      (D : G.ActiveEndpointDyadicGrouping X.activeJobs beta L K),
      EndpointNaturalIsolatedSharpStepData G X D
        (naturalSharpJobScale d0 (sharpScaledA lambda)
          sharpConcreteGamma (sharpScaledEta lambda) n)
        (fixedSlackPaddedSlotTarget sharpConcreteGamma
          (naturalSharpJobScale d0 (sharpScaledA lambda)
            sharpConcreteGamma (sharpScaledEta lambda) n))
        lambda (sharpScaledA lambda) sharpConcreteGamma
        (sharpScaledEta lambda) (2 * sharpScaledEta lambda)
        (sharpScaledEta lambda) sharpConcreteDelta
        (hpositive n hn)
        (fixedSlackPaddedSlotTarget_le sharpConcreteGamma
          (naturalSharpJobScale d0 (sharpScaledA lambda)
            sharpConcreteGamma (sharpScaledEta lambda) n)
          (by norm_num [sharpConcreteGamma])
          (by norm_num [sharpConcreteGamma]))) :
    ∃ final : OriginalIterationState H,
      EndpointSharpTrace G beta (sharpScaledA lambda) sharpConcreteDelta
        L K steps initial final ∧
      (∀ j, (final.system.fiber j).Nonempty →
        naturalSharpJobScale d0 (sharpScaledA lambda)
            sharpConcreteGamma (sharpScaledEta lambda) steps ≤
          (final.system.fiber j).card) ∧
      (∀ s, final.system.slotDegree s ≤
        naturalSharpSlotCap S0 d0 (sharpScaledA lambda)
          sharpConcreteGamma (sharpScaledEta lambda)
          (2 * sharpScaledEta lambda) (sharpScaledEta lambda) steps) ∧
      ∀ vtx,
        stateActiveStarWeight G final vtx ≤
          (1 - (1 - sharpConcreteDelta) * sharpScaledA lambda / 8) ^ steps *
              stateActiveStarWeight G initial vtx +
            (((L + 1) * (K - 1) : ℕ) : ℝ) := by
  have hgamma0C : 0 ≤ sharpConcreteGamma := by
    norm_num [sharpConcreteGamma]
  have hgamma1C : sharpConcreteGamma ≤ 1 := by
    norm_num [sharpConcreteGamma]
  have hdelta1C : sharpConcreteDelta ≤ 1 := by
    norm_num [sharpConcreteDelta]
  have ha0C : 0 ≤ sharpScaledA lambda :=
    (sharpScaled_constants lambda hlambda).1.le
  have ha1C : sharpScaledA lambda ≤ 1 := by
    simpa using (sharpScaled_rho_bounds lambda 1 hlambda (by omega)).2.1
  have hthetaC :
      (1 - sharpConcreteDelta) * sharpScaledA lambda / 8 ≤ 1 := by
    norm_num [sharpConcreteDelta]
    linarith
  exact exists_endpointNaturalIsolatedSharpIteration G initial
    steps d0 S0 lambda L K (sharpScaledA lambda) sharpConcreteGamma
    (sharpScaledEta lambda) (2 * sharpScaledEta lambda)
    (sharpScaledEta lambda) sharpConcreteDelta hbeta hdyadicCover
    hweightLower hK hlambda hgamma0C hgamma1C hdelta1C ha0C hthetaC
    (sharpScaled_constants lambda hlambda).2.2.2.1.le
    (sharpScaled_isolated_slotRate_pos lambda hlambda).le
    (sharpScaled_isolated_error_fits lambda hlambda)
    hgap0 hmargin hpositive hnextPositive htwo hjobSlot hslotPair
    hdegree0 hslot0 data

end OriginalIterationState
end RankThreeOptionSystem
end WeightedEdgeColoring
