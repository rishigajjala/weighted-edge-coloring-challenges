import WeightedEdgeColoring.RankThreeOriginalTypeSharpStep
import WeightedEdgeColoring.RankThreeIsolatedSharpConcreteRound

/-!
# Original-type bridge for isolated sharp rounds

The projection and lifting argument only uses the four qualitative
conclusions of a regular-extension round.  This file exposes that fact for
the new raw-sample-then-isolate construction, without routing it through
the older pair-event scalar-data structure.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  {Group : Type x} [Fintype Group] [DecidableEq Group]
  {H : RankThreeOptionSystem Job Slot Option}

namespace OriginalIterationState

/-- Lift and project any isolated regular-extension round with the sharp
fixed-slack conclusions. -/
theorem exists_activeIsolatedSharpRound_of_trim
    (X : OriginalIterationState H)
    (d S lambda : ℕ)
    (a gamma etaJob etaLoad etaCollision delta : ℝ)
    (hd : 0 < d) (hSd : S ≤ d)
    (hslotSlack : (S : ℝ) ≤ (1 - gamma) * d)
    (hgamma1 : gamma ≤ 1)
    (herror : (1 - gamma) * etaJob + etaLoad + etaCollision ≤
      a * gamma * (1 - gamma))
    (hslotCap0 :
      0 ≤ (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
        etaLoad + etaCollision) * d)
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
      ((X.activeSystem).inducedOnOptions trim).slotPairCodegree s t ≤ lambda)
    (members : Group → Finset (ActiveJob X.activeJobs))
    (m : ℕ)
    (hround :
      let B := (X.activeSystem).inducedOnOptions trim
      let G := B.cyclicRegularization hSd htwo
      let E : IsRegularExtension B G d S (max lambda 1) :=
        CyclicRegularization.regularExtension hd hSd htwo htrim hslot
          hjobSlot hslotPair
      ∃ M : Finset (B.CyclicOption d S),
        G.IsPartialMatching M ∧
        (∀ g, (1 - delta) * (a / (d : ℝ)) * m <
          ∑ q ∈ M, G.jobGroupCoverageWeight
            (E.liftedOldMembers members) g q) ∧
        (∀ j, ¬ G.Covers M j →
          (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d ≤
            G.residualJobDegree M j) ∧
        (∀ s, (∀ q ∈ M, s ∉ G.slots q) →
          (G.residualSlotDegree M s : ℝ) ≤
            (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
              etaLoad + etaCollision) * d)) :
    ∃ W : ActiveRegularizedProjectedRound X d,
      SharpActiveRoundGood members m d a gamma etaJob etaLoad etaCollision
        delta W := by
  let B := (X.activeSystem).inducedOnOptions trim
  let G := B.cyclicRegularization hSd htwo
  let E : IsRegularExtension B G d S (max lambda 1) :=
    CyclicRegularization.regularExtension hd hSd htwo htrim hslot
      hjobSlot hslotPair
  have hprojected := E.exists_projectedSharpFixedSlackRound_fixedSlack
    members (fun _ ↦ (1 - delta) * (a / (d : ℝ)) * m)
    d a gamma etaJob etaLoad etaCollision hgamma1 herror hslotCap0 hround
  rcases hprojected with
    ⟨M, hMext, _hM, hgroup, _hexact, hjob, hslotNext, hgap⟩
  let W : ActiveRegularizedProjectedRound X d :=
    ActiveRegularizedProjectedRound.ofRegularExtension trim htrim E M hMext
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · simpa [W] using hgroup
  · simpa [W] using hjob
  · simpa [W] using hslotNext
  · simpa [W] using hgap

/-- Complete trim/regularize/run/project step for an isolated round.  The
continuation has precisely the signature produced by the concrete padded
round theorem. -/
theorem exists_activeIsolatedSharpRound
    (X : OriginalIterationState H)
    (d S lambda K m : ℕ)
    (a gamma etaJob etaLoad etaCollision delta : ℝ)
    (hd : 0 < d) (hSd : S ≤ d)
    (hdegree : ∀ j, (X.system.fiber j).Nonempty →
      d ≤ (X.system.fiber j).card)
    (htwoCurrent : ∀ o : KeptOption X.keep,
      (X.system.slots o).card = 2)
    (hslotCurrent : ∀ s, X.system.slotDegree s ≤ S)
    (hjobSlotCurrent : ∀ j s,
      X.system.jobSlotCodegree j s ≤ lambda)
    (hslotPairCurrent : ∀ s t, s ≠ t →
      X.system.slotPairCodegree s t ≤ lambda)
    (hslotSlack : (S : ℝ) ≤ (1 - gamma) * d)
    (hgamma1 : gamma ≤ 1)
    (herror : (1 - gamma) * etaJob + etaLoad + etaCollision ≤
      a * gamma * (1 - gamma))
    (hslotCap0 :
      0 ≤ (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
        etaLoad + etaCollision) * d)
    (members : Group → Finset (ActiveJob X.activeJobs))
    (hmembers : ∀ g, (members g).card ≤ K)
    (hgroupSize : ∀ g, m ≤ (members g).card * d)
    (hnumeric : ∀
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
      let G := B.cyclicRegularization hSd htwo
      let E : IsRegularExtension B G d S (max lambda 1) :=
        CyclicRegularization.regularExtension hd hSd htwo htrim hslot
          hjobSlot hslotPair
      ∃ M : Finset (B.CyclicOption d S),
        G.IsPartialMatching M ∧
        (∀ g, (1 - delta) * (a / (d : ℝ)) * m <
          ∑ q ∈ M, G.jobGroupCoverageWeight
            (E.liftedOldMembers members) g q) ∧
        (∀ j, ¬ G.Covers M j →
          (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d ≤
            G.residualJobDegree M j) ∧
        (∀ s, (∀ q ∈ M, s ∉ G.slots q) →
          (G.residualSlotDegree M s : ℝ) ≤
            (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
              etaLoad + etaCollision) * d)) :
    ∃ W : ActiveRegularizedProjectedRound X d,
      SharpActiveRoundGood members m d a gamma etaJob etaLoad etaCollision
        delta W := by
  rcases X.exists_activeRegularizingTrim d hdegree with ⟨trim, htrim⟩
  have htwo : ∀ o : KeptOption trim,
      ((((X.activeSystem).inducedOnOptions trim).slots o).card) = 2 := by
    intro o
    exact htwoCurrent o.1.1
  have hslot : ∀ s,
      ((X.activeSystem).inducedOnOptions trim).slotDegree s ≤ S := by
    intro s
    exact ((X.activeSystem).inducedOnOptions_slotDegree_le trim s).trans
      ((X.system.inducedOnJobs_slotDegree_le X.activeJobs s).trans
        (hslotCurrent s))
  have hjobSlot : ∀ j s,
      ((X.activeSystem).inducedOnOptions trim).jobSlotCodegree j s ≤ lambda := by
    intro j s
    calc
      ((X.activeSystem).inducedOnOptions trim).jobSlotCodegree j s ≤
          X.activeSystem.jobSlotCodegree j s :=
        X.activeSystem.inducedOnOptions_jobSlotCodegree_le trim j s
      _ = X.system.jobSlotCodegree j.1 s :=
        X.system.inducedOnJobs_jobSlotCodegree X.activeJobs j s
      _ ≤ lambda := hjobSlotCurrent j.1 s
  have hslotPair : ∀ s t, s ≠ t →
      ((X.activeSystem).inducedOnOptions trim).slotPairCodegree s t ≤ lambda := by
    intro s t hst
    exact (((X.activeSystem).inducedOnOptions_slotPairCodegree_le trim s t).trans
      (X.system.inducedOnJobs_slotPairCodegree_le X.activeJobs s t)).trans
        (hslotPairCurrent s t hst)
  have hsupport : ∀ g,
      m ≤ (linearRowSupport
        (((X.activeSystem).inducedOnOptions trim).jobGroupCoverageWeight
          members) g).card := by
    intro g
    rw [((X.activeSystem).inducedOnOptions trim).jobGroupCoverage_support_card_eq_sum
      members g]
    calc
      m ≤ (members g).card * d := hgroupSize g
      _ = ∑ _j ∈ members g, d := by simp
      _ = ∑ j ∈ members g,
          (((X.activeSystem).inducedOnOptions trim).fiber j).card := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [htrim j]
  exact exists_activeIsolatedSharpRound_of_trim X d S lambda
    a gamma etaJob etaLoad etaCollision delta hd hSd hslotSlack hgamma1
    herror hslotCap0 trim htrim htwo hslot hjobSlot hslotPair members m
    (hnumeric trim htrim htwo hslot hjobSlot hslotPair)

end OriginalIterationState
end WeightedEdgeColoring.RankThreeOptionSystem
