import WeightedEdgeColoring.RankThreeOriginalTypeIteration
import WeightedEdgeColoring.RankThreeCyclicRegularization
import WeightedEdgeColoring.RankThreeRegularExtensionSharpRound
import WeightedEdgeColoring.RankThreeSharpFixedSlackUniform

/-!
# One concrete sharp step on an original-type iteration state

This module joins the deterministic iteration plumbing to the cyclic slot
regularization and the uniform sharp round.  Empty current fibres are first
removed from the job type.  Every remaining fibre is trimmed to degree `d`,
the slot side is made exactly regular by the cyclic extension, and the sharp
round is projected and lifted back to the original option type.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.SharpFixedSlackNumeric

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  {Group : Type x} [Fintype Group] [DecidableEq Group]
  {H : RankThreeOptionSystem Job Slot Option}

namespace OriginalIterationState

/-- The scalar and tail estimates which remain after all graph bookkeeping
in `exists_sharpFixedSlackRound_uniformProposal` has been discharged. -/
structure UniformSharpScalarData
    {Jb Sl Op : Type*}
    [Fintype Jb] [Fintype Sl] [Fintype Op]
    [DecidableEq Jb] [DecidableEq Sl] [DecidableEq Op]
    (G : RankThreeOptionSystem Jb Sl Op)
    (members : Group → Finset Jb)
    (lambda d D R K m k : ℕ)
    (rho a gamma etaJob etaLoad etaCollision z delta : ℝ) where
  slotLambda : Sl → ℝ
  jobLambda : Jb → ℝ
  rho_nonneg : 0 ≤ rho
  rho_le_one : rho ≤ 1
  rho_eq : rho = a / (d : ℝ)
  delta_nonneg : 0 ≤ delta
  slotLambda_nonneg : ∀ s, 0 ≤ slotLambda s
  jobLambda_nonneg : ∀ j, 0 ≤ jobLambda j
  z_pos : 0 < z
  cap_le_half : increasingCap rho ≤ 1 / 2
  row_le_cap : exponentialRowWeight z ≤ increasingCap rho
  collision_le_cap : collisionWeight k ≤ increasingCap rho
  pair_product :
    exponentialRowWeight z * (pairNeighborBudget R D : ℝ) ≤ 1 / 2
  group_exponent :
    Real.exp
        ((delta * (1 - delta) + (Real.exp (-delta) - 1)) *
          (rho * (m : ℝ))) ≤
      Real.exp (-(z + 2 * increasingCap rho *
        (lowerNeighborBudget (groupSupportBudget K D) D : ℝ)))
  slot_exponent : ∀ s : G.ActiveSlot 0,
    Real.exp (slotLambda s.1 *
        ((a * (2 - gamma) * (1 - gamma) - etaLoad) * d /
          (3 * lambda : ℕ)) +
      (Real.exp (-slotLambda s.1) - 1) *
        linearRowMean (fun _ : Op ↦ rho)
          (G.residualDeleteWeight lambda) (Sum.inr s.1)) ≤
      Real.exp (-(z + 2 * increasingCap rho *
        (lowerNeighborBudget (slotSupportBudget D) D : ℝ)))
  upper_tail : ∀ j,
    Real.exp (-jobLambda j *
        ((2 * a * (1 - gamma) + etaJob) * d /
          (2 * lambda : ℕ)) +
      (Real.exp (jobLambda j) - 1) *
        linearRowMean (fun _ : Op ↦ rho)
          (G.residualDeleteWeight lambda) (Sum.inl j)) ≤
      exponentialRowWeight z / 2
  upper_product : exponentialRowWeight z *
    (increasingNeighborBudget (upperSupportBudget D) R D : ℝ) ≤ 1 / 2
  collision_threshold_pos : 0 < 2 * etaCollision * d
  collision_envelope :
    slotCollisionMomentEnvelope rho D D lambda k ≤ etaCollision * d
  collision_product : exponentialRowWeight z *
    (increasingNeighborBudget (slotSupportBudget D) R D : ℝ) ≤ 1 / 2

/-- Run the uniform theorem from its scalar-data package. -/
theorem UniformSharpScalarData.run
    {Jb Sl Op : Type*}
    [Fintype Jb] [Fintype Sl] [Fintype Op]
    [DecidableEq Jb] [DecidableEq Sl] [DecidableEq Op]
    {G : RankThreeOptionSystem Jb Sl Op}
    {members : Group → Finset Jb}
    {lambda d D R K m k : ℕ}
    {rho a gamma etaJob etaLoad etaCollision z delta : ℝ}
    (U : UniformSharpScalarData G members lambda d D R K m k
      rho a gamma etaJob etaLoad etaCollision z delta)
    (hlambda : 0 < lambda)
    (hjobInitial : ∀ j, d ≤ G.residualJobDegree ∅ j)
    (hslotInitial : ∀ s,
      (G.residualSlotDegree ∅ s : ℝ) ≤ (1 - gamma) * d)
    (hjobDegree : ∀ j, (G.fiber j).card ≤ D)
    (hslotDegree : ∀ s, G.slotDegree s ≤ D)
    (hjobSlot : ∀ j s, G.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → G.slotPairCodegree s t ≤ lambda)
    (hmembers : ∀ g, (members g).card ≤ K)
    (hgroupSupportLower : ∀ g,
      m ≤ (linearRowSupport (G.jobGroupCoverageWeight members) g).card)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R) :
    ∃ A : Finset Op,
      G.IsPartialMatching A ∧
      (∀ g, (1 - delta) * (a / (d : ℝ)) * m <
        ∑ o ∈ A, G.jobGroupCoverageWeight members g o) ∧
      (∀ j, ¬ G.Covers A j →
        (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d ≤
          G.residualJobDegree A j) ∧
      (∀ s, (∀ p ∈ A, s ∉ G.slots p) →
        (G.residualSlotDegree A s : ℝ) ≤
          (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
            etaLoad + etaCollision) * d) := by
  exact G.exists_sharpFixedSlackRound_uniformProposal members
    U.slotLambda U.jobLambda lambda d D R K m k
    rho a gamma etaJob etaLoad etaCollision z delta hlambda
    U.rho_nonneg U.rho_le_one U.rho_eq hjobInitial hslotInitial
    hjobDegree hslotDegree hjobSlot hslotPair hmembers hgroupSupportLower
    hgroupIncidence U.delta_nonneg U.slotLambda_nonneg U.jobLambda_nonneg
    U.z_pos U.cap_le_half U.row_le_cap U.collision_le_cap U.pair_product
    U.group_exponent U.slot_exponent U.upper_tail U.upper_product
    U.collision_threshold_pos U.collision_envelope U.collision_product

/-- Quantitative conclusions retained by the original-type driver after one
active, regularized, projected sharp round. -/
def SharpActiveRoundGood
    (members : Group → Finset (ActiveJob (activeJobs (H := H) X)))
    (m d : ℕ) (a gamma etaJob etaLoad etaCollision delta : ℝ)
    (W : ActiveRegularizedProjectedRound X d) : Prop :=
  (∀ g, (1 - delta) * (a / (d : ℝ)) * m <
    ∑ o ∈ W.selected,
      (((X.activeSystem).inducedOnOptions W.trim).jobGroupCoverageWeight
        members g o)) ∧
  (∀ j, ¬ ((X.activeSystem).inducedOnOptions W.trim).Covers W.selected j →
    (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d ≤
      ((((X.activeSystem).inducedOnOptions W.trim).inducedOnOptions
        W.next).fiber j).card) ∧
  (∀ s,
    (((X.activeSystem).inducedOnOptions W.trim).inducedOnOptions
      W.next).slotDegree s ≤
      (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
        etaLoad + etaCollision) * d) ∧
  (∀ j s, ¬ ((X.activeSystem).inducedOnOptions W.trim).Covers W.selected j →
    (((X.activeSystem).inducedOnOptions W.trim).inducedOnOptions
      W.next).slotDegree s ≤
      (1 - gamma) *
        ((((X.activeSystem).inducedOnOptions W.trim).inducedOnOptions
          W.next).fiber j).card)

/-- The slot part of `SharpActiveRoundGood` is already a statement about
the next keep set on the original option type. -/
theorem SharpActiveRoundGood.originalKeep_slotDegree
    {X : OriginalIterationState H} {d m : ℕ}
    {a gamma etaJob etaLoad etaCollision delta : ℝ}
    {members : Group → Finset (ActiveJob X.activeJobs)}
    {W : ActiveRegularizedProjectedRound X d}
    (hgood : SharpActiveRoundGood members m d a gamma etaJob etaLoad
      etaCollision delta W) (s : Slot) :
    ((H.inducedOnOptions W.originalKeep).slotDegree s : ℝ) ≤
      (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
        etaLoad + etaCollision) * d := by
  rw [W.originalKeep_slotDegree]
  exact hgood.2.2.1 s

/-- The job part transfers exactly to each active original job. -/
theorem SharpActiveRoundGood.originalKeep_fiber_card
    {X : OriginalIterationState H} {d m : ℕ}
    {a gamma etaJob etaLoad etaCollision delta : ℝ}
    {members : Group → Finset (ActiveJob X.activeJobs)}
    {W : ActiveRegularizedProjectedRound X d}
    (hgood : SharpActiveRoundGood members m d a gamma etaJob etaLoad
      etaCollision delta W)
    (j : ActiveJob X.activeJobs)
    (huncovered :
      ¬ ((X.activeSystem).inducedOnOptions W.trim).Covers W.selected j) :
    (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d ≤
      ((H.inducedOnOptions W.originalKeep).fiber j.1).card := by
  rw [W.originalKeep_fiber_card]
  exact hgood.2.1 j huncovered

/-- The preserved gap also transfers to the original option type. -/
theorem SharpActiveRoundGood.originalKeep_sameGap
    {X : OriginalIterationState H} {d m : ℕ}
    {a gamma etaJob etaLoad etaCollision delta : ℝ}
    {members : Group → Finset (ActiveJob X.activeJobs)}
    {W : ActiveRegularizedProjectedRound X d}
    (hgood : SharpActiveRoundGood members m d a gamma etaJob etaLoad
      etaCollision delta W)
    (j : ActiveJob X.activeJobs) (s : Slot)
    (huncovered :
      ¬ ((X.activeSystem).inducedOnOptions W.trim).Covers W.selected j) :
    ((H.inducedOnOptions W.originalKeep).slotDegree s : ℝ) ≤
      (1 - gamma) *
        ((H.inducedOnOptions W.originalKeep).fiber j.1).card := by
  rw [W.originalKeep_slotDegree, W.originalKeep_fiber_card]
  exact hgood.2.2.2 j s huncovered

/-- Every nonempty fibre of the fully lifted next keep set satisfies the job
lower bound.  The proof traces one surviving option back through all three
subtype layers; its local residual certificate shows that its active owner
was not covered in the round. -/
theorem SharpActiveRoundGood.originalKeep_nonempty_fiber_lower
    {X : OriginalIterationState H} {d m : ℕ}
    {a gamma etaJob etaLoad etaCollision delta : ℝ}
    {members : Group → Finset (ActiveJob X.activeJobs)}
    {W : ActiveRegularizedProjectedRound X d}
    (hgood : SharpActiveRoundGood members m d a gamma etaJob etaLoad
      etaCollision delta W) :
    ∀ j, ((H.inducedOnOptions W.originalKeep).fiber j).Nonempty →
      (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d ≤
        ((H.inducedOnOptions W.originalKeep).fiber j).card := by
  intro j hj
  rcases hj with ⟨o, hofiber⟩
  have howner : H.owner o.1 = j :=
    (H.inducedOnOptions W.originalKeep).mem_fiber.mp hofiber
  rcases H.mem_liftKeptOptionSet.mp o.2 with ⟨q, hqkeep, hqval⟩
  have hqkeep' : q ∈ X.system.liftActiveJobSet X.activeJobs
      (X.activeSystem.liftKeptOptionSet W.trim W.next) := by
    simpa [ActiveRegularizedProjectedRound.currentKeep,
      liftActiveKeptOptionSet] using hqkeep
  rcases X.system.mem_liftActiveJobSet.mp hqkeep' with
    ⟨r, hrkeep, hrval⟩
  rcases X.activeSystem.mem_liftKeptOptionSet.mp hrkeep with
    ⟨z, hznext, hzval⟩
  let jactive : ActiveJob X.activeJobs :=
    ((X.activeSystem).inducedOnOptions W.trim).owner z
  have hjactive : jactive.1 = j := by
    change H.owner z.1.1.1 = j
    rw [hzval, hrval, hqval]
    exact howner
  have huncovered :
      ¬ ((X.activeSystem).inducedOnOptions W.trim).Covers
        W.selected jactive := by
    rintro ⟨p, hp, hpowner⟩
    have hres := ((X.activeSystem).inducedOnOptions W.trim).mem_residualOptions.mp
      (W.next_subset_residual hznext) p hp
    exact hres.1 (by
      dsimp [jactive] at hpowner ⊢
      exact hpowner.symm)
  have hlower := hgood.originalKeep_fiber_card jactive huncovered
  simpa [hjactive] using hlower

/-- If the protected next job scale is positive, the next active jobs are
exactly the current active jobs not covered by this round. -/
theorem SharpActiveRoundGood.result_activeJobs
    {X : OriginalIterationState H} {d m : ℕ}
    {a gamma etaJob etaLoad etaCollision delta : ℝ}
    {members : Group → Finset (ActiveJob X.activeJobs)}
    {W : ActiveRegularizedProjectedRound X d}
    (hgood : SharpActiveRoundGood members m d a gamma etaJob etaLoad
      etaCollision delta W)
    (hpositive : 0 <
      (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d) :
    W.result.activeJobs =
      X.activeJobs.filter fun j ↦ ¬ X.system.Covers W.currentSelection j := by
  ext j
  simp only [Finset.mem_filter]
  constructor
  · intro hjnext
    rcases (W.result.mem_activeJobs j).mp hjnext with ⟨o, hofiber⟩
    have howner : H.owner o.1 = j :=
      (H.inducedOnOptions W.originalKeep).mem_fiber.mp hofiber
    rcases H.mem_liftKeptOptionSet.mp o.2 with ⟨q, hqkeep, hqval⟩
    have hownerq : X.system.owner q = j := by
      change H.owner q.1 = j
      rw [hqval]
      exact howner
    have hactive : j ∈ X.activeJobs := by
      rw [X.mem_activeJobs]
      exact ⟨q, X.system.mem_fiber.mpr hownerq⟩
    have hnot : ¬ X.system.Covers W.currentSelection j := by
      rintro ⟨p, hp, hpowner⟩
      have hres := X.system.mem_residualOptions.mp
        (W.currentKeep_subset_residual hqkeep) p hp
      exact hres.1 (hownerq.trans hpowner.symm)
    exact ⟨hactive, hnot⟩
  · rintro ⟨hjactive, hnot⟩
    let ja : ActiveJob X.activeJobs := ⟨j, hjactive⟩
    have hlocalNot :
        ¬ ((X.activeSystem).inducedOnOptions W.trim).Covers W.selected ja := by
      intro hlocal
      exact hnot ((X.system.covers_liftActiveKeptOptionSet_iff
        X.activeJobs W.trim W.selected ja).mpr hlocal)
    have hlower := hgood.originalKeep_fiber_card ja hlocalNot
    have hposCard : 0 <
        ((H.inducedOnOptions W.originalKeep).fiber j).card := by
      have : (0 : ℝ) <
          ((H.inducedOnOptions W.originalKeep).fiber j).card := by
        simpa [ja] using hpositive.trans_le hlower
      exact_mod_cast this
    exact (W.result.mem_activeJobs j).mpr (Finset.card_pos.mp (by
      simpa [ActiveRegularizedProjectedRound.result,
        OriginalIterationState.system] using hposCard))

/-- Run one fully assembled sharp round after an exact active-job trim.

The four graph bounds are stated on the trimmed active system; the companion
theorem below obtains them from bounds on the current system.  All remaining
analytic assumptions are carried by `U`. -/
theorem exists_activeSharpRound_of_trim
    (X : OriginalIterationState H)
    (d S lambda R K m k : ℕ)
    (rho a gamma etaJob etaLoad etaCollision z delta : ℝ)
    (hd : 0 < d) (hlambda : 0 < lambda) (hSd : S ≤ d)
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
    (hmembers : ∀ g, (members g).card ≤ K)
    (hgroupSupportLower : ∀ g,
      m ≤ (linearRowSupport
        (((X.activeSystem).inducedOnOptions trim).jobGroupCoverageWeight
          members) g).card)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (U : UniformSharpScalarData
      (((X.activeSystem).inducedOnOptions trim).cyclicRegularization hSd htwo)
      ((CyclicRegularization.regularExtension hd hSd htwo htrim hslot
        hjobSlot hslotPair).liftedOldMembers members)
      (max lambda 1) d d R K m k
      rho a gamma etaJob etaLoad etaCollision z delta) :
    ∃ W : ActiveRegularizedProjectedRound X d,
      SharpActiveRoundGood members m d a gamma etaJob etaLoad etaCollision
        delta W := by
  let B := (X.activeSystem).inducedOnOptions trim
  let G := B.cyclicRegularization hSd htwo
  let E : IsRegularExtension B G d S (max lambda 1) :=
    CyclicRegularization.regularExtension hd hSd htwo htrim hslot
      hjobSlot hslotPair
  have hlambdaExt : 0 < max lambda 1 := by omega
  have hjobInitial : ∀ j, d ≤ G.residualJobDegree ∅ j := by
    intro j
    rw [G.residualJobDegree_empty, E.jobDegree_eq j]
  have hslotInitial : ∀ s,
      (G.residualSlotDegree ∅ s : ℝ) ≤ (1 - gamma) * d := by
    intro s
    rw [G.residualSlotDegree_empty, E.slotDegree_eq s]
    exact hslotSlack
  have hjobDegree : ∀ j, (G.fiber j).card ≤ d := by
    intro j
    rw [E.jobDegree_eq j]
  have hslotDegree : ∀ s, G.slotDegree s ≤ d := by
    intro s
    rw [E.slotDegree_eq s]
    exact hSd
  have hmembersExt : ∀ g,
      ((E.liftedOldMembers members) g).card ≤ K := by
    intro g
    simpa [IsRegularExtension.liftedOldMembers] using hmembers g
  have hsupportExt : ∀ g,
      m ≤ (linearRowSupport
        (G.jobGroupCoverageWeight (E.liftedOldMembers members)) g).card := by
    intro g
    rw [E.linearRowSupport_liftedOldMembers_card members g]
    exact hgroupSupportLower g
  have hincidenceExt : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ E.liftedOldMembers members g)).card ≤ R :=
    E.liftedOldMembers_incidence_le members R hgroupIncidence
  have hround := U.run hlambdaExt hjobInitial hslotInitial
    hjobDegree hslotDegree E.jobSlotCodegree_le E.slotPairCodegree_le
    hmembersExt hsupportExt hincidenceExt
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

/-- Complete one-step constructor from an original-type state.  The
continuation `hnumeric` supplies only the scalar data after the deterministic
trim and all induced graph bounds have been chosen. -/
theorem exists_activeSharpRound
    (X : OriginalIterationState H)
    (d S lambda R K m k : ℕ)
    (rho a gamma etaJob etaLoad etaCollision z delta : ℝ)
    (hd : 0 < d) (hlambda : 0 < lambda) (hSd : S ≤ d)
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
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
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
      UniformSharpScalarData
        (((X.activeSystem).inducedOnOptions trim).cyclicRegularization
          hSd htwo)
        ((CyclicRegularization.regularExtension hd hSd htwo htrim hslot
          hjobSlot hslotPair).liftedOldMembers members)
        (max lambda 1) d d R K m k
        rho a gamma etaJob etaLoad etaCollision z delta) :
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
    calc
      ((X.activeSystem).inducedOnOptions trim).slotPairCodegree s t ≤
          X.activeSystem.slotPairCodegree s t :=
        X.activeSystem.inducedOnOptions_slotPairCodegree_le trim s t
      _ ≤ X.system.slotPairCodegree s t :=
        X.system.inducedOnJobs_slotPairCodegree_le X.activeJobs s t
      _ ≤ lambda := hslotPairCurrent s t hst
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
  exact exists_activeSharpRound_of_trim X d S lambda R K m k
    rho a gamma etaJob etaLoad etaCollision z delta hd hlambda hSd
    hslotSlack hgamma1 herror hslotCap0 trim htrim htwo hslot hjobSlot
    hslotPair members hmembers hsupport hgroupIncidence
    (hnumeric trim htrim htwo hslot hjobSlot hslotPair)

end OriginalIterationState

end WeightedEdgeColoring.RankThreeOptionSystem
