import WeightedEdgeColoring.RankThreeFixedRateTargetIteration
import WeightedEdgeColoring.RankThreeJobRestriction
import WeightedEdgeColoring.ProfileLargeEdgePackage

/-!
# Restricting the matching system to the large graph edges

The endpoint iteration assumes that every job edge has weight at least a
fixed threshold.  In the application, this is true only for the large
edges.  This file supplies the honest restriction: both the graph edge type
and the job type are replaced by the same subtype.  A matching in that
system lifts to the original option system, and its residual active-star
weight is exactly the weight of the available large edges in the original
graph.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})

/-- Restrict a simple weighted graph to a finite set of edge indices. -/
abbrev edgeRestriction (R : Finset G.E) : WeightedSimpleGraph where
  V := G.V
  E := {e : G.E // e ∈ R}
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := inferInstance
  fst e := G.fst e.1
  snd e := G.snd e.1
  noLoop e := G.noLoop e.1
  simple := by
    intro e f hef
    apply Subtype.ext
    exact G.simple hef
  weight e := G.weight e.1
  weight_pos e := G.weight_pos e.1
  weight_le_one e := G.weight_le_one e.1

@[simp] theorem edgeRestriction_inc (R : Finset G.E) (v : G.V)
    (e : (G.edgeRestriction R).E) :
    (G.edgeRestriction R).Inc v e ↔ G.Inc v e.1 := by
  rfl

@[simp] theorem edgeRestriction_weight (R : Finset G.E)
    (e : (G.edgeRestriction R).E) :
    (G.edgeRestriction R).weight e = G.weight e.1 := by
  rfl

/-- The original edges whose weight is at least `beta`. -/
def largeEdgeJobs (beta : ℝ) : Finset G.E :=
  Finset.univ.filter fun e ↦ beta ≤ G.weight e

@[simp] theorem mem_largeEdgeJobs {beta : ℝ} {e : G.E} :
    e ∈ G.largeEdgeJobs beta ↔ beta ≤ G.weight e := by
  simp [largeEdgeJobs]

/-- The simple graph consisting only of edges of weight at least `beta`. -/
abbrev largeEdgeRestriction (beta : ℝ) : WeightedSimpleGraph :=
  G.edgeRestriction (G.largeEdgeJobs beta)

/-- Every edge of the restricted graph has weight at least `beta`. -/
theorem largeEdgeRestriction_weight_lower (beta : ℝ)
    (e : (G.largeEdgeRestriction beta).E) :
    beta ≤ (G.largeEdgeRestriction beta).weight e := by
  exact G.mem_largeEdgeJobs.mp e.2

end WeightedSimpleGraph

namespace RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Restricting jobs commutes with taking residual fibres, after forgetting
the subtype proof on each option. -/
theorem inducedOnJobs_residualFiber_card
    (active : Finset Job)
    (A : Finset (H.ActiveJobOption active))
    (j : ActiveJob active) :
    ((H.inducedOnJobs active).residualFiber A j).card =
      (H.residualFiber (H.liftActiveJobSet active A) j.1).card := by
  classical
  let valEmbedding : H.ActiveJobOption active ↪ Option :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hmap :
      ((H.inducedOnJobs active).residualFiber A j).map valEmbedding =
        H.residualFiber (H.liftActiveJobSet active A) j.1 := by
    ext o
    constructor
    · intro ho
      rcases Finset.mem_map.mp ho with ⟨q, hq, rfl⟩
      rw [(H.inducedOnJobs active).mem_residualFiber] at hq
      rw [H.mem_residualFiber]
      refine ⟨congrArg Subtype.val hq.1, ?_⟩
      intro p hp
      rcases H.mem_liftActiveJobSet.mp hp with ⟨r, hr, rfl⟩
      have hqr := hq.2 r hr
      exact ⟨fun h ↦ hqr.1 (Subtype.ext h), hqr.2⟩
    · intro ho
      rw [H.mem_residualFiber] at ho
      have hactive : H.owner o ∈ active := by simpa [ho.1] using j.2
      let q : H.ActiveJobOption active := ⟨o, hactive⟩
      apply Finset.mem_map.mpr
      refine ⟨q, ?_, rfl⟩
      rw [(H.inducedOnJobs active).mem_residualFiber]
      refine ⟨Subtype.ext ho.1, ?_⟩
      intro r hr
      have hbase := ho.2 r.1
        (H.mem_liftActiveJobSet.mpr ⟨r, hr, rfl⟩)
      exact ⟨fun h ↦ hbase.1 (congrArg Subtype.val h), hbase.2⟩
  simpa using congrArg Finset.card hmap

/-- A restricted job is active after the restricted matching exactly when
its original job is active after the lifted matching. -/
theorem mem_residual_activeJobs_inducedOnJobs_iff
    (active : Finset Job)
    (A : Finset (H.ActiveJobOption active))
    (j : ActiveJob active) :
    j ∈ ((H.inducedOnJobs active).residualSystem A).activeJobs ↔
      j.1 ∈ (H.residualSystem (H.liftActiveJobSet active A)).activeJobs := by
  rw [(H.inducedOnJobs active).residualSystem A |>.mem_activeJobs,
    (H.residualSystem (H.liftActiveJobSet active A)).mem_activeJobs]
  rw [← Finset.card_pos, ← Finset.card_pos,
    (H.inducedOnJobs active).residualSystem_fiber_card,
    H.residualSystem_fiber_card]
  change 0 < ((H.inducedOnJobs active).residualFiber A j).card ↔
    0 < (H.residualFiber (H.liftActiveJobSet active A) j.1).card
  rw [H.inducedOnJobs_residualFiber_card active A j]

end RankThreeOptionSystem

namespace WeightedSimpleGraph

universe u v w

variable (G : WeightedSimpleGraph.{u})
  {Slot : Type v} {Option : Type w}
  [Fintype Slot] [Fintype Option]
  [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem G.E Slot Option)

/-- The rank-three option system obtained by retaining precisely the jobs
whose graph-edge weight is at least `beta`. -/
abbrev largeEdgeJobSystem (beta : ℝ) :=
  H.inducedOnJobs (G.largeEdgeJobs beta)

/-- Forget the large-owner proof on a matching. -/
abbrev liftLargeEdgeJobSet (beta : ℝ)
    (A : Finset (H.ActiveJobOption (G.largeEdgeJobs beta))) : Finset Option :=
  H.liftActiveJobSet (G.largeEdgeJobs beta) A

/-- A matching on the large-edge jobs is a matching in the original system. -/
theorem liftLargeEdgeJobSet_isPartialMatching
    (beta : ℝ)
    {A : Finset (H.ActiveJobOption (G.largeEdgeJobs beta))}
    (hA : (G.largeEdgeJobSystem H beta).IsPartialMatching A) :
    H.IsPartialMatching (G.liftLargeEdgeJobSet H beta A) := by
  exact H.liftActiveJobSet_isPartialMatching (G.largeEdgeJobs beta) hA

/-- Lifting preserves exactly whether a given large-edge job is covered. -/
theorem covers_liftLargeEdgeJobSet_iff
    (beta : ℝ)
    (A : Finset (H.ActiveJobOption (G.largeEdgeJobs beta)))
    (e : (G.largeEdgeRestriction beta).E) :
    H.Covers (G.liftLargeEdgeJobSet H beta A) e.1 ↔
      (G.largeEdgeJobSystem H beta).Covers A e := by
  exact H.covers_liftActiveJobSet_iff (G.largeEdgeJobs beta) A e

/-- Every lifted option is owned by a `beta`-large edge. -/
theorem owner_large_of_mem_liftLargeEdgeJobSet
    {beta : ℝ}
    {A : Finset (H.ActiveJobOption (G.largeEdgeJobs beta))}
    {o : Option} (ho : o ∈ G.liftLargeEdgeJobSet H beta A) :
    beta ≤ G.weight (H.owner o) := by
  rcases H.mem_liftActiveJobSet.mp ho with ⟨q, _hq, rfl⟩
  exact G.mem_largeEdgeJobs.mp q.2

/-- A large edge has exactly the same job degree before and after the job
restriction. -/
theorem largeEdgeJobSystem_fiber_card (beta : ℝ)
    (e : (G.largeEdgeRestriction beta).E) :
    ((G.largeEdgeJobSystem H beta).fiber e).card =
      (H.fiber e.1).card := by
  exact H.inducedOnJobs_fiber_card (G.largeEdgeJobs beta) e

/-- Restricting to large jobs cannot increase a slot degree. -/
theorem largeEdgeJobSystem_slotDegree_le (beta : ℝ) (s : Slot) :
    (G.largeEdgeJobSystem H beta).slotDegree s ≤ H.slotDegree s := by
  exact H.inducedOnJobs_slotDegree_le (G.largeEdgeJobs beta) s

/-- Restricting to large jobs preserves each relevant job-slot codegree. -/
theorem largeEdgeJobSystem_jobSlotCodegree (beta : ℝ)
    (e : (G.largeEdgeRestriction beta).E) (s : Slot) :
    (G.largeEdgeJobSystem H beta).jobSlotCodegree e s =
      H.jobSlotCodegree e.1 s := by
  exact H.inducedOnJobs_jobSlotCodegree (G.largeEdgeJobs beta) e s

/-- Restricting to large jobs cannot increase a slot-pair codegree. -/
theorem largeEdgeJobSystem_slotPairCodegree_le (beta : ℝ) (s t : Slot) :
    (G.largeEdgeJobSystem H beta).slotPairCodegree s t ≤
      H.slotPairCodegree s t := by
  exact H.inducedOnJobs_slotPairCodegree_le (G.largeEdgeJobs beta) s t

/-- Original large edges which still have an option after selecting `M`. -/
def residualActiveLargeEdges (beta : ℝ) (M : Finset Option) : Finset G.E :=
  (H.residualSystem M).activeJobs.filter fun e ↦ beta ≤ G.weight e

@[simp] theorem mem_residualActiveLargeEdges
    {beta : ℝ} {M : Finset Option} {e : G.E} :
    e ∈ G.residualActiveLargeEdges H beta M ↔
    e ∈ (H.residualSystem M).activeJobs ∧ beta ≤ G.weight e := by
  simp [residualActiveLargeEdges]

/-- The `beta`-large original edges not covered by a selected option set. -/
def uncoveredLargeEdges (beta : ℝ) (M : Finset Option) : Finset G.E :=
  (G.largeEdgeJobs beta).filter fun e ↦ ¬ H.Covers M e

@[simp] theorem mem_uncoveredLargeEdges
    {beta : ℝ} {M : Finset Option} {e : G.E} :
    e ∈ G.uncoveredLargeEdges H beta M ↔
      beta ≤ G.weight e ∧ ¬ H.Covers M e := by
  simp [uncoveredLargeEdges]

/-- Weight of available large jobs incident with an original graph vertex. -/
def residualActiveLargeStarWeight
    (beta : ℝ) (M : Finset Option) (vtx : G.V) : ℝ :=
  ∑ e ∈ G.activeStarEdgeSet (G.residualActiveLargeEdges H beta M) vtx,
    G.weight e

/-- Weight at a vertex of the `beta`-large jobs left uncovered by `M`. -/
def uncoveredLargeStarWeight
    (beta : ℝ) (M : Finset Option) (vtx : G.V) : ℝ :=
  ∑ e ∈ G.activeStarEdgeSet (G.uncoveredLargeEdges H beta M) vtx,
    G.weight e

/-- The initial active large-edge weight is at most the whole star weight. -/
theorem residualActiveLargeStarWeight_empty_le_starWeight
    (beta : ℝ) (vtx : G.V) :
    G.residualActiveLargeStarWeight H beta ∅ vtx ≤ G.starWeight vtx := by
  classical
  unfold residualActiveLargeStarWeight
  let S := G.activeStarEdgeSet (G.residualActiveLargeEdges H beta ∅) vtx
  have hsub : S ⊆ (Finset.univ : Finset G.E).filter (G.Inc vtx) := by
    intro e he
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ e, (G.mem_activeStarEdgeSet _ _ _).mp he |>.2⟩
  calc
    (∑ e ∈ S, G.weight e) ≤
        ∑ e ∈ (Finset.univ : Finset G.E).filter (G.Inc vtx), G.weight e := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun e _he _heS ↦ G.weight_nonneg e)
    _ = G.starWeight vtx := by
      rw [starWeight,
        ← Finset.sum_subtype
          ((Finset.univ : Finset G.E).filter (G.Inc vtx)) (by simp)]

/-- The active large jobs in the original residual system are exactly the
values of the active jobs in the restricted residual system. -/
theorem residualActiveLargeEdges_lift_eq_map
    (beta : ℝ)
    (A : Finset (H.ActiveJobOption (G.largeEdgeJobs beta))) :
    G.residualActiveLargeEdges H beta (G.liftLargeEdgeJobSet H beta A) =
      ((G.largeEdgeJobSystem H beta).residualSystem A).activeJobs.map
        ⟨Subtype.val, Subtype.val_injective⟩ := by
  classical
  ext e
  constructor
  · intro he
    rcases (G.mem_residualActiveLargeEdges H).mp he with
      ⟨hactive, hlarge⟩
    let j : (G.largeEdgeRestriction beta).E :=
      ⟨e, G.mem_largeEdgeJobs.mpr hlarge⟩
    apply Finset.mem_map.mpr
    refine ⟨j, ?_, rfl⟩
    exact (H.mem_residual_activeJobs_inducedOnJobs_iff
      (G.largeEdgeJobs beta) A j).mpr hactive
  · intro he
    rcases Finset.mem_map.mp he with ⟨j, hj, rfl⟩
    apply (G.mem_residualActiveLargeEdges H).mpr
    refine ⟨(H.mem_residual_activeJobs_inducedOnJobs_iff
      (G.largeEdgeJobs beta) A j).mp hj, ?_⟩
    exact G.mem_largeEdgeJobs.mp j.2

/-- If every large job starts nonempty and the restricted residual has the
usual active-job identity, then residual activity is exactly noncoverage by
the lifted matching. -/
theorem residualActiveLargeEdges_lift_eq_uncoveredLargeEdges
    (beta : ℝ)
    (A : Finset (H.ActiveJobOption (G.largeEdgeJobs beta)))
    (hactive :
      ((G.largeEdgeJobSystem H beta).residualSystem A).activeJobs =
        (G.largeEdgeJobSystem H beta).activeJobs.filter fun e ↦
          ¬ (G.largeEdgeJobSystem H beta).Covers A e)
    (hnonempty : ∀ e ∈ G.largeEdgeJobs beta, (H.fiber e).Nonempty) :
    G.residualActiveLargeEdges H beta (G.liftLargeEdgeJobSet H beta A) =
      G.uncoveredLargeEdges H beta (G.liftLargeEdgeJobSet H beta A) := by
  classical
  ext e
  constructor
  · intro he
    rcases (G.mem_residualActiveLargeEdges H).mp he with
      ⟨heResidual, heLarge⟩
    let j : (G.largeEdgeRestriction beta).E :=
      ⟨e, G.mem_largeEdgeJobs.mpr heLarge⟩
    have hjResidual : j ∈
        ((G.largeEdgeJobSystem H beta).residualSystem A).activeJobs :=
      (H.mem_residual_activeJobs_inducedOnJobs_iff
        (G.largeEdgeJobs beta) A j).mpr heResidual
    have hjData : j ∈ (G.largeEdgeJobSystem H beta).activeJobs ∧
        ¬ (G.largeEdgeJobSystem H beta).Covers A j := by
      rw [hactive] at hjResidual
      exact Finset.mem_filter.mp hjResidual
    apply (G.mem_uncoveredLargeEdges H).mpr
    refine ⟨heLarge, ?_⟩
    intro heCovered
    exact hjData.2 ((G.covers_liftLargeEdgeJobSet_iff H beta A j).mp
      heCovered)
  · intro he
    rcases (G.mem_uncoveredLargeEdges H).mp he with
      ⟨heLarge, heUncovered⟩
    let j : (G.largeEdgeRestriction beta).E :=
      ⟨e, G.mem_largeEdgeJobs.mpr heLarge⟩
    have hjActive : j ∈ (G.largeEdgeJobSystem H beta).activeJobs := by
      rw [(G.largeEdgeJobSystem H beta).mem_activeJobs]
      rw [← Finset.card_pos,
        H.inducedOnJobs_fiber_card (G.largeEdgeJobs beta)]
      exact Finset.card_pos.mpr (hnonempty e (G.mem_largeEdgeJobs.mpr heLarge))
    have hjUncovered : ¬ (G.largeEdgeJobSystem H beta).Covers A j := by
      intro hjCovered
      exact heUncovered ((G.covers_liftLargeEdgeJobSet_iff H beta A j).mpr
        hjCovered)
    have hjResidual : j ∈
        ((G.largeEdgeJobSystem H beta).residualSystem A).activeJobs := by
      rw [hactive]
      exact Finset.mem_filter.mpr ⟨hjActive, hjUncovered⟩
    apply (G.mem_residualActiveLargeEdges H).mpr
    exact ⟨(H.mem_residual_activeJobs_inducedOnJobs_iff
      (G.largeEdgeJobs beta) A j).mp hjResidual, heLarge⟩

/-- Consequently, the residual active-star weight is literally the weight of
the large edges left uncovered by the lifted matching. -/
theorem residualActiveLargeStarWeight_lift_eq_uncovered
    (beta : ℝ)
    (A : Finset (H.ActiveJobOption (G.largeEdgeJobs beta)))
    (hactive :
      ((G.largeEdgeJobSystem H beta).residualSystem A).activeJobs =
        (G.largeEdgeJobSystem H beta).activeJobs.filter fun e ↦
          ¬ (G.largeEdgeJobSystem H beta).Covers A e)
    (hnonempty : ∀ e ∈ G.largeEdgeJobs beta, (H.fiber e).Nonempty)
    (vtx : G.V) :
    G.residualActiveLargeStarWeight H beta
        (G.liftLargeEdgeJobSet H beta A) vtx =
      G.uncoveredLargeStarWeight H beta
        (G.liftLargeEdgeJobSet H beta A) vtx := by
  unfold residualActiveLargeStarWeight uncoveredLargeStarWeight
  rw [G.residualActiveLargeEdges_lift_eq_uncoveredLargeEdges
    H beta A hactive hnonempty]

/-- A uniform positive lower bound on all initial large-job fibres is enough
for the exact uncovered-weight interpretation. -/
theorem residualActiveLargeStarWeight_lift_eq_uncovered_of_uniform
    (beta : ℝ) (d : ℕ) (hd : 0 < d)
    (A : Finset (H.ActiveJobOption (G.largeEdgeJobs beta)))
    (hactive :
      ((G.largeEdgeJobSystem H beta).residualSystem A).activeJobs =
        (G.largeEdgeJobSystem H beta).activeJobs.filter fun e ↦
          ¬ (G.largeEdgeJobSystem H beta).Covers A e)
    (hlower : ∀ e ∈ G.largeEdgeJobs beta, d ≤ (H.fiber e).card)
    (vtx : G.V) :
    G.residualActiveLargeStarWeight H beta
        (G.liftLargeEdgeJobSet H beta A) vtx =
      G.uncoveredLargeStarWeight H beta
        (G.liftLargeEdgeJobSet H beta A) vtx := by
  apply G.residualActiveLargeStarWeight_lift_eq_uncovered H beta A hactive
  intro e he
  exact Finset.card_pos.mp (hd.trans_le (hlower e he))

/-- Exact bridge between the active-star weight in the restricted graph and
the residual large-edge weight measured on the original graph. -/
theorem residualActiveStarWeight_largeEdgeRestriction
    (beta : ℝ)
    (A : Finset (H.ActiveJobOption (G.largeEdgeJobs beta)))
    (vtx : G.V) :
    (G.largeEdgeRestriction beta).residualActiveStarWeight
        (G.largeEdgeJobSystem H beta) A vtx =
      G.residualActiveLargeStarWeight H beta
        (G.liftLargeEdgeJobSet H beta A) vtx := by
  classical
  unfold residualActiveStarWeight residualActiveLargeStarWeight
  rw [G.residualActiveLargeEdges_lift_eq_map H beta A]
  let emb : (G.largeEdgeRestriction beta).E ↪ G.E :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hmap :
      ((G.largeEdgeRestriction beta).activeStarEdgeSet
        ((G.largeEdgeJobSystem H beta).residualSystem A).activeJobs vtx).map emb =
      G.activeStarEdgeSet
        (((G.largeEdgeJobSystem H beta).residualSystem A).activeJobs.map emb)
        vtx := by
    ext e
    simp [emb, activeStarEdgeSet]
  rw [← hmap]
  simp [emb]

/-! ## Direct fixed-rate target wrapper -/

/-- Run the fixed-rate target iteration only on the `beta`-large jobs.

The returned set is expressed on the restricted option type, so its residual
degree statements are exact.  Its lift is simultaneously certified as a
partial matching of the original option system.  The last line measures the
remaining work using the original graph edges and vertices. -/
theorem exists_fixedRate_largeEdgeIteration_to_target
    {beta : ℝ} (L lambda J d0 S0 target : ℕ) (epsilon : ℝ)
    (hbeta : 0 < beta)
    (hdyadicCover : 1 ≤ dyadicScale beta L)
    (hlambda : 0 < lambda) (hJ : 0 < J) (h2J : 2 ≤ J)
    (hS0 : 0 < S0)
    (hcodegreeScale : 6 * lambda ≤ J) (hd0 : J ≤ d0)
    (hsmall : 1280 * S0 < J)
    (hepsilon : 0 ≤ epsilon)
    (htarget : (target : ℝ) ≤ epsilon ^ 2 * (S0 : ℝ))
    (htargetScale : 10 * lambda ≤ target + 1)
    (hbudgetRange : ∀ S, target < S → S ≤ S0 →
      2 ≤ fixedRateSlotBudget lambda S)
    (hscaleRange : ∀ S, target < S → S ≤ S0 → Real.exp
      (-(fixedRateKappa * fixedRateScale lambda S / 320)) ≤
        fixedRateLLLWeight lambda J)
    (hlower0 : ∀ o, d0 ≤ (H.fiber (H.owner o)).card)
    (hjobUpper0 : ∀ e, (H.fiber e).card ≤ J)
    (hslotUpper0 : ∀ s, H.slotDegree s ≤ S0)
    (hjobSlot : ∀ e s, H.jobSlotCodegree e s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda) :
    ∃ (steps : ℕ)
      (A : Finset (H.ActiveJobOption (G.largeEdgeJobs beta))),
      fixedRateSlotCap lambda S0 steps ≤ target ∧
      H.IsPartialMatching (G.liftLargeEdgeJobSet H beta A) ∧
      (((G.largeEdgeJobSystem H beta).residualSystem A).activeJobs =
        (G.largeEdgeJobSystem H beta).activeJobs.filter (fun e ↦
          ¬ (G.largeEdgeJobSystem H beta).Covers A e)) ∧
      (∀ o : (G.largeEdgeJobSystem H beta).ResidualOption A,
        fixedRateJobFloor lambda d0 S0 steps ≤
          (((G.largeEdgeJobSystem H beta).residualSystem A).fiber
            (((G.largeEdgeJobSystem H beta).residualSystem A).owner o)).card) ∧
      (∀ s, ((G.largeEdgeJobSystem H beta).residualSystem A).slotDegree s ≤
        fixedRateSlotCap lambda S0 steps) ∧
      ∀ vtx,
        G.residualActiveLargeStarWeight H beta
            (G.liftLargeEdgeJobSet H beta A) vtx ≤
          epsilon * G.residualActiveLargeStarWeight H beta ∅ vtx +
            ((((L + 1) *
              (fixedRateBlockSize lambda S0 - 1) : ℕ) : ℝ)) := by
  let Glarge := G.largeEdgeRestriction beta
  let Hlarge := G.largeEdgeJobSystem H beta
  have hweightLower : ∀ e : Glarge.E, beta ≤ Glarge.weight e := by
    intro e
    exact G.largeEdgeRestriction_weight_lower beta e
  have hlowerLarge : ∀ o,
      d0 ≤ (Hlarge.fiber (Hlarge.owner o)).card := by
    intro o
    rw [H.inducedOnJobs_fiber_card (G.largeEdgeJobs beta)]
    exact hlower0 o.1
  have hjobUpperLarge : ∀ e, (Hlarge.fiber e).card ≤ J := by
    intro e
    rw [H.inducedOnJobs_fiber_card (G.largeEdgeJobs beta)]
    exact hjobUpper0 e.1
  have hslotUpperLarge : ∀ s, Hlarge.slotDegree s ≤ S0 := by
    intro s
    exact (H.inducedOnJobs_slotDegree_le
      (G.largeEdgeJobs beta) s).trans (hslotUpper0 s)
  have hjobSlotLarge : ∀ e s, Hlarge.jobSlotCodegree e s ≤ lambda := by
    intro e s
    rw [H.inducedOnJobs_jobSlotCodegree (G.largeEdgeJobs beta)]
    exact hjobSlot e.1 s
  have hslotPairLarge : ∀ s t, s ≠ t →
      Hlarge.slotPairCodegree s t ≤ lambda := by
    intro s t hst
    exact (H.inducedOnJobs_slotPairCodegree_le
      (G.largeEdgeJobs beta) s t).trans (hslotPair s t hst)
  rcases Hlarge.exists_fixedRate_endpointIteration_to_target Glarge
      L lambda J d0 S0 target epsilon hbeta hdyadicCover hweightLower
      hlambda hJ h2J hS0 hcodegreeScale hd0 hsmall hepsilon htarget
      htargetScale hbudgetRange hscaleRange hlowerLarge hjobUpperLarge
      hslotUpperLarge hjobSlotLarge hslotPairLarge with
    ⟨steps, A, hcap, hA, hactiveA, hlowerA, hslotA, hweightA⟩
  refine ⟨steps, A, hcap,
    G.liftLargeEdgeJobSet_isPartialMatching H beta hA,
    hactiveA, hlowerA, hslotA, ?_⟩
  intro vtx
  have hfinal := G.residualActiveStarWeight_largeEdgeRestriction H beta A vtx
  have hinitial := G.residualActiveStarWeight_largeEdgeRestriction H beta
    (∅ : Finset (H.ActiveJobOption (G.largeEdgeJobs beta))) vtx
  have hliftEmpty : G.liftLargeEdgeJobSet H beta
      (∅ : Finset (H.ActiveJobOption (G.largeEdgeJobs beta))) = ∅ := by
    simp [liftLargeEdgeJobSet, RankThreeOptionSystem.liftActiveJobSet]
  calc
    G.residualActiveLargeStarWeight H beta
        (G.liftLargeEdgeJobSet H beta A) vtx =
        (G.largeEdgeRestriction beta).residualActiveStarWeight
          (G.largeEdgeJobSystem H beta) A vtx := hfinal.symm
    _ ≤ epsilon *
          (G.largeEdgeRestriction beta).residualActiveStarWeight
            (G.largeEdgeJobSystem H beta) ∅ vtx +
          ((((L + 1) *
            (fixedRateBlockSize lambda S0 - 1) : ℕ) : ℝ)) := hweightA vtx
    _ = epsilon * G.residualActiveLargeStarWeight H beta ∅ vtx +
          ((((L + 1) *
            (fixedRateBlockSize lambda S0 - 1) : ℕ) : ℝ)) := by
      rw [hinitial, hliftEmpty]

end WeightedSimpleGraph

end

end WeightedEdgeColoring
