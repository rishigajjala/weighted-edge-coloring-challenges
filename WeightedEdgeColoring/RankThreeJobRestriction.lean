import WeightedEdgeColoring.RankThreeOptionRestriction

/-!
# Restricting a rank-three system to active jobs

After a matching round, covered jobs have empty residual fibres.  Iteration
therefore runs on the finite subtype of jobs that remain active.  Restricting
to those jobs preserves every active fibre exactly and can only decrease slot
and slot-pair degrees.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

abbrev ActiveJob (active : Finset Job) := {j : Job // j ∈ active}

abbrev ActiveJobOption (active : Finset Job) :=
  {o : Option // H.owner o ∈ active}

/-- Keep precisely the options whose owners belong to `active`, and replace
the job type by the corresponding subtype. -/
def inducedOnJobs (active : Finset Job) :
    RankThreeOptionSystem (ActiveJob active) Slot (H.ActiveJobOption active) where
  owner o := ⟨H.owner o.1, o.2⟩
  slots o := H.slots o.1
  slots_card_le_two o := H.slots_card_le_two o.1

/-- An active job keeps its entire original fibre. -/
theorem inducedOnJobs_fiber_card (active : Finset Job)
    (j : ActiveJob active) :
    ((H.inducedOnJobs active).fiber j).card = (H.fiber j.1).card := by
  let valEmbedding : H.ActiveJobOption active ↪ Option :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : ((H.inducedOnJobs active).fiber j).map valEmbedding =
      H.fiber j.1 := by
    ext o
    constructor
    · intro ho
      rcases Finset.mem_map.mp ho with ⟨p, hp, rfl⟩
      exact H.mem_fiber.mpr
        (congrArg Subtype.val ((H.inducedOnJobs active).mem_fiber.mp hp))
    · intro ho
      have howner : H.owner o = j.1 := H.mem_fiber.mp ho
      have hactive : H.owner o ∈ active := by simpa [howner] using j.2
      apply Finset.mem_map.mpr
      refine ⟨⟨o, hactive⟩, ?_, rfl⟩
      exact (H.inducedOnJobs active).mem_fiber.mpr (Subtype.ext howner)
  simpa using congrArg Finset.card hmap

/-- Active-job restriction cannot increase slot degree. -/
theorem inducedOnJobs_slotDegree_le (active : Finset Job) (s : Slot) :
    (H.inducedOnJobs active).slotDegree s ≤ H.slotDegree s := by
  let valEmbedding : H.ActiveJobOption active ↪ Option :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let A : Finset (H.ActiveJobOption active) :=
    (Finset.univ : Finset (H.ActiveJobOption active)).filter
      (fun o ↦ s ∈ (H.inducedOnJobs active).slots o)
  have hsub : A.map valEmbedding ⊆
      (Finset.univ : Finset Option).filter (fun o ↦ s ∈ H.slots o) := by
    intro o ho
    rcases Finset.mem_map.mp ho with ⟨p, hp, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
  change A.card ≤ H.slotDegree s
  have hcardA : (A.map valEmbedding).card = A.card :=
    Finset.card_map valEmbedding
  rw [← hcardA]
  exact Finset.card_le_card hsub

/-- The job-slot codegree of an active job is unchanged. -/
theorem inducedOnJobs_jobSlotCodegree (active : Finset Job)
    (j : ActiveJob active) (s : Slot) :
    (H.inducedOnJobs active).jobSlotCodegree j s =
      H.jobSlotCodegree j.1 s := by
  let valEmbedding : H.ActiveJobOption active ↪ Option :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : (((H.inducedOnJobs active).fiber j).filter
      (fun o ↦ s ∈ (H.inducedOnJobs active).slots o)).map valEmbedding =
      (H.fiber j.1).filter (fun o ↦ s ∈ H.slots o) := by
    ext o
    constructor
    · intro ho
      rcases Finset.mem_map.mp ho with ⟨p, hp, rfl⟩
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr
        ⟨H.mem_fiber.mpr
          (congrArg Subtype.val
            ((H.inducedOnJobs active).mem_fiber.mp hp'.1)), hp'.2⟩
    · intro ho
      have ho' := Finset.mem_filter.mp ho
      have howner : H.owner o = j.1 := H.mem_fiber.mp ho'.1
      have hactive : H.owner o ∈ active := by simpa [howner] using j.2
      apply Finset.mem_map.mpr
      refine ⟨⟨o, hactive⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨(H.inducedOnJobs active).mem_fiber.mpr (Subtype.ext howner), ho'.2⟩
  simpa [jobSlotCodegree] using congrArg Finset.card hmap

/-- Active-job restriction cannot increase slot-pair codegree. -/
theorem inducedOnJobs_slotPairCodegree_le (active : Finset Job)
    (s t : Slot) :
    (H.inducedOnJobs active).slotPairCodegree s t ≤
      H.slotPairCodegree s t := by
  let valEmbedding : H.ActiveJobOption active ↪ Option :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let A : Finset (H.ActiveJobOption active) :=
    (Finset.univ : Finset (H.ActiveJobOption active)).filter
      (fun o ↦ s ∈ (H.inducedOnJobs active).slots o ∧
        t ∈ (H.inducedOnJobs active).slots o)
  have hsub : A.map valEmbedding ⊆
      (Finset.univ : Finset Option).filter
        (fun o ↦ s ∈ H.slots o ∧ t ∈ H.slots o) := by
    intro o ho
    rcases Finset.mem_map.mp ho with ⟨p, hp, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
  change A.card ≤ H.slotPairCodegree s t
  have hcardA : (A.map valEmbedding).card = A.card :=
    Finset.card_map valEmbedding
  rw [← hcardA]
  exact Finset.card_le_card hsub

/-- Forget the active-owner proof on a selected option set. -/
def liftActiveJobSet (active : Finset Job)
    (A : Finset (H.ActiveJobOption active)) : Finset Option :=
  A.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_liftActiveJobSet {active : Finset Job}
    {A : Finset (H.ActiveJobOption active)} {o : Option} :
    o ∈ H.liftActiveJobSet active A ↔ ∃ q ∈ A, q.1 = o := by
  simp [liftActiveJobSet]

/-- A partial matching in the active-job system remains one in the original
system after forgetting subtype proofs. -/
theorem liftActiveJobSet_isPartialMatching
    (active : Finset Job) {A : Finset (H.ActiveJobOption active)}
    (hA : (H.inducedOnJobs active).IsPartialMatching A) :
    H.IsPartialMatching (H.liftActiveJobSet active A) := by
  constructor
  · intro o ho p hp hop
    rcases Finset.mem_map.mp ho with ⟨qo, hqo, rfl⟩
    rcases Finset.mem_map.mp hp with ⟨qp, hqp, rfl⟩
    exact hA.1 hqo hqp (fun h ↦ hop (congrArg Subtype.val h))
  · intro o ho p hp heq
    rcases Finset.mem_map.mp ho with ⟨qo, hqo, rfl⟩
    rcases Finset.mem_map.mp hp with ⟨qp, hqp, rfl⟩
    exact congrArg Subtype.val
      (hA.2 hqo hqp (Subtype.ext heq))

/-- Lifting from an active-job system preserves coverage of every active
job. -/
theorem covers_liftActiveJobSet_iff
    (active : Finset Job) (A : Finset (H.ActiveJobOption active))
    (j : ActiveJob active) :
    H.Covers (H.liftActiveJobSet active A) j.1 ↔
      (H.inducedOnJobs active).Covers A j := by
  constructor
  · rintro ⟨o, ho, howner⟩
    rcases H.mem_liftActiveJobSet.mp ho with ⟨q, hq, rfl⟩
    refine ⟨q, hq, ?_⟩
    exact Subtype.ext howner
  · rintro ⟨q, hq, howner⟩
    refine ⟨q.1, H.mem_liftActiveJobSet.mpr ⟨q, hq, rfl⟩, ?_⟩
    exact congrArg Subtype.val howner

/-- Forget both layers of subtype evidence after first restricting to active
jobs and then to a kept option set. -/
def liftActiveKeptOptionSet
    (active : Finset Job)
    (keep : Finset (H.ActiveJobOption active))
    (A : Finset (KeptOption keep)) :
    Finset Option :=
  H.liftActiveJobSet active
    ((H.inducedOnJobs active).liftKeptOptionSet keep A)

/-- A matching chosen after active-job restriction and deterministic
regularization lifts through both restriction layers. -/
theorem liftActiveKeptOptionSet_isPartialMatching
    (active : Finset Job)
    (keep : Finset (H.ActiveJobOption active))
    {A : Finset (KeptOption keep)}
    (hA : ((H.inducedOnJobs active).inducedOnOptions keep).IsPartialMatching A) :
    H.IsPartialMatching (H.liftActiveKeptOptionSet active keep A) := by
  apply H.liftActiveJobSet_isPartialMatching active
  exact (H.inducedOnJobs active).liftKeptOptionSet_isPartialMatching keep hA

/-- The two-layer lift also preserves coverage of every active job. -/
theorem covers_liftActiveKeptOptionSet_iff
    (active : Finset Job)
    (keep : Finset (H.ActiveJobOption active))
    (A : Finset (KeptOption keep))
    (j : ActiveJob active) :
    H.Covers (H.liftActiveKeptOptionSet active keep A) j.1 ↔
      ((H.inducedOnJobs active).inducedOnOptions keep).Covers A j := by
  rw [liftActiveKeptOptionSet,
    H.covers_liftActiveJobSet_iff active
      ((H.inducedOnJobs active).liftKeptOptionSet keep A) j,
    (H.inducedOnJobs active).covers_liftKeptOptionSet_iff keep A j]

end WeightedEdgeColoring.RankThreeOptionSystem
