import WeightedEdgeColoring.QuantizedOptions

/-!
# Restricting and regularizing a rank-three option system

Residual iteration may discard surplus options.  This file records that an
arbitrary finite set of kept options inherits the rank-three structure and
cannot increase any slot or codegree parameter.  It also chooses exactly `k`
options from every job fibre whenever all fibres contain at least `k` options.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- An option together with evidence that it belongs to the kept set. -/
abbrev KeptOption (keep : Finset Option) := {o : Option // o ∈ keep}

/-- The option system induced by a finite set of options. -/
def inducedOnOptions (keep : Finset Option) :
    RankThreeOptionSystem Job Slot (KeptOption keep) where
  owner o := H.owner o.1
  slots o := H.slots o.1
  slots_card_le_two o := H.slots_card_le_two o.1

/-- Forget the proof that every selected option belongs to `keep`. -/
def liftKeptOptionSet (_H : RankThreeOptionSystem Job Slot Option)
    (keep : Finset Option)
    (A : Finset (KeptOption keep)) : Finset Option :=
  A.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_liftKeptOptionSet {keep : Finset Option}
    {A : Finset (KeptOption keep)} {o : Option} :
    o ∈ H.liftKeptOptionSet keep A ↔ ∃ q ∈ A, q.1 = o := by
  simp [liftKeptOptionSet]

/-- A partial matching in an option-restricted system is still a partial
matching after the subtype proof is forgotten. -/
theorem liftKeptOptionSet_isPartialMatching
    (keep : Finset Option) {A : Finset (KeptOption keep)}
    (hA : (H.inducedOnOptions keep).IsPartialMatching A) :
    H.IsPartialMatching (H.liftKeptOptionSet keep A) := by
  constructor
  · intro o ho p hp hop
    rcases H.mem_liftKeptOptionSet.mp ho with ⟨qo, hqo, rfl⟩
    rcases H.mem_liftKeptOptionSet.mp hp with ⟨qp, hqp, rfl⟩
    exact hA.1 hqo hqp (fun h ↦ hop (congrArg Subtype.val h))
  · intro o ho p hp heq
    rcases H.mem_liftKeptOptionSet.mp ho with ⟨qo, hqo, rfl⟩
    rcases H.mem_liftKeptOptionSet.mp hp with ⟨qp, hqp, rfl⟩
    exact congrArg Subtype.val
      (hA.2 hqo hqp heq)

/-- Forgetting the kept-option proof preserves exactly which jobs are
covered. -/
theorem covers_liftKeptOptionSet_iff
    (keep : Finset Option) (A : Finset (KeptOption keep)) (j : Job) :
    H.Covers (H.liftKeptOptionSet keep A) j ↔
      (H.inducedOnOptions keep).Covers A j := by
  constructor
  · rintro ⟨o, ho, howner⟩
    rcases H.mem_liftKeptOptionSet.mp ho with ⟨q, hq, rfl⟩
    exact ⟨q, hq, howner⟩
  · rintro ⟨q, hq, howner⟩
    exact ⟨q.1, H.mem_liftKeptOptionSet.mpr ⟨q, hq, rfl⟩, howner⟩

/-- The fibre of the induced system is the kept part of the old fibre. -/
theorem inducedOnOptions_fiber_card (keep : Finset Option) (j : Job) :
    ((H.inducedOnOptions keep).fiber j).card =
      (keep.filter fun o ↦ H.owner o = j).card := by
  let valEmbedding : KeptOption keep ↪ Option :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : ((H.inducedOnOptions keep).fiber j).map valEmbedding =
      keep.filter fun o ↦ H.owner o = j := by
    ext o
    simp [valEmbedding, inducedOnOptions, and_comm]
  simpa using congrArg Finset.card hmap

/-- Restriction cannot increase a job degree. -/
theorem inducedOnOptions_fiber_card_le (keep : Finset Option) (j : Job) :
    ((H.inducedOnOptions keep).fiber j).card ≤ (H.fiber j).card := by
  rw [H.inducedOnOptions_fiber_card]
  apply Finset.card_le_card
  intro o ho
  exact H.mem_fiber.mpr (Finset.mem_filter.mp ho).2

/-- Restriction cannot increase a slot degree. -/
theorem inducedOnOptions_slotDegree_le (keep : Finset Option) (s : Slot) :
    (H.inducedOnOptions keep).slotDegree s ≤ H.slotDegree s := by
  let valEmbedding : KeptOption keep ↪ Option :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let A : Finset (KeptOption keep) :=
    (Finset.univ : Finset (KeptOption keep)).filter
      (fun o ↦ s ∈ (H.inducedOnOptions keep).slots o)
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

/-- Restriction cannot increase a job-slot codegree. -/
theorem inducedOnOptions_jobSlotCodegree_le
    (keep : Finset Option) (j : Job) (s : Slot) :
    (H.inducedOnOptions keep).jobSlotCodegree j s ≤
      H.jobSlotCodegree j s := by
  let valEmbedding : KeptOption keep ↪ Option :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let A : Finset (KeptOption keep) :=
    ((H.inducedOnOptions keep).fiber j).filter
      (fun o ↦ s ∈ (H.inducedOnOptions keep).slots o)
  have hsub : A.map valEmbedding ⊆
      (H.fiber j).filter (fun o ↦ s ∈ H.slots o) := by
    intro o ho
    rcases Finset.mem_map.mp ho with ⟨p, hp, rfl⟩
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨H.mem_fiber.mpr ((H.inducedOnOptions keep).mem_fiber.mp hp'.1), hp'.2⟩
  change A.card ≤ H.jobSlotCodegree j s
  have hcardA : (A.map valEmbedding).card = A.card :=
    Finset.card_map valEmbedding
  rw [← hcardA]
  exact Finset.card_le_card hsub

/-- Restriction cannot increase a slot-pair codegree. -/
theorem inducedOnOptions_slotPairCodegree_le
    (keep : Finset Option) (s t : Slot) :
    (H.inducedOnOptions keep).slotPairCodegree s t ≤
      H.slotPairCodegree s t := by
  let valEmbedding : KeptOption keep ↪ Option :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let A : Finset (KeptOption keep) :=
    (Finset.univ : Finset (KeptOption keep)).filter
      (fun o ↦ s ∈ (H.inducedOnOptions keep).slots o ∧
        t ∈ (H.inducedOnOptions keep).slots o)
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

/-- If every job has at least `k` options, choose a single kept set whose
intersection with every job fibre has exactly `k` elements. -/
theorem exists_jobRegularizingSet (k : ℕ)
    (hmin : ∀ j, k ≤ (H.fiber j).card) :
    ∃ keep : Finset Option,
      ∀ j, (keep.filter fun o ↦ H.owner o = j).card = k := by
  classical
  choose part hpartSub hpartCard using
    fun j ↦ (H.fiber j).exists_subset_card_eq (hmin j)
  let keep : Finset Option :=
    (Finset.univ : Finset Job).biUnion part
  refine ⟨keep, ?_⟩
  intro j
  have heq : (keep.filter fun o ↦ H.owner o = j) = part j := by
    ext o
    constructor
    · intro ho
      have hokeep := (Finset.mem_filter.mp ho).1
      have howner := (Finset.mem_filter.mp ho).2
      rcases Finset.mem_biUnion.mp hokeep with ⟨i, _hi, hoi⟩
      have hoiFiber : o ∈ H.fiber i := hpartSub i hoi
      have hoiOwner : H.owner o = i := H.mem_fiber.mp hoiFiber
      have hij : i = j := hoiOwner.symm.trans howner
      simpa [hij] using hoi
    · intro ho
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_univ j, ho⟩, ?_⟩
      exact H.mem_fiber.mp (hpartSub j ho)
  rw [heq, hpartCard]

/-- The regularizing set induces a rank-three system with every job degree
exactly `k`, while all slot and codegree bounds can only improve. -/
theorem exists_jobRegularizedSystem (k : ℕ)
    (hmin : ∀ j, k ≤ (H.fiber j).card) :
    ∃ keep : Finset Option,
      (∀ j, ((H.inducedOnOptions keep).fiber j).card = k) ∧
      (∀ s, (H.inducedOnOptions keep).slotDegree s ≤ H.slotDegree s) ∧
      (∀ j s, (H.inducedOnOptions keep).jobSlotCodegree j s ≤
        H.jobSlotCodegree j s) ∧
      (∀ s t, (H.inducedOnOptions keep).slotPairCodegree s t ≤
        H.slotPairCodegree s t) := by
  rcases H.exists_jobRegularizingSet k hmin with ⟨keep, hkeep⟩
  refine ⟨keep, ?_, H.inducedOnOptions_slotDegree_le keep,
    H.inducedOnOptions_jobSlotCodegree_le keep,
    H.inducedOnOptions_slotPairCodegree_le keep⟩
  intro j
  rw [H.inducedOnOptions_fiber_card, hkeep]

end WeightedEdgeColoring.RankThreeOptionSystem
