import WeightedEdgeColoring.RankThreeOptionRestriction
import WeightedEdgeColoring.RankThreeResidualNibble
import WeightedEdgeColoring.RankThreeResidualNibble

/-!
# Projecting a round from a regular rank-three extension

This file isolates the bookkeeping needed for slot regularization.  A
regular extension may add jobs, slots, and options, but it adds no option to
an old job.  Old options preserve their owner and their slot set under the
three embeddings.

After a matching round in the extension we discard all new selected options.
We do **not** restore old options killed by a new selected option: the next
old system is induced by precisely those old options whose images remain in
the extension residual system.  Consequently surviving old job degrees are
preserved exactly, while old slot degrees and both kinds of codegree can only
decrease.  This is the projection step used after every fresh regularization.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

universe u v w u' v' w'

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  {Job' : Type u'} {Slot' : Type v'} {Option' : Type w'}
  [Fintype Job'] [Fintype Slot'] [Fintype Option']
  [DecidableEq Job'] [DecidableEq Slot'] [DecidableEq Option']

/-- A rank-three extension which is induced on the old jobs.  The last four
fields record the degree conclusions supplied by a concrete regularization
construction. -/
structure IsRegularExtension
    (H : RankThreeOptionSystem Job Slot Option)
    (H' : RankThreeOptionSystem Job' Slot' Option')
    (J S lambda : ℕ) where
  jobEmbedding : Job ↪ Job'
  slotEmbedding : Slot ↪ Slot'
  optionEmbedding : Option ↪ Option'
  owner_optionEmbedding : ∀ o,
    H'.owner (optionEmbedding o) = jobEmbedding (H.owner o)
  slots_optionEmbedding : ∀ o,
    H'.slots (optionEmbedding o) = (H.slots o).map slotEmbedding
  old_job_induced : ∀ (j : Job) (q : Option'),
    H'.owner q = jobEmbedding j →
      ∃ o : Option, H.owner o = j ∧ optionEmbedding o = q
  jobDegree_eq : ∀ j', (H'.fiber j').card = J
  slotDegree_eq : ∀ s', H'.slotDegree s' = S
  jobSlotCodegree_le : ∀ j' s', H'.jobSlotCodegree j' s' ≤ lambda
  slotPairCodegree_le : ∀ s' t', s' ≠ t' →
    H'.slotPairCodegree s' t' ≤ lambda

variable {H : RankThreeOptionSystem Job Slot Option}
  {H' : RankThreeOptionSystem Job' Slot' Option'}
  {J S lambda : ℕ}

namespace IsRegularExtension

/-- Selected old options, obtained by pulling a matching in the extension
back through the option embedding. -/
def originalSelection
    (E : IsRegularExtension H H' J S lambda)
    (M : Finset Option') : Finset Option :=
  Finset.univ.filter fun o ↦ E.optionEmbedding o ∈ M

/-- Old options which remain after the extension round.  These are the only
old options retained for the next round.  In particular, an old option
blocked by a selected dummy option is not restored when dummy objects are
discarded. -/
def originalResidual
    (E : IsRegularExtension H H' J S lambda)
    (M : Finset Option') : Finset Option :=
  Finset.univ.filter fun o ↦
    E.optionEmbedding o ∈ H'.residualOptions M

@[simp] theorem mem_originalSelection
    (E : IsRegularExtension H H' J S lambda)
    (M : Finset Option') (o : Option) :
    o ∈ E.originalSelection M ↔ E.optionEmbedding o ∈ M := by
  simp [originalSelection]

@[simp] theorem mem_originalResidual
    (E : IsRegularExtension H H' J S lambda)
    (M : Finset Option') (o : Option) :
    o ∈ E.originalResidual M ↔
      E.optionEmbedding o ∈ H'.residualOptions M := by
  simp [originalResidual]

/-- Compatibility of old options is reflected by the extension embedding. -/
theorem compatible_iff
    (E : IsRegularExtension H H' J S lambda) (o p : Option) :
    H'.Compatible (E.optionEmbedding o) (E.optionEmbedding p) ↔
      H.Compatible o p := by
  simp only [Compatible, E.slots_optionEmbedding]
  exact Finset.disjoint_map E.slotEmbedding

/-- Pulling back an extension matching gives an old matching. -/
theorem originalSelection_isPartialMatching
    (E : IsRegularExtension H H' J S lambda)
    (M : Finset Option') (hM : H'.IsPartialMatching M) :
    H.IsPartialMatching (E.originalSelection M) := by
  constructor
  · intro o ho p hp hop
    exact (E.compatible_iff o p).mp
      (hM.1 (E.mem_originalSelection M o |>.mp ho)
      (E.mem_originalSelection M p |>.mp hp)
      (fun h ↦ hop (E.optionEmbedding.injective h)))
  · intro o ho p hp howner
    apply E.optionEmbedding.injective
    apply hM.2 (E.mem_originalSelection M o |>.mp ho)
      (E.mem_originalSelection M p |>.mp hp)
    rw [E.owner_optionEmbedding, E.owner_optionEmbedding, howner]

/-- Because no new option has an old owner, an old job is covered in the
extension exactly when its pullback is covered by an old selected option. -/
theorem covers_originalSelection_iff
    (E : IsRegularExtension H H' J S lambda)
    (M : Finset Option') (j : Job) :
    H.Covers (E.originalSelection M) j ↔
      H'.Covers M (E.jobEmbedding j) := by
  constructor
  · rintro ⟨o, ho, howner⟩
    refine ⟨E.optionEmbedding o,
      E.mem_originalSelection M o |>.mp ho, ?_⟩
    simpa [howner] using E.owner_optionEmbedding o
  · rintro ⟨q, hq, howner⟩
    rcases E.old_job_induced j q howner with ⟨o, ho, rfl⟩
    exact ⟨o, E.mem_originalSelection M o |>.mpr hq, ho⟩

/-- Every retained old option is genuinely available after the pulled-back
old matching.  The inclusion can be strict, exactly because dummy selected
options are allowed to kill old options. -/
theorem originalResidual_subset_residualOptions
    (E : IsRegularExtension H H' J S lambda)
    (M : Finset Option') :
    E.originalResidual M ⊆
      H.residualOptions (E.originalSelection M) := by
  intro o ho
  rw [H.mem_residualOptions]
  intro p hp
  have ho' := H'.mem_residualOptions.mp
    (E.mem_originalResidual M o |>.mp ho)
  have hp' : E.optionEmbedding p ∈ M :=
    E.mem_originalSelection M p |>.mp hp
  have hdata := ho' (E.optionEmbedding p) hp'
  constructor
  · intro howner
    exact hdata.1 (by
      rw [E.owner_optionEmbedding, E.owner_optionEmbedding, howner])
  · exact E.compatible_iff o p |>.mp hdata.2

/-- The retained part of an old job fibre is in bijection with the residual
fibre of the corresponding old job in the extension. -/
theorem originalResidual_fiber_card
    (E : IsRegularExtension H H' J S lambda)
    (M : Finset Option') (j : Job) :
    ((E.originalResidual M).filter fun o ↦ H.owner o = j).card =
      H'.residualJobDegree M (E.jobEmbedding j) := by
  let emb : Option ↪ Option' := E.optionEmbedding
  have hmap :
      (((E.originalResidual M).filter fun o ↦ H.owner o = j).map emb) =
        H'.residualFiber M (E.jobEmbedding j) := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_map.mp hq with ⟨o, ho, rfl⟩
      have ho' := Finset.mem_filter.mp ho
      apply H'.mem_residualFiber.mpr
      refine ⟨?_, H'.mem_residualOptions.mp
        (E.mem_originalResidual M o |>.mp ho'.1)⟩
      simpa [ho'.2] using E.owner_optionEmbedding o
    · intro hq
      have hq' := H'.mem_residualFiber.mp hq
      rcases E.old_job_induced j q hq'.1 with ⟨o, ho, rfl⟩
      apply Finset.mem_map.mpr
      refine ⟨o, Finset.mem_filter.mpr ⟨?_, ho⟩, rfl⟩
      exact E.mem_originalResidual M o |>.mpr
        (H'.mem_residualOptions.mpr hq'.2)
  unfold residualJobDegree
  rw [← hmap, Finset.card_map]

/-- Passing to the induced system on retained old options preserves the
extension's residual degree at every old job exactly. -/
theorem induced_originalResidual_fiber_card
    (E : IsRegularExtension H H' J S lambda)
    (M : Finset Option') (j : Job) :
    (((H.inducedOnOptions (E.originalResidual M)).fiber j).card) =
      H'.residualJobDegree M (E.jobEmbedding j) := by
  rw [H.inducedOnOptions_fiber_card, E.originalResidual_fiber_card M j]

/-- The retained old degree at a slot is at most the extension residual
degree at its image. -/
theorem induced_originalResidual_slotDegree_le
    (E : IsRegularExtension H H' J S lambda)
    (M : Finset Option') (s : Slot) :
    (H.inducedOnOptions (E.originalResidual M)).slotDegree s ≤
      H'.residualSlotDegree M (E.slotEmbedding s) := by
  let keep := E.originalResidual M
  let emb : KeptOption keep ↪ Option' :=
    ⟨fun o ↦ E.optionEmbedding o.1,
      fun a b h ↦ Subtype.ext (E.optionEmbedding.injective h)⟩
  let oldAt : Finset (KeptOption keep) :=
    (Finset.univ : Finset (KeptOption keep)).filter fun o ↦
      s ∈ (H.inducedOnOptions keep).slots o
  have hsub : oldAt.map emb ⊆
      (H'.residualOptions M).filter fun q ↦
        E.slotEmbedding s ∈ H'.slots q := by
    intro q hq
    rcases Finset.mem_map.mp hq with ⟨o, ho, rfl⟩
    have ho' := Finset.mem_filter.mp ho
    apply Finset.mem_filter.mpr
    change E.optionEmbedding o.1 ∈ H'.residualOptions M ∧
      E.slotEmbedding s ∈ H'.slots (E.optionEmbedding o.1)
    refine ⟨E.mem_originalResidual M o.1 |>.mp o.2, ?_⟩
    rw [E.slots_optionEmbedding]
    exact Finset.mem_map.mpr ⟨s, ho'.2, rfl⟩
  change oldAt.card ≤ H'.residualSlotDegree M (E.slotEmbedding s)
  rw [← Finset.card_map emb]
  exact Finset.card_le_card hsub

/-- Job--slot codegrees can only decrease when the extension residual is
projected back to the old option system. -/
theorem induced_originalResidual_jobSlotCodegree_le
    (E : IsRegularExtension H H' J S lambda)
    (M : Finset Option') (j : Job) (s : Slot) :
    (H.inducedOnOptions (E.originalResidual M)).jobSlotCodegree j s ≤
      lambda := by
  calc
    (H.inducedOnOptions (E.originalResidual M)).jobSlotCodegree j s ≤
        H.jobSlotCodegree j s :=
      H.inducedOnOptions_jobSlotCodegree_le (E.originalResidual M) j s
    _ ≤ H'.jobSlotCodegree (E.jobEmbedding j) (E.slotEmbedding s) := by
      let oldAt := (H.fiber j).filter fun o ↦ s ∈ H.slots o
      let emb : Option ↪ Option' := E.optionEmbedding
      have hsub : oldAt.map emb ⊆
          (H'.fiber (E.jobEmbedding j)).filter fun q ↦
            E.slotEmbedding s ∈ H'.slots q := by
        intro q hq
        rcases Finset.mem_map.mp hq with ⟨o, ho, rfl⟩
        have ho' := Finset.mem_filter.mp ho
        exact Finset.mem_filter.mpr ⟨H'.mem_fiber.mpr
          ((E.owner_optionEmbedding o).trans
            (congrArg E.jobEmbedding (H.mem_fiber.mp ho'.1))), by
              rw [E.slots_optionEmbedding]
              exact Finset.mem_map.mpr ⟨s, ho'.2, rfl⟩⟩
      change oldAt.card ≤ _
      rw [← Finset.card_map emb]
      exact Finset.card_le_card hsub
    _ ≤ lambda := E.jobSlotCodegree_le _ _

/-- Slot-pair codegrees can only decrease under the same projection. -/
theorem induced_originalResidual_slotPairCodegree_le
    (E : IsRegularExtension H H' J S lambda)
    (M : Finset Option') (s t : Slot)
    (hst : s ≠ t) :
    (H.inducedOnOptions (E.originalResidual M)).slotPairCodegree s t ≤
      lambda := by
  calc
    (H.inducedOnOptions (E.originalResidual M)).slotPairCodegree s t ≤
        H.slotPairCodegree s t :=
      H.inducedOnOptions_slotPairCodegree_le (E.originalResidual M) s t
    _ ≤ H'.slotPairCodegree (E.slotEmbedding s) (E.slotEmbedding t) := by
      let oldAt := (Finset.univ : Finset Option).filter fun o ↦
        s ∈ H.slots o ∧ t ∈ H.slots o
      let emb : Option ↪ Option' := E.optionEmbedding
      have hsub : oldAt.map emb ⊆
          (Finset.univ : Finset Option').filter fun q ↦
            E.slotEmbedding s ∈ H'.slots q ∧
            E.slotEmbedding t ∈ H'.slots q := by
        intro q hq
        rcases Finset.mem_map.mp hq with ⟨o, ho, rfl⟩
        have ho' := (Finset.mem_filter.mp ho).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [E.slots_optionEmbedding]
          exact ⟨Finset.mem_map.mpr ⟨s, ho'.1, rfl⟩,
            Finset.mem_map.mpr ⟨t, ho'.2, rfl⟩⟩⟩
      change oldAt.card ≤ _
      rw [← Finset.card_map emb]
      exact Finset.card_le_card hsub
    _ ≤ lambda := E.slotPairCodegree_le _ _
      (fun h ↦ hst (E.slotEmbedding.injective h))

end IsRegularExtension

end WeightedEdgeColoring.RankThreeOptionSystem
