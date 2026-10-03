import WeightedEdgeColoring.RankThreeOptionRestriction
import WeightedEdgeColoring.RankThreeResidualLift
import WeightedEdgeColoring.RankThreeRegularExtensionBridge
import WeightedEdgeColoring.RankThreeJobRestriction

/-!
# Iterating restricted rounds on the original option type

Regularization and projection change the option type, sometimes twice in a
single round.  This file keeps that type change out of the iteration state.
The state consists of an accumulated matching `M` of original options and a
set `keep` of original options, with `keep ⊆ residualOptions M`.

A round first restricts to `keep`, then may restrict once more to a
job-regularizing set `trim`.  Its selected and surviving options are lifted
through both subtype layers.  The selected options are added to `M`; the
survivors become the next original-type `keep` set.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

universe u v w u' v' w'

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- A matching from an induced kept-option system can be added to the
accumulated original matching whenever all kept options are residual. -/
theorem IsPartialMatching.union_liftKeptOptionSet_of_subset_residual
    {M keep : Finset Option}
    (hM : H.IsPartialMatching M)
    (hkeep : keep ⊆ H.residualOptions M)
    {A : Finset (KeptOption keep)}
    (hA : (H.inducedOnOptions keep).IsPartialMatching A) :
    H.IsPartialMatching (M ∪ H.liftKeptOptionSet keep A) := by
  have hlift := H.liftKeptOptionSet_isPartialMatching keep hA
  apply hM.union_of_cross H hlift
  · intro p hp q hq
    rcases H.mem_liftKeptOptionSet.mp hq with ⟨a, ha, rfl⟩
    have hres := H.mem_residualOptions.mp (hkeep a.2) p hp
    exact H.compatible_symm.mpr hres.2
  · intro p hp q hq
    rcases H.mem_liftKeptOptionSet.mp hq with ⟨a, ha, rfl⟩
    have hres := H.mem_residualOptions.mp (hkeep a.2) p hp
    exact Ne.symm hres.1

/-- Lift a locally residual kept set back to the original option type.  The
result is residual after the union of the accumulated matching and the
lifted local selection. -/
theorem liftKeptOptionSet_residual_subset
    {M keep : Finset Option}
    (hkeep : keep ⊆ H.residualOptions M)
    (A next : Finset (KeptOption keep))
    (hnext : next ⊆ (H.inducedOnOptions keep).residualOptions A) :
    H.liftKeptOptionSet keep next ⊆
      H.residualOptions (M ∪ H.liftKeptOptionSet keep A) := by
  intro o ho
  rcases H.mem_liftKeptOptionSet.mp ho with ⟨q, hqnext, rfl⟩
  rw [H.mem_residualOptions]
  intro p hp
  rcases Finset.mem_union.mp hp with hpM | hpA
  · exact H.mem_residualOptions.mp (hkeep q.2) p hpM
  · rcases H.mem_liftKeptOptionSet.mp hpA with ⟨a, ha, rfl⟩
    exact (H.inducedOnOptions keep).mem_residualOptions.mp
      (hnext hqnext) a ha

/-- Forgetting an active-owner proof preserves the residual relation. -/
theorem liftActiveJobSet_residual_subset
    (active : Finset Job)
    (A next : Finset (H.ActiveJobOption active))
    (hnext : next ⊆ (H.inducedOnJobs active).residualOptions A) :
    H.liftActiveJobSet active next ⊆
      H.residualOptions (H.liftActiveJobSet active A) := by
  intro o ho
  rcases H.mem_liftActiveJobSet.mp ho with ⟨q, hqnext, rfl⟩
  rw [H.mem_residualOptions]
  intro p hp
  rcases H.mem_liftActiveJobSet.mp hp with ⟨a, ha, rfl⟩
  have hlocal := (H.inducedOnJobs active).mem_residualOptions.mp
    (hnext hqnext) a ha
  exact ⟨fun howner ↦ hlocal.1 (Subtype.ext howner), hlocal.2⟩

/-- Lifting an option restriction preserves each job-fibre size exactly. -/
theorem inducedOnOptions_liftKeptOptionSet_fiber_card
    (keep : Finset Option) (A : Finset (KeptOption keep)) (j : Job) :
    ((H.inducedOnOptions (H.liftKeptOptionSet keep A)).fiber j).card =
      ((((H.inducedOnOptions keep).inducedOnOptions A).fiber j).card) := by
  let emb : KeptOption keep ↪ Option :=
    ⟨Subtype.val, Subtype.val_injective⟩
  rw [H.inducedOnOptions_fiber_card,
    (H.inducedOnOptions keep).inducedOnOptions_fiber_card]
  have hmap :
      (A.filter fun o ↦ (H.inducedOnOptions keep).owner o = j).map emb =
        (H.liftKeptOptionSet keep A).filter fun o ↦ H.owner o = j := by
    ext o
    constructor
    · intro ho
      rcases Finset.mem_map.mp ho with ⟨q, hq, rfl⟩
      have hq' := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr
        ⟨H.mem_liftKeptOptionSet.mpr ⟨q, hq'.1, rfl⟩, hq'.2⟩
    · intro ho
      have ho' := Finset.mem_filter.mp ho
      rcases H.mem_liftKeptOptionSet.mp ho'.1 with ⟨q, hqA, rfl⟩
      exact Finset.mem_map.mpr
        ⟨q, Finset.mem_filter.mpr ⟨hqA, ho'.2⟩, rfl⟩
  rw [← hmap, Finset.card_map]

/-- Lifting an option restriction preserves each slot degree exactly. -/
theorem inducedOnOptions_liftKeptOptionSet_slotDegree
    (keep : Finset Option) (A : Finset (KeptOption keep)) (s : Slot) :
    (H.inducedOnOptions (H.liftKeptOptionSet keep A)).slotDegree s =
      ((H.inducedOnOptions keep).inducedOnOptions A).slotDegree s := by
  let emb : KeptOption keep ↪ Option :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let L := (Finset.univ : Finset (KeptOption A)).filter fun o ↦
    s ∈ ((H.inducedOnOptions keep).inducedOnOptions A).slots o
  let R := (Finset.univ : Finset
    (KeptOption (H.liftKeptOptionSet keep A))).filter fun o ↦
    s ∈ (H.inducedOnOptions (H.liftKeptOptionSet keep A)).slots o
  let e : KeptOption A ↪ KeptOption (H.liftKeptOptionSet keep A) :=
    { toFun := fun o : KeptOption A ↦
        ⟨o.1.1, H.mem_liftKeptOptionSet.mpr ⟨o.1, o.2, rfl⟩⟩
      inj' := by
        intro x y h
        have hv : x.1.1 = y.1.1 :=
          congrArg
            (fun z : KeptOption (H.liftKeptOptionSet keep A) ↦ z.1) h
        exact Subtype.ext (Subtype.ext hv) }
  have hmap : L.map e = R := by
    ext o
    constructor
    · intro ho
      rcases Finset.mem_map.mp ho with ⟨q, hq, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩
    · intro ho
      have ho' := Finset.mem_filter.mp ho
      rcases H.mem_liftKeptOptionSet.mp o.2 with ⟨q, hqA, hqo⟩
      let qA : KeptOption A := ⟨q, hqA⟩
      have heqo : e qA = o := Subtype.ext hqo
      apply Finset.mem_map.mpr
      refine ⟨qA, ?_, heqo⟩
      have hslotO : s ∈ H.slots o.1 := ho'.2
      have hslotQ : s ∈ H.slots q.1 := by
        rw [hqo]
        exact hslotO
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hslotQ⟩
  change R.card = L.card
  rw [← hmap, Finset.card_map]

/-- Lifting an active-job restriction preserves an active fibre exactly. -/
theorem inducedOnOptions_liftActiveJobSet_fiber_card
    (active : Finset Job) (A : Finset (H.ActiveJobOption active))
    (j : ActiveJob active) :
    ((H.inducedOnOptions (H.liftActiveJobSet active A)).fiber j.1).card =
      ((((H.inducedOnJobs active).inducedOnOptions A).fiber j).card) := by
  let emb : H.ActiveJobOption active ↪ Option :=
    ⟨Subtype.val, Subtype.val_injective⟩
  rw [H.inducedOnOptions_fiber_card,
    (H.inducedOnJobs active).inducedOnOptions_fiber_card]
  have hmap :
      (A.filter fun o ↦ (H.inducedOnJobs active).owner o = j).map emb =
        (H.liftActiveJobSet active A).filter fun o ↦ H.owner o = j.1 := by
    ext o
    constructor
    · intro ho
      rcases Finset.mem_map.mp ho with ⟨q, hq, rfl⟩
      have hq' := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr
        ⟨H.mem_liftActiveJobSet.mpr ⟨q, hq'.1, rfl⟩,
          congrArg Subtype.val hq'.2⟩
    · intro ho
      have ho' := Finset.mem_filter.mp ho
      rcases H.mem_liftActiveJobSet.mp ho'.1 with ⟨q, hqA, rfl⟩
      apply Finset.mem_map.mpr
      refine ⟨q, Finset.mem_filter.mpr ⟨hqA, ?_⟩, rfl⟩
      exact Subtype.ext ho'.2
  rw [← hmap, Finset.card_map]

/-- Lifting an active-job restriction preserves every slot degree. -/
theorem inducedOnOptions_liftActiveJobSet_slotDegree
    (active : Finset Job) (A : Finset (H.ActiveJobOption active))
    (s : Slot) :
    (H.inducedOnOptions (H.liftActiveJobSet active A)).slotDegree s =
      ((H.inducedOnJobs active).inducedOnOptions A).slotDegree s := by
  let L := (Finset.univ : Finset (KeptOption A)).filter fun o ↦
    s ∈ ((H.inducedOnJobs active).inducedOnOptions A).slots o
  let R := (Finset.univ : Finset
    (KeptOption (H.liftActiveJobSet active A))).filter fun o ↦
    s ∈ (H.inducedOnOptions (H.liftActiveJobSet active A)).slots o
  let e : KeptOption A ↪ KeptOption (H.liftActiveJobSet active A) :=
    { toFun := fun o : KeptOption A ↦
        ⟨o.1.1, H.mem_liftActiveJobSet.mpr ⟨o.1, o.2, rfl⟩⟩
      inj' := by
        intro x y h
        have hv : x.1.1 = y.1.1 :=
          congrArg
            (fun z : KeptOption (H.liftActiveJobSet active A) ↦ z.1) h
        exact Subtype.ext (Subtype.ext hv) }
  have hmap : L.map e = R := by
    ext o
    constructor
    · intro ho
      rcases Finset.mem_map.mp ho with ⟨q, hq, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩
    · intro ho
      have ho' := Finset.mem_filter.mp ho
      rcases H.mem_liftActiveJobSet.mp o.2 with ⟨q, hqA, hqo⟩
      let qA : KeptOption A := ⟨q, hqA⟩
      have heqo : e qA = o := Subtype.ext hqo
      apply Finset.mem_map.mpr
      refine ⟨qA, ?_, heqo⟩
      have hslotO : s ∈ H.slots o.1 := ho'.2
      have hslotQ : s ∈ H.slots q.1 := by
        rw [hqo]
        exact hslotO
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hslotQ⟩
  change R.card = L.card
  rw [← hmap, Finset.card_map]

/-- Persistent original-type state for a sequence of regularized rounds. -/
structure OriginalIterationState where
  matching : Finset Option
  keep : Finset Option
  matching_isPartial : H.IsPartialMatching matching
  keep_subset_residual : keep ⊆ H.residualOptions matching

namespace OriginalIterationState

/-- Start with no selected option and any prescribed subset of the original
options.  Every option is residual from the empty matching. -/
def empty (keep : Finset Option) : OriginalIterationState H where
  matching := ∅
  keep := keep
  matching_isPartial := H.empty_isPartialMatching
  keep_subset_residual := by
    intro o ho
    simp only [mem_residualOptions]
    intro p hp
    simp at hp

/-- The canonical initial state keeps every original option. -/
def full : OriginalIterationState H :=
  empty H Finset.univ

/-- The current option system, retaining the original job and slot types. -/
def system (X : OriginalIterationState H) :=
  H.inducedOnOptions X.keep

/-- A qualitative output of one regularized projected round.

`trim` is the exact-degree job regularization of the current kept system.
The last two sets are the pulled-back selection and projected residual in
that twice-restricted option type.  A concrete regular-extension round
supplies `selected_isPartial` and `next_subset_residual`; its quantitative
degree and coverage conclusions may be carried separately by a predicate
on this witness. -/
structure RegularizedProjectedRound
    (X : OriginalIterationState H) (d : ℕ) where
  trim : Finset (KeptOption X.keep)
  trim_jobDegree_eq : ∀ j,
    ((((X.system).inducedOnOptions trim).fiber j).card) = d
  selected : Finset (KeptOption trim)
  next : Finset (KeptOption trim)
  selected_isPartial :
    ((X.system).inducedOnOptions trim).IsPartialMatching selected
  next_subset_residual :
    next ⊆ ((X.system).inducedOnOptions trim).residualOptions selected

variable {H}

/-- The ordinary fibre-trimming lemma supplies the exact-degree first layer
required by a regularized projected round. -/
theorem exists_regularizingTrim
    (X : OriginalIterationState H) (d : ℕ)
    (hdegree : ∀ j, d ≤ (X.system.fiber j).card) :
    ∃ trim : Finset (KeptOption X.keep),
      ∀ j, ((((X.system).inducedOnOptions trim).fiber j).card) = d := by
  rcases X.system.exists_jobRegularizedSystem d hdegree with
    ⟨trim, htrim, _hslot, _hjobSlot, _hslotPair⟩
  exact ⟨trim, htrim⟩

/-- Package the deterministic output of a matching round in a regular
extension as a twice-restricted round witness.  Quantitative conclusions of
the extension round can be retained alongside this witness in `Good`. -/
def RegularizedProjectedRound.ofRegularExtension
    {X : OriginalIterationState H} {d : ℕ}
    (trim : Finset (KeptOption X.keep))
    (htrim : ∀ j,
      ((((X.system).inducedOnOptions trim).fiber j).card) = d)
    {Job' : Type u'} {Slot' : Type v'} {Option' : Type w'}
    [Fintype Job'] [Fintype Slot'] [Fintype Option']
    [DecidableEq Job'] [DecidableEq Slot'] [DecidableEq Option']
    {H' : RankThreeOptionSystem Job' Slot' Option'} {S lambda : ℕ}
    (E : IsRegularExtension
      ((X.system).inducedOnOptions trim) H' d S lambda)
    (M : Finset Option') (hM : H'.IsPartialMatching M) :
    RegularizedProjectedRound H X d where
  trim := trim
  trim_jobDegree_eq := htrim
  selected := E.originalSelection M
  next := E.originalResidual M
  selected_isPartial := E.originalSelection_isPartialMatching M hM
  next_subset_residual := E.originalResidual_subset_residualOptions M

/-- Selection after forgetting the job-regularization subtype, but still in
the current kept-option type. -/
def RegularizedProjectedRound.currentSelection
    {X : OriginalIterationState H} {d : ℕ}
    (W : RegularizedProjectedRound H X d) : Finset (KeptOption X.keep) :=
  X.system.liftKeptOptionSet W.trim W.selected

/-- Projected residual after forgetting the job-regularization subtype. -/
def RegularizedProjectedRound.currentKeep
    {X : OriginalIterationState H} {d : ℕ}
    (W : RegularizedProjectedRound H X d) : Finset (KeptOption X.keep) :=
  X.system.liftKeptOptionSet W.trim W.next

/-- The selection lifted all the way to the original option type. -/
def RegularizedProjectedRound.originalSelection
    {X : OriginalIterationState H} {d : ℕ}
    (W : RegularizedProjectedRound H X d) : Finset Option :=
  H.liftKeptOptionSet X.keep W.currentSelection

/-- The projected residual lifted all the way to the original option type. -/
def RegularizedProjectedRound.originalKeep
    {X : OriginalIterationState H} {d : ℕ}
    (W : RegularizedProjectedRound H X d) : Finset Option :=
  H.liftKeptOptionSet X.keep W.currentKeep

/-- The once-lifted selection is a matching in the current kept system. -/
theorem RegularizedProjectedRound.currentSelection_isPartial
    {X : OriginalIterationState H} {d : ℕ}
    (W : RegularizedProjectedRound H X d) :
    X.system.IsPartialMatching W.currentSelection := by
  exact X.system.liftKeptOptionSet_isPartialMatching W.trim
    W.selected_isPartial

/-- The once-lifted projected residual is locally residual after the
once-lifted selection. -/
theorem RegularizedProjectedRound.currentKeep_subset_residual
    {X : OriginalIterationState H} {d : ℕ}
    (W : RegularizedProjectedRound H X d) :
    W.currentKeep ⊆ X.system.residualOptions W.currentSelection := by
  have htrim : W.trim ⊆ X.system.residualOptions ∅ := by
    intro q hq
    simp only [mem_residualOptions]
    intro p hp
    simp at hp
  have h := X.system.liftKeptOptionSet_residual_subset htrim
    W.selected W.next W.next_subset_residual
  simpa [RegularizedProjectedRound.currentSelection,
    RegularizedProjectedRound.currentKeep] using h

/-- Advance the original-type state by a regularized projected round. -/
def RegularizedProjectedRound.result
    {X : OriginalIterationState H} {d : ℕ}
    (W : RegularizedProjectedRound H X d) : OriginalIterationState H where
  matching := X.matching ∪ W.originalSelection
  keep := W.originalKeep
  matching_isPartial :=
    X.matching_isPartial.union_liftKeptOptionSet_of_subset_residual H
      X.keep_subset_residual W.currentSelection_isPartial
  keep_subset_residual :=
    H.liftKeptOptionSet_residual_subset X.keep_subset_residual
      W.currentSelection W.currentKeep W.currentKeep_subset_residual

@[simp] theorem RegularizedProjectedRound.result_matching
    {X : OriginalIterationState H} {d : ℕ}
    (W : RegularizedProjectedRound H X d) :
    W.result.matching = X.matching ∪ W.originalSelection := rfl

@[simp] theorem RegularizedProjectedRound.result_keep
    {X : OriginalIterationState H} {d : ℕ}
    (W : RegularizedProjectedRound H X d) :
    W.result.keep = W.originalKeep := rfl

/-! ## Empty-fibre-aware rounds -/

/-- Jobs whose current kept fibre is nonempty. -/
def activeJobs (X : OriginalIterationState H) : Finset Job :=
  Finset.univ.filter fun j ↦ (X.system.fiber j).Nonempty

@[simp] theorem mem_activeJobs (X : OriginalIterationState H) (j : Job) :
    j ∈ X.activeJobs ↔ (X.system.fiber j).Nonempty := by
  simp [activeJobs]

/-- Current system after deleting its empty job fibres from the job type. -/
def activeSystem (X : OriginalIterationState H) :=
  X.system.inducedOnJobs X.activeJobs

/-- A projected round after restricting to current nonempty jobs and then
trimming each of their fibres to exact degree `d`. -/
structure ActiveRegularizedProjectedRound
    (X : OriginalIterationState H) (d : ℕ) where
  trim : Finset (X.system.ActiveJobOption X.activeJobs)
  trim_jobDegree_eq : ∀ j,
    ((((X.activeSystem).inducedOnOptions trim).fiber j).card) = d
  selected : Finset (KeptOption trim)
  next : Finset (KeptOption trim)
  selected_isPartial :
    ((X.activeSystem).inducedOnOptions trim).IsPartialMatching selected
  next_subset_residual :
    next ⊆ ((X.activeSystem).inducedOnOptions trim).residualOptions selected

/-- Every current nonempty fibre can be trimmed to `d`; empty fibres do not
enter the active job type. -/
theorem exists_activeRegularizingTrim
    (X : OriginalIterationState H) (d : ℕ)
    (hdegree : ∀ j, (X.system.fiber j).Nonempty →
      d ≤ (X.system.fiber j).card) :
    ∃ trim : Finset (X.system.ActiveJobOption X.activeJobs),
      ∀ j, ((((X.activeSystem).inducedOnOptions trim).fiber j).card) = d := by
  have hactive : ∀ j : ActiveJob X.activeJobs,
      d ≤ (X.activeSystem.fiber j).card := by
    intro j
    change d ≤ ((X.system.inducedOnJobs X.activeJobs).fiber j).card
    rw [X.system.inducedOnJobs_fiber_card X.activeJobs j]
    exact hdegree j.1 ((X.mem_activeJobs j.1).mp j.2)
  rcases X.activeSystem.exists_jobRegularizedSystem d hactive with
    ⟨trim, htrim, _hslot, _hjobSlot, _hslotPair⟩
  exact ⟨trim, htrim⟩

/-- Package a regular-extension matching on the active, trimmed system. -/
def ActiveRegularizedProjectedRound.ofRegularExtension
    {X : OriginalIterationState H} {d : ℕ}
    (trim : Finset (X.system.ActiveJobOption X.activeJobs))
    (htrim : ∀ j,
      ((((X.activeSystem).inducedOnOptions trim).fiber j).card) = d)
    {Job' : Type u'} {Slot' : Type v'} {Option' : Type w'}
    [Fintype Job'] [Fintype Slot'] [Fintype Option']
    [DecidableEq Job'] [DecidableEq Slot'] [DecidableEq Option']
    {H' : RankThreeOptionSystem Job' Slot' Option'} {S lambda : ℕ}
    (E : IsRegularExtension
      ((X.activeSystem).inducedOnOptions trim) H' d S lambda)
    (M : Finset Option') (hM : H'.IsPartialMatching M) :
    ActiveRegularizedProjectedRound (H := H) X d where
  trim := trim
  trim_jobDegree_eq := htrim
  selected := E.originalSelection M
  next := E.originalResidual M
  selected_isPartial := E.originalSelection_isPartialMatching M hM
  next_subset_residual := E.originalResidual_subset_residualOptions M

/-- Forget both the trim and active-job subtype proofs. -/
def ActiveRegularizedProjectedRound.currentSelection
    {X : OriginalIterationState H} {d : ℕ}
    (W : ActiveRegularizedProjectedRound (H := H) X d) :
    Finset (KeptOption X.keep) :=
  X.system.liftActiveKeptOptionSet X.activeJobs W.trim W.selected

/-- Forget both subtype layers on the projected residual. -/
def ActiveRegularizedProjectedRound.currentKeep
    {X : OriginalIterationState H} {d : ℕ}
    (W : ActiveRegularizedProjectedRound (H := H) X d) :
    Finset (KeptOption X.keep) :=
  X.system.liftActiveKeptOptionSet X.activeJobs W.trim W.next

def ActiveRegularizedProjectedRound.originalSelection
    {X : OriginalIterationState H} {d : ℕ}
    (W : ActiveRegularizedProjectedRound (H := H) X d) : Finset Option :=
  H.liftKeptOptionSet X.keep W.currentSelection

def ActiveRegularizedProjectedRound.originalKeep
    {X : OriginalIterationState H} {d : ℕ}
    (W : ActiveRegularizedProjectedRound (H := H) X d) : Finset Option :=
  H.liftKeptOptionSet X.keep W.currentKeep

theorem ActiveRegularizedProjectedRound.currentSelection_isPartial
    {X : OriginalIterationState H} {d : ℕ}
    (W : ActiveRegularizedProjectedRound (H := H) X d) :
    X.system.IsPartialMatching W.currentSelection := by
  exact X.system.liftActiveKeptOptionSet_isPartialMatching
    X.activeJobs W.trim W.selected_isPartial

theorem ActiveRegularizedProjectedRound.currentKeep_subset_residual
    {X : OriginalIterationState H} {d : ℕ}
    (W : ActiveRegularizedProjectedRound (H := H) X d) :
    W.currentKeep ⊆ X.system.residualOptions W.currentSelection := by
  have htrim : W.trim ⊆ X.activeSystem.residualOptions ∅ := by
    intro q hq
    simp only [mem_residualOptions]
    intro p hp
    simp at hp
  have hinner := X.activeSystem.liftKeptOptionSet_residual_subset htrim
    W.selected W.next W.next_subset_residual
  have hactive :
      X.activeSystem.liftKeptOptionSet W.trim W.next ⊆
        X.activeSystem.residualOptions
          (X.activeSystem.liftKeptOptionSet W.trim W.selected) := by
    simpa using hinner
  have hlift := X.system.liftActiveJobSet_residual_subset X.activeJobs
    (X.activeSystem.liftKeptOptionSet W.trim W.selected)
    (X.activeSystem.liftKeptOptionSet W.trim W.next) hactive
  simpa [ActiveRegularizedProjectedRound.currentSelection,
    ActiveRegularizedProjectedRound.currentKeep,
    liftActiveKeptOptionSet] using hlift

/-- Advance the original-type state through the empty-fibre-aware round. -/
def ActiveRegularizedProjectedRound.result
    {X : OriginalIterationState H} {d : ℕ}
    (W : ActiveRegularizedProjectedRound (H := H) X d) : OriginalIterationState H where
  matching := X.matching ∪ W.originalSelection
  keep := W.originalKeep
  matching_isPartial :=
    X.matching_isPartial.union_liftKeptOptionSet_of_subset_residual H
      X.keep_subset_residual W.currentSelection_isPartial
  keep_subset_residual :=
    H.liftKeptOptionSet_residual_subset X.keep_subset_residual
      W.currentSelection W.currentKeep W.currentKeep_subset_residual

@[simp] theorem ActiveRegularizedProjectedRound.result_matching
    {X : OriginalIterationState H} {d : ℕ}
    (W : ActiveRegularizedProjectedRound (H := H) X d) :
    W.result.matching = X.matching ∪ W.originalSelection := rfl

@[simp] theorem ActiveRegularizedProjectedRound.result_keep
    {X : OriginalIterationState H} {d : ℕ}
    (W : ActiveRegularizedProjectedRound (H := H) X d) :
    W.result.keep = W.originalKeep := rfl

/-- The fully lifted next state has exactly the local projected slot degree. -/
theorem ActiveRegularizedProjectedRound.originalKeep_slotDegree
    {X : OriginalIterationState H} {d : ℕ}
    (W : ActiveRegularizedProjectedRound (H := H) X d) (s : Slot) :
    (H.inducedOnOptions W.originalKeep).slotDegree s =
      (((X.activeSystem).inducedOnOptions W.trim).inducedOnOptions
        W.next).slotDegree s := by
  rw [ActiveRegularizedProjectedRound.originalKeep,
    H.inducedOnOptions_liftKeptOptionSet_slotDegree]
  change (X.system.inducedOnOptions W.currentKeep).slotDegree s = _
  rw [ActiveRegularizedProjectedRound.currentKeep,
    liftActiveKeptOptionSet,
    X.system.inducedOnOptions_liftActiveJobSet_slotDegree]
  change
    (X.activeSystem.inducedOnOptions
      (X.activeSystem.liftKeptOptionSet W.trim W.next)).slotDegree s = _
  rw [X.activeSystem.inducedOnOptions_liftKeptOptionSet_slotDegree]

/-- The fully lifted next state has exactly the local projected fibre size at
every active job. -/
theorem ActiveRegularizedProjectedRound.originalKeep_fiber_card
    {X : OriginalIterationState H} {d : ℕ}
    (W : ActiveRegularizedProjectedRound (H := H) X d)
    (j : ActiveJob X.activeJobs) :
    ((H.inducedOnOptions W.originalKeep).fiber j.1).card =
      ((((X.activeSystem).inducedOnOptions W.trim).inducedOnOptions
        W.next).fiber j).card := by
  rw [ActiveRegularizedProjectedRound.originalKeep,
    H.inducedOnOptions_liftKeptOptionSet_fiber_card]
  change ((X.system.inducedOnOptions W.currentKeep).fiber j.1).card = _
  rw [ActiveRegularizedProjectedRound.currentKeep,
    liftActiveKeptOptionSet,
    X.system.inducedOnOptions_liftActiveJobSet_fiber_card]
  change
    ((X.activeSystem.inducedOnOptions
      (X.activeSystem.liftKeptOptionSet W.trim W.next)).fiber j).card = _
  rw [X.activeSystem.inducedOnOptions_liftKeptOptionSet_fiber_card]

/-- A round witness gives one transition of original-type states. -/
def QualitativeRegularizedStep
    (degree : ℕ → OriginalIterationState H → ℕ)
    (Good : ∀ n X,
      RegularizedProjectedRound H X (degree n X) → Prop)
    (n : ℕ) (X Y : OriginalIterationState H) : Prop :=
  ∃ W : RegularizedProjectedRound H X (degree n X),
    Good n X W ∧ Y = W.result

/-- Exactly `n` successive transitions, indexed from zero. -/
inductive Iterates
    (Step : ℕ → OriginalIterationState H → OriginalIterationState H → Prop) :
    ℕ → OriginalIterationState H → OriginalIterationState H → Prop
  | zero (X) : Iterates Step 0 X X
  | succ {n X Y Z} : Iterates Step n X Y → Step n Y Z →
      Iterates Step (n + 1) X Z

/-- Generic finite induction driven by qualitative projected rounds.  Every
intermediate object is an `OriginalIterationState`, so partial matching and
the residual inclusion are preserved without appearing again as induction
hypotheses. -/
theorem exists_iterates_qualitativeRegularizedStep
    (degree : ℕ → OriginalIterationState H → ℕ)
    (Good : ∀ n X,
      RegularizedProjectedRound H X (degree n X) → Prop)
    (hround : ∀ n X,
      ∃ W : RegularizedProjectedRound H X (degree n X), Good n X W)
    (initial : OriginalIterationState H) :
    ∀ steps, ∃ final,
      Iterates (QualitativeRegularizedStep degree Good) steps initial final := by
  intro steps
  induction steps with
  | zero =>
      exact ⟨initial, Iterates.zero initial⟩
  | succ n ih =>
      rcases ih with ⟨current, hreach⟩
      rcases hround n current with ⟨W, hgood⟩
      refine ⟨W.result, Iterates.succ hreach ?_⟩
      exact ⟨W, hgood, rfl⟩

/-- Empty-fibre-aware qualitative transition. -/
def QualitativeActiveRegularizedStep
    (degree : ℕ → OriginalIterationState H → ℕ)
    (Good : ∀ n X,
      ActiveRegularizedProjectedRound (H := H) X (degree n X) → Prop)
    (n : ℕ) (X Y : OriginalIterationState H) : Prop :=
  ∃ W : ActiveRegularizedProjectedRound (H := H) X (degree n X),
    Good n X W ∧ Y = W.result

/-- Finite induction for the active-job version used after the first round. -/
theorem exists_iterates_qualitativeActiveRegularizedStep
    (degree : ℕ → OriginalIterationState H → ℕ)
    (Good : ∀ n X,
      ActiveRegularizedProjectedRound (H := H) X (degree n X) → Prop)
    (hround : ∀ n X,
      ∃ W : ActiveRegularizedProjectedRound (H := H) X (degree n X), Good n X W)
    (initial : OriginalIterationState H) :
    ∀ steps, ∃ final,
      Iterates (QualitativeActiveRegularizedStep degree Good)
        steps initial final := by
  intro steps
  induction steps with
  | zero =>
      exact ⟨initial, Iterates.zero initial⟩
  | succ n ih =>
      rcases ih with ⟨current, hreach⟩
      rcases hround n current with ⟨W, hgood⟩
      refine ⟨W.result, Iterates.succ hreach ?_⟩
      exact ⟨W, hgood, rfl⟩

end OriginalIterationState

end WeightedEdgeColoring.RankThreeOptionSystem
