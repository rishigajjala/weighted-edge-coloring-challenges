import WeightedEdgeColoring.RankThreeIteration

namespace WeightedEdgeColoring

universe u v w

namespace RankThreeOptionSystem

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-!
# Expansion outside a reached slot set

Low slot-pair codegree has two useful consequences.  First, among two-slot
options touching `T`, all but at most `choose(|T|,2) * lambda` cross the
boundary of `T`.  A large boundary family must use many distinct outside
slots.  Second, if many two-slot options avoid `T` entirely, their outside
slot support must itself contain enough pairs to hold them.

The final theorem combines near-regular job fibres, a slot-degree upper
bound, and pair-codegree.  It gives a genuine support-expansion inequality,
while also exposing why this elementary count does not alone prove the
fixed-slack matching theorem: its right side is quadratic in the new support.
-/

/-- Options with two slots that touch `T`. -/
def twoSlotTouchingOptions (T : Finset Slot) : Finset Option :=
  Finset.univ.filter fun o ↦
    (H.slots o).card = 2 ∧ (H.slots o ∩ T).Nonempty

/-- Every two-slot option touching `T` is either internal to `T` or crosses
from `T` to its complement. -/
theorem twoSlotTouchingOptions_subset_internal_union_boundary
    (T : Finset Slot) :
    H.twoSlotTouchingOptions T ⊆
      H.optionsUsingTwoOf T ∪ H.boundaryOptions T := by
  intro o ho
  have hdata := (Finset.mem_filter.mp ho).2
  by_cases hout : (H.slots o \ T).Nonempty
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ o, hdata.2, hout⟩
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ o, ?_⟩
    have hsubset : H.slots o ⊆ T := by
      intro s hs
      by_contra hsT
      exact hout ⟨s, Finset.mem_sdiff.mpr ⟨hs, hsT⟩⟩
    have hinter : H.slots o ∩ T = H.slots o :=
      Finset.inter_eq_left.mpr hsubset
    rw [hinter, hdata.1]

/-- Leaving-set lower bound.  In any subfamily of two-slot options touching
`T`, all but the binomial internal-pair allowance must cross the boundary. -/
theorem card_sub_choose_mul_le_boundary_part
    {F : Finset Option} (T : Finset Slot) (lambda : ℕ)
    (hF : F ⊆ H.twoSlotTouchingOptions T)
    (hpair : ∀ s ∈ T, ∀ t ∈ T, s ≠ t →
      H.slotPairCodegree s t ≤ lambda) :
    F.card - Nat.choose T.card 2 * lambda ≤
      (F ∩ H.boundaryOptions T).card := by
  let A : Finset Option := F ∩ H.optionsUsingTwoOf T
  let B : Finset Option := F ∩ H.boundaryOptions T
  have hsub : F ⊆ A ∪ B := by
    intro o ho
    have hcases := H.twoSlotTouchingOptions_subset_internal_union_boundary
      T (hF ho)
    rcases Finset.mem_union.mp hcases with hin | hbd
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ho, hin⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ho, hbd⟩)
  have hFcard : F.card ≤ A.card + B.card := by
    calc
      F.card ≤ (A ∪ B).card := Finset.card_le_card hsub
      _ ≤ A.card + B.card := Finset.card_union_le A B
  have hA : A.card ≤ Nat.choose T.card 2 * lambda := by
    apply H.card_le_choose_mul_of_subset_optionsUsingTwoOf T lambda
    · intro o ho
      exact (Finset.mem_inter.mp ho).2
    · exact hpair
  change F.card - Nat.choose T.card 2 * lambda ≤ B.card
  omega

/-- Slots outside `T` actually used by a family `F`. -/
def outsideSlotSupport (F : Finset Option) (T : Finset Slot) : Finset Slot :=
  H.slotSupport F \ T

/-- A boundary family is covered by the pair families between `T` and its
actual outside support. -/
theorem boundaryFamily_subset_actual_pairUnion
    {F : Finset Option} (T : Finset Slot)
    (hF : F ⊆ H.boundaryOptions T) :
    F ⊆ T.biUnion fun s ↦
      (H.outsideSlotSupport F T).biUnion fun t ↦
        H.optionsUsingPair s t := by
  intro o ho
  have hboundary := (Finset.mem_filter.mp (hF ho)).2
  obtain ⟨s, hsinter⟩ := hboundary.1
  obtain ⟨t, htdiff⟩ := hboundary.2
  have hs := Finset.mem_inter.mp hsinter
  have ht := Finset.mem_sdiff.mp htdiff
  have htSupport : t ∈ H.slotSupport F := by
    apply Finset.mem_biUnion.mpr
    exact ⟨o, ho, ht.1⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨s, hs.2, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨t, Finset.mem_sdiff.mpr ⟨htSupport, ht.2⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ o, hs.1, ht.1⟩

/-- A boundary family can use at most `|T| * |U| * lambda` options when `U`
is its actual outside slot support. -/
theorem card_boundaryFamily_le_actual_support_mul
    {F : Finset Option} (T : Finset Slot) (lambda : ℕ)
    (hF : F ⊆ H.boundaryOptions T)
    (hpair : ∀ s ∈ T, ∀ t ∈ H.outsideSlotSupport F T,
      H.slotPairCodegree s t ≤ lambda) :
    F.card ≤ T.card * (H.outsideSlotSupport F T).card * lambda := by
  let U := H.outsideSlotSupport F T
  have hinner : ∀ s ∈ T,
      (U.biUnion fun t ↦ H.optionsUsingPair s t).card ≤
        U.card * lambda := by
    intro s hs
    calc
      (U.biUnion fun t ↦ H.optionsUsingPair s t).card ≤
          ∑ t ∈ U, (H.optionsUsingPair s t).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ U, lambda := by
        exact Finset.sum_le_sum fun t ht ↦ hpair s hs t ht
      _ = U.card * lambda := by simp
  calc
    F.card ≤ (T.biUnion fun s ↦
        U.biUnion fun t ↦ H.optionsUsingPair s t).card := by
      apply Finset.card_le_card
      simpa [U] using H.boundaryFamily_subset_actual_pairUnion T hF
    _ ≤ ∑ s ∈ T,
        (U.biUnion fun t ↦ H.optionsUsingPair s t).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ T, U.card * lambda :=
      Finset.sum_le_sum hinner
    _ = T.card * U.card * lambda := by simp [Nat.mul_assoc]
    _ = T.card * (H.outsideSlotSupport F T).card * lambda := rfl

/-- Division form: many boundary options force many actually used outside
slots. -/
theorem card_boundaryFamily_div_le_outsideSupport
    {F : Finset Option} (T : Finset Slot) (lambda : ℕ)
    (hF : F ⊆ H.boundaryOptions T)
    (hpair : ∀ s ∈ T, ∀ t ∈ H.outsideSlotSupport F T,
      H.slotPairCodegree s t ≤ lambda) :
    F.card / (T.card * lambda) ≤
      (H.outsideSlotSupport F T).card := by
  apply Nat.div_le_of_le_mul
  have h := H.card_boundaryFamily_le_actual_support_mul
    T lambda hF hpair
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- Combined boundary expansion: after paying for all internal pairs of
`T`, the remaining two-slot touching options force new outside slots. -/
theorem card_sub_choose_mul_div_le_outsideSupport
    {F : Finset Option} (T : Finset Slot) (lambda : ℕ)
    (hF : F ⊆ H.twoSlotTouchingOptions T)
    (hpair : ∀ s t : Slot, s ≠ t →
      H.slotPairCodegree s t ≤ lambda) :
    (F.card - Nat.choose T.card 2 * lambda) /
        (T.card * lambda) ≤
      (H.outsideSlotSupport (F ∩ H.boundaryOptions T) T).card := by
  let B : Finset Option := F ∩ H.boundaryOptions T
  have hleave : F.card - Nat.choose T.card 2 * lambda ≤ B.card :=
    H.card_sub_choose_mul_le_boundary_part T lambda hF
      (fun s hs t ht hst ↦ hpair s t hst)
  have hdiv :
      (F.card - Nat.choose T.card 2 * lambda) /
          (T.card * lambda) ≤ B.card / (T.card * lambda) :=
    Nat.div_le_div_right hleave
  have hBsub : B ⊆ H.boundaryOptions T := by
    intro o ho
    exact (Finset.mem_inter.mp ho).2
  have hBout := H.card_boundaryFamily_div_le_outsideSupport
    T lambda hBsub (fun s hs t ht ↦ by
      have htout : t ∉ T := (Finset.mem_sdiff.mp ht).2
      exact hpair s t (fun hst ↦ htout (hst ▸ hs)))
  exact hdiv.trans hBout

/-! ## Near-regular families and slot-degree expansion -/

/-- All options whose owner belongs to `J`. -/
def optionsOfJobs (J : Finset Job) : Finset Option :=
  J.biUnion H.fiber

/-- Different owner fibres are disjoint. -/
theorem fiber_pairwiseDisjoint (J : Finset Job) :
    (J : Set Job).PairwiseDisjoint H.fiber := by
  intro j _hj k _hk hjk
  change Disjoint (H.fiber j) (H.fiber k)
  rw [Finset.disjoint_left]
  intro o hoj hok
  apply hjk
  exact (H.mem_fiber.mp hoj).symm.trans (H.mem_fiber.mp hok)

/-- Exact count of the options owned by a job set. -/
theorem card_optionsOfJobs (J : Finset Job) :
    (H.optionsOfJobs J).card = ∑ j ∈ J, (H.fiber j).card := by
  unfold optionsOfJobs
  exact Finset.card_biUnion (H.fiber_pairwiseDisjoint J)

/-- Near-regular job fibres give the expected lower count. -/
theorem card_mul_le_optionsOfJobs
    (J : Finset Job) (m : ℕ)
    (hdegree : ∀ j ∈ J, m ≤ (H.fiber j).card) :
    J.card * m ≤ (H.optionsOfJobs J).card := by
  rw [H.card_optionsOfJobs J]
  calc
    J.card * m = ∑ _j ∈ J, m := by simp
    _ ≤ ∑ j ∈ J, (H.fiber j).card :=
      Finset.sum_le_sum hdegree

/-- Options touching at least one slot of `T`. -/
def optionsTouchingSlots (T : Finset Slot) : Finset Option :=
  Finset.univ.filter fun o ↦ (H.slots o ∩ T).Nonempty

/-- Touching options are covered by the one-slot incidence families. -/
theorem optionsTouchingSlots_subset_slotUnion (T : Finset Slot) :
    H.optionsTouchingSlots T ⊆
      T.biUnion fun s ↦
        (Finset.univ : Finset Option).filter fun o ↦ s ∈ H.slots o := by
  intro o ho
  obtain ⟨s, hs⟩ := (Finset.mem_filter.mp ho).2
  have hs' := Finset.mem_inter.mp hs
  apply Finset.mem_biUnion.mpr
  exact ⟨s, hs'.2, Finset.mem_filter.mpr ⟨Finset.mem_univ o, hs'.1⟩⟩

/-- A slot-degree upper bound limits how many options can touch `T`. -/
theorem card_optionsTouchingSlots_le
    (T : Finset Slot) (D : ℕ)
    (hslot : ∀ s ∈ T, H.slotDegree s ≤ D) :
    (H.optionsTouchingSlots T).card ≤ T.card * D := by
  calc
    (H.optionsTouchingSlots T).card ≤
        (T.biUnion fun s ↦
          (Finset.univ : Finset Option).filter fun o ↦
            s ∈ H.slots o).card :=
      Finset.card_le_card (H.optionsTouchingSlots_subset_slotUnion T)
    _ ≤ ∑ s ∈ T,
        ((Finset.univ : Finset Option).filter fun o ↦
          s ∈ H.slots o).card := Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ T, D := by
      exact Finset.sum_le_sum hslot
    _ = T.card * D := by simp

/-- Options of `J` that avoid every slot of `T`. -/
def ownedOptionsAvoidingSlots (J : Finset Job) (T : Finset Slot) :
    Finset Option :=
  H.optionsOfJobs J \ H.optionsTouchingSlots T

/-- Near-regularity and a slot-degree cap force many options of `J` to avoid
`T` altogether. -/
theorem card_mul_sub_card_mul_le_ownedOptionsAvoidingSlots
    (J : Finset Job) (T : Finset Slot) (m D : ℕ)
    (hdegree : ∀ j ∈ J, m ≤ (H.fiber j).card)
    (hslot : ∀ s ∈ T, H.slotDegree s ≤ D) :
    J.card * m - T.card * D ≤
      (H.ownedOptionsAvoidingSlots J T).card := by
  have htotal := H.card_mul_le_optionsOfJobs J m hdegree
  have htouch := H.card_optionsTouchingSlots_le T D hslot
  have hsplit := Finset.card_sdiff_add_card_inter
    (H.optionsOfJobs J) (H.optionsTouchingSlots T)
  unfold ownedOptionsAvoidingSlots
  have hinter :
      (H.optionsOfJobs J ∩ H.optionsTouchingSlots T).card ≤
        (H.optionsTouchingSlots T).card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

/-- Avoiding two-slot options use two slots from their actual outside
support. -/
theorem ownedOptionsAvoidingSlots_subset_optionsUsingTwoOf
    (J : Finset Job) (T : Finset Slot)
    (htwo : ∀ o ∈ H.ownedOptionsAvoidingSlots J T,
      (H.slots o).card = 2) :
    H.ownedOptionsAvoidingSlots J T ⊆
      H.optionsUsingTwoOf
        (H.outsideSlotSupport (H.ownedOptionsAvoidingSlots J T) T) := by
  intro o ho
  have hoData := Finset.mem_sdiff.mp ho
  have hnotTouch : o ∉ H.optionsTouchingSlots T := hoData.2
  have hinterEmpty : H.slots o ∩ T = ∅ := by
    by_contra hne
    apply hnotTouch
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ o, Finset.nonempty_iff_ne_empty.mpr hne⟩
  have hslotsSupport : H.slots o ⊆
      H.slotSupport (H.ownedOptionsAvoidingSlots J T) := by
    intro s hs
    apply Finset.mem_biUnion.mpr
    exact ⟨o, ho, hs⟩
  have hslotsOutside : H.slots o ⊆
      H.outsideSlotSupport (H.ownedOptionsAvoidingSlots J T) T := by
    intro s hs
    apply Finset.mem_sdiff.mpr
    refine ⟨hslotsSupport hs, ?_⟩
    intro hsT
    have : s ∈ H.slots o ∩ T := Finset.mem_inter.mpr ⟨hs, hsT⟩
    rw [hinterEmpty] at this
    simp at this
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ o, ?_⟩
  have hinter : H.slots o ∩
      H.outsideSlotSupport (H.ownedOptionsAvoidingSlots J T) T =
        H.slots o := Finset.inter_eq_left.mpr hslotsOutside
  rw [hinter, htwo o ho]

/-- Avoiding options with fewer than two slots.  Pair-codegree gives no
control over this family, so it must be kept as an explicit error term in a
fully general support count. -/
def shortOwnedOptionsAvoidingSlots (J : Finset Job) (T : Finset Slot) :
    Finset Option :=
  (H.ownedOptionsAvoidingSlots J T).filter fun o ↦ (H.slots o).card < 2

/-- The two-slot part of the avoiding owned options. -/
def twoSlotOwnedOptionsAvoidingSlots (J : Finset Job) (T : Finset Slot) :
    Finset Option :=
  (H.ownedOptionsAvoidingSlots J T).filter fun o ↦ (H.slots o).card = 2

/-- Every avoiding option is either short or has exactly two slots. -/
theorem ownedOptionsAvoidingSlots_subset_short_union_twoSlot
    (J : Finset Job) (T : Finset Slot) :
    H.ownedOptionsAvoidingSlots J T ⊆
      H.shortOwnedOptionsAvoidingSlots J T ∪
        H.twoSlotOwnedOptionsAvoidingSlots J T := by
  intro o ho
  have hle := H.slots_card_le_two o
  by_cases hlt : (H.slots o).card < 2
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨ho, hlt⟩
  · have heq : (H.slots o).card = 2 := by omega
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨ho, heq⟩

/-- The two-slot avoiding part uses two slots from its own actual outside
support. -/
theorem twoSlotOwnedOptionsAvoidingSlots_subset_optionsUsingTwoOf
    (J : Finset Job) (T : Finset Slot) :
    H.twoSlotOwnedOptionsAvoidingSlots J T ⊆
      H.optionsUsingTwoOf
        (H.outsideSlotSupport
          (H.twoSlotOwnedOptionsAvoidingSlots J T) T) := by
  intro o ho
  have hoFilter := Finset.mem_filter.mp ho
  have hoAvoid := Finset.mem_sdiff.mp hoFilter.1
  have hnotTouch : o ∉ H.optionsTouchingSlots T := hoAvoid.2
  have hinterEmpty : H.slots o ∩ T = ∅ := by
    by_contra hne
    apply hnotTouch
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ o, Finset.nonempty_iff_ne_empty.mpr hne⟩
  have hslotsSupport : H.slots o ⊆
      H.slotSupport (H.twoSlotOwnedOptionsAvoidingSlots J T) := by
    intro s hs
    apply Finset.mem_biUnion.mpr
    exact ⟨o, ho, hs⟩
  have hslotsOutside : H.slots o ⊆
      H.outsideSlotSupport
        (H.twoSlotOwnedOptionsAvoidingSlots J T) T := by
    intro s hs
    apply Finset.mem_sdiff.mpr
    refine ⟨hslotsSupport hs, ?_⟩
    intro hsT
    have : s ∈ H.slots o ∩ T := Finset.mem_inter.mpr ⟨hs, hsT⟩
    rw [hinterEmpty] at this
    simp at this
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ o, ?_⟩
  have hinter : H.slots o ∩
      H.outsideSlotSupport
        (H.twoSlotOwnedOptionsAvoidingSlots J T) T = H.slots o :=
    Finset.inter_eq_left.mpr hslotsOutside
  rw [hinter, hoFilter.2]

/-- General near-regular support expansion with the exact short-option error
term.  Writing `S` for the avoiding options with zero or one slot and `U`
for the outside support of the avoiding two-slot options,

`|J|*m - |T|*D - |S| ≤ choose(|U|,2)*lambda`.

This identifies the sharp elementary obstruction: arbitrary singleton or
dummy copies are invisible to slot-pair codegree. -/
theorem nearRegular_avoiding_support_expansion_with_short_error
    (J : Finset Job) (T : Finset Slot) (m D lambda : ℕ)
    (hdegree : ∀ j ∈ J, m ≤ (H.fiber j).card)
    (hslot : ∀ s ∈ T, H.slotDegree s ≤ D)
    (hpair : ∀ s t : Slot, s ≠ t →
      H.slotPairCodegree s t ≤ lambda) :
    J.card * m - T.card * D -
        (H.shortOwnedOptionsAvoidingSlots J T).card ≤
      Nat.choose
        (H.outsideSlotSupport
          (H.twoSlotOwnedOptionsAvoidingSlots J T) T).card 2 * lambda := by
  let F := H.ownedOptionsAvoidingSlots J T
  let S := H.shortOwnedOptionsAvoidingSlots J T
  let L := H.twoSlotOwnedOptionsAvoidingSlots J T
  let U := H.outsideSlotSupport L T
  have hlower : J.card * m - T.card * D ≤ F.card :=
    H.card_mul_sub_card_mul_le_ownedOptionsAvoidingSlots
      J T m D hdegree hslot
  have hpartition : F.card ≤ S.card + L.card := by
    calc
      F.card ≤ (S ∪ L).card := by
        apply Finset.card_le_card
        simpa [F, S, L] using
          H.ownedOptionsAvoidingSlots_subset_short_union_twoSlot J T
      _ ≤ S.card + L.card := Finset.card_union_le S L
  have hLlower : J.card * m - T.card * D - S.card ≤ L.card := by
    omega
  have hLsub : L ⊆ H.optionsUsingTwoOf U := by
    simpa [L, U] using
      H.twoSlotOwnedOptionsAvoidingSlots_subset_optionsUsingTwoOf J T
  have hLupper : L.card ≤ Nat.choose U.card 2 * lambda :=
    H.card_le_choose_mul_of_subset_optionsUsingTwoOf U lambda hLsub
      (fun s hs t ht hst ↦ hpair s t hst)
  exact hLlower.trans hLupper

/-- Support-expansion inequality combining all three hypotheses used by the
fixed-slack matching layer.  Let `U` be the actual outside slot support of
the options of `J` avoiding `T`.  If those options all have two slots, then

`|J|*m - |T|*D ≤ choose(|U|,2)*lambda`.

Thus a positive deficit on the left forces new outside support.  The
quadratic binomial term is the exact elementary obstruction left before the
deeper nibble/local-lemma argument. -/
theorem nearRegular_avoiding_support_expansion
    (J : Finset Job) (T : Finset Slot) (m D lambda : ℕ)
    (hdegree : ∀ j ∈ J, m ≤ (H.fiber j).card)
    (hslot : ∀ s ∈ T, H.slotDegree s ≤ D)
    (hpair : ∀ s t : Slot, s ≠ t →
      H.slotPairCodegree s t ≤ lambda)
    (htwo : ∀ o ∈ H.ownedOptionsAvoidingSlots J T,
      (H.slots o).card = 2) :
    J.card * m - T.card * D ≤
      Nat.choose
        (H.outsideSlotSupport (H.ownedOptionsAvoidingSlots J T) T).card 2 *
          lambda := by
  let F := H.ownedOptionsAvoidingSlots J T
  let U := H.outsideSlotSupport F T
  have hlower : J.card * m - T.card * D ≤ F.card :=
    H.card_mul_sub_card_mul_le_ownedOptionsAvoidingSlots
      J T m D hdegree hslot
  have hsub : F ⊆ H.optionsUsingTwoOf U := by
    simpa [F, U] using
      H.ownedOptionsAvoidingSlots_subset_optionsUsingTwoOf J T htwo
  have hupper : F.card ≤ Nat.choose U.card 2 * lambda :=
    H.card_le_choose_mul_of_subset_optionsUsingTwoOf U lambda hsub
      (fun s hs t ht hst ↦ hpair s t hst)
  exact hlower.trans hupper

end RankThreeOptionSystem

end WeightedEdgeColoring
