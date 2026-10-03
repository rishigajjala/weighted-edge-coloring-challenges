import WeightedEdgeColoring.RankThreeDirectNibbleHarris
import WeightedEdgeColoring.RankThreeMixedBernoulliLLL
import WeightedEdgeColoring.RankThreeGroupLLL

/-!
# Concrete residual rows for the sharp Harris nibble

This file connects the abstract lower and upper rows of the direct Harris
nibble to a rank-three option system.  Conflicts are the canonical ordered
conflicting pairs.  A lower row is a group of jobs and counts options whose
owner belongs to that group.  The upper rows are the normalized job and slot
deletion loads from `RankThreeMixedBernoulliLLL`.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

/-! ## Canonical conflicts -/

/-- First coordinate of a canonical ordered conflicting pair. -/
def canonicalConflictLeft (c : H.ConflictIndex) : Option := c.1.1

/-- Second coordinate of a canonical ordered conflicting pair. -/
def canonicalConflictRight (c : H.ConflictIndex) : Option := c.1.2

theorem canonicalConflict_ne (c : H.ConflictIndex) :
    H.canonicalConflictLeft c ≠ H.canonicalConflictRight c :=
  c.2.1

theorem canonicalConflict_complete (o p : Option) (hop : o ≠ p)
    (hbad : H.owner o = H.owner p ∨ ¬ H.Compatible o p) :
    ∃ c : H.ConflictIndex,
      (H.canonicalConflictLeft c = o ∧ H.canonicalConflictRight c = p) ∨
        (H.canonicalConflictLeft c = p ∧ H.canonicalConflictRight c = o) := by
  exact ⟨⟨(o, p), hop, hbad⟩, Or.inl ⟨rfl, rfl⟩⟩

/-! ## Job-group coverage rows -/

/-- A group row assigns coefficient one to precisely the options whose owner
belongs to the prescribed group of jobs. -/
def jobGroupCoverageWeight (members : Group → Finset Job) :
    Group → Option → ℝ :=
  fun g o ↦ if H.owner o ∈ members g then 1 else 0

theorem jobGroupCoverageWeight_nonneg (members : Group → Finset Job) :
    ∀ g o, 0 ≤ H.jobGroupCoverageWeight members g o := by
  intro g o
  unfold jobGroupCoverageWeight
  split <;> norm_num

theorem jobGroupCoverageWeight_le_one (members : Group → Finset Job) :
    ∀ g o, H.jobGroupCoverageWeight members g o ≤ 1 := by
  intro g o
  unfold jobGroupCoverageWeight
  split <;> norm_num

/-- The support of a job-group row is the union of the fibres of its jobs. -/
theorem linearRowSupport_jobGroupCoverageWeight
    (members : Group → Finset Job) (g : Group) :
    linearRowSupport (H.jobGroupCoverageWeight members) g =
      (members g).biUnion H.fiber := by
  classical
  ext o
  simp [linearRowSupport, jobGroupCoverageWeight, H.mem_fiber]

/-- A group of at most `K` jobs has coverage support at most `K*D` when all
job fibres have size at most `D`. -/
theorem jobGroupCoverage_support_card_le
    (members : Group → Finset Job) (K D : ℕ)
    (hmembers : ∀ g, (members g).card ≤ K)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D) (g : Group) :
    (linearRowSupport (H.jobGroupCoverageWeight members) g).card ≤ K * D := by
  rw [H.linearRowSupport_jobGroupCoverageWeight members g]
  calc
    ((members g).biUnion H.fiber).card ≤
        ∑ j ∈ members g, (H.fiber j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ members g, D :=
      Finset.sum_le_sum fun j _ ↦ hjobDegree j
    _ = (members g).card * D := by simp
    _ ≤ K * D := Nat.mul_le_mul_right D (hmembers g)

/-- The lower rows containing an option are exactly the groups containing
its owner. -/
theorem linearRowIncidence_jobGroupCoverageWeight
    (members : Group → Finset Job) (o : Option) :
    linearRowIncidence (H.jobGroupCoverageWeight members) o =
      Finset.univ.filter (fun g ↦ H.owner o ∈ members g) := by
  classical
  ext g
  simp [linearRowIncidence, linearRowSupport, jobGroupCoverageWeight]

theorem jobGroupCoverage_incidence_card_le
    (members : Group → Finset Job) (R : ℕ)
    (hincidence : ∀ j,
      ((Finset.univ : Finset Group).filter (fun g ↦ j ∈ members g)).card ≤ R)
    (o : Option) :
    (linearRowIncidence (H.jobGroupCoverageWeight members) o).card ≤ R := by
  rw [H.linearRowIncidence_jobGroupCoverageWeight members o]
  exact hincidence (H.owner o)

/-- Exact mean of a job-group row. -/
theorem linearRowMean_jobGroupCoverageWeight
    (q : Option → ℝ) (members : Group → Finset Job) (g : Group) :
    linearRowMean q (H.jobGroupCoverageWeight members) g =
      ∑ o ∈ linearRowSupport (H.jobGroupCoverageWeight members) g, q o := by
  classical
  rw [linearRowMean]
  unfold mean
  simp only [WeightedEdgeColoring.FiniteBernoulliSupportSplit.insideParameter]
  have hone : ∀ o : Inside
      (linearRowSupport (H.jobGroupCoverageWeight members) g),
      H.jobGroupCoverageWeight members g o = 1 := by
    intro o
    have ho := o.2
    simp [linearRowSupport, jobGroupCoverageWeight] at ho ⊢
    exact ho
  simp_rw [hone, mul_one]
  rw [Finset.sum_subtype
    (linearRowSupport (H.jobGroupCoverageWeight members) g)]
  intro o
  simp

/-- Under a uniform retention probability, a row mean is probability times
its support size. -/
theorem linearRowMean_jobGroupCoverageWeight_uniform
    (rho : ℝ) (members : Group → Finset Job) (g : Group) :
    linearRowMean (fun _ : Option ↦ rho)
        (H.jobGroupCoverageWeight members) g =
      rho * ((linearRowSupport
        (H.jobGroupCoverageWeight members) g).card : ℝ) := by
  rw [H.linearRowMean_jobGroupCoverageWeight]
  simp [mul_comm]

/-! ## Conflict incidence -/

/-- Options using one slot. -/
def slotOptionFiber (s : Slot) : Finset Option :=
  Finset.univ.filter fun o ↦ s ∈ H.slots o

@[simp] theorem mem_slotOptionFiber {s : Slot} {o : Option} :
    o ∈ H.slotOptionFiber s ↔ s ∈ H.slots o := by
  simp [slotOptionFiber]

theorem slotOptionFiber_card (s : Slot) :
    (H.slotOptionFiber s).card = H.slotDegree s := rfl

/-- Every competitor of `o` lies either in its owner fibre or in the fibre
of one of its at most two slots. -/
theorem conflictNeighbors_subset_owner_union_slots (o : Option) :
    H.conflictNeighbors o ⊆
      H.fiber (H.owner o) ∪ (H.slots o).biUnion H.slotOptionFiber := by
  intro p hp
  rcases H.mem_conflictNeighbors.mp hp with ⟨_hpo, hbad⟩
  rcases hbad with howner | hincompat
  · exact Finset.mem_union_left _ (H.mem_fiber.mpr howner)
  · apply Finset.mem_union_right
    unfold Compatible at hincompat
    rw [Finset.not_disjoint_iff] at hincompat
    rcases hincompat with ⟨s, hso, hsp⟩
    exact Finset.mem_biUnion.mpr ⟨s, hso, H.mem_slotOptionFiber.mpr hsp⟩

theorem conflictNeighbors_card_le_three_mul
    (D : ℕ) (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) (o : Option) :
    (H.conflictNeighbors o).card ≤ 3 * D := by
  calc
    (H.conflictNeighbors o).card ≤
        (H.fiber (H.owner o) ∪
          (H.slots o).biUnion H.slotOptionFiber).card :=
      Finset.card_le_card (H.conflictNeighbors_subset_owner_union_slots o)
    _ ≤ (H.fiber (H.owner o)).card +
        ((H.slots o).biUnion H.slotOptionFiber).card :=
      Finset.card_union_le _ _
    _ ≤ (H.fiber (H.owner o)).card +
        ∑ s ∈ H.slots o, (H.slotOptionFiber s).card := by
      gcongr
      exact Finset.card_biUnion_le
    _ ≤ D + ∑ _s ∈ H.slots o, D := by
      gcongr with s hs
      · exact hjobDegree (H.owner o)
      · rw [H.slotOptionFiber_card]
        exact hslotDegree s
    _ = D + (H.slots o).card * D := by simp
    _ ≤ D + 2 * D := by
      gcongr
      exact H.slots_card_le_two o
    _ = 3 * D := by omega

private def canonicalLeftIncidence (o : Option) : Finset H.ConflictIndex :=
  Finset.univ.filter fun c ↦ o = H.canonicalConflictLeft c

private def canonicalRightIncidence (o : Option) : Finset H.ConflictIndex :=
  Finset.univ.filter fun c ↦ o = H.canonicalConflictRight c

private theorem canonicalLeftIncidence_card_le (o : Option) :
    (H.canonicalLeftIncidence o).card ≤ (H.conflictNeighbors o).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun c ↦ H.canonicalConflictRight c)
  · intro c hc
    have hco : o = H.canonicalConflictLeft c :=
      (Finset.mem_filter.mp hc).2
    apply H.mem_conflictNeighbors.mpr
    constructor
    · intro hright
      apply c.2.1
      exact hco.symm.trans hright.symm
    · rcases c.2.2 with howner | hincompat
      · left
        exact howner.symm.trans (congrArg H.owner hco).symm
      · right
        change ¬ H.Compatible o c.1.2
        rw [hco]
        exact hincompat
  · intro c hc d hd hright
    apply Subtype.ext
    apply Prod.ext
    · have hc' : o = H.canonicalConflictLeft c :=
        (Finset.mem_filter.mp hc).2
      have hd' : o = H.canonicalConflictLeft d :=
        (Finset.mem_filter.mp hd).2
      exact hc'.symm.trans hd'
    · exact hright

private theorem canonicalRightIncidence_card_le (o : Option) :
    (H.canonicalRightIncidence o).card ≤ (H.conflictNeighbors o).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun c ↦ H.canonicalConflictLeft c)
  · intro c hc
    have hco : o = H.canonicalConflictRight c :=
      (Finset.mem_filter.mp hc).2
    apply H.mem_conflictNeighbors.mpr
    constructor
    · intro hleft
      exact c.2.1 (hleft.trans hco)
    · rcases c.2.2 with howner | hincompat
      · left
        exact howner.trans (congrArg H.owner hco).symm
      · right
        intro hcompat
        apply hincompat
        have hsymmetric : H.Compatible (H.canonicalConflictLeft c) o :=
          H.compatible_symm.mp hcompat
        change H.Compatible c.1.1 c.1.2
        change o = c.1.2 at hco
        change H.Compatible c.1.1 o at hsymmetric
        rw [← hco]
        exact hsymmetric
  · intro c hc d hd hleft
    apply Subtype.ext
    apply Prod.ext
    · exact hleft
    · have hc' : o = H.canonicalConflictRight c :=
        (Finset.mem_filter.mp hc).2
      have hd' : o = H.canonicalConflictRight d :=
        (Finset.mem_filter.mp hd).2
      exact hc'.symm.trans hd'

/-- Each unordered competitor contributes at most the two orientations to
the canonical ordered conflict list. -/
theorem canonicalConflict_incidence_card_le_two_mul (o : Option) :
    (optionConflictIncidence H.canonicalConflictLeft
      H.canonicalConflictRight o).card ≤
      2 * (H.conflictNeighbors o).card := by
  classical
  have hsub : optionConflictIncidence H.canonicalConflictLeft
      H.canonicalConflictRight o ⊆
      H.canonicalLeftIncidence o ∪ H.canonicalRightIncidence o := by
    intro c hc
    rcases (Finset.mem_filter.mp hc).2 with hc | hc
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  calc
    (optionConflictIncidence H.canonicalConflictLeft
      H.canonicalConflictRight o).card ≤
        (H.canonicalLeftIncidence o ∪ H.canonicalRightIncidence o).card :=
      Finset.card_le_card hsub
    _ ≤ (H.canonicalLeftIncidence o).card +
        (H.canonicalRightIncidence o).card := Finset.card_union_le _ _
    _ ≤ (H.conflictNeighbors o).card + (H.conflictNeighbors o).card :=
      Nat.add_le_add (H.canonicalLeftIncidence_card_le o)
        (H.canonicalRightIncidence_card_le o)
    _ = 2 * (H.conflictNeighbors o).card := by omega

theorem canonicalConflict_incidence_card_le_six_mul
    (D : ℕ) (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) (o : Option) :
    (optionConflictIncidence H.canonicalConflictLeft
      H.canonicalConflictRight o).card ≤ 6 * D := by
  calc
    _ ≤ 2 * (H.conflictNeighbors o).card :=
      H.canonicalConflict_incidence_card_le_two_mul o
    _ ≤ 2 * (3 * D) :=
      Nat.mul_le_mul_left 2
        (H.conflictNeighbors_card_le_three_mul D hjobDegree hslotDegree o)
    _ = 6 * D := by omega

/-! ## Incidence of normalized residual-deletion rows -/

/-- All options meeting at least one slot of `p`. -/
def optionsMeeting (p : Option) : Finset Option :=
  (H.slots p).biUnion H.slotOptionFiber

/-- All slots used by an option in `A`. -/
def slotsUsedBy (A : Finset Option) : Finset Slot :=
  A.biUnion H.slots

/-- An explicit cover of all normalized residual-deletion rows in which `p`
has a nonzero coefficient. -/
def residualDeleteRowCover (p : Option) : Finset (ResidualDeleteRow Job Slot) :=
  (H.optionsMeeting p).image (fun o ↦ Sum.inl (H.owner o)) ∪
    ((H.slotsUsedBy (H.fiber (H.owner p)) ∪
      H.slotsUsedBy (H.optionsMeeting p)).image Sum.inr)

theorem optionsMeeting_card_le_two_mul
    (D : ℕ) (hslotDegree : ∀ s, H.slotDegree s ≤ D) (p : Option) :
    (H.optionsMeeting p).card ≤ 2 * D := by
  calc
    (H.optionsMeeting p).card ≤
        ∑ s ∈ H.slots p, (H.slotOptionFiber s).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ H.slots p, D := by
      exact Finset.sum_le_sum fun s _ ↦ by
        rw [H.slotOptionFiber_card]
        exact hslotDegree s
    _ = (H.slots p).card * D := by simp
    _ ≤ 2 * D := Nat.mul_le_mul_right D (H.slots_card_le_two p)

theorem slotsUsedBy_card_le_two_mul (A : Finset Option) :
    (H.slotsUsedBy A).card ≤ 2 * A.card := by
  calc
    (H.slotsUsedBy A).card ≤ ∑ o ∈ A, (H.slots o).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _o ∈ A, 2 :=
      Finset.sum_le_sum fun o _ ↦ H.slots_card_le_two o
    _ = 2 * A.card := by simp [mul_comm]

theorem residualDeleteWeight_mem_cover
    (lambda : ℕ) (p : Option) (r : ResidualDeleteRow Job Slot)
    (hweight : H.residualDeleteWeight lambda r p ≠ 0) :
    r ∈ H.residualDeleteRowCover p := by
  classical
  rcases r with j | s
  · have hnonempty : (H.externalBlockedBy j p).Nonempty := by
      rw [← Finset.card_ne_zero]
      intro hzero
      apply hweight
      simp [residualDeleteWeight, hzero]
    rcases hnonempty with ⟨o, ho⟩
    by_cases hpj : H.owner p = j
    · simp [externalBlockedBy, hpj] at ho
    · have hblocked : o ∈ H.blockedBy j p := by
        simpa [externalBlockedBy, hpj] using ho
      have hoData := H.mem_blockedBy.mp hblocked
      unfold Compatible at hoData
      rw [Finset.not_disjoint_iff] at hoData
      rcases hoData.2 with ⟨t, hot, hpt⟩
      have homeet : o ∈ H.optionsMeeting p :=
        Finset.mem_biUnion.mpr ⟨t, hpt, H.mem_slotOptionFiber.mpr hot⟩
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨o, homeet, by simp [hoData.1]⟩
  · by_cases hsp : s ∈ H.slots p
    · simp [residualDeleteWeight, hsp] at hweight
    · have hnonempty : (H.slotBlockedBy s p).Nonempty := by
        rw [← Finset.card_ne_zero]
        intro hzero
        apply hweight
        simp [residualDeleteWeight, hsp, hzero]
      rcases hnonempty with ⟨o, ho⟩
      have hoData := Finset.mem_filter.mp ho
      have hos : s ∈ H.slots o := (Finset.mem_filter.mp hoData.1).2
      have hslot : s ∈ H.slotsUsedBy (H.fiber (H.owner p)) ∪
          H.slotsUsedBy (H.optionsMeeting p) := by
        rcases hoData.2 with howner | hincompat
        · apply Finset.mem_union_left
          exact Finset.mem_biUnion.mpr
            ⟨o, H.mem_fiber.mpr howner, hos⟩
        · apply Finset.mem_union_right
          unfold Compatible at hincompat
          rw [Finset.not_disjoint_iff] at hincompat
          rcases hincompat with ⟨t, hot, hpt⟩
          have homeet : o ∈ H.optionsMeeting p :=
            Finset.mem_biUnion.mpr
              ⟨t, hpt, H.mem_slotOptionFiber.mpr hot⟩
          exact Finset.mem_biUnion.mpr ⟨o, homeet, hos⟩
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨s, hslot, rfl⟩

theorem linearRowIncidence_residualDeleteWeight_subset
    (lambda : ℕ) (p : Option) :
    linearRowIncidence (H.residualDeleteWeight lambda) p ⊆
      H.residualDeleteRowCover p := by
  intro r hr
  have hsupport := (Finset.mem_filter.mp hr).2
  have hweight : H.residualDeleteWeight lambda r p ≠ 0 :=
    (Finset.mem_filter.mp hsupport).2
  exact H.residualDeleteWeight_mem_cover lambda p r hweight

/-- If job and slot degrees are at most `D`, one option occurs in at most
`8D` residual-deletion rows: `2D` job rows and `6D` slot rows. -/
theorem residualDeleteRowCover_card_le_eight_mul
    (D : ℕ) (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) (p : Option) :
    (H.residualDeleteRowCover p).card ≤ 8 * D := by
  let A := H.optionsMeeting p
  let B := H.slotsUsedBy (H.fiber (H.owner p))
  let C := H.slotsUsedBy A
  have hA : A.card ≤ 2 * D :=
    H.optionsMeeting_card_le_two_mul D hslotDegree p
  have hB : B.card ≤ 2 * D := by
    calc
      B.card ≤ 2 * (H.fiber (H.owner p)).card :=
        H.slotsUsedBy_card_le_two_mul (H.fiber (H.owner p))
      _ ≤ 2 * D := Nat.mul_le_mul_left 2 (hjobDegree (H.owner p))
  have hC : C.card ≤ 4 * D := by
    calc
      C.card ≤ 2 * A.card := H.slotsUsedBy_card_le_two_mul A
      _ ≤ 2 * (2 * D) := Nat.mul_le_mul_left 2 hA
      _ = 4 * D := by omega
  change ((A.image (fun o ↦ Sum.inl (H.owner o))) ∪
    ((B ∪ C).image Sum.inr)).card ≤ 8 * D
  calc
    ((A.image (fun o ↦ Sum.inl (H.owner o))) ∪
        ((B ∪ C).image Sum.inr)).card ≤
        (A.image (fun o ↦ Sum.inl (H.owner o))).card +
          ((B ∪ C).image Sum.inr).card := Finset.card_union_le _ _
    _ ≤ A.card + (B ∪ C).card :=
      Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ ≤ A.card + (B.card + C.card) := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ (2 * D) + ((2 * D) + (4 * D)) := by omega
    _ = 8 * D := by omega

theorem residualDeleteWeight_incidence_card_le_eight_mul
    (lambda D : ℕ) (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) (p : Option) :
    (linearRowIncidence (H.residualDeleteWeight lambda) p).card ≤ 8 * D := by
  exact (Finset.card_le_card
    (H.linearRowIncidence_residualDeleteWeight_subset lambda p)).trans
      (H.residualDeleteRowCover_card_le_eight_mul D
        hjobDegree hslotDegree p)

/-! ## Support sizes and row means -/

/-- Possible selected options that externally block some option of job `j`. -/
def externalJobRowCover (j : Job) : Finset Option :=
  (H.fiber j).biUnion H.optionsMeeting

/-- Possible selected options that can contribute to the deletion row of
slot `s`. -/
def slotDeleteRowCover (s : Slot) : Finset Option :=
  (H.slotOptionFiber s).biUnion fun o ↦
    H.fiber (H.owner o) ∪ H.optionsMeeting o

theorem residualDeleteWeight_job_support_subset
    (lambda : ℕ) (j : Job) :
    linearRowSupport (H.residualDeleteWeight lambda) (Sum.inl j) ⊆
      H.externalJobRowCover j := by
  intro p hp
  have hweight : H.residualDeleteWeight lambda (Sum.inl j) p ≠ 0 :=
    (Finset.mem_filter.mp hp).2
  have hnonempty : (H.externalBlockedBy j p).Nonempty := by
    rw [← Finset.card_ne_zero]
    intro hzero
    apply hweight
    simp [residualDeleteWeight, hzero]
  rcases hnonempty with ⟨o, ho⟩
  by_cases hpj : H.owner p = j
  · simp [externalBlockedBy, hpj] at ho
  · have hblocked : o ∈ H.blockedBy j p := by
      simpa [externalBlockedBy, hpj] using ho
    have hoData := H.mem_blockedBy.mp hblocked
    unfold Compatible at hoData
    rw [Finset.not_disjoint_iff] at hoData
    rcases hoData.2 with ⟨s, hos, hps⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨o, H.mem_fiber.mpr hoData.1, ?_⟩
    exact Finset.mem_biUnion.mpr
      ⟨s, hos, H.mem_slotOptionFiber.mpr hps⟩

theorem residualDeleteWeight_slot_support_subset
    (lambda : ℕ) (s : Slot) :
    linearRowSupport (H.residualDeleteWeight lambda) (Sum.inr s) ⊆
      H.slotDeleteRowCover s := by
  intro p hp
  have hweight : H.residualDeleteWeight lambda (Sum.inr s) p ≠ 0 :=
    (Finset.mem_filter.mp hp).2
  by_cases hsp : s ∈ H.slots p
  · simp [residualDeleteWeight, hsp] at hweight
  · have hnonempty : (H.slotBlockedBy s p).Nonempty := by
      rw [← Finset.card_ne_zero]
      intro hzero
      apply hweight
      simp [residualDeleteWeight, hsp, hzero]
    rcases hnonempty with ⟨o, ho⟩
    have hoData := Finset.mem_filter.mp ho
    have hos : s ∈ H.slots o := (Finset.mem_filter.mp hoData.1).2
    apply Finset.mem_biUnion.mpr
    refine ⟨o, H.mem_slotOptionFiber.mpr hos, ?_⟩
    rcases hoData.2 with howner | hincompat
    · exact Finset.mem_union_left _ (H.mem_fiber.mpr howner.symm)
    · apply Finset.mem_union_right
      unfold Compatible at hincompat
      rw [Finset.not_disjoint_iff] at hincompat
      rcases hincompat with ⟨t, hot, hpt⟩
      exact Finset.mem_biUnion.mpr
        ⟨t, hot, H.mem_slotOptionFiber.mpr hpt⟩

theorem externalJobRowCover_card_le_two_mul_sq
    (D : ℕ) (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) (j : Job) :
    (H.externalJobRowCover j).card ≤ 2 * D * D := by
  calc
    (H.externalJobRowCover j).card ≤
        ∑ o ∈ H.fiber j, (H.optionsMeeting o).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _o ∈ H.fiber j, 2 * D :=
      Finset.sum_le_sum fun o _ ↦
        H.optionsMeeting_card_le_two_mul D hslotDegree o
    _ = (H.fiber j).card * (2 * D) := by simp
    _ ≤ D * (2 * D) :=
      Nat.mul_le_mul_right (2 * D) (hjobDegree j)
    _ = 2 * D * D := by ring

theorem slotDeleteRowCover_card_le_three_mul_sq
    (D : ℕ) (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) (s : Slot) :
    (H.slotDeleteRowCover s).card ≤ 3 * D * D := by
  calc
    (H.slotDeleteRowCover s).card ≤
        ∑ o ∈ H.slotOptionFiber s,
          (H.fiber (H.owner o) ∪ H.optionsMeeting o).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ o ∈ H.slotOptionFiber s,
        ((H.fiber (H.owner o)).card + (H.optionsMeeting o).card) := by
      exact Finset.sum_le_sum fun o _ ↦ Finset.card_union_le _ _
    _ ≤ ∑ _o ∈ H.slotOptionFiber s, (D + 2 * D) := by
      apply Finset.sum_le_sum
      intro o _
      exact Nat.add_le_add (hjobDegree (H.owner o))
        (H.optionsMeeting_card_le_two_mul D hslotDegree o)
    _ = (H.slotOptionFiber s).card * (D + 2 * D) := by simp
    _ ≤ D * (D + 2 * D) := by
      apply Nat.mul_le_mul_right
      rw [H.slotOptionFiber_card]
      exact hslotDegree s
    _ = 3 * D * D := by ring

/-- Every normalized residual deletion row has support at most `3D²`. -/
theorem residualDeleteWeight_support_card_le_three_mul_sq
    (lambda D : ℕ) (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) :
    ∀ r : ResidualDeleteRow Job Slot,
      (linearRowSupport (H.residualDeleteWeight lambda) r).card ≤
        3 * D * D := by
  intro r
  rcases r with j | s
  · calc
      _ ≤ (H.externalJobRowCover j).card := Finset.card_le_card
        (H.residualDeleteWeight_job_support_subset lambda j)
      _ ≤ 2 * D * D :=
        H.externalJobRowCover_card_le_two_mul_sq D
          hjobDegree hslotDegree j
      _ ≤ 3 * D * D := by
        exact Nat.mul_le_mul_right D (by omega)
  · exact (Finset.card_le_card
      (H.residualDeleteWeight_slot_support_subset lambda s)).trans
        (H.slotDeleteRowCover_card_le_three_mul_sq D
          hjobDegree hslotDegree s)

/-- A generic row with coefficients in `[0,1]` and coordinate probabilities
at most `rho` has mean at most `rho` times its support size. -/
theorem linearRowMean_le_rho_mul_support_card
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    (q : Option → ℝ) (a : Row → Option → ℝ) (rho : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hqrho : ∀ o, q o ≤ rho)
    (ha0 : ∀ r o, 0 ≤ a r o) (ha1 : ∀ r o, a r o ≤ 1)
    (r : Row) :
    linearRowMean q a r ≤ rho * ((linearRowSupport a r).card : ℝ) := by
  rw [linearRowMean]
  unfold mean
  calc
    (∑ o : Inside (linearRowSupport a r),
        insideParameter q (linearRowSupport a r) o * a r o) ≤
        ∑ _o : Inside (linearRowSupport a r), rho := by
      apply Finset.sum_le_sum
      intro o _
      calc
        q o * a r o ≤ q o * 1 :=
          mul_le_mul_of_nonneg_left (ha1 r o) (hq0 o)
        _ = q o := by ring
        _ ≤ rho := hqrho o
    _ = rho * ((linearRowSupport a r).card : ℝ) := by
      simp [mul_comm]

theorem residualDeleteWeight_mean_le
    (q : Option → ℝ) (rho : ℝ) (lambda D : ℕ)
    (hq0 : ∀ o, 0 ≤ q o) (hqrho : ∀ o, q o ≤ rho)
    (hlambda : 0 < lambda)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hrho0 : 0 ≤ rho) (r : ResidualDeleteRow Job Slot) :
    linearRowMean q (H.residualDeleteWeight lambda) r ≤
      rho * (3 * D * D : ℕ) := by
  calc
    linearRowMean q (H.residualDeleteWeight lambda) r ≤
        rho * ((linearRowSupport
          (H.residualDeleteWeight lambda) r).card : ℝ) :=
      linearRowMean_le_rho_mul_support_card q
        (H.residualDeleteWeight lambda) rho hq0 hqrho
        (H.residualDeleteWeight_nonneg lambda)
        (H.residualDeleteWeight_le_one lambda hlambda hjobSlot hslotPair) r
    _ ≤ rho * (3 * D * D : ℕ) := by
      apply mul_le_mul_of_nonneg_left _ hrho0
      exact_mod_cast H.residualDeleteWeight_support_card_le_three_mul_sq
        lambda D hjobDegree hslotDegree r

/-- Lower bound on a job-group mean from a coordinatewise lower bound on
the retention probabilities. -/
theorem rho_mul_support_card_le_jobGroupCoverage_mean
    (q : Option → ℝ) (rho : ℝ) (members : Group → Finset Job)
    (hqrho : ∀ o, rho ≤ q o) (g : Group) :
    rho * ((linearRowSupport
      (H.jobGroupCoverageWeight members) g).card : ℝ) ≤
      linearRowMean q (H.jobGroupCoverageWeight members) g := by
  rw [H.linearRowMean_jobGroupCoverageWeight]
  calc
    rho * ((linearRowSupport
        (H.jobGroupCoverageWeight members) g).card : ℝ) =
        ∑ _o ∈ linearRowSupport
          (H.jobGroupCoverageWeight members) g, rho := by
      simp [mul_comm]
    _ ≤ ∑ o ∈ linearRowSupport
        (H.jobGroupCoverageWeight members) g, q o :=
      Finset.sum_le_sum fun o _ ↦ hqrho o

theorem weightedSum_linearRowSupport
    {Row : Type*} [Fintype Row] [DecidableEq Row]
    (a : Row → Option → ℝ) (r : Row) (S : Finset Option) :
    weightedSum (fun o : Inside (linearRowSupport a r) ↦ a r o)
        (splitEquiv (linearRowSupport a r) S).1 =
      ∑ o ∈ S, a r o := by
  rw [weightedSum_splitEquiv_inside]
  unfold linearRowSupport
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro o _ho
  by_cases hz : a r o = 0 <;> simp [hz]

/-! ## One concrete Harris round -/

/-- One sharp-Harris nibble round for the canonical conflicts, job-group
coverage rows, and normalized residual job/slot deletion rows.  All
incidence hypotheses of the abstract theorem are discharged by the rank-three
degree bounds; only the explicit numerical tail inequalities remain.
-/
theorem exists_oneRound_residual_harris
    (q : Option → ℝ) (members : Group → Finset Job)
    (lambda : ℕ) (hlambda : 0 < lambda)
    (jobBudget : Job → ℕ) (slotBudget : Slot → ℕ)
    (upperLambda : ResidualDeleteRow Job Slot → ℝ)
    (D R : ℕ) (pairX rowX cap delta eta : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (hdelta0 : 0 ≤ delta)
    (hcoefficient :
      delta * (1 - delta) + (Real.exp (-delta) - 1) ≤ 0)
    (heta : ∀ g,
      eta ≤ linearRowMean q (H.jobGroupCoverageWeight members) g)
    (hupperLambda : ∀ r, 0 ≤ upperLambda r)
    (hpairX0 : 0 ≤ pairX) (hrowX0 : 0 ≤ rowX)
    (hpairXcap : pairX ≤ cap) (hrowXcap : rowX ≤ cap)
    (hcap1 : cap < 1)
    (hpair : ∀ c : H.ConflictIndex,
      q (H.canonicalConflictLeft c) * q (H.canonicalConflictRight c) ≤
        pairX * (1 - rowX) ^ (2 * R))
    (hlowerNumeric : ∀ g,
      Real.exp
        ((delta * (1 - delta) + (Real.exp (-delta) - 1)) * eta) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport
            (H.jobGroupCoverageWeight members) g).card *
              (6 * D + 8 * D)))
    (hupperNumeric : ∀ r,
      Real.exp (-upperLambda r *
          residualDeleteThreshold lambda jobBudget slotBudget r +
        (Real.exp (upperLambda r) - 1) *
          linearRowMean q (H.residualDeleteWeight lambda) r) ≤
        rowX * (1 - rowX) ^
          ((linearRowSupport
            (H.residualDeleteWeight lambda) r).card * R)) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ g, (1 - delta) *
          linearRowMean q (H.jobGroupCoverageWeight members) g <
        ∑ o ∈ S, H.jobGroupCoverageWeight members g o) ∧
      (∀ j, ¬ H.Covers S j →
        H.residualJobDegree ∅ j ≤ H.residualJobDegree S j + jobBudget j) ∧
      (∀ s, (∀ p ∈ S, s ∉ H.slots p) →
        H.residualSlotDegree ∅ s ≤
          H.residualSlotDegree S s + slotBudget s) := by
  rcases H.exists_partialMatching_with_coarse_coverage_harris
      H.canonicalConflictLeft H.canonicalConflictRight q
      (H.jobGroupCoverageWeight members)
      (H.residualDeleteWeight lambda)
      (residualDeleteThreshold lambda jobBudget slotBudget) upperLambda
      H.canonicalConflict_ne H.canonicalConflict_complete
      (6 * D) R (8 * D) pairX rowX cap delta eta
      hq0 hq1
      (H.jobGroupCoverageWeight_nonneg members)
      (H.jobGroupCoverageWeight_le_one members)
      (H.residualDeleteWeight_nonneg lambda)
      (H.residualDeleteWeight_le_one lambda hlambda hjobSlot hslotPair)
      hdelta0 hcoefficient heta hupperLambda
      hpairX0 hrowX0 hpairXcap hrowXcap hcap1
      (H.canonicalConflict_incidence_card_le_six_mul
        D hjobDegree hslotDegree)
      (H.jobGroupCoverage_incidence_card_le members R hgroupIncidence)
      (H.residualDeleteWeight_incidence_card_le_eight_mul
        lambda D hjobDegree hslotDegree)
      hpair hlowerNumeric hupperNumeric with
    ⟨S, hmatching, hcoverage, hdeletion⟩
  refine ⟨S, hmatching, ?_, ?_, ?_⟩
  · intro g
    rw [← weightedSum_linearRowSupport
      (H.jobGroupCoverageWeight members) g S]
    exact hcoverage g
  · intro j huncovered
    have hnorm := hdeletion (Sum.inl j)
    rw [weightedSum_linearRowSupport
      (H.residualDeleteWeight lambda) (Sum.inl j) S] at hnorm
    rw [H.selected_residualDeleteWeight_job lambda S j] at hnorm
    have hden : (0 : ℝ) < (2 * lambda : ℕ) := by positivity
    have hcast : (H.externalJobDeletionLoad S j : ℝ) < jobBudget j := by
      apply (div_lt_div_iff_of_pos_right hden).mp
      simpa [residualDeleteThreshold] using hnorm
    have hload : H.externalJobDeletionLoad S j < jobBudget j := by
      exact_mod_cast hcast
    have hremoved :=
      H.removedResidualFiber_empty_card_le_externalJobDeletionLoad
        S j huncovered
    have hidentity := H.residualJobDegree_union_add_removed ∅ S j
    simp only [Finset.empty_union] at hidentity
    omega
  · intro s hunused
    have hnorm := hdeletion (Sum.inr s)
    rw [weightedSum_linearRowSupport
      (H.residualDeleteWeight lambda) (Sum.inr s) S] at hnorm
    rw [H.selected_residualDeleteWeight_slot lambda S s hunused] at hnorm
    have hden : (0 : ℝ) < (3 * lambda : ℕ) := by positivity
    have hcast : (H.slotDeletionLoad S s : ℝ) < slotBudget s := by
      apply (div_lt_div_iff_of_pos_right hden).mp
      simpa [residualDeleteThreshold] using hnorm
    have hload : H.slotDeletionLoad S s < slotBudget s := by
      exact_mod_cast hcast
    have hremoved :=
      H.removedResidualSlot_empty_card_le_slotDeletionLoad S s hunused
    have hidentity := H.residualSlotDegree_union_add_removed ∅ S s
    simp only [Finset.empty_union] at hidentity
    omega

/-- Uniform-retention form of `exists_oneRound_residual_harris`.  Lower
groups have support between `m` and `K*D`; every residual-deletion row has
support at most `3D²` and mean at most `rho * 3D²`.  The hypotheses below
are therefore scalar sufficient inequalities, independent of the row.
-/
theorem exists_oneRound_residual_harris_uniform
    (rho : ℝ) (members : Group → Finset Job)
    (lambda : ℕ) (hlambda : 0 < lambda)
    (jobBudget : Job → ℕ) (slotBudget : Slot → ℕ)
    (upperLambda : ResidualDeleteRow Job Slot → ℝ)
    (D R K m : ℕ) (pairX rowX cap delta : ℝ)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hmembers : ∀ g, (members g).card ≤ K)
    (hgroupSupportLower : ∀ g,
      m ≤ (linearRowSupport
        (H.jobGroupCoverageWeight members) g).card)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (hdelta0 : 0 ≤ delta)
    (hcoefficient :
      delta * (1 - delta) + (Real.exp (-delta) - 1) ≤ 0)
    (hupperLambda : ∀ r, 0 ≤ upperLambda r)
    (hpairX0 : 0 ≤ pairX) (hrowX0 : 0 ≤ rowX)
    (hpairXcap : pairX ≤ cap) (hrowXcap : rowX ≤ cap)
    (hcap1 : cap < 1)
    (hpairNumeric : rho * rho ≤
      pairX * (1 - rowX) ^ (2 * R))
    (hlowerNumeric :
      Real.exp
        ((delta * (1 - delta) + (Real.exp (-delta) - 1)) *
          (rho * (m : ℝ))) ≤
        rowX * (1 - cap) ^ ((K * D) * (14 * D)))
    (hupperNumeric : ∀ r,
      Real.exp (-upperLambda r *
          residualDeleteThreshold lambda jobBudget slotBudget r +
        (Real.exp (upperLambda r) - 1) *
          (rho * (3 * D * D : ℕ))) ≤
        rowX * (1 - rowX) ^ ((3 * D * D) * R)) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ g, (1 - delta) *
          linearRowMean (fun _ : Option ↦ rho)
            (H.jobGroupCoverageWeight members) g <
        ∑ o ∈ S, H.jobGroupCoverageWeight members g o) ∧
      (∀ j, ¬ H.Covers S j →
        H.residualJobDegree ∅ j ≤ H.residualJobDegree S j + jobBudget j) ∧
      (∀ s, (∀ p ∈ S, s ∉ H.slots p) →
        H.residualSlotDegree ∅ s ≤
          H.residualSlotDegree S s + slotBudget s) := by
  have hcap0 : 0 ≤ cap := hpairX0.trans hpairXcap
  have hrowX1 : rowX ≤ 1 := hrowXcap.trans hcap1.le
  apply H.exists_oneRound_residual_harris
    (fun _ : Option ↦ rho) members lambda hlambda jobBudget slotBudget
    upperLambda D R pairX rowX cap delta (rho * (m : ℝ))
    (fun _ ↦ hrho0) (fun _ ↦ hrho1)
    hjobDegree hslotDegree hjobSlot hslotPair hgroupIncidence
    hdelta0 hcoefficient
  · intro g
    rw [H.linearRowMean_jobGroupCoverageWeight_uniform]
    apply mul_le_mul_of_nonneg_left _ hrho0
    exact_mod_cast hgroupSupportLower g
  · exact hupperLambda
  · exact hpairX0
  · exact hrowX0
  · exact hpairXcap
  · exact hrowXcap
  · exact hcap1
  · intro c
    exact hpairNumeric
  · intro g
    apply hlowerNumeric.trans
    apply mul_le_mul_of_nonneg_left _ hrowX0
    apply pow_le_pow_of_le_one (sub_nonneg.mpr hcap1.le)
      (sub_le_self 1 hcap0)
    have hs := H.jobGroupCoverage_support_card_le members K D
      hmembers hjobDegree g
    calc
      (linearRowSupport
          (H.jobGroupCoverageWeight members) g).card *
          (6 * D + 8 * D) ≤
        (K * D) * (6 * D + 8 * D) :=
          Nat.mul_le_mul_right (6 * D + 8 * D) hs
      _ = (K * D) * (14 * D) := by ring
  · intro r
    have hmean : linearRowMean (fun _ : Option ↦ rho)
        (H.residualDeleteWeight lambda) r ≤
        rho * (3 * D * D : ℕ) :=
      H.residualDeleteWeight_mean_le (fun _ : Option ↦ rho) rho
        lambda D (fun _ ↦ hrho0) (fun _ ↦ le_rfl) hlambda
        hjobDegree hslotDegree hjobSlot hslotPair hrho0 r
    have hcoef : 0 ≤ Real.exp (upperLambda r) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (hupperLambda r))
    have htail :
        Real.exp (-upperLambda r *
            residualDeleteThreshold lambda jobBudget slotBudget r +
          (Real.exp (upperLambda r) - 1) *
            linearRowMean (fun _ : Option ↦ rho)
              (H.residualDeleteWeight lambda) r) ≤
          Real.exp (-upperLambda r *
            residualDeleteThreshold lambda jobBudget slotBudget r +
          (Real.exp (upperLambda r) - 1) *
            (rho * (3 * D * D : ℕ))) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hmean hcoef
      linarith
    apply htail.trans
    apply (hupperNumeric r).trans
    apply mul_le_mul_of_nonneg_left _ hrowX0
    apply pow_le_pow_of_le_one (sub_nonneg.mpr hrowX1)
      (sub_le_self 1 hrowX0)
    exact Nat.mul_le_mul_right R
      (H.residualDeleteWeight_support_card_le_three_mul_sq
        lambda D hjobDegree hslotDegree r)

end WeightedEdgeColoring.RankThreeOptionSystem
