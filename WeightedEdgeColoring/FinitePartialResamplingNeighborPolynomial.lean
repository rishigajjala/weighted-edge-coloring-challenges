import WeightedEdgeColoring.FinitePartialResamplingExponential

/-!
# The coarse partial-resampling neighbor polynomial

This file contains the finite algebra used by the coarse form of the
Harris--Srinivasan partial-resampling criterion.  A label consists of a row
and a partial categorical assignment.  Two labels conflict when they have
the same row or mention a common source.  Proper children of a root all
conflict with the root and are pairwise nonconflicting.

The main result bounds the sum of the monomials of all proper child sets by
one row factor and one factor for every source mentioned by the root.  The
last part substitutes the usual `lambda` charges into this bound.  There is
no probabilistic or existence assertion in this file.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- A witness label records a row and the partial assignment resampled in
that row. -/
abbrev Label (Source State Row : Type*) :=
  Row × PartialAssignment Source State

/-- The partial assignment mentions `i`. -/
def UsesSource (Y : PartialAssignment Source State) (i : Source) : Prop :=
  Y i ≠ none

instance usesSourceDecidable (Y : PartialAssignment Source State)
    (i : Source) : Decidable (UsesSource Y i) := by
  unfold UsesSource
  infer_instance

/-- A partial assignment mentions at least one source. -/
def NonemptyPartial (Y : PartialAssignment Source State) : Prop :=
  ∃ i, UsesSource Y i

instance nonemptyPartialDecidable (Y : PartialAssignment Source State) :
    Decidable (NonemptyPartial Y) := by
  unfold NonemptyPartial
  infer_instance

/-- Two partial assignments share a source, irrespective of the states they
place at that source. -/
def SharesSource (Y Z : PartialAssignment Source State) : Prop :=
  ∃ i, UsesSource Y i ∧ UsesSource Z i

instance sharesSourceDecidable (Y Z : PartialAssignment Source State) :
    Decidable (SharesSource Y Z) := by
  unfold SharesSource
  infer_instance

/-- The coarse conflict relation: equal rows or a common source. -/
def Conflict (a b : Label Source State Row) : Prop :=
  a.1 = b.1 ∨ SharesSource a.2 b.2

instance conflictDecidable (a b : Label Source State Row) :
    Decidable (Conflict a b) := by
  unfold Conflict
  infer_instance

theorem sharesSource_symm {Y Z : PartialAssignment Source State} :
    SharesSource Y Z ↔ SharesSource Z Y := by
  constructor
  · rintro ⟨i, hYi, hZi⟩
    exact ⟨i, hZi, hYi⟩
  · rintro ⟨i, hZi, hYi⟩
    exact ⟨i, hYi, hZi⟩

theorem conflict_symm {a b : Label Source State Row} :
    Conflict a b ↔ Conflict b a := by
  constructor
  · rintro (hrow | hsource)
    · exact Or.inl hrow.symm
    · exact Or.inr (sharesSource_symm.mp hsource)
  · rintro (hrow | hsource)
    · exact Or.inl hrow.symm
    · exact Or.inr (sharesSource_symm.mp hsource)

/-- A proper child set for `root`.  Every child is nonempty and conflicts
with the root, while distinct children do not conflict with each other. -/
def ProperChildren (root : Label Source State Row)
    (children : Finset (Label Source State Row)) : Prop :=
  (∀ child ∈ children,
      NonemptyPartial child.2 ∧ Conflict root child) ∧
  (∀ a ∈ children, ∀ b ∈ children, a ≠ b → ¬ Conflict a b)

noncomputable instance properChildrenDecidable (root : Label Source State Row)
    (children : Finset (Label Source State Row)) :
    Decidable (ProperChildren root children) :=
  Classical.propDecidable _

/-- All proper child finsets of one root. -/
noncomputable def properChildFinsets (root : Label Source State Row) :
    Finset (Finset (Label Source State Row)) :=
  Finset.univ.filter (ProperChildren root)

theorem mem_properChildFinsets_iff
    {root : Label Source State Row}
    {children : Finset (Label Source State Row)} :
    children ∈ properChildFinsets root ↔ ProperChildren root children := by
  classical
  simp [properChildFinsets]

/-- The monomial attached to a child finset. -/
def childMonomial (mu : Label Source State Row → ℝ)
    (children : Finset (Label Source State Row)) : ℝ :=
  ∏ child ∈ children, mu child

/-- The finite neighbor polynomial: the sum of the monomials of all proper
child finsets. -/
noncomputable def neighborPolynomial
    (mu : Label Source State Row → ℝ)
    (root : Label Source State Row) : ℝ :=
  ∑ children ∈ properChildFinsets root, childMonomial mu children

/-- Choose one element from a nonempty finite set and return `none` on the
empty set.  It is used only to encode a proper child set. -/
noncomputable def chooseOne {α : Type*} (s : Finset α) : Option α :=
  if h : s.Nonempty then some (Classical.choose h) else none

theorem chooseOne_mem {α : Type*} {s : Finset α} {a : α}
    (h : chooseOne s = some a) : a ∈ s := by
  classical
  unfold chooseOne at h
  split at h
  · rename_i hs
    have ha : Classical.choose hs = a := Option.some.inj h
    simpa [ha] using (Classical.choose_spec hs)
  · simp at h

theorem chooseOne_eq_some_of_mem_of_unique
    {α : Type*} {s : Finset α} {a : α}
    (ha : a ∈ s) (hunique : ∀ b ∈ s, b = a) :
    chooseOne s = some a := by
  classical
  unfold chooseOne
  split
  · rename_i hs
    congr 1
    exact hunique (Classical.choose hs) (Classical.choose_spec hs)
  · rename_i hs
    exact (hs ⟨a, ha⟩).elim

@[simp] theorem chooseOne_empty {α : Type*} :
    chooseOne (∅ : Finset α) = none := by
  simp [chooseOne]

/-- A non-row child is assigned to one source shared with its root.  The
fallback value is irrelevant for proper children, since every such child
either has the root row or shares a source with the root. -/
noncomputable def childBucket (root child : Label Source State Row) :
    Option Source :=
  if hrow : child.1 = root.1 then none
  else if hsource : SharesSource root.2 child.2 then
    some (Classical.choose hsource)
  else none

@[simp] theorem childBucket_of_sameRow
    {root child : Label Source State Row} (hrow : child.1 = root.1) :
    childBucket root child = none := by
  simp [childBucket, hrow]

theorem childBucket_eq_some_uses
    {root child : Label Source State Row} {i : Source}
    (hbucket : childBucket root child = some i) :
    UsesSource root.2 i ∧ UsesSource child.2 i := by
  classical
  unfold childBucket at hbucket
  split at hbucket
  · simp at hbucket
  · split at hbucket
    · rename_i hsource
      have hi : Classical.choose hsource = i := Option.some.inj hbucket
      simpa [hi] using Classical.choose_spec hsource
    · simp at hbucket

theorem childBucket_exists_of_conflict_of_ne_row
    {root child : Label Source State Row}
    (hconflict : Conflict root child) (hrow : child.1 ≠ root.1) :
    ∃ i, childBucket root child = some i := by
  classical
  have hsource : SharesSource root.2 child.2 := by
    rcases hconflict with hsame | hshared
    · exact (hrow hsame.symm).elim
    · exact hshared
  refine ⟨Classical.choose hsource, ?_⟩
  simp [childBucket, hrow, hsource]

theorem childBucket_injective_on_proper
    {root : Label Source State Row}
    {children : Finset (Label Source State Row)}
    (hproper : ProperChildren root children)
    {a b : Label Source State Row}
    (ha : a ∈ children) (hb : b ∈ children)
    (habucket : childBucket root a = childBucket root b) :
    a = b := by
  classical
  by_contra hab
  have hnconflict : ¬ Conflict a b := hproper.2 a ha b hb hab
  have haconflict : Conflict root a := (hproper.1 a ha).2
  have hbconflict : Conflict root b := (hproper.1 b hb).2
  by_cases harow : a.1 = root.1
  · have haBucket : childBucket root a = none :=
      childBucket_of_sameRow harow
    have hbBucket : childBucket root b = none := by
      rw [← habucket]
      exact haBucket
    have hbrow : b.1 = root.1 := by
      by_contra hbrow
      obtain ⟨i, hi⟩ :=
        childBucket_exists_of_conflict_of_ne_row hbconflict hbrow
      rw [hbBucket] at hi
      simp at hi
    apply hnconflict
    exact Or.inl (harow.trans hbrow.symm)
  · obtain ⟨i, hai⟩ :=
      childBucket_exists_of_conflict_of_ne_row haconflict harow
    have hbi : childBucket root b = some i := by
      rw [← habucket]
      exact hai
    have hauses := childBucket_eq_some_uses hai
    have hbuses := childBucket_eq_some_uses hbi
    apply hnconflict
    exact Or.inr ⟨i, hauses.2, hbuses.2⟩

/-- The fiber of a bucket inside a child finset. -/
noncomputable def bucketFiber
    (root : Label Source State Row)
    (children : Finset (Label Source State Row))
    (bucket : Option Source) : Finset (Label Source State Row) :=
  children.filter fun child ↦ childBucket root child = bucket

/-- An encoding has one optional label in the row bucket and one optional
label in every source bucket. -/
abbrev ChildEncoding (Source State Row : Type*) :=
  Option Source → Option (Label Source State Row)

/-- Encode a child set by choosing the unique child in each occupied bucket.
For non-proper finsets this is merely an arbitrary encoding. -/
noncomputable def encodeChildren
    (root : Label Source State Row)
    (children : Finset (Label Source State Row)) :
    ChildEncoding Source State Row :=
  fun bucket ↦ chooseOne (bucketFiber root children bucket)

theorem encodeChildren_at_child
    {root : Label Source State Row}
    {children : Finset (Label Source State Row)}
    (hproper : ProperChildren root children)
    {child : Label Source State Row} (hchild : child ∈ children) :
    encodeChildren root children (childBucket root child) = some child := by
  classical
  apply chooseOne_eq_some_of_mem_of_unique
  · simp [encodeChildren, bucketFiber, hchild]
  · intro other hother
    have hother' := Finset.mem_filter.mp hother
    exact childBucket_injective_on_proper hproper hother'.1 hchild hother'.2

theorem encodeChildren_injective_on_proper
    (root : Label Source State Row) :
    Set.InjOn (encodeChildren root)
      {children | ProperChildren root children} := by
  classical
  intro A hA B hB hencode
  apply Finset.ext
  intro child
  constructor
  · intro hchild
    have hAt := encodeChildren_at_child hA hchild
    have hBt : encodeChildren root B (childBucket root child) = some child := by
      rw [← hencode]
      exact hAt
    exact (Finset.mem_filter.mp (chooseOne_mem hBt)).1
  · intro hchild
    have hBt := encodeChildren_at_child hB hchild
    have hAt : encodeChildren root A (childBucket root child) = some child := by
      rw [hencode]
      exact hBt
    exact (Finset.mem_filter.mp (chooseOne_mem hAt)).1

/-- A slot accepts the root row in the `none` bucket, and accepts a label in
source bucket `i` when both the root and the label mention `i`. -/
def SlotAccepts (root : Label Source State Row) (bucket : Option Source)
    (child : Label Source State Row) : Prop :=
  match bucket with
  | none => child.1 = root.1
  | some i => UsesSource root.2 i ∧ UsesSource child.2 i

instance slotAcceptsDecidable (root : Label Source State Row)
    (bucket : Option Source) (child : Label Source State Row) :
    Decidable (SlotAccepts root bucket child) := by
  unfold SlotAccepts
  split <;> infer_instance

theorem slotAccepts_childBucket
    {root child : Label Source State Row}
    (hconflict : Conflict root child) :
    SlotAccepts root (childBucket root child) child := by
  classical
  by_cases hrow : child.1 = root.1
  · simp [childBucket, hrow, SlotAccepts]
  · obtain ⟨i, hi⟩ :=
      childBucket_exists_of_conflict_of_ne_row hconflict hrow
    have hiuses := childBucket_eq_some_uses hi
    rw [hi]
    exact hiuses

/-- Weight of one encoding slot.  Invalid choices have weight zero, which
makes the unrestricted encoding sum factor into the desired row and source
charges. -/
def slotWeight (root : Label Source State Row)
    (mu : Label Source State Row → ℝ)
    (bucket : Option Source) (choice : Option (Label Source State Row)) : ℝ :=
  match choice with
  | none => 1
  | some child => if SlotAccepts root bucket child then mu child else 0

/-- Product weight of an encoding. -/
def encodingWeight (root : Label Source State Row)
    (mu : Label Source State Row → ℝ)
    (encoding : ChildEncoding Source State Row) : ℝ :=
  ∏ bucket, slotWeight root mu bucket (encoding bucket)

theorem encodingWeight_nonneg
    (root : Label Source State Row)
    {mu : Label Source State Row → ℝ} (hmu : ∀ a, 0 ≤ mu a)
    (encoding : ChildEncoding Source State Row) :
    0 ≤ encodingWeight root mu encoding := by
  unfold encodingWeight
  apply Finset.prod_nonneg
  intro bucket _hbucket
  cases hchoice : encoding bucket with
  | none => simp [slotWeight, hchoice]
  | some child =>
      by_cases haccepts : SlotAccepts root bucket child
      · simp [slotWeight, hchoice, haccepts, hmu child]
      · simp [slotWeight, hchoice, haccepts]

theorem encodingWeight_encodeChildren
    {root : Label Source State Row}
    {children : Finset (Label Source State Row)}
    (hproper : ProperChildren root children)
    (mu : Label Source State Row → ℝ) :
    encodingWeight root mu (encodeChildren root children) =
      childMonomial mu children := by
  classical
  let occupied : Finset (Option Source) :=
    children.image (childBucket root)
  have hbucketInj : Set.InjOn (childBucket root) children := by
    intro a ha b hb hab
    exact childBucket_injective_on_proper hproper ha hb hab
  have houtside : ∀ bucket ∈ (Finset.univ : Finset (Option Source)),
      bucket ∉ occupied →
      slotWeight root mu bucket (encodeChildren root children bucket) = 1 := by
    intro bucket _hbucket hnot
    have hfiber : bucketFiber root children bucket = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro child hchild
      have hm := Finset.mem_filter.mp hchild
      apply hnot
      exact Finset.mem_image.mpr ⟨child, hm.1, hm.2⟩
    simp [encodeChildren, hfiber, slotWeight]
  have hrestrict :
      (∏ bucket ∈ occupied,
          slotWeight root mu bucket (encodeChildren root children bucket)) =
        encodingWeight root mu (encodeChildren root children) := by
    unfold encodingWeight
    apply Finset.prod_subset (Finset.subset_univ occupied)
    exact houtside
  rw [← hrestrict]
  rw [Finset.prod_image hbucketInj]
  unfold childMonomial
  apply Finset.prod_congr rfl
  intro child hchild
  rw [encodeChildren_at_child hproper hchild]
  simp [slotWeight, slotAccepts_childBucket (hproper.1 child hchild).2]

/-- Total `mu`-mass of labels from one row. -/
def rowMass (mu : Label Source State Row → ℝ) (r : Row) : ℝ :=
  ∑ Y : PartialAssignment Source State, mu (r, Y)

/-- Total `mu`-mass of labels mentioning one source. -/
def sourceMass (mu : Label Source State Row → ℝ) (i : Source) : ℝ :=
  ∑ a : Label Source State Row,
    if UsesSource a.2 i then mu a else 0

/-- The relaxed source factor is active only when the root mentions the
source. -/
def sourceFactor (root : Label Source State Row)
    (mu : Label Source State Row → ℝ) (i : Source) : ℝ :=
  if UsesSource root.2 i then 1 + sourceMass mu i else 1

theorem sum_sameRow_eq_rowMass
    (root : Label Source State Row)
    (mu : Label Source State Row → ℝ) :
    (∑ a : Label Source State Row,
        if a.1 = root.1 then mu a else 0) = rowMass mu root.1 := by
  classical
  rw [Fintype.sum_prod_type]
  unfold rowMass
  rw [Finset.sum_eq_single root.1]
  · simp
  · intro r _hr hrne
    have hne : r ≠ root.1 := hrne
    simp [hne]
  · simp

theorem sum_slotWeight_none
    (root : Label Source State Row)
    (mu : Label Source State Row → ℝ) :
    (∑ choice : Option (Label Source State Row),
      slotWeight root mu none choice) = 1 + rowMass mu root.1 := by
  rw [Fintype.sum_option]
  simp only [slotWeight, SlotAccepts]
  rw [sum_sameRow_eq_rowMass]

theorem sum_slotWeight_some
    (root : Label Source State Row)
    (mu : Label Source State Row → ℝ) (i : Source) :
    (∑ choice : Option (Label Source State Row),
      slotWeight root mu (some i) choice) = sourceFactor root mu i := by
  classical
  rw [Fintype.sum_option]
  unfold sourceFactor sourceMass
  by_cases hroot : UsesSource root.2 i
  · simp [slotWeight, SlotAccepts, hroot]
  · simp [slotWeight, SlotAccepts, hroot]

/-- The unrestricted encoding sum factors into one row term and the source
terms mentioned by the root. -/
theorem sum_encodingWeight
    (root : Label Source State Row)
    (mu : Label Source State Row → ℝ) :
    (∑ encoding : ChildEncoding Source State Row,
        encodingWeight root mu encoding) =
      (1 + rowMass mu root.1) * ∏ i, sourceFactor root mu i := by
  classical
  unfold encodingWeight
  calc
    (∑ encoding : Option Source → Option (Label Source State Row),
        ∏ bucket, slotWeight root mu bucket (encoding bucket)) =
        ∏ bucket : Option Source,
          ∑ choice : Option (Label Source State Row),
            slotWeight root mu bucket choice :=
      (Fintype.prod_sum (ι := Option Source)
        (κ := fun _ ↦ Option (Label Source State Row))
        (R := ℝ) (slotWeight root mu)).symm
    _ = (∑ choice : Option (Label Source State Row),
            slotWeight root mu none choice) *
          ∏ i : Source, ∑ choice : Option (Label Source State Row),
            slotWeight root mu (some i) choice := by
      rw [Fintype.prod_option]
    _ = (1 + rowMass mu root.1) * ∏ i, sourceFactor root mu i := by
      rw [sum_slotWeight_none]
      apply congrArg (fun x ↦ (1 + rowMass mu root.1) * x)
      apply Finset.prod_congr rfl
      intro i _hi
      exact sum_slotWeight_some root mu i

/-- Every proper child set has a distinct encoding, so the neighbor
polynomial is bounded by the unrestricted encoding sum. -/
theorem neighborPolynomial_le_row_source
    (root : Label Source State Row)
    {mu : Label Source State Row → ℝ} (hmu : ∀ a, 0 ≤ mu a) :
    neighborPolynomial mu root ≤
      (1 + rowMass mu root.1) * ∏ i, sourceFactor root mu i := by
  classical
  let proper := properChildFinsets root
  let encode := encodeChildren root
  have hinj : Set.InjOn encode proper := by
    intro A hA B hB hAB
    apply encodeChildren_injective_on_proper root
    · exact mem_properChildFinsets_iff.mp hA
    · exact mem_properChildFinsets_iff.mp hB
    · exact hAB
  have hrewrite :
      neighborPolynomial mu root =
        ∑ encoding ∈ proper.image encode, encodingWeight root mu encoding := by
    unfold neighborPolynomial
    change (∑ children ∈ proper, childMonomial mu children) = _
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro children hchildren
    symm
    exact encodingWeight_encodeChildren
      (mem_properChildFinsets_iff.mp hchildren) mu
  rw [hrewrite, ← sum_encodingWeight root mu]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun _encoding _hencoding ↦ Finset.mem_univ _)
    (fun encoding _huniv _hnot ↦ encodingWeight_nonneg root hmu encoding)

/-! ## Lambda charges -/

/-- Sum of the `lambda` entries at one source. -/
def lambdaTotal (lambda : Source → State → ℝ) (i : Source) : ℝ :=
  ∑ j, lambda i j

/-- Total charge of one row. -/
def coarseSelfCharge
    (q : Row → PartialAssignment Source State → ℝ)
    (lambda : Source → State → ℝ) (r : Row) : ℝ :=
  ∑ Y : PartialAssignment Source State,
    q r Y * partialLambdaProduct lambda Y

/-- Charge of one row through one source. -/
def coarseSourceCharge
    (q : Row → PartialAssignment Source State → ℝ)
    (lambda : Source → State → ℝ) (r : Row) (i : Source) : ℝ :=
  ∑ Y : PartialAssignment Source State,
    if UsesSource Y i then q r Y * partialLambdaProduct lambda Y else 0

/-- The coarse Harris--Srinivasan witness charge. -/
noncomputable def coarseMu
    (q : Row → PartialAssignment Source State → ℝ)
    (lambda : Source → State → ℝ)
    (a : Label Source State Row) : ℝ :=
  q a.1 a.2 * partialLambdaProduct lambda a.2 /
    (1 - coarseSelfCharge q lambda a.1)

/-- Product of the source totals over the support of `Y`. -/
def supportLambdaProduct (lambda : Source → State → ℝ)
    (Y : PartialAssignment Source State) : ℝ :=
  partialLambdaProduct (fun i _j ↦ lambdaTotal lambda i) Y

private theorem partialLambdaProduct_nonneg
    {lambda : Source → State → ℝ} (hlambda : ∀ i j, 0 ≤ lambda i j)
    (Y : PartialAssignment Source State) :
    0 ≤ partialLambdaProduct lambda Y := by
  unfold partialLambdaProduct partialProduct
  apply Finset.prod_nonneg
  intro i _hi
  cases hYi : Y i with
  | none => simp
  | some j => simpa [hYi] using hlambda i j

theorem coarseMu_nonneg
    {q : Row → PartialAssignment Source State → ℝ}
    {lambda : Source → State → ℝ}
    (hq : ∀ r Y, 0 ≤ q r Y) (hlambda : ∀ i j, 0 ≤ lambda i j)
    (hself : ∀ r, coarseSelfCharge q lambda r < 1)
    (a : Label Source State Row) :
    0 ≤ coarseMu q lambda a := by
  unfold coarseMu
  exact div_nonneg
    (mul_nonneg (hq a.1 a.2) (partialLambdaProduct_nonneg hlambda a.2))
    (sub_nonneg.mpr (hself a.1).le)

/-- First identity in (10): the total `mu`-mass in a row. -/
theorem rowMass_coarseMu
    (q : Row → PartialAssignment Source State → ℝ)
    (lambda : Source → State → ℝ) (r : Row) :
    rowMass (coarseMu q lambda) r =
      coarseSelfCharge q lambda r /
        (1 - coarseSelfCharge q lambda r) := by
  unfold rowMass coarseMu coarseSelfCharge
  rw [Finset.sum_div]

/-- Second identity in (10): the total `mu`-mass through one source. -/
theorem sourceMass_coarseMu
    (q : Row → PartialAssignment Source State → ℝ)
    (lambda : Source → State → ℝ) (i : Source) :
    sourceMass (coarseMu q lambda) i =
      ∑ r, coarseSourceCharge q lambda r i /
        (1 - coarseSelfCharge q lambda r) := by
  classical
  unfold sourceMass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _hr
  unfold coarseSourceCharge coarseMu
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro Y _hY
  by_cases huses : UsesSource Y i
  · simp [huses]
  · simp [huses]

theorem sourceFactor_coarseMu_le
    {q : Row → PartialAssignment Source State → ℝ}
    {lambda : Source → State → ℝ}
    (hsource : ∀ i,
      (∑ r, coarseSourceCharge q lambda r i /
        (1 - coarseSelfCharge q lambda r)) ≤ lambdaTotal lambda i - 1)
    (root : Label Source State Row) (i : Source) :
    sourceFactor root (coarseMu q lambda) i ≤
      match root.2 i with
      | none => 1
      | some _j => lambdaTotal lambda i := by
  unfold sourceFactor
  by_cases huses : UsesSource root.2 i
  · have hsourceMass := hsource i
    rw [← sourceMass_coarseMu q lambda i] at hsourceMass
    cases hYi : root.2 i with
    | none => exact (huses hYi).elim
    | some j =>
        simp [UsesSource, hYi, huses]
        linarith
  · have hnone : root.2 i = none := by
      simpa [UsesSource] using huses
    simp [hnone, huses]

theorem prod_sourceFactor_coarseMu_le
    {q : Row → PartialAssignment Source State → ℝ}
    {lambda : Source → State → ℝ}
    (hq : ∀ r Y, 0 ≤ q r Y) (hlambda : ∀ i j, 0 ≤ lambda i j)
    (hself : ∀ r, coarseSelfCharge q lambda r < 1)
    (hsource : ∀ i,
      (∑ r, coarseSourceCharge q lambda r i /
        (1 - coarseSelfCharge q lambda r)) ≤ lambdaTotal lambda i - 1)
    (root : Label Source State Row) :
    (∏ i, sourceFactor root (coarseMu q lambda) i) ≤
      supportLambdaProduct lambda root.2 := by
  unfold supportLambdaProduct partialLambdaProduct partialProduct
  apply Finset.prod_le_prod
  · intro i _hi
    unfold sourceFactor
    by_cases huses : UsesSource root.2 i
    · simp only [huses, if_true]
      have hmass : 0 ≤ sourceMass (coarseMu q lambda) i := by
        unfold sourceMass
        exact Finset.sum_nonneg fun a _ha ↦ by
          by_cases hauses : UsesSource a.2 i
          · simp [hauses, coarseMu_nonneg hq hlambda hself a]
          · simp [hauses]
      linarith
    · simp [huses]
  · intro i _hi
    exact sourceFactor_coarseMu_le hsource root i

/-- Equation (11): after substituting the coarse charges, the neighbor
polynomial is at most the row denominator times the product of the source
totals on the root support. -/
theorem neighborPolynomial_coarseMu_le
    {q : Row → PartialAssignment Source State → ℝ}
    {lambda : Source → State → ℝ}
    (hq : ∀ r Y, 0 ≤ q r Y) (hlambda : ∀ i j, 0 ≤ lambda i j)
    (hself : ∀ r, coarseSelfCharge q lambda r < 1)
    (hsource : ∀ i,
      (∑ r, coarseSourceCharge q lambda r i /
        (1 - coarseSelfCharge q lambda r)) ≤ lambdaTotal lambda i - 1)
    (root : Label Source State Row) :
    neighborPolynomial (coarseMu q lambda) root ≤
      (1 / (1 - coarseSelfCharge q lambda root.1)) *
        supportLambdaProduct lambda root.2 := by
  have hgeneral := neighborPolynomial_le_row_source root
    (coarseMu_nonneg hq hlambda hself)
  have hrow :
      1 + rowMass (coarseMu q lambda) root.1 =
        1 / (1 - coarseSelfCharge q lambda root.1) := by
    rw [rowMass_coarseMu]
    have hne : 1 - coarseSelfCharge q lambda root.1 ≠ 0 :=
      ne_of_gt (sub_pos.mpr (hself root.1))
    field_simp
    ring
  rw [hrow] at hgeneral
  exact hgeneral.trans (mul_le_mul_of_nonneg_left
    (prod_sourceFactor_coarseMu_le hq hlambda hself hsource root)
    (one_div_nonneg.mpr (sub_nonneg.mpr (hself root.1).le)))

/-- Multiplying a coordinatewise scaled probability monomial by the support
product recovers the `lambda` monomial. -/
theorem partialLambdaProduct_mul_supportLambdaProduct
    {p lambda : Source → State → ℝ}
    (hscale : ∀ i j, lambda i j = lambdaTotal lambda i * p i j)
    (Y : PartialAssignment Source State) :
    partialLambdaProduct p Y * supportLambdaProduct lambda Y =
      partialLambdaProduct lambda Y := by
  unfold supportLambdaProduct partialLambdaProduct partialProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  cases hYi : Y i with
  | none => simp [hYi]
  | some j =>
      simp [hYi, hscale i j, mul_comm]

/-- The complete algebraic lambda substitution: the root weight times its
neighbor polynomial is at most its witness charge. -/
theorem rootWeight_mul_neighborPolynomial_le_coarseMu
    {q : Row → PartialAssignment Source State → ℝ}
    {p lambda : Source → State → ℝ}
    (hq : ∀ r Y, 0 ≤ q r Y) (hp : ∀ i j, 0 ≤ p i j)
    (hlambda : ∀ i j, 0 ≤ lambda i j)
    (hscale : ∀ i j, lambda i j = lambdaTotal lambda i * p i j)
    (hself : ∀ r, coarseSelfCharge q lambda r < 1)
    (hsource : ∀ i,
      (∑ r, coarseSourceCharge q lambda r i /
        (1 - coarseSelfCharge q lambda r)) ≤ lambdaTotal lambda i - 1)
    (root : Label Source State Row) :
    (q root.1 root.2 * partialLambdaProduct p root.2) *
        neighborPolynomial (coarseMu q lambda) root ≤
      coarseMu q lambda root := by
  have hrootWeight :
      0 ≤ q root.1 root.2 * partialLambdaProduct p root.2 :=
    mul_nonneg (hq root.1 root.2)
      (partialLambdaProduct_nonneg hp root.2)
  calc
    (q root.1 root.2 * partialLambdaProduct p root.2) *
          neighborPolynomial (coarseMu q lambda) root ≤
        (q root.1 root.2 * partialLambdaProduct p root.2) *
          ((1 / (1 - coarseSelfCharge q lambda root.1)) *
            supportLambdaProduct lambda root.2) :=
      mul_le_mul_of_nonneg_left
        (neighborPolynomial_coarseMu_le hq hlambda hself hsource root)
        hrootWeight
    _ = q root.1 root.2 *
          (partialLambdaProduct p root.2 *
            supportLambdaProduct lambda root.2) /
          (1 - coarseSelfCharge q lambda root.1) := by ring
    _ = q root.1 root.2 * partialLambdaProduct lambda root.2 /
          (1 - coarseSelfCharge q lambda root.1) := by
      rw [partialLambdaProduct_mul_supportLambdaProduct hscale]
    _ = coarseMu q lambda root := by rfl

end WeightedEdgeColoring.FinitePartialResamplingNeighborPolynomial
