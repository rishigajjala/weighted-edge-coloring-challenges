import WeightedEdgeColoring.FinitePartialResamplingCapped

/-!
# Finite histories and resampling tables

This file defines finite partial-resampling histories and their probability
distributions.

For a bad row, a nonnegative hitting weight on compatible partial
assignments is normalized to a probability distribution.  A selected
partial assignment says which sources are refreshed.  The refresh kernel is
an ordinary finite product, and its total mass is proved to be one without
using `MeasureTheory`.

The second half of the file records the same refresh operation by a table.
Cell zero gives the initial state of a source and each later use of that
source advances its pointer by one.  A history of length `h` reads at most
the first `h+1` cells of every source.  Finite table prefixes carry the
expected product mass, whose total is again proved to be one.

Termination and simultaneous avoidance require a separate witness-history
bound that turns the charge inequalities into a uniform bound on the length
of a run; they are not conclusions of this module.
-/

namespace WeightedEdgeColoring.FinitePartialResamplingProcess

open scoped BigOperators
open WeightedEdgeColoring.FinitePartialResamplingExponential

noncomputable section

variable {Source State Row : Type*}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- The part of a row's hitting weight compatible with a complete state. -/
def compatiblePatchWeight
    (weight : Row → PartialAssignment Source State → ℝ)
    (r : Row) (z : Source → State) (Y : PartialAssignment Source State) : ℝ :=
  if Compatible Y z then weight r Y else 0

/-- Total hitting weight available at a complete state for one row. -/
def compatiblePatchTotal
    (weight : Row → PartialAssignment Source State → ℝ)
    (r : Row) (z : Source → State) : ℝ :=
  ∑ Y : PartialAssignment Source State, compatiblePatchWeight weight r z Y

theorem compatiblePatchWeight_nonneg
    {weight : Row → PartialAssignment Source State → ℝ}
    (hweight : ∀ r Y, 0 ≤ weight r Y)
    (r : Row) (z : Source → State) (Y : PartialAssignment Source State) :
    0 ≤ compatiblePatchWeight weight r z Y := by
  unfold compatiblePatchWeight
  split
  · exact hweight r Y
  · exact le_rfl

theorem compatiblePatchTotal_nonneg
    {weight : Row → PartialAssignment Source State → ℝ}
    (hweight : ∀ r Y, 0 ≤ weight r Y)
    (r : Row) (z : Source → State) :
    0 ≤ compatiblePatchTotal weight r z := by
  unfold compatiblePatchTotal
  exact Finset.sum_nonneg fun Y _ ↦
    compatiblePatchWeight_nonneg hweight r z Y

/-- Normalize the compatible hitting weights.  At a bad state the hitting
property supplies `1 ≤ compatiblePatchTotal`, so this is a probability law.
-/
def normalizedPatchWeight
    (weight : Row → PartialAssignment Source State → ℝ)
    (r : Row) (z : Source → State) (Y : PartialAssignment Source State) : ℝ :=
  compatiblePatchWeight weight r z Y / compatiblePatchTotal weight r z

theorem normalizedPatchWeight_nonneg
    {weight : Row → PartialAssignment Source State → ℝ}
    (hweight : ∀ r Y, 0 ≤ weight r Y)
    {r : Row} {z : Source → State}
    (htotal : 0 < compatiblePatchTotal weight r z)
    (Y : PartialAssignment Source State) :
    0 ≤ normalizedPatchWeight weight r z Y := by
  exact div_nonneg
    (compatiblePatchWeight_nonneg hweight r z Y) htotal.le

theorem normalizedPatchWeight_eq_zero_of_incompatible
    (weight : Row → PartialAssignment Source State → ℝ)
    {r : Row} {z : Source → State} {Y : PartialAssignment Source State}
    (hY : ¬ Compatible Y z) :
    normalizedPatchWeight weight r z Y = 0 := by
  simp [normalizedPatchWeight, compatiblePatchWeight, hY]

/-- Normalization is exact whenever the compatible total is nonzero. -/
theorem sum_normalizedPatchWeight
    (weight : Row → PartialAssignment Source State → ℝ)
    {r : Row} {z : Source → State}
    (htotal : compatiblePatchTotal weight r z ≠ 0) :
    (∑ Y : PartialAssignment Source State,
      normalizedPatchWeight weight r z Y) = 1 := by
  calc
    (∑ Y : PartialAssignment Source State,
        normalizedPatchWeight weight r z Y) =
        (∑ Y : PartialAssignment Source State,
          compatiblePatchWeight weight r z Y) /
            compatiblePatchTotal weight r z := by
      simp only [normalizedPatchWeight]
      rw [Finset.sum_div]
    _ = compatiblePatchTotal weight r z /
          compatiblePatchTotal weight r z := by
      rfl
    _ = 1 := div_self htotal

/-- Dividing by a compatible total of at least one can only decrease an
individual hitting weight. -/
theorem normalizedPatchWeight_le_weight
    {weight : Row → PartialAssignment Source State → ℝ}
    (hweight : ∀ r Y, 0 ≤ weight r Y)
    {r : Row} {z : Source → State}
    (htotal : 1 ≤ compatiblePatchTotal weight r z)
    (Y : PartialAssignment Source State) :
    normalizedPatchWeight weight r z Y ≤ weight r Y := by
  by_cases hcompat : Compatible Y z
  · have hden : 0 < compatiblePatchTotal weight r z :=
      lt_of_lt_of_le zero_lt_one htotal
    unfold normalizedPatchWeight compatiblePatchWeight
    simp only [hcompat, if_true]
    calc
      weight r Y / compatiblePatchTotal weight r z ≤ weight r Y / 1 := by
        exact div_le_div_of_nonneg_left (hweight r Y) zero_lt_one htotal
      _ = weight r Y := div_one _
  · simp [normalizedPatchWeight, compatiblePatchWeight, hcompat,
      hweight r Y]

/-- One-coordinate factor in a refresh step.  Untouched coordinates must
keep their old state; touched coordinates receive a fresh `prob` sample. -/
def resampleCoordinateMass
    (prob : Source → State → ℝ)
    (Y : PartialAssignment Source State) (old : Source → State)
    (i : Source) (a : State) : ℝ :=
  match Y i with
  | none => if a = old i then 1 else 0
  | some _ => prob i a

/-- Product mass of obtaining `new` after refreshing precisely the sources
mentioned by `Y`. -/
def resampleMass
    (prob : Source → State → ℝ)
    (Y : PartialAssignment Source State)
    (old new : Source → State) : ℝ :=
  ∏ i, resampleCoordinateMass prob Y old i (new i)

theorem resampleCoordinateMass_nonneg
    {prob : Source → State → ℝ} (hprob : ∀ i a, 0 ≤ prob i a)
    (Y : PartialAssignment Source State) (old : Source → State)
    (i : Source) (a : State) :
    0 ≤ resampleCoordinateMass prob Y old i a := by
  cases hYi : Y i with
  | none =>
      simp only [resampleCoordinateMass, hYi]
      split
      · norm_num
      · norm_num
  | some b =>
      simpa [resampleCoordinateMass, hYi] using hprob i a

theorem resampleMass_nonneg
    {prob : Source → State → ℝ} (hprob : ∀ i a, 0 ≤ prob i a)
    (Y : PartialAssignment Source State)
    (old new : Source → State) :
    0 ≤ resampleMass prob Y old new := by
  unfold resampleMass
  exact Finset.prod_nonneg fun i _ ↦
    resampleCoordinateMass_nonneg hprob Y old i (new i)

theorem sum_resampleCoordinateMass
    (prob : Source → State → ℝ)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (Y : PartialAssignment Source State) (old : Source → State)
    (i : Source) :
    (∑ a, resampleCoordinateMass prob Y old i a) = 1 := by
  cases hYi : Y i with
  | none => simp [resampleCoordinateMass, hYi]
  | some b => simpa [resampleCoordinateMass, hYi] using hprobSum i

/-- The finite independent refresh kernel has total mass one. -/
theorem sum_resampleMass
    (prob : Source → State → ℝ)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (Y : PartialAssignment Source State) (old : Source → State) :
    (∑ new : Source → State, resampleMass prob Y old new) = 1 := by
  calc
    (∑ new : Source → State, resampleMass prob Y old new) =
        ∏ i, ∑ a, resampleCoordinateMass prob Y old i a := by
      unfold resampleMass
      exact (Fintype.prod_sum
        (fun i a ↦ resampleCoordinateMass prob Y old i a)).symm
    _ = ∏ _i : Source, (1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact sum_resampleCoordinateMass prob hprobSum Y old i
    _ = 1 := by simp

/-- A positive refresh transition cannot change an untouched source. -/
theorem eq_old_of_resampleMass_pos
    {prob : Source → State → ℝ}
    {Y : PartialAssignment Source State}
    {old new : Source → State} {i : Source}
    (hYi : Y i = none) (hpos : 0 < resampleMass prob Y old new) :
    new i = old i := by
  by_contra hne
  have hzero : resampleMass prob Y old new = 0 := by
    unfold resampleMass
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [resampleCoordinateMass, hYi, hne]
  exact (ne_of_gt hpos) hzero

/-- Joint mass of selecting a compatible patch and then refreshing every
source mentioned by that patch. -/
def praStepMass
    (prob : Source → State → ℝ)
    (weight : Row → PartialAssignment Source State → ℝ)
    (r : Row) (old : Source → State)
    (Y : PartialAssignment Source State) (new : Source → State) : ℝ :=
  normalizedPatchWeight weight r old Y * resampleMass prob Y old new

theorem praStepMass_nonneg
    {prob : Source → State → ℝ} (hprob : ∀ i a, 0 ≤ prob i a)
    {weight : Row → PartialAssignment Source State → ℝ}
    (hweight : ∀ r Y, 0 ≤ weight r Y)
    {r : Row} {old : Source → State}
    (htotal : 0 < compatiblePatchTotal weight r old)
    (Y : PartialAssignment Source State) (new : Source → State) :
    0 ≤ praStepMass prob weight r old Y new := by
  exact mul_nonneg
    (normalizedPatchWeight_nonneg hweight htotal Y)
    (resampleMass_nonneg hprob Y old new)

/-- One legal PRA step is an ordinary finite probability kernel. -/
theorem sum_praStepMass
    (prob : Source → State → ℝ)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (weight : Row → PartialAssignment Source State → ℝ)
    {r : Row} {old : Source → State}
    (htotal : compatiblePatchTotal weight r old ≠ 0) :
    (∑ Y : PartialAssignment Source State,
      ∑ new : Source → State, praStepMass prob weight r old Y new) = 1 := by
  calc
    (∑ Y : PartialAssignment Source State,
        ∑ new : Source → State, praStepMass prob weight r old Y new) =
        ∑ Y : PartialAssignment Source State,
          normalizedPatchWeight weight r old Y *
            (∑ new : Source → State, resampleMass prob Y old new) := by
      apply Finset.sum_congr rfl
      intro Y _hY
      unfold praStepMass
      rw [Finset.mul_sum]
    _ = ∑ Y : PartialAssignment Source State,
          normalizedPatchWeight weight r old Y := by
      apply Finset.sum_congr rfl
      intro Y _hY
      rw [sum_resampleMass prob hprobSum Y old]
      simp
    _ = 1 := sum_normalizedPatchWeight weight htotal

/-- The normalized one-step mass is bounded by the corresponding
unnormalized hitting weight times the independent refresh mass. -/
theorem praStepMass_le_unnormalized
    {prob : Source → State → ℝ} (hprob : ∀ i a, 0 ≤ prob i a)
    {weight : Row → PartialAssignment Source State → ℝ}
    (hweight : ∀ r Y, 0 ≤ weight r Y)
    {r : Row} {old : Source → State}
    (htotal : 1 ≤ compatiblePatchTotal weight r old)
    (Y : PartialAssignment Source State) (new : Source → State) :
    praStepMass prob weight r old Y new ≤
      weight r Y * resampleMass prob Y old new := by
  unfold praStepMass
  exact mul_le_mul_of_nonneg_right
    (normalizedPatchWeight_le_weight hweight htotal Y)
    (resampleMass_nonneg hprob Y old new)

/-- Positive one-step mass certifies that the selected patch is compatible
with the old complete state. -/
theorem compatible_of_praStepMass_pos
    {prob : Source → State → ℝ}
    {weight : Row → PartialAssignment Source State → ℝ}
    {r : Row} {old new : Source → State}
    {Y : PartialAssignment Source State}
    (hpos : 0 < praStepMass prob weight r old Y new) :
    Compatible Y old := by
  by_contra hnot
  have hzero : praStepMass prob weight r old Y new = 0 := by
    simp [praStepMass,
      normalizedPatchWeight_eq_zero_of_incompatible weight hnot]
  exact (ne_of_gt hpos) hzero

/-- Number of table cells already consumed at every source. -/
abbrev Pointer (Source : Type*) := Source → ℕ

/-- An unbounded notation for a resampling table.  The finite-prefix lemmas
below show that a finite run uses only finitely many cells. -/
abbrev ResamplingTable (Source State : Type*) := Source → ℕ → State

/-- The complete state currently exposed by a table and pointer. -/
def tableChoice (T : ResamplingTable Source State)
    (p : Pointer Source) : Source → State :=
  fun i ↦ T i (p i)

/-- Advance exactly the sources mentioned by a partial assignment. -/
def advancePointer (p : Pointer Source)
    (Y : PartialAssignment Source State) : Pointer Source :=
  fun i ↦ match Y i with
    | none => p i
    | some _ => p i + 1

@[simp] theorem advancePointer_none
    (p : Pointer Source) (Y : PartialAssignment Source State)
    (i : Source) (hYi : Y i = none) :
    advancePointer p Y i = p i := by
  simp [advancePointer, hYi]

@[simp] theorem advancePointer_some
    (p : Pointer Source) (Y : PartialAssignment Source State)
    (i : Source) (a : State) (hYi : Y i = some a) :
    advancePointer p Y i = p i + 1 := by
  simp [advancePointer, hYi]

theorem advancePointer_le_succ
    (p : Pointer Source) (Y : PartialAssignment Source State) (i : Source) :
    advancePointer p Y i ≤ p i + 1 := by
  cases hYi : Y i with
  | none => simp [advancePointer, hYi]
  | some a => simp [advancePointer, hYi]

/-- A process step records the selected row and the compatible patch that is
refreshed. -/
abbrev ResamplingStep (Source State Row : Type*) :=
  Row × PartialAssignment Source State

/-- Pointer after executing a finite history in chronological order. -/
def runPointer (p : Pointer Source) :
    List (ResamplingStep Source State Row) → Pointer Source
  | [] => p
  | step :: history =>
      runPointer (advancePointer p step.2) history

theorem runPointer_le_add_length
    (p : Pointer Source)
    (history : List (ResamplingStep Source State Row)) (i : Source) :
    runPointer p history i ≤ p i + history.length := by
  induction history generalizing p with
  | nil => simp [runPointer]
  | cons step history ih =>
      have htail := ih (p := advancePointer p step.2)
      have hstep := advancePointer_le_succ p step.2 i
      simp only [runPointer, List.length_cons]
      omega

/-- The all-zero initial pointer. -/
def initialPointer : Pointer Source := fun _ ↦ 0

theorem runPointer_initial_le_length
    (history : List (ResamplingStep Source State Row)) (i : Source) :
    runPointer (initialPointer : Pointer Source) history i ≤ history.length := by
  simpa [initialPointer] using
    (runPointer_le_add_length
      (initialPointer : Pointer Source) history i)

/-- Advancing a table pointer preserves untouched states and exposes the next
fresh cell at touched sources. -/
theorem tableChoice_advancePointer
    (T : ResamplingTable Source State) (p : Pointer Source)
    (Y : PartialAssignment Source State) (i : Source) :
    tableChoice T (advancePointer p Y) i =
      match Y i with
      | none => tableChoice T p i
      | some _ => T i (p i + 1) := by
  cases hYi : Y i with
  | none => simp [tableChoice, advancePointer, hYi]
  | some a => simp [tableChoice, advancePointer, hYi]

/-- A table realizes a history when every selected patch agrees with the
state visible just before that step. -/
def RealizesFrom (T : ResamplingTable Source State) :
    Pointer Source → List (ResamplingStep Source State Row) → Prop
  | _p, [] => True
  | p, step :: history =>
      Compatible step.2 (tableChoice T p) ∧
        RealizesFrom T (advancePointer p step.2) history

/-- Realization from the all-zero pointer. -/
def Realizes (T : ResamplingTable Source State)
    (history : List (ResamplingStep Source State Row)) : Prop :=
  RealizesFrom T initialPointer history

@[simp] theorem realizesFrom_nil
    (T : ResamplingTable Source State) (p : Pointer Source) :
    RealizesFrom (Row := Row) T p [] := by
  simp [RealizesFrom]

@[simp] theorem realizesFrom_cons
    (T : ResamplingTable Source State) (p : Pointer Source)
    (step : ResamplingStep Source State Row)
    (history : List (ResamplingStep Source State Row)) :
    RealizesFrom T p (step :: history) ↔
      Compatible step.2 (tableChoice T p) ∧
        RealizesFrom T (advancePointer p step.2) history := by
  rfl

/-- Complete state exposed after a history. -/
def finalTableChoice (T : ResamplingTable Source State)
    (p : Pointer Source)
    (history : List (ResamplingStep Source State Row)) : Source → State :=
  tableChoice T (runPointer p history)

/-- Product of the normalized patch choices along one realized history.
This is the part of a finite run's mass not already stored in the table. -/
def historyPatchMass
    (weight : Row → PartialAssignment Source State → ℝ)
    (T : ResamplingTable Source State) :
    Pointer Source → List (ResamplingStep Source State Row) → ℝ
  | _p, [] => 1
  | p, step :: history =>
      normalizedPatchWeight weight step.1 (tableChoice T p) step.2 *
        historyPatchMass weight T (advancePointer p step.2) history

/-- Every row selected along a history has compatible hitting total at least
one.  This is the precise process hypothesis supplied when the selected row
is bad and the hitting weights cover every bad complete state. -/
def HasHittingTotalsFrom
    (weight : Row → PartialAssignment Source State → ℝ)
    (T : ResamplingTable Source State) :
    Pointer Source → List (ResamplingStep Source State Row) → Prop
  | _p, [] => True
  | p, step :: history =>
      1 ≤ compatiblePatchTotal weight step.1 (tableChoice T p) ∧
        HasHittingTotalsFrom weight T (advancePointer p step.2) history

/-- Product of the unnormalized hitting weights labelling a history. -/
def historyHittingProduct
    (weight : Row → PartialAssignment Source State → ℝ) :
    List (ResamplingStep Source State Row) → ℝ
  | [] => 1
  | step :: history =>
      weight step.1 step.2 * historyHittingProduct weight history

theorem historyPatchMass_nonneg
    {weight : Row → PartialAssignment Source State → ℝ}
    (hweight : ∀ r Y, 0 ≤ weight r Y)
    (T : ResamplingTable Source State) (p : Pointer Source)
    (history : List (ResamplingStep Source State Row))
    (htotals : HasHittingTotalsFrom weight T p history) :
    0 ≤ historyPatchMass weight T p history := by
  induction history generalizing p with
  | nil => simp [historyPatchMass]
  | cons step history ih =>
      rcases htotals with ⟨hhead, htail⟩
      have hheadPos : 0 < compatiblePatchTotal weight step.1
          (tableChoice T p) := lt_of_lt_of_le zero_lt_one hhead
      exact mul_nonneg
        (normalizedPatchWeight_nonneg hweight hheadPos step.2)
        (ih (p := advancePointer p step.2) htail)

/-- Along legal bad-row steps, normalization can only decrease the product
of patch weights.  This is the finite history inequality consumed by the
later witness-history count. -/
theorem historyPatchMass_le_historyHittingProduct
    {weight : Row → PartialAssignment Source State → ℝ}
    (hweight : ∀ r Y, 0 ≤ weight r Y)
    (T : ResamplingTable Source State) (p : Pointer Source)
    (history : List (ResamplingStep Source State Row))
    (htotals : HasHittingTotalsFrom weight T p history) :
    historyPatchMass weight T p history ≤
      historyHittingProduct weight history := by
  induction history generalizing p with
  | nil => simp [historyPatchMass, historyHittingProduct]
  | cons step history ih =>
      rcases htotals with ⟨hhead, htail⟩
      have hnorm : normalizedPatchWeight weight step.1
          (tableChoice T p) step.2 ≤ weight step.1 step.2 :=
        normalizedPatchWeight_le_weight hweight hhead step.2
      have htailNonneg :
          0 ≤ historyPatchMass weight T (advancePointer p step.2) history :=
        historyPatchMass_nonneg hweight T (advancePointer p step.2)
          history htail
      have htailLe := ih (p := advancePointer p step.2) htail
      exact mul_le_mul hnorm htailLe htailNonneg (hweight step.1 step.2)

/-- A finite prefix with `h+1` cells at every source suffices for every run
of length at most `h`. -/
abbrev FiniteResamplingTable (Source State : Type*) (h : ℕ) :=
  Source → Fin (h + 1) → State

/-- Product mass of one finite resampling-table prefix. -/
def finiteTableMass (prob : Source → State → ℝ) {h : ℕ}
    (T : FiniteResamplingTable Source State h) : ℝ :=
  ∏ i, ∏ k, prob i (T i k)

theorem finiteTableMass_nonneg
    {prob : Source → State → ℝ} (hprob : ∀ i a, 0 ≤ prob i a)
    {h : ℕ} (T : FiniteResamplingTable Source State h) :
    0 ≤ finiteTableMass prob T := by
  unfold finiteTableMass
  exact Finset.prod_nonneg fun i _ ↦
    Finset.prod_nonneg fun k _ ↦ hprob i (T i k)

theorem sum_sourceTableMass
    (prob : Source → State → ℝ)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (h : ℕ) (i : Source) :
    (∑ word : Fin (h + 1) → State, ∏ k, prob i (word k)) = 1 := by
  calc
    (∑ word : Fin (h + 1) → State, ∏ k, prob i (word k)) =
        ∏ _k : Fin (h + 1), ∑ a, prob i a := by
      exact (Fintype.prod_sum (fun _k a ↦ prob i a)).symm
    _ = ∏ _k : Fin (h + 1), (1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro k _hk
      exact hprobSum i
    _ = 1 := by simp

/-- The independent product masses of all finite table prefixes sum to one.
This is the finite replacement for a probability space of infinite tables.
-/
theorem sum_finiteTableMass
    (prob : Source → State → ℝ)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (h : ℕ) :
    (∑ T : FiniteResamplingTable Source State h,
      finiteTableMass prob T) = 1 := by
  calc
    (∑ T : FiniteResamplingTable Source State h,
        finiteTableMass prob T) =
        ∏ i, ∑ word : Fin (h + 1) → State,
          ∏ k, prob i (word k) := by
      unfold finiteTableMass
      exact (Fintype.prod_sum
        (ι := Source) (κ := fun _ ↦ Fin (h + 1) → State) (R := ℝ)
        (fun i word ↦ ∏ k, prob i (word k))).symm
    _ = ∏ _i : Source, (1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact sum_sourceTableMass prob hprobSum h i
    _ = 1 := by simp

/-- Extend a finite prefix by an arbitrary fallback state.  Runs within the
prefix horizon never inspect the fallback branch. -/
def extendFiniteTable (fallback : Source → State) {h : ℕ}
    (T : FiniteResamplingTable Source State h) :
    ResamplingTable Source State :=
  fun i k ↦ if hk : k < h + 1 then T i ⟨k, hk⟩ else fallback i

theorem extendFiniteTable_apply_of_lt
    (fallback : Source → State) {h : ℕ}
    (T : FiniteResamplingTable Source State h)
    (i : Source) (k : ℕ) (hk : k < h + 1) :
    extendFiniteTable fallback T i k = T i ⟨k, hk⟩ := by
  simp [extendFiniteTable, hk]

/-- The final state of a run of length at most `h` is read inside a prefix of
length `h+1`; no infinite table construction is needed. -/
theorem finalTableChoice_extendFiniteTable
    (fallback : Source → State) {h : ℕ}
    (T : FiniteResamplingTable Source State h)
    (history : List (ResamplingStep Source State Row))
    (hhistory : history.length ≤ h) (i : Source) :
    finalTableChoice (extendFiniteTable fallback T)
        (initialPointer : Pointer Source) history i =
      T i ⟨runPointer (initialPointer : Pointer Source) history i, by
        have hrun := runPointer_initial_le_length
          (Row := Row) history i
        omega⟩ := by
  unfold finalTableChoice tableChoice
  apply extendFiniteTable_apply_of_lt

end

end WeightedEdgeColoring.FinitePartialResamplingProcess
