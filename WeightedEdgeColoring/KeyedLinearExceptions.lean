import WeightedEdgeColoring.PreCoverLinearGrouping
import WeightedEdgeColoring.FiniteKeyedCardinality

/-!
# Keyed linear-grouping exceptions

This file turns the rank-level exception estimate from
`PreCoverLinearGrouping` into a finite-set estimate, first in one cell and
then over all cells of a finite key partition.  Cells smaller than the
grouping parameter contribute no exceptions.  Consequently every active
cell satisfies the integral estimate `M * |E| <= 2 * |S|`, and summing over
the key fibers introduces no factor for the number of cells.
-/

namespace WeightedEdgeColoring

noncomputable section

universe u v

/-- The objects discarded from one cell by linear grouping.  Small cells
are left untouched; in an active cell these are exactly the objects whose
ranks lie in the first linear group. -/
def linearCellExceptions {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → ℝ) (M : ℕ) : Finset α :=
  if M ≤ S.card then
    (linearExceptionalIndices S.card M).image (finiteCellItem S weight)
  else ∅

/-- Every cell exception is an object of the cell. -/
theorem linearCellExceptions_subset
    {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → ℝ) (M : ℕ) :
    linearCellExceptions S weight M ⊆ S := by
  classical
  intro x hx
  simp only [linearCellExceptions] at hx
  split at hx
  · rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
    exact finiteCellItem_mem S weight i
  · simp at hx

/-- In an active cell, injectivity of the canonical enumeration gives the
exact exception cardinality. -/
theorem card_linearCellExceptions_of_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → ℝ) {M : ℕ} (hMS : M ≤ S.card) :
    (linearCellExceptions S weight M).card =
      (linearExceptionalIndices S.card M).card := by
  classical
  rw [linearCellExceptions, if_pos hMS]
  exact Finset.card_image_of_injective _ (finiteCellItem_injective S weight)

/-- A small cell has no exceptions. -/
@[simp] theorem linearCellExceptions_eq_empty_of_lt
    {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → ℝ) {M : ℕ} (hSM : S.card < M) :
    linearCellExceptions S weight M = ∅ := by
  simp [linearCellExceptions, Nat.not_le.mpr hSM]

/-- Exact cardinality, including the inactive-cell convention. -/
theorem card_linearCellExceptions
    {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → ℝ) (M : ℕ) :
    (linearCellExceptions S weight M).card =
      if M ≤ S.card then (linearExceptionalIndices S.card M).card else 0 := by
  classical
  by_cases hMS : M ≤ S.card
  · simp [hMS, card_linearCellExceptions_of_le S weight hMS]
  · simp [linearCellExceptions, hMS]

/-- Integral form of the `2/M` exception estimate in one cell. -/
theorem mul_card_linearCellExceptions_le_two_mul
    {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → ℝ) {M : ℕ} (hM : 0 < M) :
    M * (linearCellExceptions S weight M).card ≤ 2 * S.card := by
  classical
  by_cases hMS : M ≤ S.card
  · rw [card_linearCellExceptions_of_le S weight hMS]
    have hbound := card_linearExceptionalIndices_le_two_mul_div hM hMS
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hreal :
        (M : ℝ) * ((linearExceptionalIndices S.card M).card : ℝ) ≤
          2 * (S.card : ℝ) := by
      calc
        (M : ℝ) * ((linearExceptionalIndices S.card M).card : ℝ) ≤
            (M : ℝ) * (2 * (S.card : ℝ) / (M : ℝ)) :=
          mul_le_mul_of_nonneg_left hbound hMR.le
        _ = 2 * (S.card : ℝ) := by field_simp
    exact_mod_cast hreal
  · have hSM : S.card < M := Nat.lt_of_not_ge hMS
    simp [linearCellExceptions_eq_empty_of_lt S weight hSM]

/-- Union of the linear-grouping exceptions over all key fibers. -/
def keyedLinearExceptions
    {α : Type u} {κ : Type v}
    [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (B : Finset α) (key : α → κ) (weight : α → ℝ) (M : ℕ) : Finset α :=
  (Finset.univ : Finset κ).biUnion fun k ↦
    linearCellExceptions (B.filter fun x ↦ key x = k) weight M

/-- The keyed union contains only objects from the original finite set. -/
theorem keyedLinearExceptions_subset
    {α : Type u} {κ : Type v}
    [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (B : Finset α) (key : α → κ) (weight : α → ℝ) (M : ℕ) :
    keyedLinearExceptions B key weight M ⊆ B := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨k, _hk, hxk⟩
  exact Finset.mem_filter.mp
    (linearCellExceptions_subset (B.filter fun y ↦ key y = k) weight M hxk) |>.1

/-- The fiber of the global union over `k` is exactly the exception set
constructed in the `k`-cell. -/
theorem filter_keyedLinearExceptions_eq
    {α : Type u} {κ : Type v}
    [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (B : Finset α) (key : α → κ) (weight : α → ℝ) (M : ℕ) (k : κ) :
    (keyedLinearExceptions B key weight M).filter (fun x ↦ key x = k) =
      linearCellExceptions (B.filter fun x ↦ key x = k) weight M := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨hxU, hxkey⟩
    rcases Finset.mem_biUnion.mp hxU with ⟨j, _hj, hxj⟩
    have hxcell := linearCellExceptions_subset
      (B.filter fun y ↦ key y = j) weight M hxj
    have hxkeyj : key x = j := (Finset.mem_filter.mp hxcell).2
    have hjk : j = k := hxkeyj.symm.trans hxkey
    have hcells : B.filter (fun y ↦ key y = j) =
        B.filter (fun y ↦ key y = k) := by
      ext y
      simp [hjk]
    rwa [hcells] at hxj
  · intro hx
    have hxcell := linearCellExceptions_subset
      (B.filter fun y ↦ key y = k) weight M hx
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hx⟩,
      (Finset.mem_filter.mp hxcell).2⟩

/-- Global `2/M` exception bound.  The proof sums the integral cell bounds
through the key fibers, with no loss depending on the number of keys. -/
theorem mul_card_keyedLinearExceptions_le_two_mul
    {α : Type u} {κ : Type v}
    [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (B : Finset α) (key : α → κ) (weight : α → ℝ)
    {M : ℕ} (hM : 0 < M) :
    M * (keyedLinearExceptions B key weight M).card ≤ 2 * B.card := by
  classical
  apply mul_card_le_mul_card_of_fiberwise
    (keyedLinearExceptions B key weight M) B key M 2
  intro k
  rw [filter_keyedLinearExceptions_eq B key weight M k]
  exact mul_card_linearCellExceptions_le_two_mul
    (B.filter fun x ↦ key x = k) weight hM

/-- A predicate is constant on the key cells of `B`.  This is the form used
when keys encode endpoint pairs and the predicate is incidence at a fixed
vertex. -/
def PredicateConstantOnKeyCells
    {α : Type u} {κ : Type v} [DecidableEq α]
    (B : Finset α) (key : α → κ) (P : α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ B → ∀ ⦃y⦄, y ∈ B → key x = key y → (P x ↔ P y)

/-- The keyed exception estimate survives filtering by any predicate that
is constant on key cells.  This is the degree-accounting form: selecting
all endpoint-pair cells incident with a vertex does not pay a number-of-cells
factor. -/
theorem mul_card_filter_keyedLinearExceptions_le_two_mul
    {α : Type u} {κ : Type v}
    [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (B : Finset α) (key : α → κ) (weight : α → ℝ)
    (P : α → Prop) [DecidablePred P]
    {M : ℕ} (hM : 0 < M) (hconst : PredicateConstantOnKeyCells B key P) :
    M * ((keyedLinearExceptions B key weight M).filter P).card ≤
      2 * (B.filter P).card := by
  classical
  apply mul_card_filter_le_mul_card_filter_of_fiberwise
    (keyedLinearExceptions B key weight M) B key P M 2
  intro k
  by_cases hk : ∃ x ∈ B, key x = k ∧ P x
  · rcases hk with ⟨x, hxB, hxkey, hxP⟩
    have hPcell : ∀ y ∈ B, key y = k → P y := by
      intro y hyB hykey
      exact (hconst hxB hyB (hxkey.trans hykey.symm)).mp hxP
    have hleft :
        ((keyedLinearExceptions B key weight M).filter P).filter
            (fun y ↦ key y = k) =
          (keyedLinearExceptions B key weight M).filter
            (fun y ↦ key y = k) := by
      ext y
      simp only [Finset.mem_filter]
      constructor
      · exact fun hy ↦ ⟨hy.1.1, hy.2⟩
      · intro hy
        have hyB := keyedLinearExceptions_subset B key weight M hy.1
        exact ⟨⟨hy.1, hPcell y hyB hy.2⟩, hy.2⟩
    have hright :
        (B.filter P).filter (fun y ↦ key y = k) =
          B.filter (fun y ↦ key y = k) := by
      ext y
      simp only [Finset.mem_filter]
      constructor
      · exact fun hy ↦ ⟨hy.1.1, hy.2⟩
      · intro hy
        exact ⟨⟨hy.1, hPcell y hy.1 hy.2⟩, hy.2⟩
    rw [hleft, hright, filter_keyedLinearExceptions_eq B key weight M k]
    exact mul_card_linearCellExceptions_le_two_mul
      (B.filter fun y ↦ key y = k) weight hM
  · have hleft :
        ((keyedLinearExceptions B key weight M).filter P).filter
            (fun y ↦ key y = k) = ∅ := by
      ext y
      constructor
      · intro hy
        exfalso
        rcases Finset.mem_filter.mp hy with ⟨hyEP, hykey⟩
        rcases Finset.mem_filter.mp hyEP with ⟨hyE, hyP⟩
        exact hk ⟨y, keyedLinearExceptions_subset B key weight M hyE,
          hykey, hyP⟩
      · simp
    have hright :
        (B.filter P).filter (fun y ↦ key y = k) = ∅ := by
      ext y
      constructor
      · intro hy
        exfalso
        rcases Finset.mem_filter.mp hy with ⟨hyBP, hykey⟩
        rcases Finset.mem_filter.mp hyBP with ⟨hyB, hyP⟩
        exact hk ⟨y, hyB, hykey, hyP⟩
      · simp
    simp [hleft, hright]

end

end WeightedEdgeColoring
