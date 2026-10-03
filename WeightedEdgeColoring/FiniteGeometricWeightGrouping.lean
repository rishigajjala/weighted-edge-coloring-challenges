import WeightedEdgeColoring.FiniteBlockGrouping

open scoped BigOperators
open Finset

namespace WeightedEdgeColoring

/-! # Grouping finite geometric weight classes -/

/-- The elements of `S` assigned to bucket `i`. -/
def weightClass {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (S : Finset α) (bucket : α → ι) (i : ι) : Finset α :=
  S.filter fun a ↦ bucket a = i

/-- A finite bucket map is a geometric weight classification at ratio `κ` if
all weights are positive and any two items in one bucket differ by at most a
factor `κ` in either ordered direction. -/
def IsGeometricWeightClassing {α ι : Type*} [DecidableEq α]
    (S : Finset α) (w : α → ℝ) (κ : ℝ) (bucket : α → ι) : Prop :=
  (∀ a ∈ S, 0 < w a) ∧
  ∀ i, ∀ a ∈ S, bucket a = i → ∀ b ∈ S, bucket b = i → w a ≤ κ * w b

private theorem exists_weightClass_finpartition {α ι : Type*}
    [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (S : Finset α) (bucket : α → ι) :
    ∃ P : Finpartition S,
      ∀ A ∈ P.parts, ∃ i, A = weightClass S bucket i := by
  classical
  let C : Finset (Finset α) :=
    ((Finset.univ : Finset ι).image (weightClass S bucket)).erase ∅
  have hsubset : ∀ A ∈ C, A ⊆ S := by
    intro A hA
    simp only [C, Finset.mem_erase, Finset.mem_image] at hA
    rcases hA.2 with ⟨i, _hi, rfl⟩
    exact Finset.filter_subset _ _
  have hunique : ∀ a ∈ S, ∃! A, A ∈ C ∧ a ∈ A := by
    intro a ha
    refine ⟨weightClass S bucket (bucket a), ?_, ?_⟩
    · constructor
      · simp only [C, Finset.mem_erase, Finset.mem_image]
        constructor
        · intro hempty
          have : a ∈ (∅ : Finset α) := by
            rw [← hempty]
            exact Finset.mem_filter.mpr ⟨ha, rfl⟩
          simpa using this
        · exact ⟨bucket a, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_filter.mpr ⟨ha, rfl⟩
    · intro A hA
      rcases hA.1 with hAC
      simp only [C, Finset.mem_erase, Finset.mem_image] at hAC
      rcases hAC.2 with ⟨i, _hi, rfl⟩
      have hai : bucket a = i := (Finset.mem_filter.mp hA.2).2
      subst i
      rfl
  let P : Finpartition S := Finpartition.ofExistsUnique C hsubset hunique
    (by simp [C])
  refine ⟨P, ?_⟩
  intro A hA
  change A ∈ C at hA
  simp only [C, Finset.mem_erase, Finset.mem_image] at hA
  exact hA.2.imp fun i hi ↦ hi.2.symm

/-- A block of fewer than `K` items in one geometric class has
weight at most `(K-1)` times the class-scale bound `κ * w b`, for any item
`b` in that block. This is the local leftover-weight estimate; summing it over
classes gives the corresponding global bound once class representatives are
chosen. -/
theorem geometric_small_block_weight_le {α ι : Type*}
    [DecidableEq α] [DecidableEq ι]
    (S T : Finset α) (w : α → ℝ) (κ : ℝ) (bucket : α → ι)
    (K : ℕ) (hκ : 1 < κ)
    (hgeom : IsGeometricWeightClassing S w κ bucket)
    (i : ι) (hT : T ⊆ weightClass S bucket i) (hcard : T.card < K)
    (b : α) (hb : b ∈ T) :
    (∑ a ∈ T, w a) ≤ (K - 1 : ℕ) * (κ * w b) := by
  have hbClass := hT hb
  have hbS : b ∈ S := (Finset.mem_filter.mp hbClass).1
  have hbBucket : bucket b = i := (Finset.mem_filter.mp hbClass).2
  have hκ0 : 0 ≤ κ := (lt_trans (by norm_num) hκ).le
  have hwb0 : 0 ≤ w b := (hgeom.1 b hbS).le
  calc
    (∑ a ∈ T, w a) ≤ ∑ _a ∈ T, κ * w b := by
      apply Finset.sum_le_sum
      intro a ha
      have haClass := hT ha
      exact hgeom.2 i a (Finset.mem_filter.mp haClass).1
        (Finset.mem_filter.mp haClass).2 b hbS hbBucket
    _ = (T.card : ℕ) * (κ * w b) := by simp
    _ ≤ (K - 1 : ℕ) * (κ * w b) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (Nat.le_pred_of_lt hcard)
      · exact mul_nonneg hκ0 hwb0

/-- Finite geometric classes can be refined into blocks. A block is either
full, with size from `K` through `2*K-1`, or it is the sole leftover block of
its class and has fewer than `K` elements. Every block stays inside one
geometric class, so its weights remain within factor `κ`. -/
theorem exists_geometric_block_finpartition {α ι : Type*}
    [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (S : Finset α) (w : α → ℝ) (κ : ℝ) (bucket : α → ι)
    (K : ℕ) (_hκ : 1 < κ) (hK : 0 < K)
    (hgeom : IsGeometricWeightClassing S w κ bucket) :
    ∃ P : Finpartition S,
      ∀ T ∈ P.parts,
        ((K ≤ T.card ∧ T.card ≤ 2 * K - 1) ∨ T.card < K) ∧
        (∃ i, T ⊆ weightClass S bucket i) ∧
        (∀ a ∈ T, ∀ b ∈ T, w a ≤ κ * w b) := by
  classical
  obtain ⟨C, hC⟩ := exists_weightClass_finpartition S bucket
  let Q : ∀ A ∈ C.parts, Finpartition A := fun A hA ↦
    if hlarge : K ≤ A.card then
      Classical.choose (exists_finpartition_card_between A K hK hlarge)
    else Finpartition.indiscrete (C.nonempty_of_mem_parts hA).ne_empty
  have hQlarge : ∀ A (hA : A ∈ C.parts), K ≤ A.card →
      ∀ T ∈ (Q A hA).parts, K ≤ T.card ∧ T.card ≤ 2 * K - 1 := by
    intro A hA hlarge T hT
    simp only [Q, dif_pos hlarge] at hT ⊢
    exact (Classical.choose_spec
      (exists_finpartition_card_between A K hK hlarge)) T hT
  have hQsmall : ∀ A (hA : A ∈ C.parts), ¬K ≤ A.card →
      (Q A hA).parts = {A} := by
    intro A hA hsmall
    simp [Q, hsmall, Finpartition.indiscrete]
  refine ⟨C.bind Q, ?_⟩
  intro T hT
  rw [Finpartition.mem_bind] at hT
  rcases hT with ⟨A, hA, hTA⟩
  have hclass := hC A hA
  rcases hclass with ⟨i, rfl⟩
  have hTsub : T ⊆ weightClass S bucket i :=
    (Q (weightClass S bucket i) hA).le hTA
  refine ⟨?_, ⟨i, hTsub⟩, ?_⟩
  · by_cases hlarge : K ≤ (weightClass S bucket i).card
    · exact Or.inl (hQlarge _ hA hlarge T hTA)
    · right
      have hparts := hQsmall _ hA hlarge
      rw [hparts] at hTA
      have hEq : T = weightClass S bucket i := by simpa using hTA
      subst T
      omega
  · intro a ha b hb
    have haClass := hTsub ha
    have hbClass := hTsub hb
    exact hgeom.2 i a (Finset.mem_filter.mp haClass).1
      (Finset.mem_filter.mp haClass).2 b
      (Finset.mem_filter.mp hbClass).1 (Finset.mem_filter.mp hbClass).2


/-- Strengthened geometric grouping: a small part contained in bucket `i` is
exactly that whole bucket. Consequently each bucket contains at most one small
part. -/
theorem exists_geometric_block_finpartition_small_eq_class {α ι : Type*}
    [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (S : Finset α) (w : α → ℝ) (κ : ℝ) (bucket : α → ι)
    (K : ℕ) (_hκ : 1 < κ) (hK : 0 < K)
    (hgeom : IsGeometricWeightClassing S w κ bucket) :
    ∃ P : Finpartition S,
      (∀ T ∈ P.parts,
        ((K ≤ T.card ∧ T.card ≤ 2 * K - 1) ∨ T.card < K) ∧
        (∃ i, T ⊆ weightClass S bucket i) ∧
        (∀ a ∈ T, ∀ b ∈ T, w a ≤ κ * w b)) ∧
      (∀ i T, T ∈ P.parts → T.card < K →
        T ⊆ weightClass S bucket i → T = weightClass S bucket i) := by
  classical
  obtain ⟨C, hC⟩ := exists_weightClass_finpartition S bucket
  let Q : ∀ A ∈ C.parts, Finpartition A := fun A hA ↦
    if hlarge : K ≤ A.card then
      Classical.choose (exists_finpartition_card_between A K hK hlarge)
    else Finpartition.indiscrete (C.nonempty_of_mem_parts hA).ne_empty
  have hQlarge : ∀ A (hA : A ∈ C.parts), K ≤ A.card →
      ∀ T ∈ (Q A hA).parts, K ≤ T.card ∧ T.card ≤ 2 * K - 1 := by
    intro A hA hlarge T hT
    simp only [Q, dif_pos hlarge] at hT ⊢
    exact (Classical.choose_spec
      (exists_finpartition_card_between A K hK hlarge)) T hT
  have hQsmall : ∀ A (hA : A ∈ C.parts), ¬K ≤ A.card →
      (Q A hA).parts = {A} := by
    intro A hA hsmall
    simp [Q, hsmall, Finpartition.indiscrete]
  let P : Finpartition S := C.bind Q
  have hsource : ∀ T ∈ P.parts,
      ∃ A, ∃ hA : A ∈ C.parts, T ∈ (Q A hA).parts := by
    intro T hT
    exact Finpartition.mem_bind.mp hT
  have hprops : ∀ T ∈ P.parts,
      ((K ≤ T.card ∧ T.card ≤ 2 * K - 1) ∨ T.card < K) ∧
      (∃ i, T ⊆ weightClass S bucket i) ∧
      (∀ a ∈ T, ∀ b ∈ T, w a ≤ κ * w b) := by
    intro T hT
    rcases hsource T hT with ⟨A, hA, hTA⟩
    rcases hC A hA with ⟨i, rfl⟩
    have hTsub : T ⊆ weightClass S bucket i :=
      (Q (weightClass S bucket i) hA).le hTA
    refine ⟨?_, ⟨i, hTsub⟩, ?_⟩
    · by_cases hlarge : K ≤ (weightClass S bucket i).card
      · exact Or.inl (hQlarge _ hA hlarge T hTA)
      · right
        have hparts := hQsmall _ hA hlarge
        rw [hparts] at hTA
        have hEq : T = weightClass S bucket i := by simpa using hTA
        subst T
        omega
    · intro a ha b hb
      have haClass := hTsub ha
      have hbClass := hTsub hb
      exact hgeom.2 i a (Finset.mem_filter.mp haClass).1
        (Finset.mem_filter.mp haClass).2 b
        (Finset.mem_filter.mp hbClass).1 (Finset.mem_filter.mp hbClass).2
  refine ⟨P, hprops, ?_⟩
  intro i T hTP hTsmall hTi
  rcases hsource T hTP with ⟨A, hA, hTA⟩
  rcases hC A hA with ⟨j, rfl⟩
  have hnotlarge : ¬K ≤ (weightClass S bucket j).card := by
    intro hlarge
    have := (hQlarge _ hA hlarge T hTA).1
    omega
  have hparts := hQsmall _ hA hnotlarge
  rw [hparts] at hTA
  have hTj : T = weightClass S bucket j := by simpa using hTA
  have hTnonempty : T.Nonempty := P.nonempty_of_mem_parts hTP
  obtain ⟨a, haT⟩ := hTnonempty
  have haj : bucket a = j := by
    have : a ∈ weightClass S bucket j := hTj ▸ haT
    exact (Finset.mem_filter.mp this).2
  have hai : bucket a = i :=
    (Finset.mem_filter.mp (hTi haT)).2
  have hji : j = i := haj.symm.trans hai
  exact hTj.trans (congrArg (weightClass S bucket) hji)

/-- In the strengthened grouping, two small parts assigned to the same bucket
are equal. -/
theorem exists_geometric_block_finpartition_small_unique {α ι : Type*}
    [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (S : Finset α) (w : α → ℝ) (κ : ℝ) (bucket : α → ι)
    (K : ℕ) (hκ : 1 < κ) (hK : 0 < K)
    (hgeom : IsGeometricWeightClassing S w κ bucket) :
    ∃ P : Finpartition S,
      (∀ T ∈ P.parts,
        ((K ≤ T.card ∧ T.card ≤ 2 * K - 1) ∨ T.card < K) ∧
        (∃ i, T ⊆ weightClass S bucket i) ∧
        (∀ a ∈ T, ∀ b ∈ T, w a ≤ κ * w b)) ∧
      (∀ i T, T ∈ P.parts → T.card < K →
        T ⊆ weightClass S bucket i →
        ∀ U, U ∈ P.parts → U.card < K →
          U ⊆ weightClass S bucket i → T = U) := by
  obtain ⟨P, hP, hsmall⟩ :=
    exists_geometric_block_finpartition_small_eq_class
      S w κ bucket K hκ hK hgeom
  refine ⟨P, hP, ?_⟩
  intro i T hTP hTc hTi U hUP hUc hUi
  rw [hsmall i T hTP hTc hTi, hsmall i U hUP hUc hUi]

end WeightedEdgeColoring
