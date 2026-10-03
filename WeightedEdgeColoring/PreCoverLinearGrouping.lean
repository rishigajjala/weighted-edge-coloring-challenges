import WeightedEdgeColoring.BPGeneralFiniteClassDegree
import WeightedEdgeColoring.FiniteExactDemandFloorRemainderBound

/-!
# Linear grouping before exact-demand covers

This file isolates the deterministic part of the linear-grouping reduction.
Inside one finite cell, number the objects in nonincreasing weight order and
put consecutive ranks into blocks of width `ceil (m / M)`.  The first block
is exceptional.  Every later block injects into the preceding block by
subtracting the block width.  Rounding a later block to the weight of its
first object is safe because every image in the preceding block is at least
that heavy.

The statements are independent of a cover or a coloring.  In particular,
`linearGroupDemand_le_previous` is the coordinatewise demand inequality that
can be fed into an exact-demand construction later.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u

/-- A finite cell, canonically sorted in nonincreasing weight order. -/
def finiteCellByDecreasingWeight {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → ℝ) : List α :=
  S.toList.mergeSort fun x y ↦ decide (weight y ≤ weight x)

theorem finiteCellByDecreasingWeight_pairwise
    {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → ℝ) :
    (finiteCellByDecreasingWeight S weight).Pairwise
      (fun x y ↦ weight y ≤ weight x) := by
  have hsorted := List.pairwise_mergeSort
    (le := fun x y : α ↦ decide (weight y ≤ weight x))
    (fun a b c hab hbc ↦ by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact hbc.trans hab)
    (fun a b ↦ by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total (weight b) (weight a))
    S.toList
  simpa [finiteCellByDecreasingWeight] using hsorted

@[simp] theorem length_finiteCellByDecreasingWeight
    {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → ℝ) :
    (finiteCellByDecreasingWeight S weight).length = S.card := by
  simp [finiteCellByDecreasingWeight]

theorem mem_finiteCellByDecreasingWeight
    {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → ℝ) (x : α) :
    x ∈ finiteCellByDecreasingWeight S weight ↔ x ∈ S := by
  simp [finiteCellByDecreasingWeight]

/-- The object at a rank in the canonical decreasing ordering of a cell. -/
def finiteCellItem {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → ℝ) (i : Fin S.card) : α :=
  (finiteCellByDecreasingWeight S weight).get
    ⟨i.1, by simpa using i.2⟩

theorem finiteCellItem_mem
    {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → ℝ) (i : Fin S.card) :
    finiteCellItem S weight i ∈ S := by
  rw [← mem_finiteCellByDecreasingWeight S weight]
  exact List.get_mem _ _

/-- Distinct ranks in the canonical ordering name distinct objects. -/
theorem finiteCellItem_injective
    {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → ℝ) :
    Function.Injective (finiteCellItem S weight) := by
  intro i j hij
  apply Fin.ext
  by_contra hne
  have hnodup : (finiteCellByDecreasingWeight S weight).Nodup := by
    rw [finiteCellByDecreasingWeight, List.nodup_mergeSort]
    exact S.nodup_toList
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hneq := (List.pairwise_iff_getElem.mp hnodup)
      i.1 j.1 (by simpa using i.2) (by simpa using j.2) hlt
    exact hneq (by
      simpa [finiteCellItem, List.get_eq_getElem] using hij)
  · have hneq := (List.pairwise_iff_getElem.mp hnodup)
      j.1 i.1 (by simpa using j.2) (by simpa using i.2) hlt
    exact hneq (by
      simpa [finiteCellItem, List.get_eq_getElem] using hij.symm)

/-- Increasing the rank in the canonical ordering cannot increase weight. -/
theorem finiteCellItem_weight_antitone
    {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → ℝ) (i j : Fin S.card)
    (hij : i.1 ≤ j.1) :
    weight (finiteCellItem S weight j) ≤
      weight (finiteCellItem S weight i) := by
  rcases hij.eq_or_lt with hij | hij
  · have hfin : i = j := Fin.ext hij
    subst j
    exact le_rfl
  · have hi : i.1 < (finiteCellByDecreasingWeight S weight).length := by
      simpa using i.2
    have hj : j.1 < (finiteCellByDecreasingWeight S weight).length := by
      simpa using j.2
    have hrel := (List.pairwise_iff_getElem.mp
      (finiteCellByDecreasingWeight_pairwise S weight))
      i.1 j.1 hi hj hij
    simpa [finiteCellItem, List.get_eq_getElem] using hrel

/-- Width used by linear grouping of `m` objects into about `M` blocks. -/
def linearGroupSize (m M : ℕ) : ℕ :=
  Nat.ceil ((m : ℝ) / (M : ℝ))

/-- Consecutive ranks in the half-open interval `[a, a + k)`. -/
def linearGroupIndices (m k a : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ a ≤ i.1 ∧ i.1 < a + k

/-- Group number `g` in the canonical grouping with parameter `M`. -/
def linearNumberedGroup (m M g : ℕ) : Finset (Fin m) :=
  linearGroupIndices m (linearGroupSize m M) (g * linearGroupSize m M)

/-- The first group, which is discarded by the pre-cover reduction. -/
def linearExceptionalIndices (m M : ℕ) : Finset (Fin m) :=
  linearGroupIndices m (linearGroupSize m M) 0

@[simp] theorem mem_linearGroupIndices {m k a : ℕ} {i : Fin m} :
    i ∈ linearGroupIndices m k a ↔ a ≤ i.1 ∧ i.1 < a + k := by
  simp [linearGroupIndices]

@[simp] theorem mem_linearExceptionalIndices {m M : ℕ} {i : Fin m} :
    i ∈ linearExceptionalIndices m M ↔ i.1 < linearGroupSize m M := by
  simp [linearExceptionalIndices]

/-- A positive-size cell has positive group width when `M` is positive. -/
theorem linearGroupSize_pos {m M : ℕ} (hm : 0 < m) (hM : 0 < M) :
    0 < linearGroupSize m M := by
  apply Nat.ceil_pos.mpr
  positivity

/-- The chosen ceiling width covers all `m` ranks in at most `M` groups. -/
theorem le_linearGroupSize_mul_parameter (m : ℕ) {M : ℕ} (hM : 0 < M) :
    m ≤ linearGroupSize m M * M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hceil : (m : ℝ) / (M : ℝ) ≤ linearGroupSize m M :=
    Nat.le_ceil ((m : ℝ) / (M : ℝ))
  have hmul : (m : ℝ) ≤
      (linearGroupSize m M : ℝ) * (M : ℝ) :=
    (div_le_iff₀ hMR).mp hceil
  exact_mod_cast hmul

/-- Every nonempty numbered group has number below `M`.  Thus a cell has at
most `M` representatives (and at most `M-1` retained representatives after
discarding group zero). -/
theorem linearNumberedGroup_nonempty_index_lt
    {m M g : ℕ} (hm : 0 < m) (hM : 0 < M)
    (hne : (linearNumberedGroup m M g).Nonempty) : g < M := by
  rcases hne with ⟨i, hi⟩
  have hi' := mem_linearGroupIndices.mp hi
  have hk : 0 < linearGroupSize m M := linearGroupSize_pos hm hM
  have hstart : g * linearGroupSize m M < m :=
    hi'.1.trans_lt i.2
  have hmul : g * linearGroupSize m M <
      linearGroupSize m M * M :=
    hstart.trans_le (le_linearGroupSize_mul_parameter m hM)
  have hmul' : g * linearGroupSize m M <
      M * linearGroupSize m M := by
    simpa [Nat.mul_comm] using hmul
  exact (Nat.mul_lt_mul_right hk).mp hmul'

/-- The exceptional set has the exact expected truncated cardinality. -/
theorem card_linearExceptionalIndices (m M : ℕ) :
    (linearExceptionalIndices m M).card =
      min m (linearGroupSize m M) := by
  let k := linearGroupSize m M
  let e : {i : Fin m // i ∈ linearExceptionalIndices m M} ≃
      Fin (min m k) :=
    { toFun := fun i ↦
        ⟨i.1.1, (Nat.lt_min).2 ⟨i.1.2,
          (mem_linearExceptionalIndices.mp i.2)⟩⟩
      invFun := fun i ↦
        ⟨⟨i.1, ((Nat.lt_min).1 i.2).1⟩,
          mem_linearExceptionalIndices.mpr ((Nat.lt_min).1 i.2).2⟩
      left_inv := fun i ↦ by simp
      right_inv := fun i ↦ by simp }
  calc
    (linearExceptionalIndices m M).card =
        Fintype.card {i : Fin m // i ∈ linearExceptionalIndices m M} := by
      rw [Fintype.card_coe]
    _ = Fintype.card (Fin (min m k)) := Fintype.card_congr e
    _ = min m (linearGroupSize m M) := by simp [k]

/-- At most one group width is discarded from a cell. -/
theorem card_linearExceptionalIndices_le (m M : ℕ) :
    (linearExceptionalIndices m M).card ≤ linearGroupSize m M := by
  rw [card_linearExceptionalIndices]
  exact min_le_right _ _

/-- When `m ≥ M > 0`, the group width is at most `2m/M`.

This is the ceiling estimate used in the asymptotic exception count. -/
theorem linearGroupSize_le_two_mul_div {m M : ℕ}
    (hM : 0 < M) (hMm : M ≤ m) :
    (linearGroupSize m M : ℝ) ≤ 2 * (m : ℝ) / (M : ℝ) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hratio0 : 0 ≤ (m : ℝ) / (M : ℝ) := by positivity
  have hceil : (linearGroupSize m M : ℝ) ≤
      (m : ℝ) / (M : ℝ) + 1 := by
    exact (Nat.ceil_lt_add_one hratio0).le
  have hratio1 : (1 : ℝ) ≤ (m : ℝ) / (M : ℝ) := by
    apply (le_div_iff₀ hMR).2
    simpa using (show (M : ℝ) ≤ m by exact_mod_cast hMm)
  calc
    (linearGroupSize m M : ℝ) ≤ (m : ℝ) / (M : ℝ) + 1 := hceil
    _ ≤ 2 * (m : ℝ) / (M : ℝ) := by
      rw [show 2 * (m : ℝ) / (M : ℝ) =
        2 * ((m : ℝ) / (M : ℝ)) by ring]
      linarith

/-- The complete exact exception estimate for a nonempty parameter range. -/
theorem card_linearExceptionalIndices_le_two_mul_div {m M : ℕ}
    (hM : 0 < M) (hMm : M ≤ m) :
    ((linearExceptionalIndices m M).card : ℝ) ≤
      2 * (m : ℝ) / (M : ℝ) := by
  have hcard : ((linearExceptionalIndices m M).card : ℝ) ≤
      (linearGroupSize m M : ℝ) := by
    exact_mod_cast card_linearExceptionalIndices_le m M
  exact hcard.trans (linearGroupSize_le_two_mul_div hM hMm)

/-- Every consecutive group has at most its prescribed width. -/
theorem card_linearGroupIndices_le (m k a : ℕ) :
    (linearGroupIndices m k a).card ≤ k := by
  let f : {i : Fin m // i ∈ linearGroupIndices m k a} → Fin k := fun i ↦
    ⟨i.1.1 - a, by
      have hi := mem_linearGroupIndices.mp i.2
      omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    have hval := congrArg Fin.val hij
    have hi := mem_linearGroupIndices.mp i.2
    have hj := mem_linearGroupIndices.mp j.2
    dsimp [f] at hval
    omega
  rw [← Fintype.card_coe]
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- The rank obtained by moving one group width to the left. -/
def previousLinearIndex {m : ℕ} (k : ℕ) (i : Fin m) : Fin m :=
  ⟨i.1 - k, (Nat.sub_le i.1 k).trans_lt i.2⟩

@[simp] theorem previousLinearIndex_val {m : ℕ} (k : ℕ) (i : Fin m) :
    (previousLinearIndex k i).1 = i.1 - k := rfl

/-- Subtracting the group width embeds a later group into the immediately
preceding group. -/
def previousLinearGroupEmbedding (m k a : ℕ) :
    {i : Fin m // i ∈ linearGroupIndices m k (a + k)} ↪
      {i : Fin m // i ∈ linearGroupIndices m k a} where
  toFun i := by
    have hi := mem_linearGroupIndices.mp i.2
    refine ⟨previousLinearIndex k i.1, ?_⟩
    apply mem_linearGroupIndices.mpr
    change a ≤ i.1.1 - k ∧ i.1.1 - k < a + k
    omega
  inj' := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    have hval := congrArg (fun z ↦ z.1.1) hij
    have hi := mem_linearGroupIndices.mp i.2
    have hj := mem_linearGroupIndices.mp j.2
    dsimp at hval
    omega

@[simp] theorem previousLinearGroupEmbedding_val
    (m k a : ℕ)
    (i : {i : Fin m // i ∈ linearGroupIndices m k (a + k)}) :
    (previousLinearGroupEmbedding m k a i).1.1 = i.1.1 - k := by
  rfl

/-- The first rank of a nonempty later group, obtained from any member of
that group. -/
def linearGroupRepresentative (m k a : ℕ)
    (i : {i : Fin m // i ∈ linearGroupIndices m k (a + k)}) : Fin m := by
  have hi := mem_linearGroupIndices.mp i.2
  exact ⟨a + k, by omega⟩

@[simp] theorem linearGroupRepresentative_val
    (m k a : ℕ)
    (i : {i : Fin m // i ∈ linearGroupIndices m k (a + k)}) :
    (linearGroupRepresentative m k a i).1 = a + k := rfl

/-- The preceding image lies strictly before the rounded representative. -/
theorem previousLinearGroupEmbedding_lt_representative
    {m k a : ℕ} (_hk : 0 < k)
    (i : {i : Fin m // i ∈ linearGroupIndices m k (a + k)}) :
    (previousLinearGroupEmbedding m k a i).1.1 <
      (linearGroupRepresentative m k a i).1 := by
  have hi := mem_linearGroupIndices.mp i.2
  simp only [previousLinearGroupEmbedding_val,
    linearGroupRepresentative_val]
  omega

/-- Rounding every object in a later group to its first (heaviest) object is
dominated by the corresponding original object in the preceding group. -/
theorem roundedLinearWeight_le_previous
    {m k a : ℕ} (weight : Fin m → ℝ)
    (hdecreasing : ∀ i j : Fin m, i.1 ≤ j.1 → weight j ≤ weight i)
    (hk : 0 < k)
    (i : {i : Fin m // i ∈ linearGroupIndices m k (a + k)}) :
    weight (linearGroupRepresentative m k a i) ≤
      weight (previousLinearGroupEmbedding m k a i) := by
  apply hdecreasing
  exact (previousLinearGroupEmbedding_lt_representative hk i).le

/-- Canonical finite-cell specialization of the preceding dominance lemma. -/
theorem roundedFiniteCellWeight_le_previous
    {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → ℝ) {k a : ℕ} (hk : 0 < k)
    (i : {i : Fin S.card //
      i ∈ linearGroupIndices S.card k (a + k)}) :
    weight (finiteCellItem S weight
        (linearGroupRepresentative S.card k a i)) ≤
      weight (finiteCellItem S weight
        (previousLinearGroupEmbedding S.card k a i)) := by
  apply roundedLinearWeight_le_previous
    (fun j ↦ weight (finiteCellItem S weight j))
    (finiteCellItem_weight_antitone S weight) hk i

/-- In a cell of one external type, the canonical predecessor is both
type preserving and heavy enough to dominate the rounded representative. -/
theorem finiteCell_previous_type_and_weight
    {α : Type u} [Fintype α] [DecidableEq α]
    {ι : Type*} (S : Finset α) (weight : α → ℝ) (kind : α → ι)
    (t₀ : ι) (hcell : ∀ x ∈ S, kind x = t₀)
    {k a : ℕ} (hk : 0 < k)
    (i : {i : Fin S.card //
      i ∈ linearGroupIndices S.card k (a + k)}) :
    kind (finiteCellItem S weight
        (previousLinearGroupEmbedding S.card k a i)) =
        kind (finiteCellItem S weight i) ∧
      weight (finiteCellItem S weight
          (linearGroupRepresentative S.card k a i)) ≤
        weight (finiteCellItem S weight
          (previousLinearGroupEmbedding S.card k a i)) := by
  constructor
  · rw [hcell _ (finiteCellItem_mem S weight _),
      hcell _ (finiteCellItem_mem S weight _)]
  · exact roundedFiniteCellWeight_le_previous S weight hk i

/-- Counts one type coordinate in one consecutive group. -/
def linearGroupDemand {ι : Type*} [DecidableEq ι]
    {m : ℕ} (kind : Fin m → ι) (k a : ℕ) (t : ι) : ℕ :=
  ((linearGroupIndices m k a).filter fun i ↦ kind i = t).card

/-- A type-preserving predecessor injection gives the coordinatewise demand
inequality needed before constructing exact-demand covers. -/
theorem linearGroupDemand_le_previous
    {ι : Type*} [DecidableEq ι] {m k a : ℕ}
    (kind : Fin m → ι)
    (htype : ∀ i : {i : Fin m // i ∈ linearGroupIndices m k (a + k)},
      kind (previousLinearGroupEmbedding m k a i) = kind i)
    (t : ι) :
    linearGroupDemand kind k (a + k) t ≤ linearGroupDemand kind k a t := by
  let source := (linearGroupIndices m k (a + k)).filter fun i ↦ kind i = t
  let target := (linearGroupIndices m k a).filter fun i ↦ kind i = t
  let f : {i : Fin m // i ∈ source} → {i : Fin m // i ∈ target} := fun i ↦ by
    let j : {i : Fin m // i ∈ linearGroupIndices m k (a + k)} :=
      ⟨i.1, (Finset.mem_filter.mp i.2).1⟩
    refine ⟨previousLinearGroupEmbedding m k a j, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨(previousLinearGroupEmbedding m k a j).2, ?_⟩
    rw [htype j]
    exact (Finset.mem_filter.mp i.2).2
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    have hval := congrArg (fun z ↦ z.1.1) hij
    have hi := mem_linearGroupIndices.mp (Finset.mem_filter.mp i.2).1
    have hj := mem_linearGroupIndices.mp (Finset.mem_filter.mp j.2).1
    simp only [f, previousLinearGroupEmbedding_val] at hval
    omega
  change source.card ≤ target.card
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_le_of_injective f hf

/-- In a single cell all ranks have the same external type, so the
predecessor embedding is automatically type preserving. -/
theorem linearGroupDemand_le_previous_of_constant
    {ι : Type*} [DecidableEq ι] {m k a : ℕ}
    (kind : Fin m → ι) (t₀ : ι) (hcell : ∀ i, kind i = t₀) (t : ι) :
    linearGroupDemand kind k (a + k) t ≤ linearGroupDemand kind k a t := by
  apply linearGroupDemand_le_previous kind (t := t)
  intro i
  rw [hcell, hcell]

/-- Coordinatewise demand domination for a canonically sorted finite cell of
one external type. -/
theorem finiteCell_linearGroupDemand_le_previous
    {α : Type u} [Fintype α] [DecidableEq α]
    {ι : Type*} [DecidableEq ι]
    (S : Finset α) (weight : α → ℝ) (kind : α → ι)
    (t₀ : ι) (hcell : ∀ x ∈ S, kind x = t₀)
    (k a : ℕ) (t : ι) :
    linearGroupDemand (fun i ↦ kind (finiteCellItem S weight i))
        k (a + k) t ≤
      linearGroupDemand (fun i ↦ kind (finiteCellItem S weight i))
        k a t := by
  apply linearGroupDemand_le_previous_of_constant
    (fun i ↦ kind (finiteCellItem S weight i)) t₀
  intro i
  exact hcell _ (finiteCellItem_mem S weight i)

namespace WeightedMultigraph

/-- Exception accounting for pre-cover linear grouping.  Once the chosen
exceptional edges lie in the first `T` harmonic classes, the established
finite-class degree lemma bounds them by `n(T+1)` at every vertex. -/
theorem degreeOn_preCoverExceptions_le
    (G : WeightedMultigraph.{u}) {n T : ℕ} (X : Finset G.E)
    (hX : X ⊆ G.finiteHarmonicHeadEdges T)
    (hlocal : G.LocallyPacksInto n) (v : G.V) :
    G.degreeOn X v ≤ n * (T + 1) := by
  apply (Finset.card_le_card ?_).trans
    (G.degreeOn_finiteHarmonicHeadEdges_le T hlocal v)
  intro e he
  simp only [Finset.mem_filter] at he ⊢
  exact ⟨hX he.1, he.2⟩

end WeightedMultigraph

end


end WeightedEdgeColoring
