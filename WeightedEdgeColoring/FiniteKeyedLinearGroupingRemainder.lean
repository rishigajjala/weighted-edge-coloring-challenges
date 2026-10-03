import WeightedEdgeColoring.FiniteKeyedLinearRoundedCover
import WeightedEdgeColoring.KeyedLinearExceptions

/-!
# Items outside the keyed linear-grouping target range

The target occurrences in `FiniteKeyedLinearRoundedCover` use all later
groups of every active key cell.  This file records their image in the
original item type.  An item outside that image is either in the first group
of an active cell or belongs to an inactive cell of size below `M`.

The active first groups cost at most `2|Item|/M` in total.  The inactive
cells cost at most `|κ| M`.  This gives the explicit finite remainder bound
needed by the graph-side packet assembly.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance
namespace KeyedLinearRoundedCover

noncomputable section

universe u v

variable {B : BinPackingInstance.{u}}
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
variable (key : B.Item → κ) (M : ℕ)

/-- The image of all actual later-group target occurrences. -/
def targetItems : Finset B.Item := by
  classical
  exact (Finset.univ : Finset (TargetOccurrence key M)).image
    (targetItem key M)

/-- Original items that do not occur in the later-group target range. -/
def nonTargetItems : Finset B.Item :=
  Finset.univ \ targetItems key M

/-- All items in cells that are too small to be activated. -/
def inactiveCellItems : Finset B.Item :=
  Finset.univ.filter fun i ↦ (cell key (key i)).card < M

/-- A convenient explicit superset of the target complement: active first
groups together with every inactive cell. -/
def groupingRemainder : Finset B.Item :=
  keyedLinearExceptions (Finset.univ : Finset B.Item) key B.weight M ∪
    inactiveCellItems key M

/-- The key cells partition the whole item type. -/
theorem sum_cell_card :
    (∑ a : κ, (cell key a).card) = Fintype.card B.Item := by
  simpa [cell] using
    (card_eq_sum_card_filter_fiber
      (Finset.univ : Finset B.Item) key).symm

/-- Fiberwise cardinality identity for the actual target complement. -/
theorem card_nonTargetItems_eq_sum_filter_key :
    (nonTargetItems key M).card =
      ∑ a : κ,
        ((nonTargetItems key M).filter fun i ↦ key i = a).card :=
  card_eq_sum_card_filter_fiber (nonTargetItems key M) key

/-- The canonical decreasing enumeration is an equivalence from ranks to
the objects of a finite cell. -/
def finiteCellItemEquiv (S : Finset B.Item) :
    Fin S.card ≃ {i : B.Item // i ∈ S} := by
  let f : Fin S.card → {i : B.Item // i ∈ S} := fun r ↦
    ⟨finiteCellItem S B.weight r, finiteCellItem_mem S B.weight r⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).2
  constructor
  · intro r s hrs
    apply finiteCellItem_injective S B.weight
    exact congrArg Subtype.val hrs
  · simp

/-- Every rank at or after the first group of an active cell is named by a
target occurrence. -/
theorem finiteCellItem_mem_targetItems_of_width_le
    (hM : 0 < M) (a : κ)
    (hactive : M ≤ (cell key a).card)
    (r : Fin (cell key a).card)
    (hr : width key M a ≤ r.1) :
    finiteCellItem (cell key a) B.weight r ∈ targetItems key M := by
  let m := (cell key a).card
  let k := width key M a
  have hm : 0 < m := lt_of_lt_of_le hM hactive
  have hk : 0 < k := by
    dsimp [k]
    exact linearGroupSize_pos hm hM
  let q := r.1 / k
  have hqmul : q * k ≤ r.1 := by
    dsimp [q]
    exact Nat.div_mul_le_self r.1 k
  have hmod : r.1 % k < k := Nat.mod_lt _ hk
  have hdecomp : k * (r.1 / k) + r.1 % k = r.1 :=
    Nat.div_add_mod r.1 k
  have hupper : r.1 < q * k + k := by
    dsimp [q]
    rw [Nat.mul_comm] at hdecomp
    omega
  have hqpos : 0 < q := by
    have hr' : k ≤ r.1 := by simpa [k] using hr
    dsimp [q]
    exact Nat.div_pos hr' hk
  have hcover : m ≤ k * M := by
    dsimp [m, k]
    exact le_linearGroupSize_mul_parameter (cell key a).card hM
  have hqM : q < M := by
    by_contra hnot
    have hMq : M ≤ q := Nat.le_of_not_gt hnot
    have hmul : M * k ≤ q * k := Nat.mul_le_mul_right k hMq
    have hcover' : m ≤ M * k := by simpa [Nat.mul_comm] using hcover
    exact (not_lt_of_ge (hcover'.trans (hmul.trans hqmul))) r.2
  let s : Fin (M - 1) := ⟨q - 1, by omega⟩
  have hstart : (q - 1) * k + k = q * k := by
    calc
      (q - 1) * k + k = (q - 1) * k + 1 * k := by simp
      _ = ((q - 1) + 1) * k := by rw [Nat.add_mul]
      _ = q * k := by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hqpos))]
  have hrLater : r ∈ laterIndices key M a s := by
    apply mem_linearGroupIndices.mpr
    change (q - 1) * k + k ≤ r.1 ∧
      r.1 < (q - 1) * k + k + k
    rw [hstart]
    exact ⟨hqmul, hupper⟩
  let z : RoundedItem (B := B) key M :=
    ⟨(a, s), hactive, ⟨r, hrLater⟩⟩
  let o : TargetOccurrence key M := ⟨z, ⟨r, hrLater⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨o, Finset.mem_univ _, ?_⟩
  rfl

/-- In an active cell, every item outside its first linear group belongs to
the actual target range. -/
theorem mem_targetItems_of_active_of_not_linearCellExceptions
    (hM : 0 < M) (i : B.Item)
    (hactive : M ≤ (cell key (key i)).card)
    (hnot : i ∉ linearCellExceptions
      (cell key (key i)) B.weight M) :
    i ∈ targetItems key M := by
  let S := cell key (key i)
  have hiS : i ∈ S := by simp [S, cell]
  let r : Fin S.card := (finiteCellItemEquiv (B := B) S).symm ⟨i, hiS⟩
  have hri : finiteCellItem S B.weight r = i := by
    have h := (finiteCellItemEquiv (B := B) S).apply_symm_apply ⟨i, hiS⟩
    exact congrArg Subtype.val h
  have hrNot : r ∉ linearExceptionalIndices S.card M := by
    intro hr
    apply hnot
    rw [linearCellExceptions, if_pos (by simpa [S] using hactive)]
    exact Finset.mem_image.mpr ⟨r, hr, hri⟩
  have hrWidth : linearGroupSize S.card M ≤ r.1 := by
    exact Nat.le_of_not_gt fun hlt ↦
      hrNot (mem_linearExceptionalIndices.mpr hlt)
  have htarget := finiteCellItem_mem_targetItems_of_width_le
    key M hM (key i) hactive r (by simpa [S, width] using hrWidth)
  simpa [S, hri] using htarget

/-- Every item outside the target range lies in an active first group or in
an inactive key cell. -/
theorem nonTargetItems_subset_groupingRemainder (hM : 0 < M) :
    nonTargetItems key M ⊆ groupingRemainder key M := by
  classical
  intro i hi
  have hiNotTarget := (Finset.mem_sdiff.mp hi).2
  by_cases hactive : M ≤ (cell key (key i)).card
  · by_cases hex : i ∈ keyedLinearExceptions
        (Finset.univ : Finset B.Item) key B.weight M
    · exact Finset.mem_union_left _ hex
    · have hlocal : i ∉ linearCellExceptions
          (cell key (key i)) B.weight M := by
        intro hiLocal
        apply hex
        apply Finset.mem_biUnion.mpr
        exact ⟨key i, Finset.mem_univ _, by simpa [cell] using hiLocal⟩
      exact (hiNotTarget
        (mem_targetItems_of_active_of_not_linearCellExceptions
          key M hM i hactive hlocal)).elim
  · have hsmall : (cell key (key i)).card < M := Nat.lt_of_not_ge hactive
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsmall⟩

/-- Inactive cells contain at most `M` items per possible key. -/
theorem card_inactiveCellItems_le :
    (inactiveCellItems key M).card ≤ Fintype.card κ * M := by
  classical
  rw [card_eq_sum_card_filter_fiber (inactiveCellItems key M) key]
  calc
    (∑ a : κ,
        ((inactiveCellItems key M).filter fun i ↦ key i = a).card) ≤
        ∑ _a : κ, M := by
      apply Finset.sum_le_sum
      intro a _ha
      let F := (inactiveCellItems key M).filter fun i ↦ key i = a
      by_cases hF : F.Nonempty
      · rcases hF with ⟨i, hiF⟩
        have hi := Finset.mem_filter.mp hiF
        have hiInactive := (Finset.mem_filter.mp hi.1).2
        have hsmall : (cell key a).card < M := by
          simpa [hi.2] using hiInactive
        have hsub : F ⊆ cell key a := by
          intro j hj
          have hjkey := (Finset.mem_filter.mp hj).2
          simp [cell, hjkey]
        exact (Finset.card_le_card hsub).trans hsmall.le
      · have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
        change F.card ≤ M
        rw [hz]
        exact Nat.zero_le _
    _ = Fintype.card κ * M := by simp

/-- Real form of the global active-first-group estimate. -/
theorem card_keyedLinearExceptions_le_two_mul_div (hM : 0 < M) :
    ((keyedLinearExceptions (Finset.univ : Finset B.Item)
      key B.weight M).card : ℝ) ≤
      2 * (Fintype.card B.Item : ℝ) / (M : ℝ) := by
  have hnat := mul_card_keyedLinearExceptions_le_two_mul
    (Finset.univ : Finset B.Item) key B.weight hM
  have hreal : (M : ℝ) *
      ((keyedLinearExceptions (Finset.univ : Finset B.Item)
        key B.weight M).card : ℝ) ≤
      2 * (Fintype.card B.Item : ℝ) := by
    exact_mod_cast (by simpa using hnat)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  apply (le_div_iff₀ hMR).2
  simpa [mul_comm] using hreal

/-- Explicit finite remainder bound for keyed linear grouping. -/
theorem card_nonTargetItems_le_two_mul_div_add_key_mul
    (hM : 0 < M) :
    ((nonTargetItems key M).card : ℝ) ≤
      2 * (Fintype.card B.Item : ℝ) / (M : ℝ) +
        (Fintype.card κ : ℝ) * M := by
  have hsub := Finset.card_le_card
    (nonTargetItems_subset_groupingRemainder key M hM)
  have hunion := Finset.card_union_le
    (keyedLinearExceptions (Finset.univ : Finset B.Item) key B.weight M)
    (inactiveCellItems key M)
  have hnat : (nonTargetItems key M).card ≤
      (keyedLinearExceptions (Finset.univ : Finset B.Item)
        key B.weight M).card + (inactiveCellItems key M).card :=
    hsub.trans (by simpa [groupingRemainder] using hunion)
  have hnatReal : ((nonTargetItems key M).card : ℝ) ≤
      ((keyedLinearExceptions (Finset.univ : Finset B.Item)
        key B.weight M).card : ℝ) +
        ((inactiveCellItems key M).card : ℝ) := by
    exact_mod_cast hnat
  have hactive := card_keyedLinearExceptions_le_two_mul_div key M hM
  have hinactive : ((inactiveCellItems key M).card : ℝ) ≤
      (Fintype.card κ : ℝ) * M := by
    exact_mod_cast card_inactiveCellItems_le key M
  linarith

end


end KeyedLinearRoundedCover
end BinPackingInstance
end WeightedEdgeColoring
