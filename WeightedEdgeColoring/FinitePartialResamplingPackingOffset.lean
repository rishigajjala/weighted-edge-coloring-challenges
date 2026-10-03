import WeightedEdgeColoring.FinitePartialResamplingPackingSelection

/-!
# Packing selection with a deterministic row offset

Sequential applications of the categorical packing selector need to keep
load already fixed in earlier passes.  This file absorbs a nonnegative
deterministic offset into the selector by adding `K` dummy sources for every
row.  Each dummy source contributes `offset r / K` only to its own row, so
its column sum is at most one.  The dummy state law is arbitrary and its
state is irrelevant to the contribution.
-/

namespace WeightedEdgeColoring.FiniteCategoricalSelection

open scoped BigOperators
open FinitePartialResamplingNumerics

noncomputable section

universe uSource uState uRow

variable {Source : Type uSource} {State : Type uState} {Row : Type uRow}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype Row] [DecidableEq Row]

/-- Sources used only to encode a deterministic row offset. -/
private abbrev OffsetSource (Row : Type uRow) (K : ℕ) := Row × Fin K

/-- The probability law on original and dummy sources. -/
private def offsetProb
    (prob : Source → State → ℝ) (dummyProb : State → ℝ) :
    (Source ⊕ OffsetSource Row K) → State → ℝ
  | Sum.inl i => prob i
  | Sum.inr _ => dummyProb

/-- The original coefficient on an original source and the evenly split
deterministic offset on a dummy source. -/
private noncomputable def offsetUse
    (use : Source → State → Row → ℝ) (offset : Row → ℝ) (K : ℕ) :
    (Source ⊕ OffsetSource Row K) → State → Row → ℝ
  | Sum.inl i => use i
  | Sum.inr d => fun _a r =>
      if d.1 = r then offset r / K else 0

private theorem offsetProb_nonneg
    {K : ℕ}
    (prob : Source → State → ℝ) (dummyProb : State → ℝ)
    (hprob0 : ∀ i a, 0 ≤ prob i a)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a) :
    ∀ (i : Source ⊕ OffsetSource Row K) a,
      0 ≤ offsetProb (Row := Row) prob dummyProb i a := by
  intro i a
  cases i with
  | inl i => exact hprob0 i a
  | inr d => exact hdummy0 a

private theorem sum_offsetProb
    {K : ℕ}
    (prob : Source → State → ℝ) (dummyProb : State → ℝ)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (hdummySum : ∑ a, dummyProb a = 1) :
    ∀ i : Source ⊕ OffsetSource Row K,
      ∑ a, offsetProb (Row := Row) prob dummyProb i a = 1 := by
  intro i
  cases i with
  | inl i => exact hprobSum i
  | inr d => exact hdummySum

private theorem offsetUse_nonneg
    (use : Source → State → Row → ℝ) (offset : Row → ℝ) (K : ℕ)
    (huse0 : ∀ i a r, 0 ≤ use i a r)
    (hoffset0 : ∀ r, 0 ≤ offset r) :
    ∀ i a r, 0 ≤ offsetUse use offset K i a r := by
  intro i a r
  cases i with
  | inl i => exact huse0 i a r
  | inr d =>
      change 0 ≤ if d.1 = r then offset r / (K : ℝ) else 0
      split
      · exact div_nonneg (hoffset0 r) (Nat.cast_nonneg K)
      · exact le_rfl

private theorem offsetUse_le_one
    (use : Source → State → Row → ℝ) (offset : Row → ℝ) (K : ℕ)
    (hK : 0 < K)
    (huse1 : ∀ i a r, use i a r ≤ 1)
    (hoffsetK : ∀ r, offset r ≤ K) :
    ∀ i a r, offsetUse use offset K i a r ≤ 1 := by
  intro i a r
  cases i with
  | inl i => exact huse1 i a r
  | inr d =>
      change (if d.1 = r then offset r / (K : ℝ) else 0) ≤ 1
      split
      · exact (div_le_one (by exact_mod_cast hK : (0 : ℝ) < K)).2
          (hoffsetK r)
      · norm_num

private theorem offsetUse_dummy_column
    (offset : Row → ℝ) (K : ℕ) (hK : 0 < K)
    (hoffset0 : ∀ r, 0 ≤ offset r)
    (hoffsetK : ∀ r, offset r ≤ K)
    (d : OffsetSource Row K) (a : State) :
    (∑ r, offsetUse (Source := Source)
      (fun _ _ _ => 0) offset K (Sum.inr d) a r) ≤ 1 := by
  classical
  change (∑ r : Row, if d.1 = r then offset r / (K : ℝ) else 0) ≤ 1
  have hsum :
      (∑ r : Row, if d.1 = r then offset r / (K : ℝ) else 0) =
        offset d.1 / (K : ℝ) := by
    rw [Finset.sum_eq_single d.1]
    · simp
    · intro b _hb hbd
      simp [Ne.symm hbd]
    · simp
  rw [hsum]
  exact (div_le_one (by exact_mod_cast hK : (0 : ℝ) < K)).2
    (hoffsetK d.1)

private theorem rowMean_offsetUse
    (prob : Source → State → ℝ) (dummyProb : State → ℝ)
    (use : Source → State → Row → ℝ) (offset : Row → ℝ) (K : ℕ)
    (hK : 0 < K) (hdummySum : ∑ a, dummyProb a = 1)
    (r : Row) :
    rowMean (offsetProb (Row := Row) prob dummyProb)
        (offsetUse use offset K) r =
      offset r + rowMean prob use r := by
  classical
  unfold rowMean
  rw [Fintype.sum_sum_type]
  simp only [offsetProb, offsetUse]
  have hdummy :
    (∑ d : OffsetSource Row K, ∑ a : State,
        dummyProb a * if d.1 = r then offset r / K else 0) =
        offset r := by
    calc
      (∑ d : OffsetSource Row K, ∑ a : State,
          dummyProb a * if d.1 = r then offset r / K else 0) =
          ∑ d : OffsetSource Row K,
            if d.1 = r then offset r / K else 0 := by
        apply Finset.sum_congr rfl
        intro d _hd
        by_cases hdr : d.1 = r
        · simp only [hdr, if_true]
          rw [← Finset.sum_mul, hdummySum, one_mul]
        · simp [hdr]
      _ = ∑ _k : Fin K, offset r / K := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        simp
      _ = offset r := by
        have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp
  rw [hdummy]
  ring

private theorem rowLoad_offsetUse
    (use : Source → State → Row → ℝ) (offset : Row → ℝ) (K : ℕ)
    (hK : 0 < K)
    (choice : (Source ⊕ OffsetSource Row K) → State) (r : Row) :
    rowLoad (offsetUse use offset K) r choice =
      offset r + rowLoad use r (fun i => choice (Sum.inl i)) := by
  classical
  unfold rowLoad
  rw [Fintype.sum_sum_type]
  simp only [offsetUse]
  have hdummy :
    (∑ d : OffsetSource Row K,
        if d.1 = r then offset r / K else 0) =
        offset r := by
    calc
      (∑ d : OffsetSource Row K,
          if d.1 = r then offset r / K else 0) =
          ∑ _k : Fin K, offset r / K := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        simp
      _ = offset r := by
        have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp
  rw [hdummy]
  ring

/-- Support-preserving categorical packing with a deterministic load already
present in every row.  The hypotheses `offset r ≤ K` let `K` identical dummy
sources encode the offset.  Consequently the only extra column cost is one.

This is the form used by a sequential independent-group pass: `offset`
contains the actual load fixed in earlier groups and the expected load of
groups not processed yet. -/
theorem exists_supported_choice_offset_add_rowLoad_lt_packingThreshold
    (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C) (hC1 : 1 ≤ C)
    (K : ℕ) (hK : 0 < K)
    (prob : Source → State → ℝ) (dummyProb : State → ℝ)
    (use : Source → State → Row → ℝ) (offset : Row → ℝ)
    (hprob0 : ∀ i a, 0 ≤ prob i a)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1)
    (huse0 : ∀ i a r, 0 ≤ use i a r)
    (huse1 : ∀ i a r, use i a r ≤ 1)
    (hoffset0 : ∀ r, 0 ≤ offset r)
    (hoffsetK : ∀ r, offset r ≤ K)
    (hmean : ∀ r, offset r + rowMean prob use r ≤ R)
    (hcolumn : ∀ i a, ∑ r, use i a r ≤ C) :
    ∃ choice : Source → State,
      (∀ i, 0 < prob i (choice i)) ∧
      ∀ r, offset r + rowLoad use r choice < packingThreshold R C := by
  let combinedProb : (Source ⊕ OffsetSource Row K) → State → ℝ :=
    offsetProb (Row := Row) prob dummyProb
  let combinedUse : (Source ⊕ OffsetSource Row K) → State → Row → ℝ :=
    offsetUse use offset K
  have hcombined0 : ∀ i a, 0 ≤ combinedProb i a :=
    offsetProb_nonneg prob dummyProb hprob0 hdummy0
  have hcombinedSum : ∀ i, ∑ a, combinedProb i a = 1 :=
    sum_offsetProb prob dummyProb hprobSum hdummySum
  have hcombinedUse0 : ∀ i a r, 0 ≤ combinedUse i a r :=
    offsetUse_nonneg use offset K huse0 hoffset0
  have hcombinedUse1 : ∀ i a r, combinedUse i a r ≤ 1 :=
    offsetUse_le_one use offset K hK huse1 hoffsetK
  have hcombinedMean : ∀ r, rowMean combinedProb combinedUse r ≤ R := by
    intro r
    change rowMean (offsetProb (Row := Row) prob dummyProb)
      (offsetUse use offset K) r ≤ R
    rw [rowMean_offsetUse prob dummyProb use offset K hK hdummySum r]
    exact hmean r
  have hcombinedColumn : ∀ i a, ∑ r, combinedUse i a r ≤ C := by
    intro i a
    cases i with
    | inl i => simpa [combinedUse, offsetUse] using hcolumn i a
    | inr d =>
        change (∑ r, offsetUse use offset K (Sum.inr d) a r) ≤ C
        have hdummy :
            (∑ r, offsetUse use offset K (Sum.inr d) a r) ≤ 1 := by
          simpa [offsetUse] using
            (offsetUse_dummy_column (Source := Source) offset K hK
              hoffset0 hoffsetK d a)
        exact hdummy.trans hC1
  obtain ⟨combinedChoice, hchoicePos, hchoiceLoad⟩ :=
    exists_supported_choice_rowLoad_lt_packingThreshold
      R C hR hC combinedProb combinedUse hcombined0 hcombinedSum
      hcombinedUse0 hcombinedUse1 hcombinedMean hcombinedColumn
  let choice : Source → State := fun i => combinedChoice (Sum.inl i)
  refine ⟨choice, ?_, ?_⟩
  · intro i
    simpa [combinedProb, offsetProb, choice] using hchoicePos (Sum.inl i)
  · intro r
    have hload := hchoiceLoad r
    change rowLoad (offsetUse use offset K) r combinedChoice <
      packingThreshold R C at hload
    rw [rowLoad_offsetUse use offset K hK combinedChoice r] at hload
    simpa [choice] using hload

end

end WeightedEdgeColoring.FiniteCategoricalSelection
