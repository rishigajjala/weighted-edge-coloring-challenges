import WeightedEdgeColoring.ColorDependentExtendedProfileCandidateRows
import WeightedEdgeColoring.WeightedMomentTwoSidedSelection

/-!
# Fixed-block selection for colour-dependent profiles

This file separates the deterministic selection step from the later
calculation of the block-variance envelopes.  The source is a vertex and a
fixed colour block.  Its categorical state is the padded product word on
that block.  Capacity rows are one-sided and are kept below their own exact
product-law means.  Moment rows are inserted with their complementary rows,
so their selected loads stay on both sides of their exact means.

The last theorem specializes the capacity part to the colour-dependent
candidate rows.  The moment coefficients and their sparse caps are explicit
arguments.  This is intentional: the same selector can be used for the raw
option-mass row, the weighted diagonal row, and the conditional squared
block row without repeating the partial-resampling proof.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace FiniteCategoricalSelection

universe u₁ u₂ u₃ u₄

variable {Source : Type u₁} {State : Type u₂}
variable {CapacityRow : Type u₃} {MomentRow : Type u₄}
variable [Fintype Source] [DecidableEq Source]
variable [Fintype State] [DecidableEq State]
variable [Fintype CapacityRow] [DecidableEq CapacityRow]
variable [Fintype MomentRow] [DecidableEq MomentRow]

/-- Capacity rows together with the upper and complementary-lower copies of
the moment rows. -/
abbrev CapacityMomentRow := CapacityRow ⊕ (MomentRow × Bool)

/-- One-sided capacity coefficients and two-sided moment coefficients in a
single packing instance. -/
def capacityMomentUse
    (capacityUse : Source → State → CapacityRow → ℝ)
    (momentUse : Source → State → MomentRow → ℝ)
    (momentCap : Source → MomentRow → ℝ) :
    Source → State → CapacityMomentRow (CapacityRow := CapacityRow)
      (MomentRow := MomentRow) → ℝ
  | i, a, Sum.inl row => capacityUse i a row
  | i, a, Sum.inr row =>
      WeightedMomentTwoSidedSelection.signedUse momentUse momentCap i a row

theorem sum_capacityMomentUse_eq
    (capacityUse : Source → State → CapacityRow → ℝ)
    (momentUse : Source → State → MomentRow → ℝ)
    (momentCap : Source → MomentRow → ℝ)
    (i : Source) (a : State) :
    (∑ row, capacityMomentUse capacityUse momentUse momentCap i a row) =
      (∑ row, capacityUse i a row) + ∑ row, momentCap i row := by
  rw [Fintype.sum_sum_type]
  congr 1
  exact WeightedMomentTwoSidedSelection.sum_signedUse_eq_sum_cap
    momentUse momentCap i a

/-- A single mean-relative packing choice controls all capacity rows from
above and every moment row from both sides.  The deviation uses only common
upper bounds `R` and `C`; the conclusions retain each row's exact mean. -/
theorem exists_supported_choice_capacity_and_twoSided_moment
    (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C) (hC1 : 1 ≤ C)
    (K : ℕ) (hK : 0 < K) (hRK : R ≤ K)
    (prob : Source → State → ℝ) (dummyProb : State → ℝ)
    (capacityUse : Source → State → CapacityRow → ℝ)
    (momentUse : Source → State → MomentRow → ℝ)
    (momentCap : Source → MomentRow → ℝ)
    (hprob0 : ∀ i a, 0 ≤ prob i a)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1)
    (hcapacity0 : ∀ i a row, 0 ≤ capacityUse i a row)
    (hcapacity1 : ∀ i a row, capacityUse i a row ≤ 1)
    (hmoment0 : ∀ i a row, 0 ≤ momentUse i a row)
    (hmomentCap : ∀ i a row, momentUse i a row ≤ momentCap i row)
    (hcap1 : ∀ i row, momentCap i row ≤ 1)
    (hcapacityMean : ∀ row, rowMean prob capacityUse row ≤ R)
    (hmomentMeanUpper : ∀ row, rowMean prob momentUse row ≤ R)
    (hmomentMeanLower : ∀ row,
      (∑ i, momentCap i row) - rowMean prob momentUse row ≤ R)
    (hcolumn : ∀ i a,
      (∑ row, capacityUse i a row) + ∑ row, momentCap i row ≤ C) :
    ∃ choice : Source → State,
      (∀ i, 0 < prob i (choice i)) ∧
      (∀ row : CapacityRow,
        rowLoad capacityUse row choice <
          rowMean prob capacityUse row +
            FinitePartialResamplingNumerics.packingDeviation R C) ∧
      ∀ row : MomentRow,
        |rowLoad momentUse row choice - rowMean prob momentUse row| <
          FinitePartialResamplingNumerics.packingDeviation R C := by
  let use := capacityMomentUse capacityUse momentUse momentCap
  have huse0 : ∀ i a row, 0 ≤ use i a row := by
    intro i a row
    rcases row with capacity | moment
    · exact hcapacity0 i a capacity
    · rcases moment with ⟨row, sign⟩
      cases sign
      · exact hmoment0 i a row
      · exact sub_nonneg.mpr (hmomentCap i a row)
  have huse1 : ∀ i a row, use i a row ≤ 1 := by
    intro i a row
    rcases row with capacity | moment
    · exact hcapacity1 i a capacity
    · rcases moment with ⟨row, sign⟩
      cases sign
      · exact (hmomentCap i a row).trans (hcap1 i row)
      · dsimp [use, capacityMomentUse,
          WeightedMomentTwoSidedSelection.signedUse]
        linarith [hmoment0 i a row, hcap1 i row]
  have hmean : ∀ row, rowMean prob use row ≤ R := by
    intro row
    rcases row with capacity | moment
    · simpa [use, capacityMomentUse] using hcapacityMean capacity
    · rcases moment with ⟨row, sign⟩
      cases sign
      · simpa [use, capacityMomentUse] using hmomentMeanUpper row
      · change rowMean prob
            (WeightedMomentTwoSidedSelection.signedUse momentUse momentCap)
              (row, true) ≤ R
        rw [WeightedMomentTwoSidedSelection.rowMean_signedUse_true
          prob momentUse momentCap hprobSum]
        linarith [hmomentMeanLower row]
  have huseColumn : ∀ i a, ∑ row, use i a row ≤ C := by
    intro i a
    rw [show (∑ row, use i a row) =
        (∑ row, capacityUse i a row) + ∑ row, momentCap i row by
      exact sum_capacityMomentUse_eq capacityUse momentUse momentCap i a]
    exact hcolumn i a
  obtain ⟨choice, hsupport, hrows⟩ :=
    exists_supported_choice_rowLoad_lt_rowMean_add_deviation
      R C hR hC hC1 K hK hRK prob dummyProb use
      hprob0 hprobSum hdummy0 hdummySum huse0 huse1 hmean huseColumn
  refine ⟨choice, hsupport, ?_, ?_⟩
  · intro row
    simpa [use, capacityMomentUse] using hrows (Sum.inl row)
  · intro row
    have hu := hrows (Sum.inr (row, false))
    have hl := hrows (Sum.inr (row, true))
    change rowLoad momentUse row choice <
      rowMean prob momentUse row +
        FinitePartialResamplingNumerics.packingDeviation R C at hu
    change rowLoad
        (WeightedMomentTwoSidedSelection.signedUse momentUse momentCap)
          (row, true) choice <
      rowMean prob
        (WeightedMomentTwoSidedSelection.signedUse momentUse momentCap)
          (row, true) +
        FinitePartialResamplingNumerics.packingDeviation R C at hl
    rw [WeightedMomentTwoSidedSelection.rowLoad_signedUse_true,
      WeightedMomentTwoSidedSelection.rowMean_signedUse_true
        prob momentUse momentCap hprobSum] at hl
    rw [abs_lt]
    constructor <;> linarith

/-- Add a second one-sided row family while retaining the two-sided moment
family.  Quadratic error rows belong in `UpperRow`; only signed option-mass
rows should pay for a complementary lower copy. -/
theorem exists_supported_choice_capacity_upper_and_twoSided_moment
    {UpperRow : Type*} [Fintype UpperRow] [DecidableEq UpperRow]
    (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C) (hC1 : 1 ≤ C)
    (K : ℕ) (hK : 0 < K) (hRK : R ≤ K)
    (prob : Source → State → ℝ) (dummyProb : State → ℝ)
    (capacityUse : Source → State → CapacityRow → ℝ)
    (upperUse : Source → State → UpperRow → ℝ)
    (momentUse : Source → State → MomentRow → ℝ)
    (momentCap : Source → MomentRow → ℝ)
    (hprob0 : ∀ i a, 0 ≤ prob i a)
    (hprobSum : ∀ i, ∑ a, prob i a = 1)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1)
    (hcapacity0 : ∀ i a row, 0 ≤ capacityUse i a row)
    (hcapacity1 : ∀ i a row, capacityUse i a row ≤ 1)
    (hupper0 : ∀ i a row, 0 ≤ upperUse i a row)
    (hupper1 : ∀ i a row, upperUse i a row ≤ 1)
    (hmoment0 : ∀ i a row, 0 ≤ momentUse i a row)
    (hmomentCap : ∀ i a row, momentUse i a row ≤ momentCap i row)
    (hcap1 : ∀ i row, momentCap i row ≤ 1)
    (hcapacityMean : ∀ row, rowMean prob capacityUse row ≤ R)
    (hupperMean : ∀ row, rowMean prob upperUse row ≤ R)
    (hmomentMeanUpper : ∀ row, rowMean prob momentUse row ≤ R)
    (hmomentMeanLower : ∀ row,
      (∑ i, momentCap i row) - rowMean prob momentUse row ≤ R)
    (hcolumn : ∀ i a,
      (∑ row, capacityUse i a row) +
          (∑ row, upperUse i a row) +
            ∑ row, momentCap i row ≤ C) :
    ∃ choice : Source → State,
      (∀ i, 0 < prob i (choice i)) ∧
      (∀ row : CapacityRow,
        rowLoad capacityUse row choice < rowMean prob capacityUse row +
          FinitePartialResamplingNumerics.packingDeviation R C) ∧
      (∀ row : UpperRow,
        rowLoad upperUse row choice < rowMean prob upperUse row +
          FinitePartialResamplingNumerics.packingDeviation R C) ∧
      ∀ row : MomentRow,
        |rowLoad momentUse row choice - rowMean prob momentUse row| <
          FinitePartialResamplingNumerics.packingDeviation R C := by
  let combinedCapacity : Source → State → (CapacityRow ⊕ UpperRow) → ℝ :=
    fun i a row ↦ match row with
      | Sum.inl capacity => capacityUse i a capacity
      | Sum.inr upper => upperUse i a upper
  obtain ⟨choice, hsupport, hcombined, hmoment⟩ :=
    exists_supported_choice_capacity_and_twoSided_moment
      R C hR hC hC1 K hK hRK prob dummyProb combinedCapacity
      momentUse momentCap hprob0 hprobSum hdummy0 hdummySum
      (by intro i a row; rcases row with row | row
          <;> simp [combinedCapacity, hcapacity0, hupper0])
      (by intro i a row; rcases row with row | row
          <;> simp [combinedCapacity, hcapacity1, hupper1])
      hmoment0 hmomentCap hcap1
      (by
        intro row
        rcases row with row | row
        · simpa [combinedCapacity] using hcapacityMean row
        · simpa [combinedCapacity] using hupperMean row)
      hmomentMeanUpper hmomentMeanLower
      (by
        intro i a
        simpa [combinedCapacity, Fintype.sum_sum_type, add_assoc] using
          hcolumn i a)
  refine ⟨choice, hsupport, ?_, ?_, hmoment⟩
  · intro row
    simpa [combinedCapacity] using hcombined (Sum.inl row)
  · intro row
    simpa [combinedCapacity] using hcombined (Sum.inr row)

end FiniteCategoricalSelection

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})
variable {B k n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- The common finite state of a word on one fixed block. -/
abbrev ColorDependentExtendedProfilePackedBlockState
    (_G : WeightedSimpleGraph.{u}) :=
  FiniteDependentWordPadding.PackedWordState
    (Color := Fin k) (extendedProfileStateBound β q r)

/-- Restriction of the colour-dependent proposal to one fixed block. -/
def colorDependentExtendedProfileBlockProposal (b : Fin B) :
    G.E → Fin k → ℝ :=
  fun e i ↦ proposal e (b, i)

/-- Restriction of the realization family to one fixed block. -/
def colorDependentExtendedProfileBlockRealization (b : Fin B) :
    ∀ v i, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦
        G.colorDependentExtendedProfileBlockProposal proposal b e.1 i)
      s β q r hβ hr :=
  fun v i ↦ R v (b, i)

/-- Padded product probability at the block source `(v,b)`. -/
def paddedColorDependentExtendedProfileBlockProbability
    (omega : ℝ) (source : G.V × Fin B)
    (a : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) : ℝ :=
  G.paddedColorDependentExtendedProfileWordProbability
    (proposal := G.colorDependentExtendedProfileBlockProposal proposal source.2)
    (G.colorDependentExtendedProfileBlockRealization proposal R source.2)
    omega source.1 a

/-- Decode the `i`th state of a padded block word. -/
def decodeColorDependentExtendedProfileBlock
    (source : G.V × Fin B)
    (a : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) (i : Fin k) :
    G.ColorDependentExtendedProfileState R source.1 (source.2, i) :=
  G.decodeColorDependentExtendedProfileWord
    (proposal := G.colorDependentExtendedProfileBlockProposal proposal source.2)
    (G.colorDependentExtendedProfileBlockRealization proposal R source.2)
    source.1 a i

/-- Encode a genuine state word on one block. -/
def encodeColorDependentExtendedProfileBlock
    (v : G.V) (b : Fin B)
    (word : ∀ i : Fin k,
      G.ColorDependentExtendedProfileState R v (b, i)) :
    G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r) :=
  G.encodeColorDependentExtendedProfileWord
    (proposal := G.colorDependentExtendedProfileBlockProposal proposal b)
    (G.colorDependentExtendedProfileBlockRealization proposal R b) v word

@[simp] theorem decode_encodeColorDependentExtendedProfileBlock
    (v : G.V) (b : Fin B)
    (word : ∀ i : Fin k,
      G.ColorDependentExtendedProfileState R v (b, i)) :
    G.decodeColorDependentExtendedProfileBlock proposal R (v, b)
      (G.encodeColorDependentExtendedProfileBlock proposal R v b word) = word := by
  exact G.decode_encodeColorDependentExtendedProfileWord
    (proposal := G.colorDependentExtendedProfileBlockProposal proposal b)
    (G.colorDependentExtendedProfileBlockRealization proposal R b) v word

theorem paddedColorDependentExtendedProfileBlockProbability_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (source : G.V × Fin B)
    (a : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) :
    0 ≤ G.paddedColorDependentExtendedProfileBlockProbability
      proposal R omega source a := by
  exact G.paddedColorDependentExtendedProfileWordProbability_nonneg
    (proposal := G.colorDependentExtendedProfileBlockProposal proposal source.2)
    (G.colorDependentExtendedProfileBlockRealization proposal R source.2)
    hs hq hr0 hleft homega0 homega1 source.1 a

theorem sum_paddedColorDependentExtendedProfileBlockProbability
    (omega : ℝ) (source : G.V × Fin B) :
    ∑ a, G.paddedColorDependentExtendedProfileBlockProbability
      proposal R omega source a = 1 := by
  exact G.sum_paddedColorDependentExtendedProfileWordProbability
    (proposal := G.colorDependentExtendedProfileBlockProposal proposal source.2)
    (G.colorDependentExtendedProfileBlockRealization proposal R source.2)
    omega source.1

/-- Lift the one-colour candidate rows to independent block sources. -/
def colorDependentBlockCandidateUse
    (N : ℕ) (scale rho omega : ℝ) (source : G.V × Fin B)
    (a : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r))
    (row : G.ColorDependentExtendedProfileCapacityRow
      (G.ColorDependentCandidateRowAt R)) : ℝ :=
  if h : source.2 = row.1.1 then
    G.scaledColorDependentCandidateAtomUse proposal R N scale rho omega
      source.1 row.1
      (by
        have hcolor : (source.2, row.1.2) = row.1 := by
          apply Prod.ext
          · exact h
          · rfl
        exact hcolor ▸ G.decodeColorDependentExtendedProfileBlock
          proposal R source a row.1.2) row.2
  else 0

theorem colorDependentBlockCandidateUse_nonneg
    (N : ℕ) (scale rho omega : ℝ)
    (huse0 : ∀ v c z row,
      0 ≤ G.scaledColorDependentCandidateAtomUse
        proposal R N scale rho omega v c z row)
    (source : G.V × Fin B)
    (a : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r))
    (row : G.ColorDependentExtendedProfileCapacityRow
      (G.ColorDependentCandidateRowAt R)) :
    0 ≤ G.colorDependentBlockCandidateUse
      proposal R N scale rho omega source a row := by
  unfold colorDependentBlockCandidateUse
  split
  · exact huse0 _ _ _ _
  · exact le_rfl

theorem colorDependentBlockCandidateUse_le_one
    (N : ℕ) (scale rho omega : ℝ)
    (huse1 : ∀ v c z row,
      G.scaledColorDependentCandidateAtomUse
        proposal R N scale rho omega v c z row ≤ 1)
    (source : G.V × Fin B)
    (a : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r))
    (row : G.ColorDependentExtendedProfileCapacityRow
      (G.ColorDependentCandidateRowAt R)) :
    G.colorDependentBlockCandidateUse
      proposal R N scale rho omega source a row ≤ 1 := by
  unfold colorDependentBlockCandidateUse
  split
  · exact huse1 _ _ _ _
  · norm_num

/-- The lifted block row has exactly the original one-colour product-law
mean.  Thus zero-mean reservoir rows incur no artificial common mean. -/
theorem colorDependentBlockCandidate_rowMean_eq
    (omega scale rho : ℝ)
    (row : G.ColorDependentExtendedProfileCapacityRow
      (G.ColorDependentCandidateRowAt R)) :
    FiniteCategoricalSelection.rowMean
        (G.paddedColorDependentExtendedProfileBlockProbability
          proposal R omega)
        (G.colorDependentBlockCandidateUse
          proposal R n scale rho omega) row =
      ∑ v, ∑ z : G.ColorDependentExtendedProfileState R v row.1,
        G.smoothedColorDependentExtendedProfileProbability
            R omega v row.1 z *
          G.scaledColorDependentCandidateAtomUse
            proposal R n scale rho omega v row.1 z row.2 := by
  classical
  unfold FiniteCategoricalSelection.rowMean
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single row.1.1]
  · apply Finset.sum_congr rfl
    intro v _hv
    simp only [colorDependentBlockCandidateUse, dite_true]
    simpa [colorDependentExtendedProfileBlockRealization,
      colorDependentExtendedProfileBlockProposal,
      paddedColorDependentExtendedProfileBlockProbability,
      decodeColorDependentExtendedProfileBlock] using
      (G.sum_paddedColorDependentProbability_mul_decode_coordinate
        (proposal := G.colorDependentExtendedProfileBlockProposal proposal row.1.1)
        (G.colorDependentExtendedProfileBlockRealization proposal R row.1.1)
        omega v row.1.2
        (fun z ↦ G.scaledColorDependentCandidateAtomUse
          proposal R n scale rho omega v row.1 z row.2))
  · intro b _hb hb
    have hne : b ≠ row.1.1 := hb
    simp [colorDependentBlockCandidateUse, hne]
  · simp

/-- Concrete fixed-block selector.  `momentUse` may be the normalized raw
block option-mass, diagonal, or conditional weighted-square row.  Its cap
is sparse, and hence the two signed copies cost exactly one cap column.
The capacity conclusion is relative to its exact colour-row mean. -/
theorem exists_colorDependentExtendedProfileBlock_capacity_and_twoSided
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (scale rho : ℝ)
    {MomentRow : Type*} [Fintype MomentRow] [DecidableEq MomentRow]
    (momentUse : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r) → MomentRow → ℝ)
    (momentCap : (G.V × Fin B) → MomentRow → ℝ)
    (meanBound columnBound : ℝ)
    (hmeanBound : 0 < meanBound) (hcolumnBound : 0 ≤ columnBound)
    (hcolumnOne : 1 ≤ columnBound)
    (K : ℕ) (hK : 0 < K) (hmeanK : meanBound ≤ K)
    (dummyProb : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r) → ℝ)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1)
    (hcapacity0 : ∀ v c z row,
      0 ≤ G.scaledColorDependentCandidateAtomUse
        proposal R n scale rho omega v c z row)
    (hcapacity1 : ∀ v c z row,
      G.scaledColorDependentCandidateAtomUse
        proposal R n scale rho omega v c z row ≤ 1)
    (hcapacityMean : ∀ row : G.ColorDependentExtendedProfileCapacityRow
        (G.ColorDependentCandidateRowAt R),
      (∑ v, ∑ z : G.ColorDependentExtendedProfileState R v row.1,
        G.smoothedColorDependentExtendedProfileProbability
            R omega v row.1 z *
          G.scaledColorDependentCandidateAtomUse
            proposal R n scale rho omega v row.1 z row.2) ≤ meanBound)
    (hmoment0 : ∀ src a row, 0 ≤ momentUse src a row)
    (hmomentCap : ∀ src a row,
      momentUse src a row ≤ momentCap src row)
    (hcap1 : ∀ src row, momentCap src row ≤ 1)
    (hmomentMeanUpper : ∀ row,
      FiniteCategoricalSelection.rowMean
        (G.paddedColorDependentExtendedProfileBlockProbability
          proposal R omega) momentUse row ≤ meanBound)
    (hmomentMeanLower : ∀ row,
      (∑ src, momentCap src row) -
        FiniteCategoricalSelection.rowMean
          (G.paddedColorDependentExtendedProfileBlockProbability
            proposal R omega) momentUse row ≤ meanBound)
    (hcolumn : ∀ src a,
      (∑ row, G.colorDependentBlockCandidateUse
        proposal R n scale rho omega src a row) +
        ∑ row, momentCap src row ≤ columnBound) :
    ∃ selected : ∀ v (b : Fin B) (i : Fin k),
        G.ColorDependentExtendedProfileState R v (b, i),
      (∀ v b,
        0 < G.paddedColorDependentExtendedProfileBlockProbability
          proposal R omega (v, b)
          (G.encodeColorDependentExtendedProfileBlock
            proposal R v b (selected v b))) ∧
      (∀ row : G.ColorDependentExtendedProfileCapacityRow
          (G.ColorDependentCandidateRowAt R),
        FiniteCategoricalSelection.rowLoad
          (G.colorDependentBlockCandidateUse
            proposal R n scale rho omega) row
          (fun src ↦ G.encodeColorDependentExtendedProfileBlock
            proposal R src.1 src.2 (selected src.1 src.2)) <
        (∑ v, ∑ z : G.ColorDependentExtendedProfileState R v row.1,
          G.smoothedColorDependentExtendedProfileProbability
              R omega v row.1 z *
            G.scaledColorDependentCandidateAtomUse
              proposal R n scale rho omega v row.1 z row.2) +
          FinitePartialResamplingNumerics.packingDeviation
            meanBound columnBound) ∧
      ∀ row : MomentRow,
        |FiniteCategoricalSelection.rowLoad momentUse row
            (fun src ↦ G.encodeColorDependentExtendedProfileBlock
              proposal R src.1 src.2 (selected src.1 src.2)) -
          FiniteCategoricalSelection.rowMean
            (G.paddedColorDependentExtendedProfileBlockProbability
              proposal R omega) momentUse row| <
          FinitePartialResamplingNumerics.packingDeviation
            meanBound columnBound := by
  let prob := G.paddedColorDependentExtendedProfileBlockProbability
    proposal R omega
  let capacityUse := G.colorDependentBlockCandidateUse
    proposal R n scale rho omega
  obtain ⟨choice, hsupport, hcapacity, hmoment⟩ :=
    FiniteCategoricalSelection.exists_supported_choice_capacity_and_twoSided_moment
        meanBound columnBound hmeanBound hcolumnBound hcolumnOne
        K hK hmeanK prob dummyProb capacityUse momentUse momentCap
        (G.paddedColorDependentExtendedProfileBlockProbability_nonneg
          proposal R hs hq hr0 hleft homega0 homega1)
        (G.sum_paddedColorDependentExtendedProfileBlockProbability
          proposal R omega)
        hdummy0 hdummySum
        (G.colorDependentBlockCandidateUse_nonneg
          proposal R n scale rho omega hcapacity0)
        (G.colorDependentBlockCandidateUse_le_one
          proposal R n scale rho omega hcapacity1)
        hmoment0 hmomentCap hcap1
        (fun row ↦ by
          rw [G.colorDependentBlockCandidate_rowMean_eq
            proposal R omega scale rho row]
          exact hcapacityMean row)
        hmomentMeanUpper hmomentMeanLower hcolumn
  have hdecode : ∀ src, ∃ word : ∀ i : Fin k,
      G.ColorDependentExtendedProfileState R src.1 (src.2, i),
      G.encodeColorDependentExtendedProfileBlock
          proposal R src.1 src.2 word = choice src ∧
        0 < G.paddedColorDependentExtendedProfileBlockProbability
          proposal R omega src (choice src) := by
    intro src
    let blockProposal :=
      G.colorDependentExtendedProfileBlockProposal proposal src.2
    let blockR := G.colorDependentExtendedProfileBlockRealization
      proposal R src.2
    obtain ⟨word, hcode, hmass⟩ :=
      G.exists_colorDependentExtendedProfileWord_of_padded_pos
        (proposal := blockProposal) blockR
        hs hq hr0 hleft homega0 homega1 src.1 (choice src)
        (hsupport src)
    exact ⟨word, hcode, hsupport src⟩
  let selected : ∀ v (b : Fin B) (i : Fin k),
      G.ColorDependentExtendedProfileState R v (b, i) :=
    fun v b ↦ Classical.choose (hdecode (v, b))
  have hcode : ∀ src,
      G.encodeColorDependentExtendedProfileBlock proposal R src.1 src.2
          (selected src.1 src.2) = choice src := by
    intro src
    exact (Classical.choose_spec (hdecode src)).1
  refine ⟨selected, ?_, ?_, ?_⟩
  · intro v b
    rw [hcode (v, b)]
    exact hsupport (v, b)
  · intro row
    have hrow := hcapacity row
    rw [G.colorDependentBlockCandidate_rowMean_eq
      proposal R omega scale rho row] at hrow
    simpa [capacityUse, prob, hcode] using hrow
  · intro row
    simpa only [hcode] using hmoment row

/-- One-sided companion used for nonnegative quadratic rows.  It avoids the
spurious complementary lower-row cost when a vertex has many tiny edges. -/
theorem exists_colorDependentExtendedProfileBlock_capacity_and_upper
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (scale rho : ℝ)
    {UpperRow : Type*} [Fintype UpperRow] [DecidableEq UpperRow]
    (upperUse : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r) → UpperRow → ℝ)
    (meanBound columnBound : ℝ)
    (hmeanBound : 0 < meanBound) (hcolumnBound : 0 ≤ columnBound)
    (hcolumnOne : 1 ≤ columnBound)
    (K : ℕ) (hK : 0 < K) (hmeanK : meanBound ≤ K)
    (dummyProb : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r) → ℝ)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1)
    (hcapacity0 : ∀ v c z row,
      0 ≤ G.scaledColorDependentCandidateAtomUse
        proposal R n scale rho omega v c z row)
    (hcapacity1 : ∀ v c z row,
      G.scaledColorDependentCandidateAtomUse
        proposal R n scale rho omega v c z row ≤ 1)
    (hcapacityMean : ∀ row : G.ColorDependentExtendedProfileCapacityRow
        (G.ColorDependentCandidateRowAt R),
      (∑ v, ∑ z : G.ColorDependentExtendedProfileState R v row.1,
        G.smoothedColorDependentExtendedProfileProbability
            R omega v row.1 z *
          G.scaledColorDependentCandidateAtomUse
            proposal R n scale rho omega v row.1 z row.2) ≤ meanBound)
    (hupper0 : ∀ src a row, 0 ≤ upperUse src a row)
    (hupper1 : ∀ src a row, upperUse src a row ≤ 1)
    (hupperMean : ∀ row,
      FiniteCategoricalSelection.rowMean
        (G.paddedColorDependentExtendedProfileBlockProbability
          proposal R omega) upperUse row ≤ meanBound)
    (hcolumn : ∀ src a,
      (∑ row, G.colorDependentBlockCandidateUse
        proposal R n scale rho omega src a row) +
        ∑ row, upperUse src a row ≤ columnBound) :
    ∃ selected : ∀ v (b : Fin B) (i : Fin k),
        G.ColorDependentExtendedProfileState R v (b, i),
      (∀ v b,
        0 < G.paddedColorDependentExtendedProfileBlockProbability
          proposal R omega (v, b)
          (G.encodeColorDependentExtendedProfileBlock
            proposal R v b (selected v b))) ∧
      (∀ row : G.ColorDependentExtendedProfileCapacityRow
          (G.ColorDependentCandidateRowAt R),
        FiniteCategoricalSelection.rowLoad
          (G.colorDependentBlockCandidateUse
            proposal R n scale rho omega) row
          (fun src ↦ G.encodeColorDependentExtendedProfileBlock
            proposal R src.1 src.2 (selected src.1 src.2)) <
        (∑ v, ∑ z : G.ColorDependentExtendedProfileState R v row.1,
          G.smoothedColorDependentExtendedProfileProbability
              R omega v row.1 z *
            G.scaledColorDependentCandidateAtomUse
              proposal R n scale rho omega v row.1 z row.2) +
          FinitePartialResamplingNumerics.packingDeviation
            meanBound columnBound) ∧
      ∀ row : UpperRow,
        FiniteCategoricalSelection.rowLoad upperUse row
            (fun src ↦ G.encodeColorDependentExtendedProfileBlock
              proposal R src.1 src.2 (selected src.1 src.2)) <
          FiniteCategoricalSelection.rowMean
            (G.paddedColorDependentExtendedProfileBlockProbability
              proposal R omega) upperUse row +
          FinitePartialResamplingNumerics.packingDeviation
            meanBound columnBound := by
  let prob := G.paddedColorDependentExtendedProfileBlockProbability
    proposal R omega
  let capacityUse := G.colorDependentBlockCandidateUse
    proposal R n scale rho omega
  let combinedUse : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r) →
      (G.ColorDependentExtendedProfileCapacityRow
        (G.ColorDependentCandidateRowAt R) ⊕ UpperRow) → ℝ :=
    fun src a row ↦ match row with
      | Sum.inl capacity => capacityUse src a capacity
      | Sum.inr upper => upperUse src a upper
  obtain ⟨choice, hsupport, hrows⟩ :=
    FiniteCategoricalSelection.exists_supported_choice_rowLoad_lt_rowMean_add_deviation
      meanBound columnBound hmeanBound hcolumnBound hcolumnOne
      K hK hmeanK prob dummyProb combinedUse
      (G.paddedColorDependentExtendedProfileBlockProbability_nonneg
        proposal R hs hq hr0 hleft homega0 homega1)
      (G.sum_paddedColorDependentExtendedProfileBlockProbability
        proposal R omega)
      hdummy0 hdummySum
      (by intro src a row; rcases row with row | row
          <;> simp [combinedUse, capacityUse,
            G.colorDependentBlockCandidateUse_nonneg
              proposal R n scale rho omega hcapacity0,
            hupper0])
      (by intro src a row; rcases row with row | row
          <;> simp [combinedUse, capacityUse,
            G.colorDependentBlockCandidateUse_le_one
              proposal R n scale rho omega hcapacity1,
            hupper1])
      (by
        intro row
        rcases row with row | row
        · change FiniteCategoricalSelection.rowMean prob capacityUse row ≤
            meanBound
          rw [G.colorDependentBlockCandidate_rowMean_eq
            proposal R omega scale rho row]
          exact hcapacityMean row
        · simpa [combinedUse] using hupperMean row)
      (by
        intro src a
        simpa [combinedUse, capacityUse, Fintype.sum_sum_type] using
          hcolumn src a)
  have hdecode : ∀ src, ∃ word : ∀ i : Fin k,
      G.ColorDependentExtendedProfileState R src.1 (src.2, i),
      G.encodeColorDependentExtendedProfileBlock
          proposal R src.1 src.2 word = choice src := by
    intro src
    let blockProposal :=
      G.colorDependentExtendedProfileBlockProposal proposal src.2
    let blockR := G.colorDependentExtendedProfileBlockRealization
      proposal R src.2
    obtain ⟨word, hcode, _hmass⟩ :=
      G.exists_colorDependentExtendedProfileWord_of_padded_pos
        (proposal := blockProposal) blockR hs hq hr0 hleft homega0 homega1
        src.1 (choice src) (hsupport src)
    exact ⟨word, hcode⟩
  let selected : ∀ v (b : Fin B) (i : Fin k),
      G.ColorDependentExtendedProfileState R v (b, i) :=
    fun v b ↦ Classical.choose (hdecode (v, b))
  have hcode : ∀ src,
      G.encodeColorDependentExtendedProfileBlock proposal R src.1 src.2
          (selected src.1 src.2) = choice src := by
    intro src
    exact Classical.choose_spec (hdecode src)
  refine ⟨selected, ?_, ?_, ?_⟩
  · intro v b
    rw [hcode (v, b)]
    exact hsupport (v, b)
  · intro row
    have hrow := hrows (Sum.inl row)
    change FiniteCategoricalSelection.rowLoad capacityUse row choice <
      FiniteCategoricalSelection.rowMean prob capacityUse row +
        FinitePartialResamplingNumerics.packingDeviation meanBound columnBound at hrow
    rw [G.colorDependentBlockCandidate_rowMean_eq
      proposal R omega scale rho row] at hrow
    simpa [capacityUse, prob, hcode] using hrow
  · intro row
    simpa [combinedUse, hcode] using hrows (Sum.inr row)

end WeightedSimpleGraph

end

end WeightedEdgeColoring
