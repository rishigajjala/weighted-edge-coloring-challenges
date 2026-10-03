import WeightedEdgeColoring.MultigraphLargeStarCategoricalDependency
import WeightedEdgeColoring.FiniteCategoricalSupportSplit

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u w₁ w₂ w₃

variable (G : WeightedMultigraph.{u})
variable {Color : Type w₁} [Fintype Color] [DecidableEq Color]
variable {State : Type w₂} [Fintype State] [DecidableEq State]
variable {Row : Type w₃} [Fintype Row] [DecidableEq Row]

/-- Sources in profile synchronization are vertex--colour pairs. -/
abbrev ProfileSource (Color : Type w₁) := G.V × Color

/-- The exact finite ledger still required to connect the bounded profile
menus to categorical selection.  `prob` is the padded profile law and `use`
records the normalized contribution of one selected profile to one load or
loss row.  The final two fields are the only combinatorial incidence bounds
needed by the local lemma. -/
structure ProfileSynchronizationLedger
    (prob : G.ProfileSource Color → State → ℝ)
    (use : G.ProfileSource Color → State → Row → ℝ)
    (A0 A1 B0 B1 K : ℕ) : Prop where
  prob_nonneg : ∀ src a, 0 ≤ prob src a
  prob_sum : ∀ src, ∑ a, prob src a = 1
  use_nonneg : ∀ src a row, 0 ≤ use src a row
  use_le_one : ∀ src a row, use src a row ≤ 1
  row_support_card : ∀ row,
    (FiniteCategoricalSelection.rowSupport use row).card ≤ A0 + A1 * K
  source_incidence_card : ∀ src,
    (FiniteCategoricalSelection.rowSupportIncidence use src).card ≤ B0 + B1 * K

/-- A valid profile ledger has polynomial row-support overlap degree. -/
theorem ProfileSynchronizationLedger.overlapNeighbor_card_le
    {prob : G.ProfileSource Color → State → ℝ}
    {use : G.ProfileSource Color → State → Row → ℝ}
    {A0 A1 B0 B1 K : ℕ}
    (L : G.ProfileSynchronizationLedger prob use A0 A1 B0 B1 K)
    (row : Row) :
    (FiniteCategoricalSupportSplit.overlapNeighbor use row).card ≤
      (A0 + A1 * K) * (B0 + B1 * K) := by
  -- The two overlap-neighbour definitions have the same membership test.
  have heq : FiniteCategoricalSupportSplit.overlapNeighbor use row =
      FiniteCategoricalSelection.rowSupportOverlapNeighbor use row := by
    ext t
    simp only [FiniteCategoricalSupportSplit.overlapNeighbor,
      FiniteCategoricalSelection.rowSupportOverlapNeighbor,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, ⟨src, hsrc⟩⟩
      refine ⟨hne, ?_⟩
      rw [Finset.not_disjoint_iff]
      exact ⟨src, (Finset.mem_inter.mp hsrc).1,
        (Finset.mem_inter.mp hsrc).2⟩
    · rintro ⟨hne, hnot⟩
      rw [Finset.not_disjoint_iff] at hnot
      rcases hnot with ⟨src, hleft, hright⟩
      exact ⟨hne, ⟨src, Finset.mem_inter.mpr ⟨hleft, hright⟩⟩⟩
  rw [heq]
  exact FiniteCategoricalSelection.rowSupportOverlapNeighbor_card_le_polynomial
    use A0 A1 B0 B1 K L.row_support_card L.source_incidence_card row

/-- Under local `n`-bin packing, the chosen locality parameter `K` really
bounds every beta-large star.  This is the graph-specific input used when
proving the two support-cardinality fields of the ledger. -/
theorem profileSynchronization_largeStar_card_le
    {n K : ℕ} (hlocal : G.LocallyPacksInto n)
    {beta : ℝ} (hbeta : 0 < beta)
    (hK : (n : ℝ) < ((K + 1 : ℕ) : ℝ) * beta) :
    ∀ v, (G.largeStarEdges beta v).card ≤ K := by
  exact G.largeStarEdges_card_le_of_locallyPacksInto hlocal hbeta hK

/-- Full profile-synchronization selection once the explicit profile ledger
and its Chernoff thresholds are supplied.  The dependency degree is the
polynomial forced by the large-star incidence bounds. -/
theorem exists_profileSynchronization_choice
    (prob : G.ProfileSource Color → State → ℝ)
    (use : G.ProfileSource Color → State → Row → ℝ)
    (A0 A1 B0 B1 K : ℕ)
    (L : G.ProfileSynchronizationLedger prob use A0 A1 B0 B1 K)
    (threshold lambda : Row → ℝ) (p x : ℝ)
    (hlambda : ∀ row, 0 ≤ lambda row)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hnumeric : p ≤ x * (1 - x) ^
      ((A0 + A1 * K) * (B0 + B1 * K)))
    (hchernoff : ∀ row,
      Real.exp (-lambda row * threshold row +
        (Real.exp (lambda row) - 1) *
          FiniteCategoricalSelection.rowMean prob use row) ≤ p) :
    ∃ choice : G.ProfileSource Color → State, ∀ row,
      FiniteCategoricalSelection.rowLoad use row choice < threshold row := by
  apply FiniteCategoricalSupportSplit.exists_choice_rowLoad_lt_of_support_overlap
    prob use threshold lambda p x
    ((A0 + A1 * K) * (B0 + B1 * K))
    L.prob_nonneg L.prob_sum L.use_nonneg L.use_le_one hlambda
    L.overlapNeighbor_card_le hx0 hx1 hnumeric hchernoff

/-- Combined graph-and-probability interface.  The large-star estimate is
returned together with the synchronized profile choice, so an application
only has to construct the concrete padded menu ledger and verify its two
affine incidence bounds. -/
theorem exists_profileSynchronization_choice_of_localPacking
    {n K : ℕ} (hlocal : G.LocallyPacksInto n)
    {beta : ℝ} (hbeta : 0 < beta)
    (hK : (n : ℝ) < ((K + 1 : ℕ) : ℝ) * beta)
    (prob : G.ProfileSource Color → State → ℝ)
    (use : G.ProfileSource Color → State → Row → ℝ)
    (A0 A1 B0 B1 : ℕ)
    (L : G.ProfileSynchronizationLedger prob use A0 A1 B0 B1 K)
    (threshold lambda : Row → ℝ) (p x : ℝ)
    (hlambda : ∀ row, 0 ≤ lambda row)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hnumeric : p ≤ x * (1 - x) ^
      ((A0 + A1 * K) * (B0 + B1 * K)))
    (hchernoff : ∀ row,
      Real.exp (-lambda row * threshold row +
        (Real.exp (lambda row) - 1) *
          FiniteCategoricalSelection.rowMean prob use row) ≤ p) :
    (∀ v, (G.largeStarEdges beta v).card ≤ K) ∧
      ∃ choice : G.ProfileSource Color → State, ∀ row,
        FiniteCategoricalSelection.rowLoad use row choice < threshold row := by
  refine ⟨G.profileSynchronization_largeStar_card_le hlocal hbeta hK, ?_⟩
  exact G.exists_profileSynchronization_choice prob use A0 A1 B0 B1 K L
    threshold lambda p x hlambda hx0 hx1 hnumeric hchernoff

end WeightedMultigraph

end

end WeightedEdgeColoring
