import WeightedEdgeColoring.ExtendedProfileSelectedOptionArrays

/-!
# Clipping selected profile options edge by edge

The selected equation-(23) array can have total mass larger than one on an
edge.  This file divides every option of that edge by `max 1 S_e`.  The
operation never increases a capacity load, leaves total coloured mass
`min 1 S_e`, and preserves the positive support of every option.  The
remaining mass is represented explicitly as an uncoloured option.

This is only deterministic finite algebra.  No matching or rounding theorem
is used here.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})
variable {B k : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- The common denominator used to clip every option of one edge. -/
def selectedBlockNormalizationDenominator
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) : ℝ :=
  max 1 (G.selectedBlockAllOptionMass R0 rho omega choice e)

theorem one_le_selectedBlockNormalizationDenominator
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) :
    1 ≤ G.selectedBlockNormalizationDenominator R0 rho omega choice e := by
  exact le_max_left _ _

theorem selectedBlockNormalizationDenominator_pos
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) :
    0 < G.selectedBlockNormalizationDenominator R0 rho omega choice e := by
  exact zero_lt_one.trans_le
    (G.one_le_selectedBlockNormalizationDenominator R0 rho omega choice e)

/-- A selected large-slot option after edgewise clipping. -/
def selectedBlockNormalizedLargeOptionMass
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (i j : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  G.selectedBlockLargeOptionMass R0 rho omega choice e c i j /
    G.selectedBlockNormalizationDenominator R0 rho omega choice e

/-- A selected tiny-reservoir option after edgewise clipping. -/
def selectedBlockNormalizedTinyOptionMass
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k)) : ℝ :=
  G.selectedBlockTinyOptionMass R0 rho omega choice e c /
    G.selectedBlockNormalizationDenominator R0 rho omega choice e

/-- Mass of the private option which leaves an edge uncoloured. -/
def selectedBlockResidualOptionMass
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) : ℝ :=
  1 - min 1 (G.selectedBlockAllOptionMass R0 rho omega choice e)

theorem selectedBlockNormalizedLargeOptionMass_nonneg
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (i j : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.selectedBlockNormalizedLargeOptionMass
      R0 rho omega choice e c i j := by
  exact div_nonneg
    (G.selectedBlockLargeOptionMass_nonneg R0 hn hs hq hr0 hleft
      homega0 homega1 hrho choice e c i j)
    (G.selectedBlockNormalizationDenominator_pos
      R0 rho omega choice e).le

theorem selectedBlockNormalizedTinyOptionMass_nonneg
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k)) :
    0 ≤ G.selectedBlockNormalizedTinyOptionMass
      R0 rho omega choice e c := by
  exact div_nonneg
    (G.selectedBlockTinyOptionMass_nonneg R0 hn hs hq hr0 hleft
      homega0 homega1 hrho choice e c)
    (G.selectedBlockNormalizationDenominator_pos
      R0 rho omega choice e).le

theorem selectedBlockResidualOptionMass_nonneg
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) :
    0 ≤ G.selectedBlockResidualOptionMass R0 rho omega choice e := by
  unfold selectedBlockResidualOptionMass
  exact sub_nonneg.mpr (min_le_left _ _)

/-- Clipping never increases a large option. -/
theorem selectedBlockNormalizedLargeOptionMass_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (i j : Fin (explicitLargeSlotBound β q r)) :
    G.selectedBlockNormalizedLargeOptionMass
        R0 rho omega choice e c i j ≤
      G.selectedBlockLargeOptionMass R0 rho omega choice e c i j := by
  let x := G.selectedBlockLargeOptionMass R0 rho omega choice e c i j
  let d := G.selectedBlockNormalizationDenominator R0 rho omega choice e
  have hx : 0 ≤ x := G.selectedBlockLargeOptionMass_nonneg R0
    hn hs hq hr0 hleft homega0 homega1 hrho choice e c i j
  have hd : 0 < d :=
    G.selectedBlockNormalizationDenominator_pos R0 rho omega choice e
  have hd1 : 1 ≤ d :=
    G.one_le_selectedBlockNormalizationDenominator R0 rho omega choice e
  change x / d ≤ x
  apply (div_le_iff₀ hd).2
  simpa using mul_le_mul_of_nonneg_left hd1 hx

/-- Clipping never increases a tiny option. -/
theorem selectedBlockNormalizedTinyOptionMass_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k)) :
    G.selectedBlockNormalizedTinyOptionMass R0 rho omega choice e c ≤
      G.selectedBlockTinyOptionMass R0 rho omega choice e c := by
  let x := G.selectedBlockTinyOptionMass R0 rho omega choice e c
  let d := G.selectedBlockNormalizationDenominator R0 rho omega choice e
  have hx : 0 ≤ x := G.selectedBlockTinyOptionMass_nonneg R0
    hn hs hq hr0 hleft homega0 homega1 hrho choice e c
  have hd : 0 < d :=
    G.selectedBlockNormalizationDenominator_pos R0 rho omega choice e
  have hd1 : 1 ≤ d :=
    G.one_le_selectedBlockNormalizationDenominator R0 rho omega choice e
  change x / d ≤ x
  apply (div_le_iff₀ hd).2
  simpa using mul_le_mul_of_nonneg_left hd1 hx

/-- Clipping preserves positive support for a large option. -/
theorem selectedBlockNormalizedLargeOptionMass_pos_iff
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (i j : Fin (explicitLargeSlotBound β q r)) :
    0 < G.selectedBlockNormalizedLargeOptionMass
        R0 rho omega choice e c i j ↔
      0 < G.selectedBlockLargeOptionMass R0 rho omega choice e c i j := by
  let d := G.selectedBlockNormalizationDenominator R0 rho omega choice e
  have hd : 0 < d :=
    G.selectedBlockNormalizationDenominator_pos R0 rho omega choice e
  change 0 < G.selectedBlockLargeOptionMass
      R0 rho omega choice e c i j / d ↔ _
  constructor
  · intro h
    rcases div_pos_iff.mp h with hpos | hneg
    · exact hpos.1
    · exact (not_lt_of_ge hd.le hneg.2).elim
  · intro h
    exact div_pos h hd

/-- Clipping preserves positive support for a tiny option. -/
theorem selectedBlockNormalizedTinyOptionMass_pos_iff
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k)) :
    0 < G.selectedBlockNormalizedTinyOptionMass
        R0 rho omega choice e c ↔
      0 < G.selectedBlockTinyOptionMass R0 rho omega choice e c := by
  let d := G.selectedBlockNormalizationDenominator R0 rho omega choice e
  have hd : 0 < d :=
    G.selectedBlockNormalizationDenominator_pos R0 rho omega choice e
  change 0 < G.selectedBlockTinyOptionMass R0 rho omega choice e c / d ↔ _
  constructor
  · intro h
    rcases div_pos_iff.mp h with hpos | hneg
    · exact hpos.1
    · exact (not_lt_of_ge hd.le hneg.2).elim
  · intro h
    exact div_pos h hd

/-- The total clipped coloured mass of an edge is exactly `min 1 S_e`. -/
theorem sum_selectedBlockNormalizedOptionMass
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) :
    (∑ c : Fin (B * k), (
      (∑ i, ∑ j,
        G.selectedBlockNormalizedLargeOptionMass
          R0 rho omega choice e c i j) +
        G.selectedBlockNormalizedTinyOptionMass
          R0 rho omega choice e c)) =
      min 1 (G.selectedBlockAllOptionMass R0 rho omega choice e) := by
  let d := G.selectedBlockNormalizationDenominator R0 rho omega choice e
  have hmass : 0 ≤ G.selectedBlockAllOptionMass R0 rho omega choice e :=
    G.selectedBlockAllOptionMass_nonneg R0 hn hs hq hr0 hleft
      homega0 homega1 hrho choice e
  change
    (∑ c : Fin (B * k), (
      (∑ i, ∑ j,
        G.selectedBlockLargeOptionMass R0 rho omega choice e c i j / d) +
        G.selectedBlockTinyOptionMass R0 rho omega choice e c / d)) = _
  have hfactor :
      (∑ c : Fin (B * k), (
        (∑ i, ∑ j,
          G.selectedBlockLargeOptionMass R0 rho omega choice e c i j / d) +
          G.selectedBlockTinyOptionMass R0 rho omega choice e c / d)) =
        G.selectedBlockAllOptionMass R0 rho omega choice e / d := by
    unfold selectedBlockAllOptionMass
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _hc
    rw [add_div, Finset.sum_div]
    apply congrArg₂ (· + ·) ?_ rfl
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.sum_div]
  rw [hfactor]
  change G.selectedBlockAllOptionMass R0 rho omega choice e /
      max 1 (G.selectedBlockAllOptionMass R0 rho omega choice e) = _
  exact OptionNormalization.div_max_one_eq_min_one _ hmass

/-! ## The large and tiny supports are disjoint -/

theorem selectedBlockLargeOptionMass_eq_zero_of_tiny
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (i j : Fin (explicitLargeSlotBound β q r))
    (htiny : G.weight e < β) :
    G.selectedBlockLargeOptionMass R0 rho omega choice e c i j = 0 := by
  unfold selectedBlockLargeOptionMass extendedProfileProductOptionMass
  simp [pairedOption, extendedProfileEdgeColorMass,
    not_le_of_gt htiny]

theorem selectedBlockTinyOptionMass_eq_zero_of_large
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (hlarge : β ≤ G.weight e) :
    G.selectedBlockTinyOptionMass R0 rho omega choice e c = 0 := by
  unfold selectedBlockTinyOptionMass extendedProfileTinyProductOptionMass
  simp [pairedOption, extendedProfileTinyEdgeColorMass,
    not_lt_of_ge hlarge]

theorem selectedBlockNormalizedLargeOptionMass_eq_zero_of_tiny
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (i j : Fin (explicitLargeSlotBound β q r))
    (htiny : G.weight e < β) :
    G.selectedBlockNormalizedLargeOptionMass
        R0 rho omega choice e c i j = 0 := by
  unfold selectedBlockNormalizedLargeOptionMass
  rw [G.selectedBlockLargeOptionMass_eq_zero_of_tiny
    R0 rho omega choice e c i j htiny]
  exact zero_div _

theorem selectedBlockNormalizedTinyOptionMass_eq_zero_of_large
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (hlarge : β ≤ G.weight e) :
    G.selectedBlockNormalizedTinyOptionMass
        R0 rho omega choice e c = 0 := by
  unfold selectedBlockNormalizedTinyOptionMass
  rw [G.selectedBlockTinyOptionMass_eq_zero_of_large
    R0 rho omega choice e c hlarge]
  exact zero_div _

/-- Coloured and uncoloured option masses add to one on every edge. -/
theorem sum_selectedBlockNormalizedOptionMass_add_residual
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) :
    (∑ c : Fin (B * k), (
      (∑ i, ∑ j,
        G.selectedBlockNormalizedLargeOptionMass
          R0 rho omega choice e c i j) +
        G.selectedBlockNormalizedTinyOptionMass
          R0 rho omega choice e c)) +
      G.selectedBlockResidualOptionMass R0 rho omega choice e = 1 := by
  rw [G.sum_selectedBlockNormalizedOptionMass R0 hn hs hq hr0 hleft
    homega0 homega1 hrho choice e]
  unfold selectedBlockResidualOptionMass
  ring

/-- On a large edge, the normalized ordinary options and its private
uncoloured option form a probability distribution. -/
theorem sum_selectedBlockNormalizedLarge_add_residual_of_large
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (hlarge : β ≤ G.weight e) :
    (∑ c : Fin (B * k), ∑ i, ∑ j,
      G.selectedBlockNormalizedLargeOptionMass
        R0 rho omega choice e c i j) +
      G.selectedBlockResidualOptionMass R0 rho omega choice e = 1 := by
  have hzero (c : Fin (B * k)) :
      G.selectedBlockNormalizedTinyOptionMass
          R0 rho omega choice e c = 0 :=
    G.selectedBlockNormalizedTinyOptionMass_eq_zero_of_large
      R0 rho omega choice e c hlarge
  simpa only [hzero, add_zero] using
    (G.sum_selectedBlockNormalizedOptionMass_add_residual R0
      hn hs hq hr0 hleft homega0 homega1 hrho choice e)

/-- On a tiny edge, the normalized colour options and its private uncoloured
option form a probability distribution. -/
theorem sum_selectedBlockNormalizedTiny_add_residual_of_tiny
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (htiny : G.weight e < β) :
    (∑ c : Fin (B * k),
      G.selectedBlockNormalizedTinyOptionMass
        R0 rho omega choice e c) +
      G.selectedBlockResidualOptionMass R0 rho omega choice e = 1 := by
  have hzero (c : Fin (B * k))
      (i j : Fin (explicitLargeSlotBound β q r)) :
      G.selectedBlockNormalizedLargeOptionMass
          R0 rho omega choice e c i j = 0 :=
    G.selectedBlockNormalizedLargeOptionMass_eq_zero_of_tiny
      R0 rho omega choice e c i j htiny
  simpa only [hzero, Finset.sum_const_zero, zero_add] using
    (G.sum_selectedBlockNormalizedOptionMass_add_residual R0
      hn hs hq hr0 hleft homega0 homega1 hrho choice e)

/-- Fractional load of one ordinary slot after clipping. -/
def selectedBlockNormalizedLargeSlotLoad
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileLargeRow
      (n := B * k) (β := β) (q := q) (r := r)) : ℝ :=
  ∑ e : G.E, (
    (if row.1 = G.fst e then
      ∑ j, G.selectedBlockNormalizedLargeOptionMass
        R0 rho omega choice e row.2.1 row.2.2 j
    else 0) +
    (if row.1 = G.snd e then
      ∑ i, G.selectedBlockNormalizedLargeOptionMass
        R0 rho omega choice e row.2.1 i row.2.2
    else 0))

/-- Weighted fractional load of one tiny reservoir after clipping. -/
def selectedBlockNormalizedTinyReservoirLoad
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileTinyRow (n := B * k)) : ℝ :=
  ∑ e : G.E, if G.Inc row.1 e then
    G.weight e * G.selectedBlockNormalizedTinyOptionMass
      R0 rho omega choice e row.2
  else 0

/-- Every clipped ordinary-slot load is at most its selected raw load. -/
theorem selectedBlockNormalizedLargeSlotLoad_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileLargeRow
      (n := B * k) (β := β) (q := q) (r := r)) :
    G.selectedBlockNormalizedLargeSlotLoad R0 rho omega choice row ≤
      G.selectedBlockLargeSlotLoad R0 rho omega choice row := by
  unfold selectedBlockNormalizedLargeSlotLoad selectedBlockLargeSlotLoad
  apply Finset.sum_le_sum
  intro e _he
  apply add_le_add
  · by_cases hfst : row.1 = G.fst e
    · simp only [hfst, if_true]
      exact Finset.sum_le_sum fun j _hj ↦
        G.selectedBlockNormalizedLargeOptionMass_le R0 hn hs hq hr0
          hleft homega0 homega1 hrho choice e row.2.1 row.2.2 j
    · simp [hfst]
  · by_cases hsnd : row.1 = G.snd e
    · simp only [hsnd, if_true]
      exact Finset.sum_le_sum fun i _hi ↦
        G.selectedBlockNormalizedLargeOptionMass_le R0 hn hs hq hr0
          hleft homega0 homega1 hrho choice e row.2.1 i row.2.2
    · simp [hsnd]

/-- Every clipped tiny-reservoir load is at most its selected raw load. -/
theorem selectedBlockNormalizedTinyReservoirLoad_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileTinyRow (n := B * k)) :
    G.selectedBlockNormalizedTinyReservoirLoad R0 rho omega choice row ≤
      G.selectedBlockTinyReservoirLoad R0 rho omega choice row := by
  unfold selectedBlockNormalizedTinyReservoirLoad
    selectedBlockTinyReservoirLoad
  apply Finset.sum_le_sum
  intro e _he
  by_cases hinc : G.Inc row.1 e
  · simp only [hinc, if_true]
    exact mul_le_mul_of_nonneg_left
      (G.selectedBlockNormalizedTinyOptionMass_le R0 hn hs hq hr0
        hleft homega0 homega1 hrho choice e row.2)
      (G.weight_nonneg e)
  · simp [hinc]

/-- A positive clipped large option still uses fitting slots at both ends. -/
theorem selectedBlockNormalizedLargeOptionMass_pos_fits
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (i j : Fin (explicitLargeSlotBound β q r))
    (hpos : 0 < G.selectedBlockNormalizedLargeOptionMass
      R0 rho omega choice e c i j) :
    G.ExtendedLargeSlotFits R0 (G.fst e) (G.fstStarEdge e)
        (G.decodedExtendedProfileBlockSelection R0 choice (G.fst e) c) i ∧
      G.ExtendedLargeSlotFits R0 (G.snd e) (G.sndStarEdge e)
        (G.decodedExtendedProfileBlockSelection R0 choice (G.snd e) c) j := by
  apply G.selectedBlockLargeOptionMass_pos_fits R0 hn hs hq hr0 hleft
    homega0 homega1 hrho choice e c i j
  exact (G.selectedBlockNormalizedLargeOptionMass_pos_iff
    R0 rho omega choice e c i j).mp hpos

/-- A positive clipped tiny option is still supported by two positive
reservoirs and an edge below the tiny threshold. -/
theorem selectedBlockNormalizedTinyOptionMass_pos_fit
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (hpos : 0 < G.selectedBlockNormalizedTinyOptionMass
      R0 rho omega choice e c) :
    (G.weight e < β ∧
      0 < G.extendedProfileReservoirSize R0 (G.fst e)
        (G.decodedExtendedProfileBlockSelection R0 choice (G.fst e) c)) ∧
    (G.weight e < β ∧
      0 < G.extendedProfileReservoirSize R0 (G.snd e)
        (G.decodedExtendedProfileBlockSelection R0 choice (G.snd e) c)) := by
  apply G.selectedBlockTinyOptionMass_pos_fit R0 hn hs hq hr0 hleft
    homega0 homega1 hrho choice e c
  exact (G.selectedBlockNormalizedTinyOptionMass_pos_iff
    R0 rho omega choice e c).mp hpos

end WeightedSimpleGraph

end

end WeightedEdgeColoring
