import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileBlockVarianceRows
import WeightedEdgeColoring.LargeEdgeOptions
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeExtraCapture
import WeightedEdgeColoring.WeightedMomentProposal

/-!
# Clipped selected options for color-dependent profiles

The fixed-block selector produces one extended state for every vertex and
color.  This file decodes its equation-(23) arrays and clips every edge by
`max 1 S_e`.  The clipped ordinary mass and a private residual form an exact
probability distribution on every macroscopic edge, ready for the generic
`LargeEdgeOptions` stack.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

def selectedColorDependentLargeOptionMass
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k)
    (i j : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  G.colorDependentExtendedProfileLargeProductMass proposal R rho omega e c
    (G.decodeColorDependentExtendedProfileBlock proposal R
      (G.fst e, c.1) (choice (G.fst e, c.1)) c.2)
    (G.decodeColorDependentExtendedProfileBlock proposal R
      (G.snd e, c.1) (choice (G.snd e, c.1)) c.2) i j

def selectedColorDependentTinyOptionMass
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k) : ℝ :=
  G.colorDependentExtendedProfileTinyProductMass proposal R rho omega e c
    (G.decodeColorDependentExtendedProfileBlock proposal R
      (G.fst e, c.1) (choice (G.fst e, c.1)) c.2)
    (G.decodeColorDependentExtendedProfileBlock proposal R
      (G.snd e, c.1) (choice (G.snd e, c.1)) c.2)

def selectedColorDependentAllOptionMass
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) : ℝ :=
  ∑ c : (Fin B × Fin k),
    ((∑ i, ∑ j, G.selectedColorDependentLargeOptionMass
      proposal R rho omega choice e c i j) +
      G.selectedColorDependentTinyOptionMass
        proposal R rho omega choice e c)

theorem selectedColorDependentAllOptionMass_eq_total
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) :
    G.selectedColorDependentAllOptionMass proposal R rho omega choice e =
      G.selectedColorDependentTotalOptionMass
        proposal R rho omega choice e := by
  unfold selectedColorDependentAllOptionMass
    selectedColorDependentTotalOptionMass colorDependentBlockOptionMass
    colorDependentCoordinateOptionMass
    selectedColorDependentLargeOptionMass selectedColorDependentTinyOptionMass
  rw [Fintype.sum_prod_type]

theorem selectedColorDependentLargeOptionMass_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k)
    (i j : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.selectedColorDependentLargeOptionMass
      proposal R rho omega choice e c i j := by
  exact G.colorDependentExtendedProfileLargeProductMass_nonneg proposal R
    hs hq hr0 hleft homega0 homega1 hrho e c _ _ i j

theorem selectedColorDependentTinyOptionMass_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k) :
    0 ≤ G.selectedColorDependentTinyOptionMass
      proposal R rho omega choice e c := by
  exact G.colorDependentExtendedProfileTinyProductMass_nonneg proposal R
    hs hq hr0 hleft homega0 homega1 hrho e c _ _

theorem selectedColorDependentAllOptionMass_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) :
    0 ≤ G.selectedColorDependentAllOptionMass
      proposal R rho omega choice e := by
  unfold selectedColorDependentAllOptionMass
  exact Finset.sum_nonneg fun c _hc ↦ add_nonneg
    (Finset.sum_nonneg fun i _hi ↦ Finset.sum_nonneg fun j _hj ↦
      G.selectedColorDependentLargeOptionMass_nonneg proposal R
        hs hq hr0 hleft homega0 homega1 hrho choice e c i j)
    (G.selectedColorDependentTinyOptionMass_nonneg proposal R
      hs hq hr0 hleft homega0 homega1 hrho choice e c)

def selectedColorDependentNormalizationDenominator
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) : ℝ :=
  max 1 (G.selectedColorDependentAllOptionMass
    proposal R rho omega choice e)

theorem selectedColorDependentNormalizationDenominator_pos
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) :
    0 < G.selectedColorDependentNormalizationDenominator
      proposal R rho omega choice e :=
  zero_lt_one.trans_le (le_max_left _ _)

def selectedColorDependentNormalizedLargeOptionMass
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k)
    (i j : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  G.selectedColorDependentLargeOptionMass proposal R rho omega choice e c i j /
    G.selectedColorDependentNormalizationDenominator
      proposal R rho omega choice e

/-- A selected tiny-reservoir option after the same edgewise clipping. -/
def selectedColorDependentNormalizedTinyOptionMass
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k) : ℝ :=
  G.selectedColorDependentTinyOptionMass proposal R rho omega choice e c /
    G.selectedColorDependentNormalizationDenominator
      proposal R rho omega choice e

def selectedColorDependentResidualOptionMass
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) : ℝ :=
  1 - min 1 (G.selectedColorDependentAllOptionMass
    proposal R rho omega choice e)

theorem selectedColorDependentNormalizedLargeOptionMass_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k)
    (i j : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.selectedColorDependentNormalizedLargeOptionMass
      proposal R rho omega choice e c i j := by
  exact div_nonneg
    (G.selectedColorDependentLargeOptionMass_nonneg proposal R
      hs hq hr0 hleft homega0 homega1 hrho choice e c i j)
    (G.selectedColorDependentNormalizationDenominator_pos
      proposal R rho omega choice e).le

/-- Clipping never increases an ordinary large-slot option. -/
theorem selectedColorDependentNormalizedLargeOptionMass_le
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k)
    (i j : Fin (explicitLargeSlotBound β q r)) :
    G.selectedColorDependentNormalizedLargeOptionMass
        proposal R rho omega choice e c i j ≤
      G.selectedColorDependentLargeOptionMass
        proposal R rho omega choice e c i j := by
  let x := G.selectedColorDependentLargeOptionMass
    proposal R rho omega choice e c i j
  let d := G.selectedColorDependentNormalizationDenominator
    proposal R rho omega choice e
  have hx : 0 ≤ x := G.selectedColorDependentLargeOptionMass_nonneg proposal R
    hs hq hr0 hleft homega0 homega1 hrho choice e c i j
  have hd : 0 < d := G.selectedColorDependentNormalizationDenominator_pos
    proposal R rho omega choice e
  have hd1 : 1 ≤ d := le_max_left _ _
  change x / d ≤ x
  apply (div_le_iff₀ hd).2
  simpa using mul_le_mul_of_nonneg_left hd1 hx

theorem selectedColorDependentResidualOptionMass_nonneg
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) :
    0 ≤ G.selectedColorDependentResidualOptionMass
      proposal R rho omega choice e :=
  sub_nonneg.mpr (min_le_left _ _)

theorem selectedColorDependentNormalizedTinyOptionMass_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k) :
    0 ≤ G.selectedColorDependentNormalizedTinyOptionMass
      proposal R rho omega choice e c := by
  exact div_nonneg
    (G.selectedColorDependentTinyOptionMass_nonneg proposal R
      hs hq hr0 hleft homega0 homega1 hrho choice e c)
    (G.selectedColorDependentNormalizationDenominator_pos
      proposal R rho omega choice e).le

/-- Clipping never increases a tiny-reservoir option. -/
theorem selectedColorDependentNormalizedTinyOptionMass_le
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k) :
    G.selectedColorDependentNormalizedTinyOptionMass
        proposal R rho omega choice e c ≤
      G.selectedColorDependentTinyOptionMass
        proposal R rho omega choice e c := by
  let x := G.selectedColorDependentTinyOptionMass
    proposal R rho omega choice e c
  let d := G.selectedColorDependentNormalizationDenominator
    proposal R rho omega choice e
  have hx : 0 ≤ x := G.selectedColorDependentTinyOptionMass_nonneg proposal R
    hs hq hr0 hleft homega0 homega1 hrho choice e c
  have hd : 0 < d := G.selectedColorDependentNormalizationDenominator_pos
    proposal R rho omega choice e
  have hd1 : 1 ≤ d := le_max_left _ _
  change x / d ≤ x
  apply (div_le_iff₀ hd).2
  simpa using mul_le_mul_of_nonneg_left hd1 hx

theorem selectedColorDependentNormalizedLargeOptionMass_pos_iff
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k)
    (i j : Fin (explicitLargeSlotBound β q r)) :
    0 < G.selectedColorDependentNormalizedLargeOptionMass
        proposal R rho omega choice e c i j ↔
      0 < G.selectedColorDependentLargeOptionMass
        proposal R rho omega choice e c i j := by
  unfold selectedColorDependentNormalizedLargeOptionMass
  let d := G.selectedColorDependentNormalizationDenominator
    proposal R rho omega choice e
  have hd : 0 < d :=
    G.selectedColorDependentNormalizationDenominator_pos
      proposal R rho omega choice e
  constructor
  · intro h
    rcases div_pos_iff.mp h with hpos | hneg
    · exact hpos.1
    · exact (not_lt_of_ge hd.le hneg.2).elim
  · intro h
    exact div_pos h hd

theorem selectedColorDependentNormalizedTinyOptionMass_pos_iff
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k) :
    0 < G.selectedColorDependentNormalizedTinyOptionMass
        proposal R rho omega choice e c ↔
      0 < G.selectedColorDependentTinyOptionMass
        proposal R rho omega choice e c := by
  unfold selectedColorDependentNormalizedTinyOptionMass
  let d := G.selectedColorDependentNormalizationDenominator
    proposal R rho omega choice e
  have hd : 0 < d :=
    G.selectedColorDependentNormalizationDenominator_pos
      proposal R rho omega choice e
  constructor
  · intro h
    rcases div_pos_iff.mp h with hpos | hneg
    · exact hpos.1
    · exact (not_lt_of_ge hd.le hneg.2).elim
  · intro h
    exact div_pos h hd

/-- Every positive ordinary option uses a positive proposal coordinate. -/
theorem proposal_pos_of_selectedColorDependentNormalizedLarge_pos
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k)
    (i j : Fin (explicitLargeSlotBound β q r))
    (hpos : 0 < G.selectedColorDependentNormalizedLargeOptionMass
      proposal R rho omega choice e c i j) :
    0 < proposal e c := by
  have hraw :=
    (G.selectedColorDependentNormalizedLargeOptionMass_pos_iff
      proposal R rho omega choice e c i j).mp hpos
  by_contra hnot
  have hzero : proposal e c = 0 :=
    le_antisymm (le_of_not_gt hnot) (hproposal0 e c)
  unfold selectedColorDependentLargeOptionMass
    colorDependentExtendedProfileLargeProductMass pairedOption
    colorDependentExtendedProfileLargeEdgeColorMass at hraw
  simp [hzero] at hraw

/-- The same support statement for a positive tiny-reservoir option. -/
theorem proposal_pos_of_selectedColorDependentNormalizedTiny_pos
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k)
    (hpos : 0 < G.selectedColorDependentNormalizedTinyOptionMass
      proposal R rho omega choice e c) :
    0 < proposal e c := by
  have hraw :=
    (G.selectedColorDependentNormalizedTinyOptionMass_pos_iff
      proposal R rho omega choice e c).mp hpos
  by_contra hnot
  have hzero : proposal e c = 0 :=
    le_antisymm (le_of_not_gt hnot) (hproposal0 e c)
  unfold selectedColorDependentTinyOptionMass
    colorDependentExtendedProfileTinyProductMass pairedOption
    colorDependentExtendedProfileTinyEdgeColorMass at hraw
  simp [hzero] at hraw

theorem selectedColorDependentTinyOptionMass_eq_zero_of_large
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k) (hlarge : β ≤ G.weight e) :
    G.selectedColorDependentTinyOptionMass
      proposal R rho omega choice e c = 0 := by
  unfold selectedColorDependentTinyOptionMass
    colorDependentExtendedProfileTinyProductMass pairedOption
    colorDependentExtendedProfileTinyEdgeColorMass
  simp [not_lt_of_ge hlarge]

theorem selectedColorDependentLargeOptionMass_eq_zero_of_tiny
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k)
    (i j : Fin (explicitLargeSlotBound β q r))
    (htiny : G.weight e < β) :
    G.selectedColorDependentLargeOptionMass
      proposal R rho omega choice e c i j = 0 := by
  unfold selectedColorDependentLargeOptionMass
    colorDependentExtendedProfileLargeProductMass pairedOption
    colorDependentExtendedProfileLargeEdgeColorMass
  simp [not_le_of_gt htiny]

theorem selectedColorDependentNormalizedLargeOptionMass_eq_zero_of_tiny
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (c : Fin B × Fin k)
    (i j : Fin (explicitLargeSlotBound β q r))
    (htiny : G.weight e < β) :
    G.selectedColorDependentNormalizedLargeOptionMass
        proposal R rho omega choice e c i j = 0 := by
  unfold selectedColorDependentNormalizedLargeOptionMass
  rw [G.selectedColorDependentLargeOptionMass_eq_zero_of_tiny
    proposal R rho omega choice e c i j htiny]
  exact zero_div _

/-- For every edge, the clipped large and tiny arrays together with the
private residual have total mass one. -/
theorem sum_selectedColorDependentNormalizedOptionMass_add_residual
    (rho omega : ℝ)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) :
    (∑ c : Fin B × Fin k,
      ((∑ i, ∑ j,
        G.selectedColorDependentNormalizedLargeOptionMass
          proposal R rho omega choice e c i j) +
        G.selectedColorDependentNormalizedTinyOptionMass
          proposal R rho omega choice e c)) +
      G.selectedColorDependentResidualOptionMass
        proposal R rho omega choice e = 1 := by
  let S := G.selectedColorDependentAllOptionMass
    proposal R rho omega choice e
  let d := G.selectedColorDependentNormalizationDenominator
    proposal R rho omega choice e
  have hS0 : 0 ≤ S := G.selectedColorDependentAllOptionMass_nonneg proposal R
    hs hq hr0 hleft homega0 homega1 hrho choice e
  have hfactor :
      (∑ c : Fin B × Fin k,
        ((∑ i, ∑ j,
          G.selectedColorDependentNormalizedLargeOptionMass
            proposal R rho omega choice e c i j) +
          G.selectedColorDependentNormalizedTinyOptionMass
            proposal R rho omega choice e c)) = S / d := by
    unfold selectedColorDependentNormalizedLargeOptionMass
      selectedColorDependentNormalizedTinyOptionMass
    unfold S selectedColorDependentAllOptionMass
    change
      (∑ c : Fin B × Fin k,
        ((∑ i, ∑ j,
          G.selectedColorDependentLargeOptionMass
            proposal R rho omega choice e c i j / d) +
          G.selectedColorDependentTinyOptionMass
            proposal R rho omega choice e c / d)) =
        (∑ c : Fin B × Fin k,
          ((∑ i, ∑ j,
            G.selectedColorDependentLargeOptionMass
              proposal R rho omega choice e c i j) +
            G.selectedColorDependentTinyOptionMass
              proposal R rho omega choice e c)) / d
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _hc
    have hj (i : Fin (explicitLargeSlotBound β q r)) :
        (∑ j, G.selectedColorDependentLargeOptionMass
          proposal R rho omega choice e c i j / d) =
          (∑ j, G.selectedColorDependentLargeOptionMass
            proposal R rho omega choice e c i j) / d := by
      exact (Finset.sum_div Finset.univ
        (fun j ↦ G.selectedColorDependentLargeOptionMass
          proposal R rho omega choice e c i j) d).symm
    calc
      ((∑ i, ∑ j, G.selectedColorDependentLargeOptionMass
          proposal R rho omega choice e c i j / d) +
        G.selectedColorDependentTinyOptionMass
          proposal R rho omega choice e c / d) =
          ((∑ i, (∑ j, G.selectedColorDependentLargeOptionMass
            proposal R rho omega choice e c i j) / d) +
            G.selectedColorDependentTinyOptionMass
              proposal R rho omega choice e c / d) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _hi
            exact hj i
      _ = ((∑ i, ∑ j, G.selectedColorDependentLargeOptionMass
            proposal R rho omega choice e c i j) / d) +
            G.selectedColorDependentTinyOptionMass
              proposal R rho omega choice e c / d := by
            congr 1
            exact (Finset.sum_div Finset.univ
              (fun i ↦ ∑ j, G.selectedColorDependentLargeOptionMass
                proposal R rho omega choice e c i j) d).symm
      _ = _ := (add_div _ _ _).symm
  rw [hfactor]
  change S / max 1 S + (1 - min 1 S) = 1
  rw [OptionNormalization.div_max_one_eq_min_one S hS0]
  ring

/-- On a profile-tiny edge only the tiny array and residual remain. -/
theorem sum_selectedColorDependentNormalizedTiny_add_residual_of_tiny
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (htiny : G.weight e < β) :
    (∑ c : Fin B × Fin k,
      G.selectedColorDependentNormalizedTinyOptionMass
        proposal R rho omega choice e c) +
      G.selectedColorDependentResidualOptionMass
        proposal R rho omega choice e = 1 := by
  have hzero (c : Fin B × Fin k)
      (i j : Fin (explicitLargeSlotBound β q r)) :
      G.selectedColorDependentNormalizedLargeOptionMass
          proposal R rho omega choice e c i j = 0 :=
    G.selectedColorDependentNormalizedLargeOptionMass_eq_zero_of_tiny
      proposal R rho omega choice e c i j htiny
  have htotal :=
    G.sum_selectedColorDependentNormalizedOptionMass_add_residual
      proposal R rho omega hs hq hr0 hleft homega0 homega1 hrho choice e
  simp_rw [hzero] at htotal
  simpa using htotal

/-- On a macroscopic edge, clipping the ordinary array and adding the
private residual gives total mass exactly one. -/
theorem sum_selectedColorDependentNormalizedLarge_add_residual_of_large
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (e : G.E) (hlarge : β ≤ G.weight e) :
    (∑ c : Fin B × Fin k, ∑ i, ∑ j,
      G.selectedColorDependentNormalizedLargeOptionMass
        proposal R rho omega choice e c i j) +
      G.selectedColorDependentResidualOptionMass
        proposal R rho omega choice e = 1 := by
  let S := G.selectedColorDependentAllOptionMass
    proposal R rho omega choice e
  let d := G.selectedColorDependentNormalizationDenominator
    proposal R rho omega choice e
  have hS0 : 0 ≤ S := G.selectedColorDependentAllOptionMass_nonneg proposal R
    hs hq hr0 hleft homega0 homega1 hrho choice e
  have htiny : ∀ c : Fin B × Fin k,
      G.selectedColorDependentTinyOptionMass
        proposal R rho omega choice e c = 0 := fun c ↦
    G.selectedColorDependentTinyOptionMass_eq_zero_of_large
      proposal R rho omega choice e c hlarge
  have hraw : (∑ c : Fin B × Fin k, ∑ i, ∑ j,
      G.selectedColorDependentLargeOptionMass
        proposal R rho omega choice e c i j) = S := by
    unfold S selectedColorDependentAllOptionMass
    simp only [htiny, add_zero]
  have hfactor :
      (∑ c : Fin B × Fin k, ∑ i, ∑ j,
        G.selectedColorDependentNormalizedLargeOptionMass
          proposal R rho omega choice e c i j) = S / d := by
    unfold selectedColorDependentNormalizedLargeOptionMass
    have hquot := congrArg (fun x : ℝ ↦ x / d) hraw
    simpa only [Finset.sum_div] using hquot
  rw [hfactor]
  change S / max 1 S + (1 - min 1 S) = 1
  rw [OptionNormalization.div_max_one_eq_min_one S hS0]
  ring

/-! ## Loss caused by clipping -/

/-- The clipping residual is controlled by the gap below any target at most
one, plus the absolute error from that target.  The target is allowed to
depend on the edge; for the retained core it will be
`rho * s * proposalMass proposal e`. -/
theorem selectedColorDependentResidualOptionMass_le_target_add_abs
    (rho omega target : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (htarget : target ≤ 1) (e : G.E) :
    G.selectedColorDependentResidualOptionMass
        proposal R rho omega choice e ≤
      (1 - target) +
        |G.selectedColorDependentAllOptionMass
            proposal R rho omega choice e - target| := by
  unfold selectedColorDependentResidualOptionMass
  by_cases htotal : 1 ≤
      G.selectedColorDependentAllOptionMass proposal R rho omega choice e
  · rw [min_eq_left htotal]
    have hgap : 0 ≤ 1 - target := sub_nonneg.mpr htarget
    simpa only [sub_self] using add_nonneg hgap (abs_nonneg
      (G.selectedColorDependentAllOptionMass
        proposal R rho omega choice e - target))
  · have htotal' :
        G.selectedColorDependentAllOptionMass proposal R rho omega choice e ≤ 1 :=
      le_of_not_ge htotal
    rw [min_eq_right htotal']
    have habs : target -
          G.selectedColorDependentAllOptionMass proposal R rho omega choice e ≤
        |G.selectedColorDependentAllOptionMass
            proposal R rho omega choice e - target| := by
      rw [← neg_sub]
      exact neg_le_abs _
    linarith

/-- Weighted absolute error is bounded by the square root of the weighted
quadratic error.  This version has an edge-dependent target. -/
theorem selectedColorDependentAbsoluteError_le_sqrt
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (target : G.E → ℝ) (v : G.V) (sigma : ℝ) (hsigma0 : 0 ≤ sigma)
    (hquad :
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedColorDependentAllOptionMass
          proposal R rho omega choice e.1 - target e.1) ^ 2) ≤ sigma) :
    (∑ e : G.StarEdge v, G.weight e.1 *
      |G.selectedColorDependentAllOptionMass
        proposal R rho omega choice e.1 - target e.1|) ≤
        Real.sqrt (G.starWeight v * sigma) := by
  let S : Finset (G.StarEdge v) := Finset.univ
  have hcs := WeightedMultigraph.weighted_abs_error_sq_le S
    (fun e : G.StarEdge v ↦ G.weight e.1)
    (fun e : G.StarEdge v ↦
      G.selectedColorDependentAllOptionMass
        proposal R rho omega choice e.1 - target e.1)
    (fun e _ ↦ G.weight_nonneg e.1)
  apply Real.le_sqrt_of_sq_le
  calc
    (∑ e : G.StarEdge v, G.weight e.1 *
      |G.selectedColorDependentAllOptionMass
        proposal R rho omega choice e.1 - target e.1|) ^ 2 ≤
        G.starWeight v *
          ∑ e : G.StarEdge v, G.weight e.1 *
            (G.selectedColorDependentAllOptionMass
              proposal R rho omega choice e.1 - target e.1) ^ 2 := by
      simpa [S, starWeight] using hcs
    _ ≤ G.starWeight v * sigma := by
      apply mul_le_mul_of_nonneg_left hquad
      unfold starWeight
      exact Finset.sum_nonneg fun e _ ↦ G.weight_nonneg e.1

/-- Star-wise clipping loss with an arbitrary edge-dependent target. -/
theorem weightedResidualStar_selectedColorDependentResidual_le_sqrt
    (rho omega : ℝ)
    (choice : (G.V × Fin B) →
      G.ColorDependentExtendedProfilePackedBlockState
        (k := k) (β := β) (q := q) (r := r))
    (target : G.E → ℝ) (htarget : ∀ e, target e ≤ 1)
    (v : G.V) (sigma : ℝ) (hsigma0 : 0 ≤ sigma)
    (hquad :
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedColorDependentAllOptionMass
          proposal R rho omega choice e.1 - target e.1) ^ 2) ≤ sigma) :
    G.weightedResidualStar
        (G.selectedColorDependentResidualOptionMass
          proposal R rho omega choice) v ≤
      (∑ e : G.StarEdge v, G.weight e.1 * (1 - target e.1)) +
        Real.sqrt (G.starWeight v * sigma) := by
  classical
  unfold weightedResidualStar
  have hpoint (e : G.E) :
      (if G.Inc v e then
          G.selectedColorDependentResidualOptionMass
              proposal R rho omega choice e * G.weight e
        else 0) ≤
      (if G.Inc v e then
          ((1 - target e) +
            |G.selectedColorDependentAllOptionMass
              proposal R rho omega choice e - target e|) * G.weight e
        else 0) := by
    by_cases hinc : G.Inc v e
    · simp only [if_pos hinc]
      exact mul_le_mul_of_nonneg_right
        (G.selectedColorDependentResidualOptionMass_le_target_add_abs
          proposal R rho omega (target e) choice (htarget e) e)
        (G.weight_nonneg e)
    · simp [hinc]
  calc
    (∑ e, if G.Inc v e then
        G.selectedColorDependentResidualOptionMass
          proposal R rho omega choice e * G.weight e else 0) ≤
      ∑ e, if G.Inc v e then
        ((1 - target e) +
          |G.selectedColorDependentAllOptionMass
            proposal R rho omega choice e - target e|) * G.weight e else 0 :=
      Finset.sum_le_sum fun e _ ↦ hpoint e
    _ = (∑ e : G.StarEdge v, G.weight e.1 * (1 - target e.1)) +
        ∑ e : G.StarEdge v, G.weight e.1 *
          |G.selectedColorDependentAllOptionMass
            proposal R rho omega choice e.1 - target e.1| := by
      calc
        (∑ e : G.E, if G.Inc v e then
            ((1 - target e) +
              |G.selectedColorDependentAllOptionMass
                proposal R rho omega choice e - target e|) * G.weight e else 0) =
            ∑ e ∈ (Finset.univ : Finset G.E).filter (G.Inc v),
              ((1 - target e) +
                |G.selectedColorDependentAllOptionMass
                  proposal R rho omega choice e - target e|) * G.weight e := by
              rw [Finset.sum_filter]
        _ = ∑ e : G.StarEdge v,
              ((1 - target e.1) +
                |G.selectedColorDependentAllOptionMass
                  proposal R rho omega choice e.1 - target e.1|) * G.weight e.1 := by
              exact Finset.sum_subtype
                ((Finset.univ : Finset G.E).filter (G.Inc v))
                (by intro e; simp)
                (fun e ↦ ((1 - target e) +
                  |G.selectedColorDependentAllOptionMass
                    proposal R rho omega choice e - target e|) * G.weight e)
        _ = _ := by
              simp_rw [add_mul]
              rw [Finset.sum_add_distrib]
              congr 1 <;>
                apply Finset.sum_congr rfl <;>
                intro e _he <;> ring
    _ ≤ (∑ e : G.StarEdge v, G.weight e.1 * (1 - target e.1)) +
        Real.sqrt (G.starWeight v * sigma) := by
      exact add_le_add le_rfl
        (G.selectedColorDependentAbsoluteError_le_sqrt
          proposal R rho omega choice target v sigma hsigma0 hquad)

end WeightedMultigraph

end

end WeightedEdgeColoring
