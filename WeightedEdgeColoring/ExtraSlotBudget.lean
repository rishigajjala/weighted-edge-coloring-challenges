import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace WeightedEdgeColoring

/-!
# Numerical budget for leave-uncoloured slots

The large-edge construction gives a vertex/class residual mass `R` exactly
`ceil (R / (1-gamma)) + t` counting slots.  Uniformly spreading the residual
over those slots leaves a fixed `gamma` fraction of degree slack.
-/

noncomputable section

/-- Number of extra counting slots assigned to residual mass `R`. -/
def extraSlotCount (R gamma : ℝ) (t : ℕ) : ℕ :=
  Nat.ceil (R / (1 - gamma)) + t

theorem extraSlotCount_pos (R gamma : ℝ) {t : ℕ} (ht : 0 < t) :
    0 < extraSlotCount R gamma t := by
  unfold extraSlotCount
  omega

/-- The additive reserve is contained literally in the extra-slot count. -/
theorem extraSlotCount_ge_reserve (R gamma : ℝ) (t : ℕ) :
    t ≤ extraSlotCount R gamma t := by
  unfold extraSlotCount
  omega

/-- A quantity at most one, divided by any positive count containing the
reserve `t`, is at most `1/t`.  This form is useful when the numerator is an
edge residual but the denominator was chosen from the whole vertex--class
residual. -/
theorem residual_div_count_le_inv_reserve
    (R : ℝ) {B t : ℕ} (hR : R ≤ 1) (ht : 0 < t) (hBt : t ≤ B) :
    R / (B : ℝ) ≤ 1 / (t : ℝ) := by
  have htReal : (0 : ℝ) < t := by exact_mod_cast ht
  have hBtReal : (t : ℝ) ≤ B := by exact_mod_cast hBt
  have hBReal : (0 : ℝ) < B := lt_of_lt_of_le htReal hBtReal
  calc
    R / (B : ℝ) ≤ 1 / (B : ℝ) := by
      exact div_le_div_of_nonneg_right hR hBReal.le
    _ ≤ 1 / (t : ℝ) := by
      exact one_div_le_one_div_of_le htReal hBtReal

/-- With two positive counts containing the reserve, a quantity at most one
spread over their Cartesian product has point mass at most `1/t^2`. -/
theorem residual_div_mul_counts_le_inv_reserve_sq
    (R : ℝ) {B₁ B₂ t : ℕ} (hR : R ≤ 1) (ht : 0 < t)
    (hB₁t : t ≤ B₁) (hB₂t : t ≤ B₂) :
    R / ((B₁ * B₂ : ℕ) : ℝ) ≤ 1 / (t : ℝ) ^ 2 := by
  have htReal : (0 : ℝ) < t := by exact_mod_cast ht
  have hB₁tReal : (t : ℝ) ≤ B₁ := by exact_mod_cast hB₁t
  have hB₂tReal : (t : ℝ) ≤ B₂ := by exact_mod_cast hB₂t
  have hprod : (t : ℝ) ^ 2 ≤ ((B₁ * B₂ : ℕ) : ℝ) := by
    push_cast
    nlinarith [mul_le_mul hB₁tReal hB₂tReal htReal.le
      (le_trans htReal.le hB₁tReal)]
  have hsq : (0 : ℝ) < (t : ℝ) ^ 2 := sq_pos_of_pos htReal
  have hBprod : (0 : ℝ) < ((B₁ * B₂ : ℕ) : ℝ) :=
    lt_of_lt_of_le hsq hprod
  calc
    R / ((B₁ * B₂ : ℕ) : ℝ) ≤ 1 / ((B₁ * B₂ : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_right hR hBprod.le
    _ ≤ 1 / (t : ℝ) ^ 2 := by
      exact one_div_le_one_div_of_le hsq hprod

/-- A unit residual spread over the extra slots has point mass at most the
reciprocal of the additive reserve. -/
theorem residual_div_extraSlotCount_le_inv_reserve
    (R gamma : ℝ) {t : ℕ}
    (hR : R ≤ 1) (ht : 0 < t) :
    R / (extraSlotCount R gamma t : ℕ) ≤ 1 / (t : ℝ) := by
  have hcount : (t : ℝ) ≤ (extraSlotCount R gamma t : ℕ) := by
    exact_mod_cast extraSlotCount_ge_reserve R gamma t
  have htReal : (0 : ℝ) < t := by exact_mod_cast ht
  have hcountReal : (0 : ℝ) < (extraSlotCount R gamma t : ℕ) :=
    lt_of_lt_of_le htReal hcount
  calc
    R / (extraSlotCount R gamma t : ℕ) ≤
        1 / (extraSlotCount R gamma t : ℕ) := by
      exact div_le_div_of_nonneg_right hR hcountReal.le
    _ ≤ 1 / (t : ℝ) := by
      exact one_div_le_one_div_of_le htReal hcount

/-- Every extra slot has load at most `1-gamma`. -/
theorem residual_div_extraSlotCount_le
    (R gamma : ℝ) (t : ℕ)
    (hR : 0 ≤ R) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1)
    (ht : 0 < t) :
    R / (extraSlotCount R gamma t : ℕ) ≤ 1 - gamma := by
  have hgap : 0 < 1 - gamma := sub_pos.mpr hgamma1
  have hceil : R / (1 - gamma) ≤
      (Nat.ceil (R / (1 - gamma)) : ℝ) := Nat.le_ceil _
  have hcount : (Nat.ceil (R / (1 - gamma)) : ℝ) ≤
      (extraSlotCount R gamma t : ℕ) := by
    exact_mod_cast Nat.le_add_right (Nat.ceil (R / (1 - gamma))) t
  have hscaled : R ≤ (1 - gamma) *
      (extraSlotCount R gamma t : ℕ) := by
    have hscaled' : R ≤ (extraSlotCount R gamma t : ℕ) *
        (1 - gamma) :=
      (div_le_iff₀ hgap).mp (hceil.trans hcount)
    simpa [mul_comm] using hscaled'
  have hcountPos : (0 : ℝ) < (extraSlotCount R gamma t : ℕ) := by
    exact_mod_cast extraSlotCount_pos R gamma ht
  apply (div_le_iff₀ hcountPos).2
  simpa [mul_comm] using hscaled

/-- The number of extra slots is at most the unrounded quotient plus the
one-unit ceiling loss and the additive reserve. -/
theorem extraSlotCount_cast_le
    (R gamma : ℝ) (t : ℕ)
    (hR : 0 ≤ R) (hgamma1 : gamma < 1) :
    (extraSlotCount R gamma t : ℕ) ≤
      R / (1 - gamma) + 1 + t := by
  have hgap : 0 < 1 - gamma := sub_pos.mpr hgamma1
  have hquot : 0 ≤ R / (1 - gamma) := div_nonneg hR hgap.le
  have hceil : ((Nat.ceil (R / (1 - gamma)) : ℕ) : ℝ) ≤
      R / (1 - gamma) + 1 :=
    (Nat.ceil_lt_add_one hquot).le
  unfold extraSlotCount
  push_cast
  linarith

/-- Multiplying by the replication scale preserves the fixed slot-degree
slack. -/
theorem scaled_residual_div_extraSlotCount_le
    (R gamma : ℝ) (t N : ℕ)
    (hR : 0 ≤ R) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1)
    (ht : 0 < t) :
    (N : ℝ) * (R / (extraSlotCount R gamma t : ℕ)) ≤
      (1 - gamma) * N := by
  have h := residual_div_extraSlotCount_le R gamma t hR hgamma0 hgamma1 ht
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left h hN
  nlinarith

end

end WeightedEdgeColoring
