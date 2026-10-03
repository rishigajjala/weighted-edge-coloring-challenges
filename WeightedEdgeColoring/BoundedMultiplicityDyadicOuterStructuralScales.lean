import WeightedEdgeColoring.DyadicSimpleClosedIterationScales

/-!
# Structural polynomial scales for the simple-graph application

These lemmas pay the quantization floor loss, ordinary and extra
codegrees, and the initial slot gap.  They are independent of the random
nibble estimates.
-/

namespace WeightedEdgeColoring

noncomputable section

open RankThreeOptionSystem.OriginalIterationState

/-- A fixed coefficient which pays every local extra-choice support. -/
def boundedMultiplicityDyadicSupportCoefficient (beta extraGamma : ℝ) : ℕ :=
  Nat.ceil (2 * ((2 : ℝ) ^ 20 / beta / (1 - extraGamma) + 2)) + 1

/-- A fixed coefficient which pays ordinary quantization choices and local
extra choices together. -/
def boundedMultiplicityDyadicChoiceCoefficient
    (placeCount : ℕ) (beta extraGamma : ℝ) : ℕ :=
  2 ^ 20 * placeCount ^ 2 +
    boundedMultiplicityDyadicSupportCoefficient beta extraGamma

/-- A fixed codegree coefficient for the ordinary slots. -/
def boundedMultiplicityDyadicCodegreeCoefficient (placeCount : ℕ) (scale : ℝ) : ℕ :=
  Nat.ceil ((placeCount : ℝ) * scale) + 1

/-- One coefficient pays both the ordinary slot codegree and the fixed
endpoint-pair multiplicity in the extra bank. -/
def boundedMultiplicityDyadicFixedCodegreeCoefficient
    (mult placeCount : ℕ) (scale : ℝ) : ℕ :=
  boundedMultiplicityDyadicCodegreeCoefficient placeCount scale + mult

theorem boundedMultiplicityDyadic_palette_le_two_pow_mul
    {m palette : ℕ} (hm : 1 ≤ m) (hpalette : palette < (m + 1) ^ 20) :
    palette ≤ 2 ^ 20 * m ^ 20 := by
  have hbase : m + 1 ≤ 2 * m := by omega
  have hp := Nat.pow_le_pow_left hbase 20
  have hlt : palette < (2 * m) ^ 20 := hpalette.trans_le hp
  calc
    palette ≤ (2 * m) ^ 20 := hlt.le
    _ = 2 ^ 20 * m ^ 20 := by ring

theorem boundedMultiplicityDyadic_support_budget
    {m palette : ℕ} {beta extraGamma : ℝ}
    (hm : 1 ≤ m) (hbeta : 0 < beta) (hextraGamma : extraGamma < 1)
    (hpalette : palette ≤ 2 ^ 20 * m ^ 20) :
    2 * (((palette : ℝ) / beta / (1 - extraGamma)) + 1 +
        dyadicSimpleReserveScale m) ≤
      (boundedMultiplicityDyadicSupportCoefficient beta extraGamma * m ^ 20 : ℕ) := by
  have hgap : 0 < 1 - extraGamma := sub_pos.mpr hextraGamma
  have hpaletteR : (palette : ℝ) ≤ (2 : ℝ) ^ 20 * m ^ 20 := by
    exact_mod_cast hpalette
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm20 : (1 : ℝ) ≤ m ^ 20 := one_le_pow₀ hmR
  have hreserve : (dyadicSimpleReserveScale m : ℝ) ≤ m ^ 20 := by
    unfold dyadicSimpleReserveScale
    push_cast
    exact pow_le_pow_right₀ hmR (by omega)
  let c : ℝ := 2 * ((2 : ℝ) ^ 20 / beta / (1 - extraGamma) + 2)
  have hmain :
      2 * (((palette : ℝ) / beta / (1 - extraGamma)) + 1 +
          dyadicSimpleReserveScale m) ≤ c * m ^ 20 := by
    have hfirst : (palette : ℝ) / beta / (1 - extraGamma) ≤
        ((2 : ℝ) ^ 20 / beta / (1 - extraGamma)) * m ^ 20 := by
      calc
        (palette : ℝ) / beta / (1 - extraGamma) ≤
            (((2 : ℝ) ^ 20 * m ^ 20) / beta) / (1 - extraGamma) := by
          exact div_le_div_of_nonneg_right
            (div_le_div_of_nonneg_right hpaletteR hbeta.le) hgap.le
        _ = ((2 : ℝ) ^ 20 / beta / (1 - extraGamma)) * m ^ 20 := by ring
    dsimp [c]
    nlinarith
  have hceil : c ≤ (Nat.ceil c : ℕ) := Nat.le_ceil c
  have hcoef : c ≤ boundedMultiplicityDyadicSupportCoefficient beta extraGamma := by
    change c ≤ ((Nat.ceil c + 1 : ℕ) : ℝ)
    exact hceil.trans (by exact_mod_cast Nat.le_succ (Nat.ceil c))
  have hmul := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ (m : ℝ) ^ 20)
  exact hmain.trans (by
    exact_mod_cast hmul)

theorem boundedMultiplicityDyadic_choice_budget
    {m palette placeCount : ℕ} {beta extraGamma : ℝ}
    (hpalette : palette ≤ 2 ^ 20 * m ^ 20) :
    palette * placeCount * placeCount +
        boundedMultiplicityDyadicSupportCoefficient beta extraGamma * m ^ 20 ≤
      boundedMultiplicityDyadicChoiceCoefficient placeCount beta extraGamma * m ^ 20 := by
  unfold boundedMultiplicityDyadicChoiceCoefficient
  calc
    palette * placeCount * placeCount +
        boundedMultiplicityDyadicSupportCoefficient beta extraGamma * m ^ 20 ≤
      (2 ^ 20 * m ^ 20) * placeCount * placeCount +
        boundedMultiplicityDyadicSupportCoefficient beta extraGamma * m ^ 20 := by gcongr
    _ = (2 ^ 20 * placeCount ^ 2 +
        boundedMultiplicityDyadicSupportCoefficient beta extraGamma) * m ^ 20 := by ring

theorem boundedMultiplicityDyadic_ordinaryJobCodegree
    {m palette placeCount : ℕ} {scale : ℝ}
    (hm : 1 ≤ m) (hscale0 : 0 ≤ scale)
    (hpalette : m ^ 20 ≤ palette) :
    (dyadicSimpleQuantizationScale m : ℝ) *
        ((placeCount : ℝ) * scale / palette) ≤
      dyadicSimpleCodegreeScale
        (boundedMultiplicityDyadicCodegreeCoefficient placeCount scale) m := by
  have hpaletteR : (0 : ℝ) < palette := by
    have : 0 < m ^ 20 := pow_pos (by omega) _
    exact_mod_cast this.trans_le hpalette
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcoeff : (placeCount : ℝ) * scale ≤
      boundedMultiplicityDyadicCodegreeCoefficient placeCount scale := by
    exact (Nat.le_ceil _).trans (by
      dsimp [boundedMultiplicityDyadicCodegreeCoefficient]
      norm_num)
  have hratio :
      (dyadicSimpleQuantizationScale m : ℝ) / palette ≤ (m : ℝ) ^ 10 := by
    apply (div_le_iff₀ hpaletteR).2
    have hpaletteLower : (m : ℝ) ^ 20 ≤ palette := by exact_mod_cast hpalette
    have hm10 : 0 ≤ (m : ℝ) ^ 10 := by positivity
    calc
      (dyadicSimpleQuantizationScale m : ℝ) ≤
          (m : ℝ) ^ 10 * (m : ℝ) ^ 20 := by
        unfold dyadicSimpleQuantizationScale
        push_cast
        exact le_of_eq (by ring)
      _ ≤ (m : ℝ) ^ 10 * palette :=
        mul_le_mul_of_nonneg_left hpaletteLower hm10
  unfold dyadicSimpleCodegreeScale
  push_cast
  calc
    (dyadicSimpleQuantizationScale m : ℝ) *
        ((placeCount : ℝ) * scale / palette) =
      ((placeCount : ℝ) * scale) *
        ((dyadicSimpleQuantizationScale m : ℝ) / palette) := by ring
    _ ≤ (boundedMultiplicityDyadicCodegreeCoefficient placeCount scale : ℕ) *
        (m : ℝ) ^ 10 := by gcongr
    _ ≤ (boundedMultiplicityDyadicCodegreeCoefficient placeCount scale : ℕ) *
        (m : ℝ) ^ 14 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hmR (by omega)) (by positivity)

theorem boundedMultiplicityDyadic_extraCodegree_for_coefficient
    {m A : ℕ} (hm : 1 ≤ m) (hA : 1 ≤ A) :
    (dyadicSimpleQuantizationScale m : ℝ) /
        dyadicSimpleReserveScale m ≤ dyadicSimpleCodegreeScale A m := by
  exact dyadicSimple_extraCodegree_le A m (by omega) (by omega)

theorem boundedMultiplicityDyadic_ordinaryJobCodegree_fixed
    {mult m palette placeCount : ℕ} {scale : ℝ}
    (hm : 1 ≤ m) (hscale0 : 0 ≤ scale)
    (hpalette : m ^ 20 ≤ palette) :
    (dyadicSimpleQuantizationScale m : ℝ) *
        ((placeCount : ℝ) * scale / palette) ≤
      dyadicSimpleCodegreeScale
        (boundedMultiplicityDyadicFixedCodegreeCoefficient
          mult placeCount scale) m := by
  have hbase := boundedMultiplicityDyadic_ordinaryJobCodegree
    (m := m) (palette := palette) (placeCount := placeCount)
    (scale := scale) hm hscale0 hpalette
  unfold dyadicSimpleCodegreeScale at hbase ⊢
  unfold boundedMultiplicityDyadicFixedCodegreeCoefficient
  push_cast at hbase ⊢
  have hpow : (0 : ℝ) ≤ (m : ℝ) ^ 14 := by positivity
  nlinarith

theorem boundedMultiplicityDyadic_extraPairCodegree_fixed
    {mult m placeCount : ℕ} {scale : ℝ} (hm : 1 ≤ m) :
    (mult : ℝ) * (dyadicSimpleQuantizationScale m : ℝ) /
        dyadicSimpleReserveScale m ≤
      dyadicSimpleCodegreeScale
        (boundedMultiplicityDyadicFixedCodegreeCoefficient
          mult placeCount scale) m := by
  have hratio : (dyadicSimpleQuantizationScale m : ℝ) /
      dyadicSimpleReserveScale m = (m : ℝ) ^ 14 := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    unfold dyadicSimpleQuantizationScale dyadicSimpleReserveScale
    push_cast
    field_simp [hm0]
  rw [show (mult : ℝ) * (dyadicSimpleQuantizationScale m : ℝ) /
      dyadicSimpleReserveScale m = (mult : ℝ) *
        ((dyadicSimpleQuantizationScale m : ℝ) /
          dyadicSimpleReserveScale m) by ring, hratio]
  unfold dyadicSimpleCodegreeScale
    boundedMultiplicityDyadicFixedCodegreeCoefficient
  push_cast
  have hmPow : (m : ℝ) ^ 14 ≥ 0 := by positivity
  nlinarith

/-- The floor target simultaneously pays the ordinary slots and the local
extra slots when the choice loss is at most one `gamma` fraction of `N`. -/
theorem boundedMultiplicityDyadic_initial_slot_caps
    {N C : ℕ} {gamma ordinaryRate : ℝ}
    (hgamma0 : 0 ≤ gamma) (hgammaHalf : gamma ≤ 1 / 2)
    (hCN : C ≤ N)
    (hloss : (C : ℝ) + 1 ≤ gamma * N)
    (hordinaryRate : ordinaryRate ≤ 1 - 4 * gamma) :
    (N : ℝ) * ordinaryRate ≤
        fixedSlackPaddedSlotTarget gamma (N - C) ∧
      (1 - 2 * gamma) * N ≤
        fixedSlackPaddedSlotTarget gamma (N - C) ∧
      (fixedSlackPaddedSlotTarget gamma (N - C) : ℝ) ≤
        (1 - gamma) * (N - C) := by
  have htargetLower := fixedSlackPaddedSlotTarget_lower gamma (N - C)
  have htargetUpper :
      ((fixedSlackPaddedSlotTarget gamma (N - C) : ℕ) : ℝ) ≤
        (1 - gamma) * (N - C : ℕ) := by
    unfold fixedSlackPaddedSlotTarget
    exact Nat.floor_le
      (mul_nonneg (by linarith) (Nat.cast_nonneg (N - C)))
  have hsub : ((N - C : ℕ) : ℝ) = (N : ℝ) - C := by
    rw [Nat.cast_sub hCN]
  have hextra : (1 - 2 * gamma) * N ≤
      (1 - gamma) * (N - C : ℕ) - 1 := by
    rw [hsub]
    have hcoef : 0 ≤ 1 - gamma := by linarith
    have hC : (1 - gamma) * C ≤ C := by
      nlinarith [mul_nonneg hgamma0 (show (0 : ℝ) ≤ C by positivity)]
    nlinarith
  have hord : (N : ℝ) * ordinaryRate ≤
      (1 - gamma) * (N - C : ℕ) - 1 := by
    have hrate : ordinaryRate ≤ 1 - 2 * gamma := by linarith
    have hmul := mul_le_mul_of_nonneg_left hrate
      (show (0 : ℝ) ≤ N by positivity)
    exact hmul.trans (by simpa [mul_comm] using hextra)
  rw [hsub] at htargetUpper
  exact ⟨hord.trans htargetLower.le, hextra.trans htargetLower.le,
    htargetUpper⟩

end

end WeightedEdgeColoring
