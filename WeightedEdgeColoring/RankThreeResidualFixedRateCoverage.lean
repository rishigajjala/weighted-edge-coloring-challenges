import WeightedEdgeColoring.RankThreeResidualFixedRateParameters

/-!
# A uniform coverage rate for the fixed-rate residual round

The exact group-coverage fraction is the common lower mean divided by
`16*K`.  When the dyadic block size is between `S/(10*lambda)` and
`S/(5*lambda)`, this fraction is bounded below by a constant multiple of
`1/lambda`.  This file records the lower bound used in the iteration.
-/

namespace WeightedEdgeColoring

/-- A convenient round-independent lower bound for the covered-weight
fraction. -/
noncomputable def fixedRateCoverageRate (lambda : ℕ) : ℝ :=
  fixedRateKappa / (64 * (lambda : ℝ))

theorem fixedRateCoverageRate_nonneg (lambda : ℕ) :
    0 ≤ fixedRateCoverageRate lambda := by
  exact div_nonneg fixedRateKappa_nonneg
    (mul_nonneg (by norm_num) (Nat.cast_nonneg lambda))

theorem fixedRateCoverageRate_le_one
    (lambda : ℕ) (hlambda : 0 < lambda) :
    fixedRateCoverageRate lambda ≤ 1 := by
  have hlambdaR : (1 : ℝ) ≤ (lambda : ℝ) := by exact_mod_cast hlambda
  rw [fixedRateCoverageRate, div_le_one (by positivity : (0 : ℝ) < 64 * lambda)]
  norm_num [fixedRateKappa]
  linarith

/-- The common lower mean from the active-slot theorem gives at least the
fixed coverage rate after the count-to-weight conversion. -/
theorem fixedRateCoverageRate_le_activeSlot_fraction
    (lambda J S K m dJob dSlot : ℕ)
    (hlambda : 0 < lambda) (hJ : 0 < J) (hK : 0 < K)
    (hgroupSize : S ≤ 10 * lambda * K)
    (hKupper : 5 * lambda * K ≤ S)
    (hjobHalf : J ≤ 2 * dJob) (hslotHalf : S ≤ 2 * dSlot)
    (hcodegree : 6 * lambda ≤ J) (hsupport : K * dJob ≤ m) :
    fixedRateCoverageRate lambda ≤
      RankThreeOptionSystem.activeSlotUniformLowerMean
        (fixedRateRho lambda J) m dJob dSlot lambda / (16 * (K : ℝ)) := by
  have hmean := fixedRate_lower_floor_le_activeSlotMean
    lambda J S K m dJob dSlot hlambda hJ hgroupSize hjobHalf hslotHalf
    hcodegree hsupport
  have hlambdaR : (0 : ℝ) < (lambda : ℝ) := by positivity
  have hKR : (0 : ℝ) < (K : ℝ) := by positivity
  have hKupperR : (5 : ℝ) * (lambda : ℝ) * (K : ℝ) ≤ (S : ℝ) := by
    exact_mod_cast hKupper
  have hscalar : fixedRateCoverageRate lambda ≤
      (fixedRateKappa * fixedRateScale lambda S / 20) /
        (16 * (K : ℝ)) := by
    rw [fixedRateCoverageRate, fixedRateScale]
    field_simp
    have hkappa0 := fixedRateKappa_nonneg
    nlinarith
  exact hscalar.trans (div_le_div_of_nonneg_right hmean (by positivity))

end WeightedEdgeColoring
