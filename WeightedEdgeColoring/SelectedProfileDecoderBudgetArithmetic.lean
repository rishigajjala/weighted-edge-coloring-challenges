import Mathlib

/-!
# Scalar arithmetic for selected-profile decoding

This graph-independent estimate is shared by the simple and bounded-
multiplicity decoder wrappers.
-/

namespace WeightedEdgeColoring

/-- The explicit decoder loss is at most `37*epsilon*n` under the natural
outer scale bounds. -/
theorem selectedProfileDecoderLoss_le
    {trace star sigma rhoS extraGamma reserve beta epsilon n : ℝ}
    (hepsilon : 0 ≤ epsilon) (hn : 0 ≤ n)
    (htrace : trace ≤ epsilon * n)
    (hstar0 : 0 ≤ star) (hstar : star ≤ n)
    (hsigma0 : 0 ≤ sigma) (hsigma : sigma ≤ epsilon ^ 2 * n)
    (hrhoS : 0 ≤ 1 - rhoS) (hrhoSLoss : 1 - rhoS ≤ epsilon)
    (hgamma0 : 0 ≤ extraGamma) (hgammaHalf : extraGamma ≤ 1 / 2)
    (hone : 1 ≤ epsilon * n) (hreserve : reserve ≤ epsilon * n)
    (hbeta : beta ≤ epsilon * n) :
    trace +
        4 * ((1 - rhoS) * star + Real.sqrt (star * sigma)) /
          (1 - extraGamma) +
        8 * (1 + reserve) +
        ((1 - rhoS) * star + Real.sqrt (star * sigma)) + 2 * beta ≤
      37 * epsilon * n := by
  have hεn0 : 0 ≤ epsilon * n := mul_nonneg hepsilon hn
  have hlin : (1 - rhoS) * star ≤ epsilon * n := by
    exact (mul_le_mul hrhoSLoss hstar hstar0 hepsilon).trans_eq (by ring)
  have hprod0 : 0 ≤ star * sigma := mul_nonneg hstar0 hsigma0
  have hprod : star * sigma ≤ (epsilon * n) ^ 2 := by
    calc
      star * sigma ≤ n * (epsilon ^ 2 * n) :=
        mul_le_mul hstar hsigma hsigma0 hn
      _ = (epsilon * n) ^ 2 := by ring
  have hsqrt : Real.sqrt (star * sigma) ≤ epsilon * n := by
    rw [← Real.sqrt_sq hεn0]
    exact Real.sqrt_le_sqrt hprod
  have hA : (1 - rhoS) * star + Real.sqrt (star * sigma) ≤
      2 * epsilon * n := by linarith
  have hA0 : 0 ≤ (1 - rhoS) * star + Real.sqrt (star * sigma) :=
    add_nonneg (mul_nonneg hrhoS hstar0) (Real.sqrt_nonneg _)
  have hgap : (1 / 2 : ℝ) ≤ 1 - extraGamma := by linarith
  have hgap0 : 0 < 1 - extraGamma := lt_of_lt_of_le (by norm_num) hgap
  have hdiv :
      4 * ((1 - rhoS) * star + Real.sqrt (star * sigma)) /
          (1 - extraGamma) ≤ 16 * epsilon * n := by
    apply (div_le_iff₀ hgap0).2
    have hleft : 4 * ((1 - rhoS) * star + Real.sqrt (star * sigma)) ≤
        8 * epsilon * n := by nlinarith
    have hright : 8 * epsilon * n ≤
        (16 * epsilon * n) * (1 - extraGamma) := by
      nlinarith
    exact hleft.trans hright
  have hreserveTerm : 8 * (1 + reserve) ≤ 16 * epsilon * n := by
    nlinarith
  nlinarith

end WeightedEdgeColoring
