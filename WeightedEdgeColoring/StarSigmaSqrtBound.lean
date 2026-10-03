import Mathlib

/-!
# A reusable square-root error bound
-/

namespace WeightedEdgeColoring

/-- A quadratic error of size `epsilon² n`, tested on a star of size at
most `n`, contributes at most `epsilon n` after Cauchy--Schwarz. -/
theorem sqrt_star_mul_sigma_le
    {star sigma epsilon n : ℝ}
    (hstar0 : 0 ≤ star) (hstar : star ≤ n)
    (hsigma0 : 0 ≤ sigma) (hsigma : sigma ≤ epsilon ^ 2 * n)
    (hepsilon0 : 0 ≤ epsilon) (hn0 : 0 ≤ n) :
    Real.sqrt (star * sigma) ≤ epsilon * n := by
  have hprod : star * sigma ≤ (epsilon * n) ^ 2 := by
    calc
      star * sigma ≤ n * (epsilon ^ 2 * n) :=
        mul_le_mul hstar hsigma hsigma0 hn0
      _ = (epsilon * n) ^ 2 := by ring
  have hepsilonN0 : 0 ≤ epsilon * n := mul_nonneg hepsilon0 hn0
  rw [← Real.sqrt_sq hepsilonN0]
  exact Real.sqrt_le_sqrt hprod

end WeightedEdgeColoring
