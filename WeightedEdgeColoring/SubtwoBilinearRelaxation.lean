import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Valid product and row-lifting inequalities for the dense-five LP

These are generic real-arithmetic implications for an *actual* product
`X = p * y`. They justify the algebraic directions of the McCormick and RLT
rows in the frozen LP generator. This module does not prove that the other
local-profile rows describe bin geometry.
-/

namespace WeightedEdgeColoring.SubtwoBilinearRelaxation

/-- The first McCormick upper row `X - U*y ≤ 0`. -/
theorem product_le_upper_mul (U p y X : ℝ)
    (hp : p ≤ U) (hy : 0 ≤ y) (hX : X = p * y) :
    X - U * y ≤ 0 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) hy]

/-- The first McCormick lower row `-X + L*y ≤ 0`. -/
theorem lower_mul_le_product (L p y X : ℝ)
    (hp : L ≤ p) (hy : 0 ≤ y) (hX : X = p * y) :
    -X + L * y ≤ 0 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) hy]

/-- The capped-variable upper row `X - h*p - L*y ≤ -h*L`. -/
theorem product_le_cap_price (L p y h X : ℝ)
    (hp : L ≤ p) (hy : y ≤ h) (hX : X = p * y) :
    X - h * p - L * y ≤ -h * L := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hy)]

/-- The capped-variable lower row `-X + h*p + U*y ≤ h*U`. -/
theorem cap_price_le_product (U p y h X : ℝ)
    (hp : p ≤ U) (hy : y ≤ h) (hX : X = p * y) :
    -X + h * p + U * y ≤ h * U := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hy)]

/-- All four McCormick rows used for a bounded price times a capped
nonnegative variable. -/
theorem all_mccormick_rows (L U p y h X : ℝ)
    (hL : L ≤ p) (hU : p ≤ U) (hy0 : 0 ≤ y) (hyh : y ≤ h)
    (hX : X = p * y) :
    X - U * y ≤ 0 ∧
    -X + L * y ≤ 0 ∧
    X - h * p - L * y ≤ -h * L ∧
    -X + h * p + U * y ≤ h * U := by
  exact ⟨product_le_upper_mul U p y X hU hy0 hX,
    lower_mul_le_product L p y X hL hy0 hX,
    product_le_cap_price L p y h X hL hyh hX,
    cap_price_le_product U p y h X hU hyh hX⟩

/-- RLT row from multiplying `s ≤ d` by `p-L ≥ 0` and substituting
`z = p*s`: `z - L*s - d*p ≤ -L*d`. -/
theorem rlt_lower_scalar (L p s d z : ℝ)
    (hp : L ≤ p) (hs : s ≤ d) (hz : z = p * s) :
    z - L * s - d * p ≤ -L * d := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hs)]

/-- RLT row from multiplying `s ≤ d` by `U-p ≥ 0`:
`-z + U*s + d*p ≤ U*d`. -/
theorem rlt_upper_scalar (U p s d z : ℝ)
    (hp : p ≤ U) (hs : s ≤ d) (hz : z = p * s) :
    -z + U * s + d * p ≤ U * d := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hs)]

private theorem product_linear_sum {I : Type*} [Fintype I]
    (a y X : I → ℝ) (p : ℝ) (hX : ∀ i, X i = p * y i) :
    (∑ i, a i * X i) = p * (∑ i, a i * y i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hX i]
  ring

/-- The exact first RLT row of a finite linear inequality after replacing
every product `p*yᵢ` by its lift `Xᵢ`. Coefficients may have either sign. -/
theorem rlt_lower_linear {I : Type*} [Fintype I]
    (a y X : I → ℝ) (L p d : ℝ)
    (hp : L ≤ p) (hrow : (∑ i, a i * y i) ≤ d)
    (hX : ∀ i, X i = p * y i) :
    (∑ i, a i * X i) - L * (∑ i, a i * y i) - d * p ≤ -L * d := by
  rw [product_linear_sum a y X p hX]
  exact rlt_lower_scalar L p (∑ i, a i * y i) d
    (p * ∑ i, a i * y i) hp hrow rfl

/-- The exact second RLT row of a finite linear inequality. -/
theorem rlt_upper_linear {I : Type*} [Fintype I]
    (a y X : I → ℝ) (U p d : ℝ)
    (hp : p ≤ U) (hrow : (∑ i, a i * y i) ≤ d)
    (hX : ∀ i, X i = p * y i) :
    -(∑ i, a i * X i) + U * (∑ i, a i * y i) + d * p ≤ U * d := by
  rw [product_linear_sum a y X p hX]
  exact rlt_upper_scalar U p (∑ i, a i * y i) d
    (p * ∑ i, a i * y i) hp hrow rfl

/-- Multiplying any valid linear price row by a nonnegative `y` yields its
lifted row when `Xᵢ = pᵢ*y`. This includes the frozen ordering and
disjoint-price rows. -/
theorem multiply_price_row {I : Type*} [Fintype I]
    (a p X : I → ℝ) (y d : ℝ)
    (hy : 0 ≤ y) (hrow : (∑ i, a i * p i) ≤ d)
    (hX : ∀ i, X i = p i * y) :
    (∑ i, a i * X i) ≤ d * y := by
  calc
    (∑ i, a i * X i) = (∑ i, a i * p i) * y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hX i]
      ring
    _ ≤ d * y := mul_le_mul_of_nonneg_right hrow hy

/-- A price ordering `p₁≤p₂` remains valid after nonnegative scaling. -/
theorem lifted_order (p₁ p₂ y X₁ X₂ : ℝ)
    (hy : 0 ≤ y) (hprice : p₁ ≤ p₂)
    (hX₁ : X₁ = p₁ * y) (hX₂ : X₂ = p₂ * y) :
    X₁ - X₂ ≤ 0 := by
  rw [hX₁, hX₂]
  nlinarith [mul_le_mul_of_nonneg_right hprice hy]

/-- A disjoint-edge price row `p₁+p₂≤1` becomes `X₁+X₂≤y`. -/
theorem lifted_disjoint_pair (p₁ p₂ y X₁ X₂ : ℝ)
    (hy : 0 ≤ y) (hprice : p₁ + p₂ ≤ 1)
    (hX₁ : X₁ = p₁ * y) (hX₂ : X₂ = p₂ * y) :
    X₁ + X₂ - y ≤ 0 := by
  rw [hX₁, hX₂]
  nlinarith [mul_le_mul_of_nonneg_right hprice hy]

end WeightedEdgeColoring.SubtwoBilinearRelaxation
