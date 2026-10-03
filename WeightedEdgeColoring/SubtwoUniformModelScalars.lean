import Mathlib

/-! Exact real-variable scalar inequalities for the two uniform five-vertex
price models.  These statements are independent of the endpoint-potential
structure, so it can later use them without importing any archive LP data. -/

namespace WeightedEdgeColoring

private theorem subtwo_pos_8490 (a : ℝ) :
    0 < 8490 * a ^ 2 - 9283 * a + 2880 := by
  nlinarith [sq_nonneg (16980 * a - 9283 : ℝ)]

theorem subtwo_uniformStar_rootBase_first {a : ℝ} (ha : 0 < a) :
    0 < (8490 * a ^ 2 - 9283 * a + 2880) / (8640 * a) := by
  exact div_pos (subtwo_pos_8490 a) (by positivity)

private theorem subtwo_pos_36010 (a : ℝ) :
    0 < 36010 * a ^ 2 - 39043 * a + 10880 := by
  nlinarith [sq_nonneg (72020 * a - 39043 : ℝ)]

private theorem subtwo_pos_5270 (a : ℝ) :
    0 < 5270 * a ^ 2 - 6453 * a + 2880 := by
  nlinarith [sq_nonneg (10540 * a - 6453 : ℝ)]

private theorem subtwo_pos_7570 (a : ℝ) :
    0 < 7570 * a ^ 2 - 7757 * a + 2000 := by
  nlinarith [sq_nonneg (15140 * a - 7757 : ℝ)]

private theorem subtwo_pos_1318 (a : ℝ) :
    0 < 1318 * a ^ 2 - 1689 * a + 576 := by
  nlinarith [sq_nonneg (2636 * a - 1689 : ℝ)]

theorem subtwo_uniformStar_rootBase_second {a : ℝ} (ha : 0 < a) :
    0 < (36010 * a ^ 2 - 39043 * a + 10880) / (8640 * a) := by
  exact div_pos (subtwo_pos_36010 a) (by positivity)

theorem subtwo_uniformStar_rootBase_third {a : ℝ} (ha : 0 < a) :
    0 < (5270 * a ^ 2 - 6453 * a + 2880) / (8640 * a) := by
  exact div_pos (subtwo_pos_5270 a) (by positivity)

theorem subtwo_uniformStar_spoke_first {a : ℝ}
    (ha : (1 / 2 : ℝ) ≤ a) :
    0 < (690 * a - 317) / 2160 := by
  have : 0 < 690 * a - 317 := by linarith
  exact div_pos this (by norm_num)

theorem subtwo_uniformStar_spoke_second {a : ℝ} (ha : 0 < a) :
    0 < (7570 * a ^ 2 - 7757 * a + 2000) / (2160 * a) := by
  exact div_pos (subtwo_pos_7570 a) (by positivity)

theorem subtwo_uniformStar_spoke_third {a : ℝ}
    (ha : a ≤ (1 : ℝ)) :
    0 < (781 - 230 * a) / 4320 := by
  have : 0 < 781 - 230 * a := by linarith
  exact div_pos this (by norm_num)

theorem subtwo_uniformStar_leaf_first {a : ℝ} (ha : 0 < a) :
    0 < (1318 * a ^ 2 - 1689 * a + 576) / (1728 * a) := by
  exact div_pos (subtwo_pos_1318 a) (by positivity)

theorem subtwo_uniformStar_leaf_second {a : ℝ}
    (ha₀ : (1 / 2 : ℝ) ≤ a) (ha₁ : a ≤ 1) :
    0 ≤ 61 * (1 - a) * (3 * a - 1) / (432 * a) := by
  have ha : 0 < a := by linarith
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  · positivity

theorem subtwo_uniformStar_outer_branch {a : ℝ}
    (ha : (1 / 2 : ℝ) ≤ a) :
    0 ≤ 23 * (2 * a - 1) / 144 := by
  apply div_nonneg
  · exact mul_nonneg (by norm_num) (by linarith)
  · norm_num

private theorem subtwo_pos_615 (a : ℝ) :
    0 < 615 * a ^ 2 - 1015 * a + 432 := by
  nlinarith [sq_nonneg (1230 * a - 1015 : ℝ)]

private theorem subtwo_pos_1937 (a : ℝ) :
    0 < 1937 * a ^ 2 - 2537 * a + 832 := by
  nlinarith [sq_nonneg (3874 * a - 2537 : ℝ)]

private theorem subtwo_pos_694 (a : ℝ) :
    0 < 694 * a ^ 2 - 745 * a + 200 := by
  nlinarith [sq_nonneg (1388 * a - 745 : ℝ)]

theorem subtwo_uniformTriangle_case_BB {a : ℝ} (ha : 0 < a) :
    (903 - 205 * a - 144 / a) / 288 < (847 / 432 : ℝ) := by
  have hq := subtwo_pos_615 a
  have hd : 0 < (615 * a ^ 2 - 1015 * a + 432) / (864 * a) :=
    div_pos hq (by positivity)
  have hid : (847 / 432 : ℝ) - (903 - 205 * a - 144 / a) / 288 =
      (615 * a ^ 2 - 1015 * a + 432) / (864 * a) := by
    field_simp
    ring
  linarith

theorem subtwo_uniformTriangle_case_BF {a : ℝ} (ha : 0 < a) :
    (4231 - 1937 * a - 832 / a) / 864 < (847 / 432 : ℝ) := by
  have hq := subtwo_pos_1937 a
  have hd : 0 < (1937 * a ^ 2 - 2537 * a + 832) / (864 * a) :=
    div_pos hq (by positivity)
  have hid : (847 / 432 : ℝ) -
      (4231 - 1937 * a - 832 / a) / 864 =
      (1937 * a ^ 2 - 2537 * a + 832) / (864 * a) := by
    field_simp
    ring
  linarith

theorem subtwo_uniformTriangle_case_FB {a : ℝ}
    (ha : (1 / 2 : ℝ) ≤ a) :
    (277 - 11 * a) / 144 < (847 / 432 : ℝ) := by
  nlinarith

theorem subtwo_uniformTriangle_case_FF {a : ℝ} (ha : 0 < a) :
    (796 - 347 * a - 100 / a) / 216 < (847 / 432 : ℝ) := by
  have hq := subtwo_pos_694 a
  have hd : 0 < (694 * a ^ 2 - 745 * a + 200) / (432 * a) :=
    div_pos hq (by positivity)
  have hid : (847 / 432 : ℝ) -
      (796 - 347 * a - 100 / a) / 216 =
      (694 * a ^ 2 - 745 * a + 200) / (432 * a) := by
    field_simp
    ring
  linarith

theorem subtwo_uniformTriangle_scalarBudget_lt :
    (847 / 432 : ℝ) < 157 / 80 := by
  norm_num

theorem subtwo_uniformModel_rho_h_balance {a : ℝ} (ha : 0 < a) :
    2 * (1 - a) / (3 * a) +
      2 * ((2 * a - 1) / (3 * a)) = (2 / 3 : ℝ) := by
  field_simp
  ring

end WeightedEdgeColoring
