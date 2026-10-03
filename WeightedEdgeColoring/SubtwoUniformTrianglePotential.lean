import WeightedEdgeColoring.SubtwoEndpointPotential
import WeightedEdgeColoring.SubtwoTwoModelGeometry
import WeightedEdgeColoring.SubtwoUniformModelScalars
import Mathlib.Tactic

/-!
# Endpoint certificate for the uniform high-price triangle

All three triangle edges have packet-price majorant `a`; the remaining
seven have majorant `1-a`. The witness is the one in the analytic
five-vertex appendix, including the mandatory pair-sum payment on 34.
-/

namespace WeightedEdgeColoring.Subtwo.UniformTrianglePotential

set_option maxHeartbeats 1000000

open EndpointPotential
open TwoModelGeometry

noncomputable def s (a : ℝ) : ℝ := 1 - a
noncomputable def q (a : ℝ) : ℝ := 2 * s a / (3 * a)
noncomputable def hval (a : ℝ) : ℝ := (2 * a - 1) / (3 * a)
noncomputable def x (a : ℝ) : ℝ := min (2 * s a) ((2 - a) / 3)
noncomputable def y (a : ℝ) : ℝ := 2 * s a - x a
noncomputable def w (a : ℝ) : ℝ := max 0 (max (y a - q a * s a) (q a * s a / 2))

noncomputable def rho (a : ℝ) : Bundle → ℝ :=
  ![2 / 3, 2 / 3, 2 / 3, 2 / 3, 2 / 3,
    2 / 3, 2 / 3, 2 / 3, 2 / 3, q a]

noncomputable def h (a : ℝ) : Vertex → ℝ :=
  ![hval a, hval a, hval a, 0, 0]

noncomputable def zLeft (a : ℝ) : Bundle → ℝ :=
  ![a, a, x a, x a, a, x a, x a, x a, x a, s a]

noncomputable def z (a : ℝ) (v : Vertex) (e : Bundle) : ℝ :=
  if v = left e then zLeft a e
  else if v = right e then 2 * T a e - zLeft a e
  else 0

noncomputable def c (a : ℝ) : Vertex → ℝ :=
  ![(a + 1) / 3, (a + 1) / 3, (a + 1) / 3, s a, s a]

noncomputable def alphaLeft (a : ℝ) : Bundle → ℝ :=
  ![a / 3, a / 3, a / 3, a / 3, a / 3,
    a / 3, a / 3, a / 3, a / 3, w a]

noncomputable def alphaRight (a : ℝ) : Bundle → ℝ :=
  ![a / 3, a / 3, s a / 3, s a / 3, a / 3,
    s a / 3, s a / 3, s a / 3, s a / 3, w a]

noncomputable def alpha (a : ℝ) (v : Vertex) (e : Bundle) : ℝ :=
  if v = left e then alphaLeft a e
  else if v = right e then alphaRight a e
  else 0

noncomputable def BH (a : ℝ) : ℝ := lightCharge * ((a + 1) / 3) + hval a
noncomputable def BO (a : ℝ) : ℝ := lightCharge * s a
noncomputable def fH (a : ℝ) : ℝ := (97 * a + 36) / 54
noncomputable def fS (a : ℝ) : ℝ := 2 / 3 + 4 * s a / 3 + residualCharge / 3
noncomputable def fOplus (a : ℝ) : ℝ := -(319 * a ^ 2 - 344 * a + 50) / (54 * a)
noncomputable def PH (a : ℝ) : ℝ := max (BH a) (fH a / 2)
noncomputable def PO (a : ℝ) : ℝ := max (BO a) (fOplus a / 2)
noncomputable def P (a : ℝ) : Vertex → ℝ :=
  ![PH a, PH a, PH a, PO a, PO a]

private theorem a_pos {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) : 0 < a := by linarith

private theorem s_nonneg {a : ℝ} (ha : a ≤ 1) : 0 ≤ s a := by
  dsimp [s]
  linarith

private theorem s_le_a {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) : s a ≤ a := by
  dsimp [s]
  linarith

private theorem hval_nonneg {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) :
    0 ≤ hval a := by
  unfold hval
  exact div_nonneg (by linarith) (by positivity)

private theorem q_nonneg {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    0 ≤ q a := by
  unfold q
  exact div_nonneg (mul_nonneg (by norm_num) (s_nonneg ha1)) (by positivity)

private theorem q_le_two_thirds {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) :
    q a ≤ 2 / 3 := by
  have hpos : 0 < 3 * a := by positivity
  unfold q
  apply (div_le_iff₀ hpos).2
  dsimp [s]
  nlinarith

private theorem x_bounds {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    s a ≤ x a ∧ x a ≤ 2 * s a ∧ x a ≤ (2 - a) / 3 := by
  unfold x
  have hs := s_nonneg ha1
  constructor
  · apply le_min
    · linarith
    · dsimp [s]; linarith
  constructor
  · exact min_le_left _ _
  · exact min_le_right _ _

private theorem y_bounds {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    0 ≤ y a ∧ y a ≤ s a := by
  obtain ⟨hxs, hx2, _⟩ := x_bounds ha ha1
  unfold y
  exact ⟨by linarith, by linarith⟩

private theorem w_nonneg (a : ℝ) : 0 ≤ w a := by
  unfold w
  exact le_max_left _ _

private theorem cH_add_h_packet {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) :
    (a + 1) / 3 + hval a * a = a := by
  have hapos := a_pos ha
  unfold hval
  field_simp
  ring

private theorem x_le_cH {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    x a ≤ (a + 1) / 3 := by
  have hx := (x_bounds ha ha1).2.2
  linarith

private theorem x_le_spoke_allowance {a : ℝ}
    (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    x a - (2 / 3) * s a ≤ a / 3 := by
  have hx := (x_bounds ha ha1).2.2
  dsimp [s] at *
  linarith

private theorem w_ge_off (a : ℝ) : y a - q a * s a ≤ w a := by
  unfold w
  exact le_trans (le_max_left _ _) (le_max_right _ _)

private theorem w_ge_pair (a : ℝ) : q a * s a / 2 ≤ w a := by
  unfold w
  exact le_trans (le_max_right _ _) (le_max_right _ _)

private theorem z_nonneg {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∀ v e, 0 ≤ z a v e := by
  have hs := s_nonneg ha1
  obtain ⟨hxs, hx2, _⟩ := x_bounds ha ha1
  dsimp [s] at hs hxs hx2
  intro v e
  fin_cases v <;> fin_cases e <;>
    simp [z, zLeft, T, left, right, s] <;> linarith

private theorem c_nonneg {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∀ v, 0 ≤ c a v := by
  have hs := s_nonneg ha1
  intro v
  fin_cases v <;> simp [c] <;> linarith

private theorem alpha_nonneg {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∀ v e, 0 ≤ alpha a v e := by
  have hs := s_nonneg ha1
  have hw := w_nonneg a
  intro v e
  fin_cases v <;> fin_cases e <;>
    simp [alpha, alphaLeft, alphaRight, left, right] <;> linarith

private theorem P_nonneg {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∀ v, 0 ≤ P a v := by
  have hs := s_nonneg ha1
  have hh := hval_nonneg ha
  have hA : 0 ≤ lightCharge := by norm_num [lightCharge]
  have hBH : 0 ≤ BH a := by
    unfold BH
    positivity
  have hBO : 0 ≤ BO a := by
    unfold BO
    positivity
  have hPH : 0 ≤ PH a := le_trans hBH (le_max_left _ _)
  have hPO : 0 ≤ PO a := le_trans hBO (le_max_left _ _)
  intro v
  fin_cases v <;> simp [P, hPH, hPO]

private theorem split (a : ℝ) :
    ∀ e, z a (left e) e + z a (right e) e = 2 * T a e := by
  intro e
  fin_cases e <;> simp [z, zLeft, T, left, right]

private theorem light {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∀ v e, Inc v e → z a v e ≤ c a v + h a v * T a e := by
  have hs := s_nonneg ha1
  have hh := hval_nonneg ha
  have hhs : 0 ≤ hval a * s a := mul_nonneg hh hs
  obtain ⟨hxs, _, hxa⟩ := x_bounds ha ha1
  have hcH := cH_add_h_packet ha
  have hxcH := x_le_cH ha ha1
  dsimp [s] at hs hhs hxs
  intro v e he
  fin_cases v <;> fin_cases e <;>
    simp [Inc, left, right, z, zLeft, T, c, h, s] at he ⊢ <;>
    linarith

private theorem baseline (a : ℝ) :
    ∀ v, lightCharge * c a v + h a v ≤ P a v := by
  intro v
  fin_cases v <;> simp [c, h, P, PH, PO, BH, BO]

private theorem off {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∀ v e f, Inc v e → Inc v f → f ≠ e →
      z a v f - rho a e * T a f ≤ alpha a v e := by
  have hsa := s_le_a ha
  have hxs := (x_bounds ha ha1).1
  have hx := x_le_spoke_allowance ha ha1
  have hy := (y_bounds ha ha1).2
  have hw := w_ge_off a
  have hxy : x a + y a = 2 * s a := by unfold y; ring
  dsimp [s] at hsa hxs hx hy hw hxy
  intro v e f he hf hfe
  fin_cases v <;> fin_cases e <;> fin_cases f <;>
    simp [Inc, left, right, z, zLeft, T, alpha, alphaLeft,
      alphaRight, rho, s] at he hf hfe ⊢ <;> linarith

private theorem same {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∀ v e, Inc v e →
      z a v e - (2 - rho a e) * T a e ≤ alpha a v e := by
  have hx := (x_bounds ha ha1).2.2
  have hy := (y_bounds ha ha1).2
  have hs := s_nonneg ha1
  have hq := q_le_two_thirds ha
  have hw := w_nonneg a
  have hxa := x_le_spoke_allowance ha ha1
  have hxy : x a + y a = 2 * s a := by unfold y; ring
  dsimp [s] at hx hy hs hxa hxy
  intro v e he
  fin_cases v <;> fin_cases e <;>
    simp [Inc, left, right, z, zLeft, T, alpha, alphaLeft,
      alphaRight, rho, s] at he ⊢ <;> nlinarith

private theorem pair {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (_ha1 : a ≤ 1) :
    ∀ e, rho a e * T a e ≤ alpha a (left e) e + alpha a (right e) e := by
  have hsa := s_le_a ha
  have hw := w_ge_pair a
  dsimp [s] at hsa hw
  intro e
  fin_cases e <;>
    simp [rho, T, alpha, alphaLeft, alphaRight, left, right, s] <;>
    nlinarith

private theorem spoke_cost_le {a : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    fS a ≤ PH a + PO a := by
  have hap := a_pos ha
  have hh : fH a / 2 ≤ PH a := le_max_right _ _
  have ho : fOplus a / 2 ≤ PO a := le_max_right _ _
  have hid : (fH a + fOplus a) / 2 - fS a =
      -((2 * a - 1) * (39 * a - 50)) / (108 * a) := by
    unfold fH fOplus fS residualCharge s
    field_simp
    ring
  have hnon : 0 ≤ -((2 * a - 1) * (39 * a - 50)) / (108 * a) := by
    apply div_nonneg
    · apply neg_nonneg.mpr
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    · positivity
  linarith

private theorem triangle_cost_le (a : ℝ) : fH a ≤ 2 * PH a := by
  have := le_max_right (BH a) (fH a / 2)
  dsimp [PH] at *
  linarith

noncomputable def fOcost (a : ℝ) : ℝ :=
  (2 - q a) * s a + q a + 2 * residualCharge * w a

noncomputable def fOpair (a : ℝ) : ℝ :=
  (2 - q a) * s a + q a + residualCharge * q a * s a

private theorem x_eq_outer_low {a : ℝ} (ha : a ≤ 4 / 5) :
    x a = (2 - a) / 3 := by
  unfold x
  exact min_eq_right (by dsimp [s]; linarith)

private theorem x_eq_outer_high {a : ℝ} (ha : 4 / 5 ≤ a) :
    x a = 2 * s a := by
  unfold x
  exact min_eq_left (by dsimp [s]; linarith)

private theorem fOpair_le_max {a : ℝ}
    (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    fOpair a ≤ max (fOplus a) (2 * BO a) := by
  have hap := a_pos ha
  by_cases hthree : a ≤ 3 / 4
  · have hid : fOpair a - fOplus a =
        25 * (2 * a - 1) * (4 * a - 3) / (54 * a) := by
      unfold fOpair fOplus q s residualCharge
      field_simp
      ring
    have hle : fOpair a ≤ fOplus a := by
      have : (2 * a - 1) * (4 * a - 3) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have : 25 * (2 * a - 1) * (4 * a - 3) / (54 * a) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · nlinarith
        · positivity
      linarith
    exact le_trans hle (le_max_left _ _)
  · have hid : fOpair a - 2 * BO a =
        (a - 1) * (139 * a - 100) / (216 * a) := by
      unfold fOpair BO q s residualCharge lightCharge
      field_simp
      ring
    have hle : fOpair a ≤ 2 * BO a := by
      have : (a - 1) * (139 * a - 100) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      have : (a - 1) * (139 * a - 100) / (216 * a) ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg this (by positivity)
      linarith
    exact le_trans hle (le_max_right _ _)

private theorem fOcost_le_max {a : ℝ}
    (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    fOcost a ≤ max (fOplus a) (2 * BO a) := by
  have hqs : 0 ≤ q a * s a := mul_nonneg (q_nonneg ha ha1) (s_nonneg ha1)
  have hpair := fOpair_le_max ha ha1
  by_cases hbranch : y a - q a * s a ≤ q a * s a / 2
  · have hw : w a = q a * s a / 2 := by
      unfold w
      rw [max_eq_right hbranch, max_eq_right (by linarith : (0:ℝ) ≤ q a * s a / 2)]
    have heq : fOcost a = fOpair a := by
      unfold fOcost fOpair
      rw [hw]
      ring
    rw [heq]
    exact hpair
  · have hw : w a = y a - q a * s a := by
      unfold w
      have hb : q a * s a / 2 ≤ y a - q a * s a := le_of_not_ge hbranch
      rw [max_eq_left hb, max_eq_right (by linarith [hqs] : (0:ℝ) ≤ y a - q a * s a)]
    have ha45 : a ≤ 4 / 5 := by
      by_contra hc
      have hx := x_eq_outer_high (show 4 / 5 ≤ a by linarith)
      have hy : y a = 0 := by unfold y; rw [hx]; ring
      rw [hy] at hbranch
      nlinarith [hqs]
    have hx := x_eq_outer_low ha45
    have heq : fOcost a = fOplus a := by
      unfold fOcost fOplus
      rw [hw]
      unfold y
      rw [hx]
      unfold q s residualCharge
      have hap := a_pos ha
      field_simp
      ring
    rw [heq]
    exact le_max_left _ _

private theorem outer_cost_le {a : ℝ}
    (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    fOcost a ≤ 2 * PO a := by
  have hc := fOcost_le_max ha ha1
  have hB : BO a ≤ PO a := le_max_left _ _
  have hF : fOplus a / 2 ≤ PO a := le_max_right _ _
  have : max (fOplus a) (2 * BO a) ≤ 2 * PO a := by
    apply max_le
    all_goals linarith
  linarith

private theorem edge {a : ℝ}
    (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∀ e, (2 - rho a e) * T a e + rho a e +
      residualCharge * (alpha a (left e) e + alpha a (right e) e) ≤
        P a (left e) + P a (right e) := by
  have hH := triangle_cost_le a
  have hS := spoke_cost_le ha ha1
  have hO := outer_cost_le ha ha1
  have hidH : (2 - 2 / 3) * a + 2 / 3 + residualCharge * (a / 3 + a / 3) = fH a := by
    unfold fH residualCharge
    ring
  have hidS : (2 - 2 / 3) * s a + 2 / 3 + residualCharge * (a / 3 + s a / 3) = fS a := by
    unfold fS s
    ring
  have hidO : (2 - q a) * s a + q a + residualCharge * (w a + w a) = fOcost a := by
    unfold fOcost
    ring
  dsimp [s] at hidS hidO
  intro e
  fin_cases e <;>
    simp [rho, T, alpha, alphaLeft, alphaRight, left, right, P, s] <;>
    linarith

noncomputable def certificate (a : ℝ) (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    EndpointPotential.Certificate (T a) (rho a) (h a) where
  z := z a
  c := c a
  alpha := alpha a
  P := P a
  z_nonneg := z_nonneg ha ha1
  c_nonneg := c_nonneg ha ha1
  alpha_nonneg := alpha_nonneg ha ha1
  P_nonneg := P_nonneg ha ha1
  split := split a
  light := light ha ha1
  baseline := baseline a
  off := off ha ha1
  same := same ha ha1
  pair := pair ha ha1
  edge := edge ha ha1

theorem certificate_budget (a : ℝ) (ha : (1 / 2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∑ v, (certificate a ha ha1).P v ≤ (157 / 40 : ℝ) := by
  have hap := a_pos ha
  have hBBid : (3 * BH a + 2 * BO a) / 2 =
      (903 - 205 * a - 144 / a) / 288 := by
    unfold BH BO hval s lightCharge
    field_simp
    ring
  have hBFid : (3 * BH a + 2 * (fOplus a / 2)) / 2 =
      (4231 - 1937 * a - 832 / a) / 864 := by
    unfold BH fOplus hval lightCharge
    field_simp
    ring
  have hFBid : (3 * (fH a / 2) + 2 * BO a) / 2 =
      (277 - 11 * a) / 144 := by
    unfold fH BO s lightCharge
    ring
  have hFFid : (3 * (fH a / 2) + 2 * (fOplus a / 2)) / 2 =
      (796 - 347 * a - 100 / a) / 216 := by
    unfold fH fOplus
    field_simp
    ring
  have hBB : (3 * BH a + 2 * BO a) / 2 < (847 / 432 : ℝ) := by
    rw [hBBid]
    exact WeightedEdgeColoring.subtwo_uniformTriangle_case_BB hap
  have hBF : (3 * BH a + 2 * (fOplus a / 2)) / 2 < (847 / 432 : ℝ) := by
    rw [hBFid]
    exact WeightedEdgeColoring.subtwo_uniformTriangle_case_BF hap
  have hFB : (3 * (fH a / 2) + 2 * BO a) / 2 < (847 / 432 : ℝ) := by
    rw [hFBid]
    exact WeightedEdgeColoring.subtwo_uniformTriangle_case_FB ha
  have hFF : (3 * (fH a / 2) + 2 * (fOplus a / 2)) / 2 < (847 / 432 : ℝ) := by
    rw [hFFid]
    exact WeightedEdgeColoring.subtwo_uniformTriangle_case_FF hap
  have hhalf : (3 * PH a + 2 * PO a) / 2 < (847 / 432 : ℝ) := by
    rcases le_total (fH a / 2) (BH a) with hH | hH <;>
      rcases le_total (fOplus a / 2) (BO a) with hO | hO
    · simpa [PH, PO, max_eq_left hH, max_eq_left hO] using hBB
    · simpa [PH, PO, max_eq_left hH, max_eq_right hO] using hBF
    · simpa [PH, PO, max_eq_right hH, max_eq_left hO] using hFB
    · simpa [PH, PO, max_eq_right hH, max_eq_right hO] using hFF
  have htarget := WeightedEdgeColoring.subtwo_uniformTriangle_scalarBudget_lt
  have hsum : (∑ v, (certificate a ha ha1).P v) = 3 * PH a + 2 * PO a := by
    simp [certificate, P, Fin.sum_univ_succ]
    ring
  rw [hsum]
  linarith

end WeightedEdgeColoring.Subtwo.UniformTrianglePotential
