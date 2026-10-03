import WeightedEdgeColoring.SubtwoUniformStarPotential
import WeightedEdgeColoring.SubtwoTwoModelGeometry
import WeightedEdgeColoring.SubtwoUniformTrianglePotential

/-! Relabelled endpoint certificates and the three-model interpolation. -/

namespace WeightedEdgeColoring.Subtwo.EndpointPotential

def swap01V : Vertex → Vertex := ![1, 0, 2, 3, 4]
def swap01E : Bundle → Bundle := ![0, 4, 5, 6, 1, 2, 3, 7, 8, 9]

private theorem swap01V_involutive (v : Vertex) : swap01V (swap01V v) = v := by
  fin_cases v <;> decide

private theorem swap01E_involutive (e : Bundle) : swap01E (swap01E e) = e := by
  fin_cases e <;> decide

private theorem swap01_inc (v : Vertex) (e : Bundle) :
    Inc v e ↔ Inc (swap01V v) (swap01E e) := by
  fin_cases v <;> fin_cases e <;> decide

private theorem swap01_endpoint_sum (f : Vertex → Bundle → ℝ) (e : Bundle) :
    f (swap01V (left e)) (swap01E e) +
      f (swap01V (right e)) (swap01E e) =
    f (left (swap01E e)) (swap01E e) +
      f (right (swap01E e)) (swap01E e) := by
  fin_cases e <;> simp [swap01V, swap01E, left, right, add_comm]

private theorem swap01_endpoint_P_sum (f : Vertex → ℝ) (e : Bundle) :
    f (swap01V (left e)) + f (swap01V (right e)) =
    f (left (swap01E e)) + f (right (swap01E e)) := by
  fin_cases e <;> simp [swap01V, swap01E, left, right, add_comm]

private theorem swap01_sum (f : Vertex → ℝ) :
    (∑ v, f (swap01V v)) = ∑ v, f v := by
  simp [Fin.sum_univ_five, swap01V]
  ring

/-- A convex combination of three endpoint witnesses, with no division by
the total weight of any subset of the models. -/
noncomputable def Certificate.mix3
    {m₀ m₁ m₂ m rho : Bundle → ℝ} {h : Vertex → ℝ}
    (C₀ : Certificate m₀ rho h) (C₁ : Certificate m₁ rho h)
    (C₂ : Certificate m₂ rho h)
    (t₀ t₁ t₂ : ℝ) (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (hsum : t₀ + t₁ + t₂ = 1)
    (hm : ∀ e, m e = t₀ * m₀ e + t₁ * m₁ e + t₂ * m₂ e) :
    Certificate m rho h where
  z := fun v e ↦ t₀*C₀.z v e+t₁*C₁.z v e+t₂*C₂.z v e
  c := fun v ↦ t₀*C₀.c v+t₁*C₁.c v+t₂*C₂.c v
  alpha := fun v e ↦ t₀*C₀.alpha v e+t₁*C₁.alpha v e+t₂*C₂.alpha v e
  P := fun v ↦ t₀*C₀.P v+t₁*C₁.P v+t₂*C₂.P v
  z_nonneg := by
    intro v e
    exact add_nonneg (add_nonneg (mul_nonneg ht₀ (C₀.z_nonneg v e))
      (mul_nonneg ht₁ (C₁.z_nonneg v e))) (mul_nonneg ht₂ (C₂.z_nonneg v e))
  c_nonneg := by
    intro v
    exact add_nonneg (add_nonneg (mul_nonneg ht₀ (C₀.c_nonneg v))
      (mul_nonneg ht₁ (C₁.c_nonneg v))) (mul_nonneg ht₂ (C₂.c_nonneg v))
  alpha_nonneg := by
    intro v e
    exact add_nonneg (add_nonneg (mul_nonneg ht₀ (C₀.alpha_nonneg v e))
      (mul_nonneg ht₁ (C₁.alpha_nonneg v e))) (mul_nonneg ht₂ (C₂.alpha_nonneg v e))
  P_nonneg := by
    intro v
    exact add_nonneg (add_nonneg (mul_nonneg ht₀ (C₀.P_nonneg v))
      (mul_nonneg ht₁ (C₁.P_nonneg v))) (mul_nonneg ht₂ (C₂.P_nonneg v))
  split := by
    intro e
    have h₀ := C₀.split e
    have h₁ := C₁.split e
    have h₂ := C₂.split e
    rw [hm e]
    nlinarith
  light := by
    intro v e he
    have h₀ := mul_le_mul_of_nonneg_left (C₀.light v e he) ht₀
    have h₁ := mul_le_mul_of_nonneg_left (C₁.light v e he) ht₁
    have h₂ := mul_le_mul_of_nonneg_left (C₂.light v e he) ht₂
    rw [hm e]
    nlinarith
  baseline := by
    intro v
    have h₀ := mul_le_mul_of_nonneg_left (C₀.baseline v) ht₀
    have h₁ := mul_le_mul_of_nonneg_left (C₁.baseline v) ht₁
    have h₂ := mul_le_mul_of_nonneg_left (C₂.baseline v) ht₂
    have hh := congrArg (fun t : ℝ ↦ t * h v) hsum
    nlinarith
  off := by
    intro v e f he hf hfe
    have h₀ := mul_le_mul_of_nonneg_left (C₀.off v e f he hf hfe) ht₀
    have h₁ := mul_le_mul_of_nonneg_left (C₁.off v e f he hf hfe) ht₁
    have h₂ := mul_le_mul_of_nonneg_left (C₂.off v e f he hf hfe) ht₂
    rw [hm f]
    nlinarith
  same := by
    intro v e he
    have h₀ := mul_le_mul_of_nonneg_left (C₀.same v e he) ht₀
    have h₁ := mul_le_mul_of_nonneg_left (C₁.same v e he) ht₁
    have h₂ := mul_le_mul_of_nonneg_left (C₂.same v e he) ht₂
    rw [hm e]
    nlinarith
  pair := by
    intro e
    have h₀ := mul_le_mul_of_nonneg_left (C₀.pair e) ht₀
    have h₁ := mul_le_mul_of_nonneg_left (C₁.pair e) ht₁
    have h₂ := mul_le_mul_of_nonneg_left (C₂.pair e) ht₂
    rw [hm e]
    nlinarith
  edge := by
    intro e
    have h₀ := mul_le_mul_of_nonneg_left (C₀.edge e) ht₀
    have h₁ := mul_le_mul_of_nonneg_left (C₁.edge e) ht₁
    have h₂ := mul_le_mul_of_nonneg_left (C₂.edge e) ht₂
    have hr := congrArg (fun t : ℝ ↦ t * rho e) hsum
    rw [hm e]
    nlinarith

theorem Certificate.mix3_budget
    {m₀ m₁ m₂ m rho : Bundle → ℝ} {h : Vertex → ℝ}
    (C₀ : Certificate m₀ rho h) (C₁ : Certificate m₁ rho h)
    (C₂ : Certificate m₂ rho h)
    (t₀ t₁ t₂ : ℝ) (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (hsum : t₀+t₁+t₂=1)
    (hm : ∀ e, m e=t₀*m₀ e+t₁*m₁ e+t₂*m₂ e)
    (B : ℝ) (h₀ : ∑ v, C₀.P v ≤ B) (h₁ : ∑ v, C₁.P v ≤ B)
    (h₂ : ∑ v, C₂.P v ≤ B) :
    ∑ v, (C₀.mix3 C₁ C₂ t₀ t₁ t₂ ht₀ ht₁ ht₂ hsum hm).P v ≤ B := by
  change ∑ v, (t₀*C₀.P v+t₁*C₁.P v+t₂*C₂.P v) ≤ B
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have h₀' := mul_le_mul_of_nonneg_left h₀ ht₀
  have h₁' := mul_le_mul_of_nonneg_left h₁ ht₁
  have h₂' := mul_le_mul_of_nonneg_left h₂ ht₂
  have hb := congrArg (fun t : ℝ ↦ t * B) hsum
  nlinarith

noncomputable def Certificate.swap01 {m rho : Bundle → ℝ} {h : Vertex → ℝ}
    (C : Certificate m rho h) :
    Certificate (fun e ↦ m (swap01E e))
      (fun e ↦ rho (swap01E e)) (fun v ↦ h (swap01V v)) where
  z := fun v e ↦ C.z (swap01V v) (swap01E e)
  c := fun v ↦ C.c (swap01V v)
  alpha := fun v e ↦ C.alpha (swap01V v) (swap01E e)
  P := fun v ↦ C.P (swap01V v)
  z_nonneg := by intro v e; exact C.z_nonneg _ _
  c_nonneg := by intro v; exact C.c_nonneg _
  alpha_nonneg := by intro v e; exact C.alpha_nonneg _ _
  P_nonneg := by intro v; exact C.P_nonneg _
  split := by
    intro e
    rw [swap01_endpoint_sum]
    exact C.split (swap01E e)
  light := by
    intro v e he
    exact C.light _ _ ((swap01_inc v e).mp he)
  baseline := by
    intro v
    exact C.baseline (swap01V v)
  off := by
    intro v e f he hf hfe
    exact C.off _ _ _ ((swap01_inc v e).mp he) ((swap01_inc v f).mp hf)
      (by intro h; exact hfe (swap01E_involutive f ▸
        swap01E_involutive e ▸ congrArg swap01E h))
  same := by
    intro v e he
    exact C.same _ _ ((swap01_inc v e).mp he)
  pair := by
    intro e
    rw [swap01_endpoint_sum]
    exact C.pair (swap01E e)
  edge := by
    intro e
    rw [swap01_endpoint_sum, swap01_endpoint_P_sum]
    exact C.edge (swap01E e)

private theorem uniformStarM_S0 (a : ℝ) :
    uniformStarM a = TwoModelGeometry.S0 a := by
  funext e
  fin_cases e <;> rfl

private theorem uniformStarM_swap_S1 (a : ℝ) :
    (fun e ↦ uniformStarM a (swap01E e)) = TwoModelGeometry.S1 a := by
  funext e
  fin_cases e <;> rfl

private theorem uniformStarRho_swap (a : ℝ) :
    (fun e ↦ uniformStarRho a (swap01E e)) = uniformStarRho a := by
  funext e
  fin_cases e <;> simp [uniformStarRho, swap01E]

private theorem uniformStarH_swap (a : ℝ) :
    (fun v ↦ uniformStarH a (swap01V v)) = uniformStarH a := by
  funext v
  fin_cases v <;> simp [uniformStarH, swap01V]

private theorem triangleRho_eq_star (a : ℝ) :
    UniformTrianglePotential.rho a = uniformStarRho a := by
  funext e
  fin_cases e <;> rfl

private theorem triangleH_eq_star (a : ℝ) :
    UniformTrianglePotential.h a = uniformStarH a := by
  funext v
  fin_cases v <;> rfl

noncomputable def uniformStarS0_certificate (a : ℝ)
    (ha : (1/2:ℝ) ≤ a) (ha1 : a ≤ 1) :
    Certificate (TwoModelGeometry.S0 a) (uniformStarRho a) (uniformStarH a) :=
  uniformStar_certificate a ha ha1

noncomputable def uniformTriangle_shared_certificate (a : ℝ)
    (ha : (1/2:ℝ) ≤ a) (ha1 : a ≤ 1) :
    Certificate (TwoModelGeometry.T a) (uniformStarRho a) (uniformStarH a) :=
  UniformTrianglePotential.certificate a ha ha1

noncomputable def uniformStarSwap_certificate (a : ℝ)
    (ha : (1/2:ℝ) ≤ a) (ha1 : a ≤ 1) :
    Certificate (TwoModelGeometry.S1 a) (uniformStarRho a) (uniformStarH a) :=
  let C := (uniformStar_certificate a ha ha1).swap01
  have hm : ∀ e, uniformStarM a (swap01E e) = TwoModelGeometry.S1 a e :=
    fun e ↦ congrFun (uniformStarM_swap_S1 a) e
  have hr : ∀ e, uniformStarRho a (swap01E e) = uniformStarRho a e :=
    fun e ↦ congrFun (uniformStarRho_swap a) e
  have hh : ∀ v, uniformStarH a (swap01V v) = uniformStarH a v :=
    fun v ↦ congrFun (uniformStarH_swap a) v
  { z := C.z
    c := C.c
    alpha := C.alpha
    P := C.P
    z_nonneg := C.z_nonneg
    c_nonneg := C.c_nonneg
    alpha_nonneg := C.alpha_nonneg
    P_nonneg := C.P_nonneg
    split := by
      intro e
      simpa only [hm e] using C.split e
    light := by
      intro v e he
      simpa only [hm e, hh v] using C.light v e he
    baseline := by
      intro v
      simpa only [hh v] using C.baseline v
    off := by
      intro v e f he hf hfe
      simpa only [hm f, hr e] using
        C.off v e f he hf hfe
    same := by
      intro v e he
      simpa only [hm e, hr e] using C.same v e he
    pair := by
      intro e
      simpa only [hm e, hr e] using C.pair e
    edge := by
      intro e
      simpa only [hm e, hr e] using C.edge e }

theorem uniformStarSwap_budget (a : ℝ) (ha : (1/2:ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∑ v, (uniformStarSwap_certificate a ha ha1).P v = (157/40:ℝ) := by
  change ∑ v, (uniformStar_certificate a ha ha1).P (swap01V v) = _
  rw [swap01_sum]
  exact uniformStar_budget a ha ha1

theorem uniformStarS0_budget (a : ℝ) (ha : (1/2:ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∑ v, (uniformStarS0_certificate a ha ha1).P v = (157/40:ℝ) := by
  exact uniformStar_budget a ha ha1

theorem uniformTriangle_shared_budget (a : ℝ)
    (ha : (1/2:ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∑ v, (uniformTriangle_shared_certificate a ha ha1).P v ≤ (157/40:ℝ) := by
  exact UniformTrianglePotential.certificate_budget a ha ha1

noncomputable def uniformModel_certificate (a x y : ℝ)
    (ha : (1/2:ℝ) < a) (ha1 : a ≤ 1)
    (hsy : 1-a ≤ y) (hyx : y ≤ x) (hxa : x ≤ a) :
    Certificate (TwoModelGeometry.M a x y) (uniformStarRho a) (uniformStarH a) :=
  (uniformStarS0_certificate a (le_of_lt ha) ha1).mix3
    (uniformStarSwap_certificate a (le_of_lt ha) ha1)
    (uniformTriangle_shared_certificate a (le_of_lt ha) ha1)
    (TwoModelGeometry.lambda0 a y)
    (TwoModelGeometry.lambda1 a x)
    (TwoModelGeometry.lambdaT a x y)
    (TwoModelGeometry.lambda0_nonneg a y ha hsy)
    (TwoModelGeometry.lambda1_nonneg a x ha hxa)
    (TwoModelGeometry.lambdaT_nonneg a x y ha hyx)
    (TwoModelGeometry.lambda_sum a x y ha)
    (TwoModelGeometry.M_eq_convex_models a x y ha)

theorem uniformModel_budget (a x y : ℝ)
    (ha : (1/2:ℝ) < a) (ha1 : a ≤ 1)
    (hsy : 1-a ≤ y) (hyx : y ≤ x) (hxa : x ≤ a) :
    ∑ v, (uniformModel_certificate a x y ha ha1 hsy hyx hxa).P v ≤
      (157/40:ℝ) := by
  have ha0 : (1/2:ℝ) ≤ a := le_of_lt ha
  let C₀ := uniformStarS0_certificate a ha0 ha1
  let C₁ := uniformStarSwap_certificate a ha0 ha1
  let C₂ := uniformTriangle_shared_certificate a ha0 ha1
  have ht₀ := TwoModelGeometry.lambda0_nonneg a y ha hsy
  have ht₁ := TwoModelGeometry.lambda1_nonneg a x ha hxa
  have ht₂ := TwoModelGeometry.lambdaT_nonneg a x y ha hyx
  have hsum := TwoModelGeometry.lambda_sum a x y ha
  have hm := TwoModelGeometry.M_eq_convex_models a x y ha
  have h₀ : ∑ v, C₀.P v ≤ (157/40:ℝ) := by
    simpa [C₀] using le_of_eq (uniformStarS0_budget a ha0 ha1)
  have h₁ : ∑ v, C₁.P v ≤ (157/40:ℝ) := by
    simpa [C₁] using le_of_eq (uniformStarSwap_budget a ha0 ha1)
  have h₂ : ∑ v, C₂.P v ≤ (157/40:ℝ) := by
    simpa [C₂] using uniformTriangle_shared_budget a ha0 ha1
  simpa only [uniformModel_certificate, C₀, C₁, C₂] using
    (C₀.mix3_budget C₁ C₂
      (TwoModelGeometry.lambda0 a y)
      (TwoModelGeometry.lambda1 a x)
      (TwoModelGeometry.lambdaT a x y)
      ht₀ ht₁ ht₂ hsum hm (157/40:ℝ) h₀ h₁ h₂)

theorem uniformModel_cap_nonneg (a x y : ℝ)
    (ha : (1/2:ℝ) < a) (ha1 : a ≤ 1)
    (hsy : 1-a ≤ y) (hyx : y ≤ x) (hxa : x ≤ a) :
    ∀ e, 0 ≤ TwoModelGeometry.M a x y e := by
  intro e
  fin_cases e <;> simp [TwoModelGeometry.M] <;> linarith

theorem uniformModel_rho_nonneg (a : ℝ)
    (ha : (1/2:ℝ) < a) (ha1 : a ≤ 1) :
    ∀ e, 0 ≤ uniformStarRho a e := by
  intro e
  fin_cases e <;> simp [uniformStarRho] <;> try { norm_num }
  change 0 ≤ 2*(1-a)/(3*a)
  exact div_nonneg (by nlinarith) (by positivity)

theorem uniformModel_rho_le_two (a : ℝ)
    (ha : (1/2:ℝ) < a) (_ha1 : a ≤ 1) :
    ∀ e, uniformStarRho a e ≤ 2 := by
  intro e
  fin_cases e <;> simp [uniformStarRho] <;> try { norm_num }
  change 2*(1-a)/(3*a) ≤ 2
  apply (div_le_iff₀ (by positivity : 0 < 3*a)).mpr
  nlinarith

theorem uniformModel_h_nonneg (a : ℝ) (ha : (1/2:ℝ) < a) :
    ∀ v, 0 ≤ uniformStarH a v := by
  intro v
  fin_cases v <;> simp [uniformStarH]
  all_goals
    change 0 ≤ (2*a-1)/(3*a)
    exact div_nonneg (by nlinarith) (by positivity)

end WeightedEdgeColoring.Subtwo.EndpointPotential
