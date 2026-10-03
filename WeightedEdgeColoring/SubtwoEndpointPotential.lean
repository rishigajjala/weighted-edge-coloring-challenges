import Mathlib.Tactic

/-!
# Endpoint bounds for the analytic five-vertex argument

This module records the linear endpoint inequalities, proves that their
feasibility is preserved by convex averaging, and proves the scalar
shared-heavy-item estimate. These are supporting theorems; the graph-wide
`SubtwoBPAsymptotic` theorem is not asserted here.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo.EndpointPotential

abbrev Vertex := Fin 5
abbrev Bundle := Fin 10

def left : Bundle → Vertex := ![0, 0, 0, 0, 1, 1, 1, 2, 2, 3]
def right : Bundle → Vertex := ![1, 2, 3, 4, 2, 3, 4, 3, 4, 4]
def Inc (v : Vertex) (e : Bundle) : Prop := v = left e ∨ v = right e

instance (v : Vertex) (e : Bundle) : Decidable (Inc v e) := by
  unfold Inc
  infer_instance

theorem left_ne_right (e : Bundle) : left e ≠ right e := by
  fin_cases e <;> decide

noncomputable def lightCharge : ℝ := 205 / 144
noncomputable def residualCharge : ℝ := 25 / 36

/-- All rows are linear in the fields and `m`, with `rho,h` fixed. -/
structure Certificate (m rho : Bundle → ℝ) (h : Vertex → ℝ) where
  z : Vertex → Bundle → ℝ
  c : Vertex → ℝ
  alpha : Vertex → Bundle → ℝ
  P : Vertex → ℝ
  z_nonneg : ∀ v e, 0 ≤ z v e
  c_nonneg : ∀ v, 0 ≤ c v
  alpha_nonneg : ∀ v e, 0 ≤ alpha v e
  P_nonneg : ∀ v, 0 ≤ P v
  split : ∀ e, z (left e) e + z (right e) e = 2 * m e
  light : ∀ v e, Inc v e → z v e ≤ c v + h v * m e
  baseline : ∀ v, lightCharge * c v + h v ≤ P v
  off : ∀ v e f, Inc v e → Inc v f → f ≠ e →
    z v f - rho e * m f ≤ alpha v e
  same : ∀ v e, Inc v e → z v e - (2 - rho e) * m e ≤ alpha v e
  pair : ∀ e, rho e * m e ≤ alpha (left e) e + alpha (right e) e
  edge : ∀ e, (2 - rho e) * m e + rho e +
    residualCharge * (alpha (left e) e + alpha (right e) e) ≤
      P (left e) + P (right e)

/-- The positive-part form removes the auxiliary packet multipliers. -/
theorem positiveParts_le (zu zv au av m rho : ℝ)
    (hz : zu + zv = 2 * m)
    (hu : zu - (2 - rho) * m ≤ au)
    (hv : zv - (2 - rho) * m ≤ av)
    (hp : rho * m ≤ au + av) (hm : 0 ≤ (2 - rho) * m) :
    max (zu - au) 0 + max (zv - av) 0 ≤ (2 - rho) * m := by
  rcases le_total (zu - au) 0 with hu0 | hu0
  · rw [max_eq_right hu0]
    rcases le_total (zv - av) 0 with hv0 | hv0
    · rw [max_eq_right hv0]; simpa using hm
    · rw [max_eq_left hv0]; linarith
  · rw [max_eq_left hu0]
    rcases le_total (zv - av) 0 with hv0 | hv0
    · rw [max_eq_right hv0]; linarith
    · rw [max_eq_left hv0]; nlinarith

/-- The shared-heavy-item estimate after off-bundle coefficient coverage.
`ru,rv` are the normalized prices of the two light remainders. -/
theorem pairedHeavy_bound (Q p Ou Ov Eu Ev ru rv zu zv au av m rho R : ℝ)
    (hm : 0 < m) (hrho : 0 ≤ rho) (hrho2 : rho ≤ 2)
    (hau : 0 ≤ au) (hav : 0 ≤ av)
    (hEu : 0 ≤ Eu) (hEv : 0 ≤ Ev)
    (hpacket_u : Eu ≤ m - p) (hpacket_v : Ev ≤ m - p)
    (hmerge : p + Ou + Ov ≤ 1) (hru : ru ≤ R) (hrv : rv ≤ R)
    (hz : zu + zv = 2 * m)
    (hsame_u : zu - (2 - rho) * m ≤ au)
    (hsame_v : zv - (2 - rho) * m ≤ av)
    (hpair : rho * m ≤ au + av)
    (hcoverage : Q ≤ 2 * p + rho * (Ou + Ov) + au * ru + av * rv +
      max (zu - au) 0 / m * Eu + max (zv - av) 0 / m * Ev) :
    Q ≤ (2 - rho) * m + rho + R * (au + av) := by
  have hmp : 0 ≤ m - p := hEu.trans hpacket_u
  have hparts := positiveParts_le zu zv au av m rho hz hsame_u hsame_v hpair
    (mul_nonneg (sub_nonneg.mpr hrho2) hm.le)
  have he_u := mul_le_mul_of_nonneg_left hpacket_u
    (div_nonneg (le_max_right (zu - au) 0) hm.le)
  have he_v := mul_le_mul_of_nonneg_left hpacket_v
    (div_nonneg (le_max_right (zv - av) 0) hm.le)
  have hsumdiv : max (zu - au) 0 / m + max (zv - av) 0 / m ≤ 2 - rho := by
    rw [← add_div, div_le_iff₀ hm]
    nlinarith [hparts]
  have hsame := mul_le_mul_of_nonneg_right hsumdiv hmp
  have hres_u := mul_le_mul_of_nonneg_left hru hau
  have hres_v := mul_le_mul_of_nonneg_left hrv hav
  have hmerge' := mul_le_mul_of_nonneg_left hmerge hrho
  nlinarith

/-- Zero-cap bundles have no heavy or same-bundle profit. -/
theorem pairedHeavy_zero_cap (Q Ou Ov ru rv au av rho R : ℝ)
    (hrho : 0 ≤ rho) (hau : 0 ≤ au) (hav : 0 ≤ av)
    (hmerge : Ou + Ov ≤ 1) (hru : ru ≤ R) (hrv : rv ≤ R)
    (hcoverage : Q ≤ rho * (Ou + Ov) + au * ru + av * rv) :
    Q ≤ rho + R * (au + av) := by
  have h₁ := mul_le_mul_of_nonneg_left hmerge hrho
  have h₂ := mul_le_mul_of_nonneg_left hru hau
  have h₃ := mul_le_mul_of_nonneg_left hrv hav
  nlinarith

/-- A no-heavy star uses its harmonic bound and the whole-star price bound. -/
theorem noHeavy_bound (Q normalized ordinary c h A : ℝ)
    (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hcoverage : Q ≤ c * normalized + h * ordinary)
    (hnormalized : normalized ≤ A) (hordinary : ordinary ≤ 1) :
    Q ≤ A * c + h := by
  have h₁ := mul_le_mul_of_nonneg_left hnormalized hc
  have h₂ := mul_le_mul_of_nonneg_left hordinary hh
  nlinarith

/-- Averaging endpoint bounds averages their cap vectors as well. -/
noncomputable def Certificate.mix {m₀ m₁ rho : Bundle → ℝ} {h : Vertex → ℝ}
    (C₀ : Certificate m₀ rho h) (C₁ : Certificate m₁ rho h)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Certificate (fun e ↦ t * m₀ e + (1 - t) * m₁ e) rho h where
  z := fun v e ↦ t * C₀.z v e + (1 - t) * C₁.z v e
  c := fun v ↦ t * C₀.c v + (1 - t) * C₁.c v
  alpha := fun v e ↦ t * C₀.alpha v e + (1 - t) * C₁.alpha v e
  P := fun v ↦ t * C₀.P v + (1 - t) * C₁.P v
  z_nonneg := by
    intro v e
    exact add_nonneg (mul_nonneg ht (C₀.z_nonneg v e))
      (mul_nonneg (sub_nonneg.mpr ht1) (C₁.z_nonneg v e))
  c_nonneg := by
    intro v
    exact add_nonneg (mul_nonneg ht (C₀.c_nonneg v))
      (mul_nonneg (sub_nonneg.mpr ht1) (C₁.c_nonneg v))
  alpha_nonneg := by
    intro v e
    exact add_nonneg (mul_nonneg ht (C₀.alpha_nonneg v e))
      (mul_nonneg (sub_nonneg.mpr ht1) (C₁.alpha_nonneg v e))
  P_nonneg := by
    intro v
    exact add_nonneg (mul_nonneg ht (C₀.P_nonneg v))
      (mul_nonneg (sub_nonneg.mpr ht1) (C₁.P_nonneg v))
  split := by
    intro e
    nlinarith [C₀.split e, C₁.split e]
  light := by
    intro v e he
    have h₀ := mul_le_mul_of_nonneg_left (C₀.light v e he) ht
    have h₁ := mul_le_mul_of_nonneg_left (C₁.light v e he) (sub_nonneg.mpr ht1)
    nlinarith
  baseline := by
    intro v
    have h₀ := mul_le_mul_of_nonneg_left (C₀.baseline v) ht
    have h₁ := mul_le_mul_of_nonneg_left (C₁.baseline v) (sub_nonneg.mpr ht1)
    nlinarith
  off := by
    intro v e f he hf hfe
    have h₀ := mul_le_mul_of_nonneg_left (C₀.off v e f he hf hfe) ht
    have h₁ := mul_le_mul_of_nonneg_left (C₁.off v e f he hf hfe) (sub_nonneg.mpr ht1)
    nlinarith
  same := by
    intro v e he
    have h₀ := mul_le_mul_of_nonneg_left (C₀.same v e he) ht
    have h₁ := mul_le_mul_of_nonneg_left (C₁.same v e he) (sub_nonneg.mpr ht1)
    nlinarith
  pair := by
    intro e
    have h₀ := mul_le_mul_of_nonneg_left (C₀.pair e) ht
    have h₁ := mul_le_mul_of_nonneg_left (C₁.pair e) (sub_nonneg.mpr ht1)
    nlinarith
  edge := by
    intro e
    have h₀ := mul_le_mul_of_nonneg_left (C₀.edge e) ht
    have h₁ := mul_le_mul_of_nonneg_left (C₁.edge e) (sub_nonneg.mpr ht1)
    nlinarith

theorem Certificate.mix_budget {m₀ m₁ rho : Bundle → ℝ} {h : Vertex → ℝ}
    (C₀ : Certificate m₀ rho h) (C₁ : Certificate m₁ rho h)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (B : ℝ)
    (h₀ : ∑ v, C₀.P v ≤ B) (h₁ : ∑ v, C₁.P v ≤ B) :
    ∑ v, (C₀.mix C₁ t ht ht1).P v ≤ B := by
  change ∑ v, (t * C₀.P v + (1 - t) * C₁.P v) ≤ B
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h₀' := mul_le_mul_of_nonneg_left h₀ ht
  have h₁' := mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr ht1)
  nlinarith

end WeightedEdgeColoring.Subtwo.EndpointPotential
