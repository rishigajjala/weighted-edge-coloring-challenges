import WeightedEdgeColoring.SubtwoBoundaryPotential

/-!
# Averaging the boundary potential

The four coordinates may be ordered separately in each local bin. In a
heavy bin the first is heavy and the second is largest among the other
three. The average below is the exact rational row in the certificate.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.SubtwoHarmonicRanks

theorem averaged_boundary_potential {B : Type*} [Fintype B]
    (mass : B → ℝ) (w : B → Fin 4 → ℝ) (boundary : B → ℝ)
    (heavy : B → Prop) [DecidablePred heavy] (T Q : ℝ)
    (hmass : ∀ b, 0 ≤ mass b) (htotal : (∑ b, mass b) ≤ 1)
    (hw : ∀ b i, 0 ≤ w b i) (hboundary : ∀ b, 0 ≤ boundary b)
    (hnormal : ∀ b, ¬heavy b → ∀ i, w b i ≤ 1 / 2)
    (hheavy : ∀ b, heavy b → 1 / 2 < w b 0)
    (hsecond : ∀ b, heavy b → w b 2 ≤ w b 1 ∧ w b 3 ≤ w b 1)
    (hcapacity : ∀ b, (∑ i, w b i) +
      (if heavy b then (2 / 3 : ℝ) * boundary b else boundary b / 2) ≤ 1)
    (hT : T ≤ ∑ b, mass b * (∑ i, harmonicCharge (w b i)))
    (hQ : Q ≤ ∑ b, mass b * boundary b) :
    (∑ b, if heavy b then mass b * (harmonicCharge (w b 2) + harmonicCharge (w b 3)) else 0) +
      (3 / 2 : ℝ) * T + (2 / 3 : ℝ) * Q ≤
      (111 / 52 : ℝ) + (893 / 1430 : ℝ) * ∑ b, if heavy b then mass b else 0 := by
  have hpoint (b : B) :
      (if heavy b then harmonicCharge (w b 2) + harmonicCharge (w b 3) else 0) +
        (3 / 2 : ℝ) * (∑ i, harmonicCharge (w b i)) + (2 / 3 : ℝ) * boundary b ≤
      (111 / 52 : ℝ) + (893 / 1430 : ℝ) * (if heavy b then 1 else 0) := by
    by_cases hb : heavy b
    · have hc := hcapacity b
      simp only [if_pos hb] at hc
      have hs := hsecond b hb
      have h := heavy_boundary_potential (w b 0) (w b 1) (w b 2) (w b 3) (boundary b)
        (hheavy b hb) (hw b 1) (hw b 2) (hw b 3) hs.1 hs.2 (hboundary b)
        (by simpa [Fin.sum_univ_succ, add_assoc] using hc)
      simp [hb, Fin.sum_univ_succ]
      linarith
    · have hc := hcapacity b
      simp only [if_neg hb] at hc
      have h := normal_boundary_potential (w b) (boundary b) (hw b) (hnormal b hb)
        (hboundary b) hc
      simpa [hb] using h
  have havg := Finset.sum_le_sum (s := (Finset.univ : Finset B))
    (fun b _ => mul_le_mul_of_nonneg_left (hpoint b) (hmass b))
  have hleft :
      (∑ b, mass b * ((if heavy b then harmonicCharge (w b 2) + harmonicCharge (w b 3) else 0) +
        (3 / 2 : ℝ) * (∑ i, harmonicCharge (w b i)) + (2 / 3 : ℝ) * boundary b)) =
      (∑ b, if heavy b then mass b * (harmonicCharge (w b 2) + harmonicCharge (w b 3)) else 0) +
        (3 / 2 : ℝ) * (∑ b, mass b * (∑ i, harmonicCharge (w b i))) +
        (2 / 3 : ℝ) * (∑ b, mass b * boundary b) := by
    simp [Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_ite, mul_left_comm]
  have hright :
      (∑ b, mass b * ((111 / 52 : ℝ) + (893 / 1430 : ℝ) * (if heavy b then 1 else 0))) =
      (111 / 52 : ℝ) * (∑ b, mass b) + (893 / 1430 : ℝ) * (∑ b, if heavy b then mass b else 0) := by
    simp [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, mul_add, mul_ite, mul_comm]
  rw [hleft, hright] at havg
  linarith

/-- The priced form is exactly the frozen potential row, with the chosen
upper packet price `sm` multiplying all resource terms. -/
theorem priced_averaged_boundary_potential {B : Type*} [Fintype B]
    (mass : B → ℝ) (w : B → Fin 4 → ℝ) (boundary : B → ℝ)
    (heavy : B → Prop) [DecidablePred heavy] (T Q sm smallPrice : ℝ)
    (hmass : ∀ b, 0 ≤ mass b) (htotal : (∑ b, mass b) ≤ 1)
    (hw : ∀ b i, 0 ≤ w b i) (hboundary : ∀ b, 0 ≤ boundary b)
    (hnormal : ∀ b, ¬heavy b → ∀ i, w b i ≤ 1 / 2)
    (hheavy : ∀ b, heavy b → 1 / 2 < w b 0)
    (hsecond : ∀ b, heavy b → w b 2 ≤ w b 1 ∧ w b 3 ≤ w b 1)
    (hcapacity : ∀ b, (∑ i, w b i) +
      (if heavy b then (2 / 3 : ℝ) * boundary b else boundary b / 2) ≤ 1)
    (hT : T ≤ ∑ b, mass b * (∑ i, harmonicCharge (w b i)))
    (hQ : Q ≤ ∑ b, mass b * boundary b) (hsm : 0 ≤ sm)
    (hprice : smallPrice ≤ sm *
      ∑ b, if heavy b then mass b * (harmonicCharge (w b 2) + harmonicCharge (w b 3)) else 0) :
    smallPrice + (3 / 2 : ℝ) * sm * T + (2 / 3 : ℝ) * sm * Q -
      (893 / 1430 : ℝ) * sm * (∑ b, if heavy b then mass b else 0) ≤ (111 / 52 : ℝ) * sm := by
  have h := averaged_boundary_potential mass w boundary heavy T Q
    hmass htotal hw hboundary hnormal hheavy hsecond hcapacity hT hQ
  have hs := mul_le_mul_of_nonneg_left h hsm
  nlinarith

end WeightedEdgeColoring.SubtwoHarmonicRanks
