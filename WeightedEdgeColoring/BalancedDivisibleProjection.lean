import WeightedEdgeColoring.DyadicLocalExtraCounts

/-!
# Balanced projection between divisible finite cyclic sets

If `B` divides `T`, a set of `T` coupled choices can be projected uniformly
onto `B` endpoint slots.  We use an arbitrary fixed equivalence
`Fin T ≃ Fin B × Fin (T/B)`; no arithmetic formula for the projection is
needed later.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

def balancedDivisibleEquiv {B T : ℕ} (hdiv : B ∣ T) :
    Fin T ≃ Fin B × Fin (T / B) := by
  apply Fintype.equivOfCardEq
  simp only [Fintype.card_fin, Fintype.card_prod]
  exact (Nat.mul_div_cancel' hdiv).symm

def balancedDivisibleProjection {B T : ℕ} (hdiv : B ∣ T) :
    Fin T → Fin B :=
  fun z ↦ (balancedDivisibleEquiv hdiv z).1

/-- Every endpoint index has exactly the same number of preimages. -/
theorem sum_balancedDivisibleProjection {B T : ℕ} (hdiv : B ∣ T)
    (f : Fin B → ℝ) :
    (∑ z : Fin T, f (balancedDivisibleProjection hdiv z)) =
      (T / B : ℕ) * ∑ i : Fin B, f i := by
  have hreindex := (balancedDivisibleEquiv hdiv).sum_comp
    (fun p : Fin B × Fin (T / B) ↦ f p.1)
  unfold balancedDivisibleProjection
  rw [hreindex, Fintype.sum_prod_type, Finset.sum_comm]
  simp [mul_comm]

/-- Uniform mass `r/T` on the coupled set has endpoint marginal `r/B`. -/
theorem sum_balancedDivisibleProjection_indicator
    {B T : ℕ} (hB : 0 < B) (hT : 0 < T) (hdiv : B ∣ T)
    (r : ℝ) (i : Fin B) :
    (∑ z : Fin T,
      if balancedDivisibleProjection hdiv z = i then r / T else 0) =
      r / B := by
  rw [show (∑ z : Fin T,
      if balancedDivisibleProjection hdiv z = i then r / T else 0) =
      ∑ z : Fin T, (if balancedDivisibleProjection hdiv z = i then
        (1 : ℝ) else 0) * (r / T) by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : balancedDivisibleProjection hdiv z = i <;> simp [hz]]
  rw [← Finset.sum_mul]
  rw [sum_balancedDivisibleProjection hdiv
    (fun j ↦ if j = i then (1 : ℝ) else 0)]
  rw [Fintype.sum_ite_eq']
  have hfactor : B * (T / B) = T := Nat.mul_div_cancel' hdiv
  have hfactorR : (B : ℝ) * ((T / B : ℕ) : ℝ) = (T : ℝ) := by
    exact_mod_cast hfactor
  field_simp [Nat.ne_of_gt hB, Nat.ne_of_gt hT]
  calc
    ((T / B : ℕ) : ℝ) * r * (B : ℝ) =
        r * ((B : ℝ) * ((T / B : ℕ) : ℝ)) := by ring
    _ = r * (T : ℝ) := by rw [hfactorR]

/-- When the target size equals the source size, the balanced projection is
injective.  The second coordinate of the defining product is then `Fin 1`. -/
theorem balancedDivisibleProjection_injective_of_eq
    {B T : ℕ} (hB : 0 < B) (hBT : B = T) (hdiv : B ∣ T) :
    Function.Injective (balancedDivisibleProjection hdiv) := by
  intro x y hxy
  apply (balancedDivisibleEquiv hdiv).injective
  apply Prod.ext hxy
  apply Fin.ext
  have hq : T / B = 1 := by
    subst T
    exact Nat.div_self hB
  have hx := ((balancedDivisibleEquiv hdiv x).2).isLt
  have hy := ((balancedDivisibleEquiv hdiv y).2).isLt
  omega

/-- Dyadic padding supplies both divisibilities needed by the common support
`max B₁ B₂`. -/
theorem dyadicCeil_both_dvd_max (a b : ℕ) :
    dyadicCeil a ∣ max (dyadicCeil a) (dyadicCeil b) ∧
      dyadicCeil b ∣ max (dyadicCeil a) (dyadicCeil b) := by
  exact ⟨dyadicCeil_dvd_max a b,
    by simpa [max_comm] using dyadicCeil_dvd_max b a⟩

end

end WeightedEdgeColoring
