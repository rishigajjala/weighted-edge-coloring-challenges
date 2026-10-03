import WeightedEdgeColoring.SubtwoFractionalTriangle

/-!
# A direct price proof for restoring a triangle

Let t_i be the fractional cost of the bundle opposite vertex i, q_i its
boundary reservation, and r_i the maximum price available while avoiding
that vertex. Split the total internal price with s=T-M. The local half-star
bound pays the s part, and the bundle bounds pay the rest. This avoids
explicit division by t_i and includes zero-cost bundles.
-/

open scoped BigOperators
namespace WeightedEdgeColoring.Subtwo

/-- The triangle reserved-palette inequality, with zero bundle costs
allowed. Every input is a local price or incident-cost inequality. -/
theorem triangle_reserved_price_bound
    (t q r profit : Fin 3 → ℝ) (M : ℝ)
    (hM : (3/2 : ℝ) ≤ M)
    (ht1 : ∀ i, t i ≤ 1)
    (hr1 : ∀ i, r i ≤ 1)
    (hincident : ∀ i, (∑ j, t j) - t i + q i ≤ M)
    (hTlo : M ≤ ∑ i, t i) (hThi : (∑ i, t i) ≤ 2)
    (hlocal : (∑ i, profit i) ≤ (3/2 : ℝ))
    (hbundle : ∀ i, profit i ≤ t i * r i) :
    (∑ i, profit i) + (∑ i, q i * (1 - r i)) ≤ 1 + M/2 := by
  let T := ∑ i, t i
  let s := T - M
  have hs0 : 0 ≤ s := by dsimp [s, T]; linarith
  have hs1 : s ≤ 1 := by dsimp [s, T]; linarith
  have hcoef : ∀ i, 0 ≤ (1-s)*t i-q i := by
    intro i
    have hq := hincident i
    have ht := ht1 i
    have hpos := mul_nonneg hs0 (sub_nonneg.mpr ht)
    change T-t i+q i ≤ M at hq
    dsimp [s] at *
    nlinarith
  have hsumBundle : (∑ i, profit i) ≤ ∑ i, t i * r i :=
    Finset.sum_le_sum (fun i _ => hbundle i)
  have hsplit : (∑ i, profit i) ≤ s*(3/2)+(1-s)*(∑ i, t i*r i) := by
    have h1 := mul_le_mul_of_nonneg_left hlocal hs0
    have h2 := mul_le_mul_of_nonneg_left hsumBundle (sub_nonneg.mpr hs1)
    nlinarith
  have hpayment :
      (1-s)*(∑ i, t i*r i)+(∑ i, q i*(1-r i)) ≤ (1-s)*T := by
    calc
      _ = ∑ i, (((1-s)*t i-q i)*r i+q i) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i, (((1-s)*t i-q i)*1+q i) := by
        apply Finset.sum_le_sum
        intro i _
        have h := mul_le_mul_of_nonneg_left (hr1 i) (hcoef i)
        linarith
      _ = (1-s)*T := by simp [T, Finset.mul_sum]
  have hcost : s*(3/2)+(1-s)*T ≤ 1+M/2 := by
    have h := triangle_palette_cost_le hM hThi
    change T-(T-M)*(T-3/2) ≤ 1+M/2 at h
    dsimp [s]
    nlinarith
  linarith

/-- The manuscript's rational constants leave a fixed strict margin for
restoring every dense triangle. -/
theorem triangle_reserved_price_lt_kappa
    (t q r profit : Fin 3 → ℝ)
    (ht1 : ∀ i, t i ≤ 1) (hr1 : ∀ i, r i ≤ 1)
    (hincident : ∀ i, (∑ j, t j)-t i+q i ≤ (1691031/1000000 : ℝ))
    (hTlo : (1999/1000 : ℝ) ≤ ∑ i, t i)
    (hThi : (∑ i, t i) ≤ 2)
    (hlocal : (∑ i, profit i) ≤ (3/2 : ℝ))
    (hbundle : ∀ i, profit i ≤ t i*r i) :
    (∑ i, profit i)+(∑ i, q i*(1-r i)) < (1999/1000 : ℝ) := by
  have h := triangle_reserved_price_bound t q r profit
    (1691031/1000000 : ℝ) (by norm_num) ht1 hr1 hincident
    (by linarith) hThi hlocal hbundle
  linarith

end WeightedEdgeColoring.Subtwo
