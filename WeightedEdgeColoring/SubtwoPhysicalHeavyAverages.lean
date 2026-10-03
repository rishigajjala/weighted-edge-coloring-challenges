import WeightedEdgeColoring.SubtwoPhysicalHeavyPrices

/-!
# Actual big and small price averages

The profile variables are averages of the two physical price contributions
in each selected heavy class. Their elementary certificate inequalities
are obtained by averaging the genuine one-bin inequalities.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable (G : WeightedMultigraph.{u})

def subtwoHeavyClassAverage (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (i k : Fin 4) (f : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, if G.SubtwoHeavyClassBin v neighbor bin i k j then (1 / (n : ℝ)) * f j else 0

theorem subtwoHeavyClassAverage_const (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (i k : Fin 4) (c : ℝ) :
    G.subtwoHeavyClassAverage v neighbor bin i k (fun _ => c) =
      G.subtwoHeavyClassMass v neighbor bin i k * c := by
  unfold subtwoHeavyClassAverage subtwoHeavyClassMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp

theorem subtwoHeavyClassAverage_add (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (i k : Fin 4) (f g : Fin n → ℝ) :
    G.subtwoHeavyClassAverage v neighbor bin i k (fun j => f j + g j) =
      G.subtwoHeavyClassAverage v neighbor bin i k f + G.subtwoHeavyClassAverage v neighbor bin i k g := by
  unfold subtwoHeavyClassAverage
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

theorem subtwoHeavyClassAverage_mul (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (i k : Fin 4) (f : Fin n → ℝ) (c : ℝ) :
    G.subtwoHeavyClassAverage v neighbor bin i k (fun j => c * f j) =
      c * G.subtwoHeavyClassAverage v neighbor bin i k f := by
  unfold subtwoHeavyClassAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

theorem subtwoHeavyClassAverage_le (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (i k : Fin 4) (f g : Fin n → ℝ)
    (hfg : ∀ j, G.SubtwoHeavyClassBin v neighbor bin i k j → f j ≤ g j) :
    G.subtwoHeavyClassAverage v neighbor bin i k f ≤ G.subtwoHeavyClassAverage v neighbor bin i k g := by
  apply Finset.sum_le_sum
  intro j hj
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left (hfg j h) (by positivity)
  · rfl

theorem subtwoHeavyClassAverage_le_const (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (i k : Fin 4) (f : Fin n → ℝ) (c : ℝ)
    (hf : ∀ j, G.SubtwoHeavyClassBin v neighbor bin i k j → f j ≤ c) :
    G.subtwoHeavyClassAverage v neighbor bin i k f ≤
      G.subtwoHeavyClassMass v neighbor bin i k * c := by
  rw [← G.subtwoHeavyClassAverage_const v neighbor bin i k c]
  exact G.subtwoHeavyClassAverage_le v neighbor bin i k f (fun _ => c) hf

def subtwoHeavyBigPrice (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (price : G.E → ℝ) (i k : Fin 4) : ℝ :=
  G.subtwoHeavyClassAverage v neighbor bin i k fun j =>
    G.subtwoOrderedFourPrices v neighbor bin price j 0 + G.subtwoOrderedFourPrices v neighbor bin price j 1

def subtwoHeavySmallPrice (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (price : G.E → ℝ) (i k : Fin 4) : ℝ :=
  G.subtwoHeavyClassAverage v neighbor bin i k fun j =>
    G.subtwoOrderedFourPrices v neighbor bin price j 2 + G.subtwoOrderedFourPrices v neighbor bin price j 3

theorem subtwoHeavyBigSmallPrice_nonneg
    (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (price : G.E → ℝ)
    (hp : ∀ e, 0 ≤ price e) (hR : 0 < G.subtwoColorPriceMax price) (i k : Fin 4) :
    0 ≤ G.subtwoHeavyBigPrice v neighbor bin price i k ∧
      0 ≤ G.subtwoHeavySmallPrice v neighbor bin price i k := by
  have ho (j : Fin n) (a : Fin 4) : 0 ≤ G.subtwoOrderedFourPrices v neighbor bin price j a :=
    G.subtwoPhysicalFourPrices_nonneg v neighbor bin price hp hR j _
  unfold subtwoHeavyBigPrice subtwoHeavySmallPrice subtwoHeavyClassAverage
  constructor <;> apply Finset.sum_nonneg <;> intro j hj <;> split_ifs
  · exact mul_nonneg (by positivity) (add_nonneg (ho j 0) (ho j 1))
  · rfl
  · exact mul_nonneg (by positivity) (add_nonneg (ho j 2) (ho j 3))
  · rfl

theorem subtwoHeavyBigSmallPrice_add_le_mass
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) (hR : 0 < G.subtwoColorPriceMax price)
    (i k : Fin 4) :
    G.subtwoHeavyBigPrice v neighbor bin price i k +
      G.subtwoHeavySmallPrice v neighbor bin price i k ≤ G.subtwoHeavyClassMass v neighbor bin i k := by
  unfold subtwoHeavyBigPrice subtwoHeavySmallPrice
  rw [← G.subtwoHeavyClassAverage_add]
  have h := G.subtwoHeavyClassAverage_le_const v neighbor bin i k _ 1 (by
    intro j hj
    have h := (G.subtwo_ordered_heavy_price_caps v neighbor hinj hne bin hbin price hp hR j hj.1).2.2.2
    simpa only [add_assoc] using h)
  simpa only [mul_one, add_assoc] using h

theorem subtwoHeavyBigPrice_le_pair_caps
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) (hR : 0 < G.subtwoColorPriceMax price)
    (i k : Fin 4) :
    G.subtwoHeavyBigPrice v neighbor bin price i k ≤ G.subtwoHeavyClassMass v neighbor bin i k *
      (G.subtwoNormalizedSetPrice price {v, neighbor i} +
        (1 / 2 : ℝ) * G.subtwoNormalizedSetPrice price {v, neighbor k}) := by
  apply G.subtwoHeavyClassAverage_le_const
  intro j hj
  have h := (G.subtwo_ordered_heavy_price_caps v neighbor hinj hne bin hbin price hp hR j hj.1).1
  simpa only [hj.2.1, hj.2.2] using h

theorem subtwoHeavySmallPrice_three_copies_complement
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price) (i k : Fin 4) :
    3 * G.subtwoHeavySmallPrice v neighbor bin price i k +
      G.subtwoHeavyClassMass v neighbor bin i k * G.subtwoNormalizedSetPrice price {neighbor i, neighbor k} ≤
      G.subtwoHeavyClassMass v neighbor bin i k := by
  have h := G.subtwoHeavyClassAverage_le_const v neighbor bin i k
    (fun j => 3 * (G.subtwoOrderedFourPrices v neighbor bin price j 2 +
      G.subtwoOrderedFourPrices v neighbor bin price j 3) +
      G.subtwoNormalizedSetPrice price {neighbor i, neighbor k}) 1 (by
    intro j hj
    have h := (G.subtwo_ordered_heavy_complement_prices v neighbor hinj hne bin hbin price hR j hj.1).2
    simpa only [hj.2.1, hj.2.2] using h)
  simpa only [G.subtwoHeavyClassAverage_add, G.subtwoHeavyClassAverage_mul,
    G.subtwoHeavyClassAverage_const, mul_one, subtwoHeavySmallPrice] using h

end
end WeightedEdgeColoring.WeightedMultigraph
