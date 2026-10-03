import WeightedEdgeColoring.SubtwoPhysicalSharedPairRows

/-!
# The directed small-price and bundle-cost row

Reindex four fixed neighbor projections so the selected heavy class is
first and second. This uses the same original bins even outside that class.
The minimum cost of the second bundle is compared with its full bin average.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.SubtwoHarmonicRanks

theorem exists_four_index_pair_perm (i k : Fin 4) (hik : i ≠ k) :
    ∃ π : Equiv.Perm (Fin 4), π 0 = i ∧ π 1 = k := by
  classical
  let first : Equiv.Perm (Fin 4) := Equiv.swap 0 i
  let a := first.symm k
  have ha : a ≠ 0 := by
    intro he
    have hk : k = i := by
      calc
        k = first a := (first.apply_symm_apply k).symm
        _ = first 0 := congrArg first he
        _ = i := by simp [first]
    exact hik hk.symm
  let second : Equiv.Perm (Fin 4) := Equiv.swap 1 a
  refine ⟨second.trans first, ?_, ?_⟩
  · have hfix : second 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm ha)
    simp [Equiv.trans_apply, hfix, first]
  · simp [Equiv.trans_apply, second, a]

end WeightedEdgeColoring.SubtwoHarmonicRanks

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable (G : WeightedMultigraph.{u})

theorem subtwoHeavySmallPrice_le_fixed_reindexed_charge
    (v : G.V) (neighbor : Fin 4 → G.V) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (i k : Fin 4) (π : Equiv.Perm (Fin 4)) (h0 : π 0 = i) (h1 : π 1 = k)
    (sm : ℝ)
    (hsm : ∀ a ∈ subtwoOtherTwoIndices i k, G.subtwoNormalizedSetPrice price {v, neighbor a} ≤ sm) :
    G.subtwoHeavySmallPrice v neighbor bin price i k ≤
      sm * ∑ j : Fin n, if G.SubtwoHeavyClassBin v neighbor bin i k j then
        (1 / (n : ℝ)) *
          (harmonicCharge (G.subtwoPhysicalFourLoads v neighbor bin j (π 2)) +
            harmonicCharge (G.subtwoPhysicalFourLoads v neighbor bin j (π 3))) else 0 := by
  unfold subtwoHeavySmallPrice subtwoHeavyClassAverage
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  split_ifs with hc
  · let w := G.subtwoPhysicalFourLoads v neighbor bin j
    let order := SubtwoHarmonicRanks.fourLoadOrder w
    have hrem : ({order 2, order 3} : Finset (Fin 4)) = {π 2, π 3} := by
      rw [← G.subtwoOtherTwoIndices_eq_of_class v neighbor bin i k j hc]
      unfold subtwoOtherTwoIndices
      rw [← h0, ← h1]
      exact SubtwoHarmonicRanks.four_perm_remaining_pair π
    have ho23 : order 2 ≠ order 3 := fun he =>
      (by decide : (2 : Fin 4) ≠ 3) (order.injective he)
    have hπ23 : π 2 ≠ π 3 := fun he =>
      (by decide : (2 : Fin 4) ≠ 3) (π.injective he)
    have hcharge : harmonicCharge (w (order 2)) + harmonicCharge (w (order 3)) =
        harmonicCharge (w (π 2)) + harmonicCharge (w (π 3)) := by
      calc
        _ = ∑ a ∈ ({order 2, order 3} : Finset (Fin 4)), harmonicCharge (w a) :=
          (Finset.sum_pair ho23).symm
        _ = ∑ a ∈ ({π 2, π 3} : Finset (Fin 4)), harmonicCharge (w a) := by rw [hrem]
        _ = _ := Finset.sum_pair hπ23
    have hcap (a : Fin 4) (ha : a ∈ ({order 2, order 3} : Finset (Fin 4))) :
        G.subtwoPhysicalFourPrices v neighbor bin price j a ≤ sm * harmonicCharge (w a) := by
      have hm := hsm a (by
        rw [G.subtwoOtherTwoIndices_eq_of_class v neighbor bin i k j hc]
        exact ha)
      exact (G.subtwoPhysicalFourPrices_le_harmonic v neighbor hne bin hbin price hR j a).trans
        (mul_le_mul_of_nonneg_right hm (harmonicCharge_nonneg _))
    have h2 := hcap (order 2) (Finset.mem_insert_self _ _)
    have h3 := hcap (order 3) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hs : G.subtwoOrderedFourPrices v neighbor bin price j 2 +
        G.subtwoOrderedFourPrices v neighbor bin price j 3 ≤
        sm * (harmonicCharge (w (π 2)) + harmonicCharge (w (π 3))) := by
      rw [← hcharge]
      change G.subtwoPhysicalFourPrices v neighbor bin price j (order 2) +
        G.subtwoPhysicalFourPrices v neighbor bin price j (order 3) ≤ _
      nlinarith
    have havg := mul_le_mul_of_nonneg_left hs (show 0 ≤ (1 / (n : ℝ)) by positivity)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using havg
  · simp

theorem subtwo_physical_cross_price_cost_row
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (i k : Fin 4) (hik : i ≠ k) (sm : ℝ) (hsm0 : 0 ≤ sm)
    (hsm : ∀ a ∈ subtwoOtherTwoIndices i k, G.subtwoNormalizedSetPrice price {v, neighbor a} ≤ sm) :
    G.subtwoHeavySmallPrice v neighbor bin price i k +
      sm * G.subtwoPhysicalBundleCost n v (neighbor k) -
      (sm / 2) * (∑ a : Fin 4, G.subtwoHeavyClassMass v neighbor bin k a) -
      (4 * sm / 21) * G.subtwoHeavyClassMass v neighbor bin i k ≤ sm / 2 := by
  obtain ⟨π, h0, h1⟩ := SubtwoHarmonicRanks.exists_four_index_pair_perm i k hik
  let w := fun j : Fin n => fun a : Fin 4 => G.subtwoPhysicalFourLoads v neighbor bin j (π a)
  have h := SubtwoHarmonicRanks.priced_profile_cross_cost_of_loads
    (fun _ : Fin n => (1 / (n : ℝ))) w
    (G.SubtwoHeavyClassBin v neighbor bin i k)
    (G.subtwoPhysicalBundleCost n v (neighbor k)) sm
    (G.subtwoHeavySmallPrice v neighbor bin price i k)
    (fun _ => by positivity) (le_of_eq (subtwo_uniform_bin_mass_sum hn))
    (fun j a => G.subtwoPhysicalFourLoads_nonneg v neighbor bin j (π a)) (by
      intro j
      dsimp only [w]
      rw [Equiv.sum_comp]
      exact G.subtwoPhysicalFourLoads_sum_le_one v neighbor hinj hne bin hbin j) (by
      intro j hj
      have hh := SubtwoHarmonicRanks.fourLoadOrder_heavy
        (G.subtwoPhysicalFourLoads v neighbor bin j) hj.1
      rw [hj.2.1] at hh
      simpa only [w, h0] using hh) (by
      simpa only [w, h1, subtwoPhysicalBundleCost] using
        G.subtwo_floorBundle_normalized_cost_le_local_charge v (neighbor k) (hne k) hn bin hbin)
    hsm0 (G.subtwoHeavySmallPrice_le_fixed_reindexed_charge v neighbor hne bin hbin
      price hR i k π h0 h1 sm hsm)
  rw [G.subtwoHeavyClassMass_first_eq v neighbor hinj hne bin hbin k]
  change _ - (4 * sm / 21) * (∑ j : Fin n,
    if G.SubtwoHeavyClassBin v neighbor bin i k j then (1 / (n : ℝ)) else 0) ≤ sm / 2
  dsimp only [w] at h
  rw [h1] at h
  linarith

end
end WeightedEdgeColoring.WeightedMultigraph
