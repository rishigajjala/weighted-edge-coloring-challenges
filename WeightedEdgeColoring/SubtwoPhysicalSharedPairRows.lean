import WeightedEdgeColoring.SubtwoPhysicalSmallPriceRows
import WeightedEdgeColoring.SubtwoPhysicalStarPriceRows

/-!
# Shared-pair price rows from actual star bins

The projections outside the heavy coordinate can be repeated twice.
If they also exclude the second-largest coordinate, they can be repeated
three times. The unused vertices provide a complementary feasible color.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable (G : WeightedMultigraph.{u})

theorem subtwoPhysicalFourLoads_two_copies_outside_heavy
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (j : Fin n) (I : Finset (Fin 4))
    (hh : ∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a)
    (hout : SubtwoHarmonicRanks.fourLoadOrder
      (G.subtwoPhysicalFourLoads v neighbor bin j) 0 ∉ I) :
    2 * (∑ a ∈ I, G.subtwoPhysicalFourLoads v neighbor bin j a) ≤ 1 := by
  let w := G.subtwoPhysicalFourLoads v neighbor bin j
  let a := SubtwoHarmonicRanks.fourLoadOrder w 0
  have ha : 1 / 2 < w a := SubtwoHarmonicRanks.fourLoadOrder_heavy w hh
  have hs : (∑ i ∈ I, w i) + w a ≤ 1 := by
    calc
      _ = ∑ i ∈ insert a I, w i := by rw [Finset.sum_insert hout]; ring
      _ ≤ ∑ i : Fin 4, w i := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun i _ _ => G.subtwoPhysicalFourLoads_nonneg v neighbor bin j i)
      _ ≤ 1 := G.subtwoPhysicalFourLoads_sum_le_one v neighbor hinj hne bin hbin j
  change 2 * (∑ i ∈ I, w i) ≤ 1
  linarith

theorem subtwoPhysicalFourLoads_three_copies_outside_heavy_second
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (j : Fin n) (I : Finset (Fin 4))
    (hh : ∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a)
    (hfirst : SubtwoHarmonicRanks.fourLoadOrder
      (G.subtwoPhysicalFourLoads v neighbor bin j) 0 ∉ I)
    (hsecond : SubtwoHarmonicRanks.fourLoadOrder
      (G.subtwoPhysicalFourLoads v neighbor bin j) 1 ∉ I) :
    3 * (∑ a ∈ I, G.subtwoPhysicalFourLoads v neighbor bin j a) ≤ 1 := by
  let w := G.subtwoPhysicalFourLoads v neighbor bin j
  let π := SubtwoHarmonicRanks.fourLoadOrder w
  have hsub : I ⊆ {π 2, π 3} := by
    rw [← SubtwoHarmonicRanks.four_perm_remaining_pair π]
    intro i hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun he => hsecond (he ▸ hi), fun he => hfirst (he ▸ hi)⟩
  have hn : π 2 ≠ π 3 := fun he => (by decide : (2 : Fin 4) ≠ 3) (π.injective he)
  have hsmall : (∑ i ∈ I, w i) ≤ w (π 2) + w (π 3) := by
    calc
      _ ≤ ∑ i ∈ ({π 2, π 3} : Finset (Fin 4)), w i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i _ _ => G.subtwoPhysicalFourLoads_nonneg v neighbor bin j i)
      _ = _ := Finset.sum_pair hn
  have hload : w (π 0) + w (π 1) + w (π 2) + w (π 3) ≤ 1 := by
    have h := G.subtwoPhysicalFourLoads_sum_le_one v neighbor hinj hne bin hbin j
    rw [← Equiv.sum_comp π w] at h
    simpa [Fin.sum_univ_succ, add_assoc] using h
  have hfit := SubtwoBinProfileRows.three_smaller_pairs_fit
    (w (π 0)) (w (π 1)) (w (π 2)) (w (π 3))
    (SubtwoHarmonicRanks.fourLoadOrder_heavy w hh)
    (G.subtwoPhysicalFourLoads_nonneg v neighbor bin j (π 2))
    (G.subtwoPhysicalFourLoads_nonneg v neighbor bin j (π 3))
    (SubtwoHarmonicRanks.fourLoadOrder_second w).1
    (SubtwoHarmonicRanks.fourLoadOrder_second w).2 hload
  change 3 * (∑ i ∈ I, w i) ≤ 1
  linarith

theorem subtwoPhysicalFourPrices_subset_complement
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (j : Fin n) (I : Finset (Fin 4)) (k : ℕ)
    (hload : (k : ℝ) * (∑ a ∈ I, G.subtwoPhysicalFourLoads v neighbor bin j a) ≤ 1) :
    (k : ℝ) * (∑ a ∈ I, G.subtwoPhysicalFourPrices v neighbor bin price j a) +
      G.subtwoNormalizedSetPrice price ((Finset.univ \ I).image neighbor) ≤ 1 := by
  apply G.subtwoPhysicalFourPrices_copies_complement v neighbor hinj hne I
    ((Finset.univ \ I).image neighbor) _ bin hbin price hR j k hload
  apply G.subtwo_disjoint_indexed_neighbors v neighbor hinj hne I (Finset.univ \ I)
  apply Finset.disjoint_left.mpr
  intro a ha hb
  exact (Finset.mem_sdiff.mp hb).2 ha


/-- Filter the actual class masses by any predicate on their two indices. -/
theorem sum_subtwoHeavyClassMass_filter
    (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (P : Fin 4 → Fin 4 → Prop) [DecidableRel P] :
    (∑ i : Fin 4, ∑ k : Fin 4,
      if P i k then G.subtwoHeavyClassMass v neighbor bin i k else 0) =
    ∑ j : Fin n, if (∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a) ∧
      P (SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j) 0)
        (SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j) 1)
      then (1 / (n : ℝ)) else 0 := by
  have hterm (i k : Fin 4) :
      (if P i k then G.subtwoHeavyClassMass v neighbor bin i k else 0) =
      ∑ j : Fin n, if G.SubtwoHeavyClassBin v neighbor bin i k j then
        (if P i k then (1 / (n : ℝ)) else 0) else 0 := by
    by_cases hP : P i k <;> simp [hP, subtwoHeavyClassMass]
  simp_rw [hterm]
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin n, ∑ k : Fin 4,
        if G.SubtwoHeavyClassBin v neighbor bin i k j then
          (if P i k then (1 / (n : ℝ)) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ j : Fin n, ∑ i : Fin 4, ∑ k : Fin 4,
        if G.SubtwoHeavyClassBin v neighbor bin i k j then
          (if P i k then (1 / (n : ℝ)) else 0) else 0 := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hh : ∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a
      · simp only [SubtwoHeavyClassBin, hh, true_and]
        simp [ite_and]
      · simp only [SubtwoHeavyClassBin, hh, false_and, if_false, Finset.sum_const_zero]

/-- The selected physical demand prices are the same average used in
all one-bin complementary-copy inequalities. -/
theorem sum_subtwoPhysicalBundlePrice_subset_as_bin_average
    (v : G.V) (neighbor : Fin 4 → G.V) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (price : G.E → ℝ) (I : Finset (Fin 4)) :
    (∑ i ∈ I, G.subtwoPhysicalBundlePrice n price v (neighbor i)) =
      ∑ j : Fin n, (1 / (n : ℝ)) *
        ∑ i ∈ I, G.subtwoPhysicalFourPrices v neighbor bin price j i := by
  simp_rw [G.subtwoPhysicalBundlePrice_as_bin_average v _ (hne _) bin price]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  rfl

/-- Averaging actual one-, two-, and three-copy patterns gives the
shared-pair certificate row. All correction masses are actual heavy classes. -/
theorem subtwo_physical_shared_pair_price_row
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) (hR : 0 < G.subtwoColorPriceMax price)
    (I : Finset (Fin 4)) :
    (∑ i ∈ I, G.subtwoPhysicalBundlePrice n price v (neighbor i)) ≤
      (1 - G.subtwoNormalizedSetPrice price ((Finset.univ \ I).image neighbor)) *
      (1 - (∑ i : Fin 4, ∑ k : Fin 4,
        if i ∉ I then G.subtwoHeavyClassMass v neighbor bin i k else 0) / 2 -
      (∑ i : Fin 4, ∑ k : Fin 4,
        if i ∉ I ∧ k ∉ I then G.subtwoHeavyClassMass v neighbor bin i k else 0) / 6) := by
  let w := G.subtwoPhysicalFourLoads v neighbor bin
  let outside := fun j : Fin n => (∃ a, 1 / 2 < w j a) ∧
    SubtwoHarmonicRanks.fourLoadOrder (w j) 0 ∉ I
  let both := fun j : Fin n => outside j ∧
    SubtwoHarmonicRanks.fourLoadOrder (w j) 1 ∉ I
  rw [G.sum_subtwoPhysicalBundlePrice_subset_as_bin_average v neighbor hne bin price I,
    G.sum_subtwoHeavyClassMass_filter v neighbor bin (fun i _ => i ∉ I),
    G.sum_subtwoHeavyClassMass_filter v neighbor bin (fun i k => i ∉ I ∧ k ∉ I)]
  have h := SubtwoBinProfileRows.shared_pair_price_row
    (fun _ : Fin n => (1 / (n : ℝ)))
    (fun j => ∑ i ∈ I, G.subtwoPhysicalFourPrices v neighbor bin price j i)
    outside both (G.subtwoNormalizedSetPrice price ((Finset.univ \ I).image neighbor))
    (fun _ => by positivity) (le_of_eq (subtwo_uniform_bin_mass_sum hn))
    (G.subtwoNormalizedSetPrice_bounds price hp hR _).2
    (fun _ hb => hb.1) (by
      intro j
      have hc := G.subtwoPhysicalFourPrices_subset_complement v neighbor hinj hne bin hbin price hR j I 1 (by
        simp only [Nat.cast_one, one_mul]
        exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
          (fun i _ _ => G.subtwoPhysicalFourLoads_nonneg v neighbor bin j i)).trans
            (G.subtwoPhysicalFourLoads_sum_le_one v neighbor hinj hne bin hbin j))
      simpa only [Nat.cast_one, one_mul] using hc) (by
      intro j hj
      have hc := G.subtwoPhysicalFourPrices_subset_complement v neighbor hinj hne bin hbin price hR j I 2 (by
        simpa only [Nat.cast_ofNat] using
          G.subtwoPhysicalFourLoads_two_copies_outside_heavy v neighbor hinj hne
            bin hbin j I hj.1 hj.2)
      simpa only [Nat.cast_ofNat] using hc) (by
      intro j hj
      have hc := G.subtwoPhysicalFourPrices_subset_complement v neighbor hinj hne bin hbin price hR j I 3 (by
        simpa only [Nat.cast_ofNat] using
          G.subtwoPhysicalFourLoads_three_copies_outside_heavy_second v neighbor hinj hne
            bin hbin j I hj.1.1 hj.1.2 hj.2)
      simpa only [Nat.cast_ofNat] using hc)
  simpa only [outside, both, w, and_assoc] using h


/-- The same shared-pair row in the affine form used by the certificate:
each lifted coordinate is the true product of its pair price and class mass. -/
theorem subtwo_physical_shared_pair_certificate_row
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) (hR : 0 < G.subtwoColorPriceMax price)
    (I : Finset (Fin 4)) :
    let m := G.subtwoNormalizedSetPrice price ((Finset.univ \ I).image neighbor)
    let μ := G.subtwoHeavyClassMass v neighbor bin
    let fac := fun i k : Fin 4 => (if i ∉ I then (1 / 2 : ℝ) else 0) +
      (if i ∉ I ∧ k ∉ I then (1 / 6 : ℝ) else 0)
    (∑ i ∈ I, G.subtwoPhysicalBundlePrice n price v (neighbor i)) + m +
      (∑ i : Fin 4, ∑ k : Fin 4, (fac i k * μ i k - fac i k * (m * μ i k))) ≤ 1 := by
  dsimp only
  let m := G.subtwoNormalizedSetPrice price ((Finset.univ \ I).image neighbor)
  let μ := G.subtwoHeavyClassMass v neighbor bin
  let out := ∑ i : Fin 4, ∑ k : Fin 4, if i ∉ I then μ i k else 0
  let both := ∑ i : Fin 4, ∑ k : Fin 4, if i ∉ I ∧ k ∉ I then μ i k else 0
  change (∑ i ∈ I, G.subtwoPhysicalBundlePrice n price v (neighbor i)) + m +
    (∑ i : Fin 4, ∑ k : Fin 4,
      (((if i ∉ I then (1 / 2 : ℝ) else 0) +
        (if i ∉ I ∧ k ∉ I then (1 / 6 : ℝ) else 0)) * μ i k -
      ((if i ∉ I then (1 / 2 : ℝ) else 0) +
        (if i ∉ I ∧ k ∉ I then (1 / 6 : ℝ) else 0)) * (m * μ i k))) ≤ 1
  have hterm (i k : Fin 4) :
      ((if i ∉ I then (1 / 2 : ℝ) else 0) +
        (if i ∉ I ∧ k ∉ I then (1 / 6 : ℝ) else 0)) * μ i k -
      ((if i ∉ I then (1 / 2 : ℝ) else 0) +
        (if i ∉ I ∧ k ∉ I then (1 / 6 : ℝ) else 0)) * (m * μ i k) =
      (1 - m) * ((if i ∉ I then μ i k else 0) / 2 +
        (if i ∉ I ∧ k ∉ I then μ i k else 0) / 6) := by
    by_cases hi : i ∉ I <;> by_cases hk : k ∉ I <;> (try simp [hi, hk]) <;> ring
  have hsum : (∑ i : Fin 4, ∑ k : Fin 4,
      (((if i ∉ I then (1 / 2 : ℝ) else 0) +
        (if i ∉ I ∧ k ∉ I then (1 / 6 : ℝ) else 0)) * μ i k -
      ((if i ∉ I then (1 / 2 : ℝ) else 0) +
        (if i ∉ I ∧ k ∉ I then (1 / 6 : ℝ) else 0)) * (m * μ i k))) =
      ∑ i : Fin 4, ∑ k : Fin 4,
        (1 - m) * ((if i ∉ I then μ i k else 0) / 2 +
          (if i ∉ I ∧ k ∉ I then μ i k else 0) / 6) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm i k
  rw [hsum]
  have heq : (∑ i : Fin 4, ∑ k : Fin 4,
      (1 - m) * ((if i ∉ I then μ i k else 0) / 2 +
        (if i ∉ I ∧ k ∉ I then μ i k else 0) / 6)) =
      (1 - m) * (out / 2 + both / 6) := by
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_div, out, both]
  rw [heq]
  have h := G.subtwo_physical_shared_pair_price_row v neighbor hinj hne hn bin hbin price hp hR I
  change _ ≤ (1 - m) * (1 - out / 2 - both / 6) at h
  nlinarith

end
end WeightedEdgeColoring.WeightedMultigraph
