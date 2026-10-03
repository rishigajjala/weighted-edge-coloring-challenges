import WeightedEdgeColoring.SubtwoPhysicalSharedPairRows

/-!
# Subset cost rows from the original star packing

The rank of a subset records whether it contains the largest and the
second-largest projection of a heavy bin. Every cost in the averaged row
is the true minimum cost of its bundle, and every class mass comes from
the same original bin assignment.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.SubtwoHarmonicRanks

noncomputable def heavySubsetRank (S : Finset (Fin 4)) (i k : Fin 4) : ℝ :=
  if S.card = 0 then 0 else
  if S.card = 1 then (if i ∈ S then 1 else if k ∈ S then 1 / 2 else 1 / 4) else
  if S.card = 2 then
    (if i ∈ S then (if k ∈ S then 3 / 2 else 5 / 4)
      else (if k ∈ S then 2 / 3 else 11 / 30)) else
  if S.card = 3 then
    (if i ∈ S then (if k ∈ S then 5 / 3 else 41 / 30) else 29 / 42) else 71 / 42

/-- The fifteen heavy-bin bounds, expressed as one subset inequality. -/
theorem heavy_subset_sum_rank (S : Finset (Fin 4)) (p : Fin 4 → ℝ)
    (h : HeavyRanks (p 0) (p 1) (p 2) (p 3)) :
    (∑ a ∈ S, p a) ≤ heavySubsetRank S 0 1 := by
  classical
  rcases h with ⟨ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd,
    habc, habd, hacd, hbcd, habcd⟩
  have hs : (∑ a ∈ S, p a) = ∑ a ∈ S, (![p 0, p 1, p 2, p 3] : Fin 4 → ℝ) a := by
    apply Finset.sum_congr rfl
    intro a ha
    fin_cases a <;> rfl
  rw [hs]
  fin_cases S <;> norm_num [heavySubsetRank] <;> linarith

theorem heavySubsetRank_image_symm (S : Finset (Fin 4)) (π : Equiv.Perm (Fin 4)) :
    heavySubsetRank (S.image π.symm) 0 1 = heavySubsetRank S (π 0) (π 1) := by
  classical
  have hc : (S.image π.symm).card = S.card := Finset.card_image_of_injective _ π.symm.injective
  have hm (a : Fin 4) : a ∈ S.image π.symm ↔ π a ∈ S := by
    constructor
    · intro ha
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp ha
      have he' : i = π a := by
        simpa only [Equiv.apply_symm_apply] using congrArg π he
      exact he' ▸ hi
    · intro ha
      exact Finset.mem_image.mpr ⟨π a, ha, π.symm_apply_apply a⟩
  simp only [heavySubsetRank, hc, hm]

end WeightedEdgeColoring.SubtwoHarmonicRanks

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable (G : WeightedMultigraph.{u})

/-- A normal bin pays every subset at the normal harmonic rank. -/
theorem subtwoPhysicalFourLoads_normal_subset_rank
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (j : Fin n) (I : Finset (Fin 4))
    (hnormal : ¬∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a) :
    (∑ a ∈ I, harmonicCharge (G.subtwoPhysicalFourLoads v neighbor bin j a)) ≤
      SubtwoHarmonicRanks.normalRank I.card := by
  apply SubtwoHarmonicRanks.normal_subset_rank I _
    (by simpa using Finset.card_le_card (Finset.subset_univ I))
    (fun a _ => G.subtwoPhysicalFourLoads_nonneg v neighbor bin j a)
    (fun a _ => le_of_not_gt (fun ha => hnormal ⟨a, ha⟩))
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
    (fun a _ _ => G.subtwoPhysicalFourLoads_nonneg v neighbor bin j a)).trans
      (G.subtwoPhysicalFourLoads_sum_le_one v neighbor hinj hne bin hbin j)

/-- A heavy bin pays its subset according to its actual two chosen indices. -/
theorem subtwoPhysicalFourLoads_heavy_subset_rank
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (j : Fin n) (I : Finset (Fin 4))
    (hh : ∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a) :
    let π := SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j)
    (∑ a ∈ I, harmonicCharge (G.subtwoPhysicalFourLoads v neighbor bin j a)) ≤
      SubtwoHarmonicRanks.heavySubsetRank I (π 0) (π 1) := by
  let w := G.subtwoPhysicalFourLoads v neighbor bin j
  let π := SubtwoHarmonicRanks.fourLoadOrder w
  have hload : w (π 0) + w (π 1) + w (π 2) + w (π 3) ≤ 1 := by
    have h := G.subtwoPhysicalFourLoads_sum_le_one v neighbor hinj hne bin hbin j
    rw [← Equiv.sum_comp π w] at h
    simpa [Fin.sum_univ_succ, add_assoc] using h
  have hsmall := SubtwoHarmonicRanks.fourLoadOrder_second w
  have hr := SubtwoHarmonicRanks.heavy_subset_ranks (w (π 0)) (w (π 1))
    (w (π 2)) (w (π 3)) (SubtwoHarmonicRanks.fourLoadOrder_heavy w hh)
    (G.subtwoPhysicalFourLoads_nonneg v neighbor bin j (π 1))
    (G.subtwoPhysicalFourLoads_nonneg v neighbor bin j (π 2))
    (G.subtwoPhysicalFourLoads_nonneg v neighbor bin j (π 3))
    hsmall.1 hsmall.2 hload
  have h := SubtwoHarmonicRanks.heavy_subset_sum_rank (I.image π.symm)
    (fun a => harmonicCharge (w (π a))) hr
  rw [SubtwoHarmonicRanks.heavySubsetRank_image_symm] at h
  have hs : (∑ a ∈ I.image π.symm, harmonicCharge (w (π a))) =
      ∑ a ∈ I, harmonicCharge (w a) := by
    rw [Finset.sum_image]
    · simp only [Equiv.apply_symm_apply]
    · exact fun a _ b _ he => π.symm.injective he
  rw [hs] at h
  exact h

/-- A function of the heavy indices can be summed either over classes
or directly over the original bins. -/
theorem sum_subtwoHeavyClassMass_weighted
    (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (f : Fin 4 → Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyClassMass v neighbor bin i k * f i k) =
      ∑ j : Fin n, if (∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a) then
        (1 / (n : ℝ)) *
          f (SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j) 0)
            (SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j) 1)
        else 0 := by
  have hterm (i k : Fin 4) : G.subtwoHeavyClassMass v neighbor bin i k * f i k =
      ∑ j : Fin n, if G.SubtwoHeavyClassBin v neighbor bin i k j then
        (1 / (n : ℝ)) * f i k else 0 := by
    unfold subtwoHeavyClassMass
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  simp_rw [hterm]
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin n, ∑ k : Fin 4,
        if G.SubtwoHeavyClassBin v neighbor bin i k j then
          (1 / (n : ℝ)) * f i k else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ j : Fin n, ∑ i : Fin 4, ∑ k : Fin 4,
        if G.SubtwoHeavyClassBin v neighbor bin i k j then
          (1 / (n : ℝ)) * f i k else 0 := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hh : ∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a
      · simp only [SubtwoHeavyClassBin, hh, true_and]
        simp [ite_and]
      · simp only [SubtwoHeavyClassBin, hh, false_and, if_false, Finset.sum_const_zero]

/-- Every subset row of the certificate holds for the true minimum bundle
costs. The correction coefficients are exactly the heavy-minus-normal ranks. -/
theorem subtwo_physical_subset_cost_row
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1) (I : Finset (Fin 4)) :
    (∑ a ∈ I, G.subtwoPhysicalBundleCost n v (neighbor a)) ≤
      SubtwoHarmonicRanks.normalRank I.card +
        ∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyClassMass v neighbor bin i k *
          (SubtwoHarmonicRanks.heavySubsetRank I i k - SubtwoHarmonicRanks.normalRank I.card) := by
  let w := G.subtwoPhysicalFourLoads v neighbor bin
  let π := fun j => SubtwoHarmonicRanks.fourLoadOrder (w j)
  let nr := SubtwoHarmonicRanks.normalRank I.card
  let rank := SubtwoHarmonicRanks.heavySubsetRank I
  have hb (j : Fin n) : (∑ a ∈ I, harmonicCharge (w j a)) ≤
      if (∃ a, 1 / 2 < w j a) then rank (π j 0) (π j 1) else nr := by
    split_ifs with hh
    · exact G.subtwoPhysicalFourLoads_heavy_subset_rank v neighbor hinj hne bin hbin j I hh
    · exact G.subtwoPhysicalFourLoads_normal_subset_rank v neighbor hinj hne bin hbin j I hh
  have hcost : (∑ a ∈ I, G.subtwoPhysicalBundleCost n v (neighbor a)) ≤
      ∑ j : Fin n, (1 / (n : ℝ)) *
        (if (∃ a, 1 / 2 < w j a) then rank (π j 0) (π j 1) else nr) := by
    calc
      _ ≤ ∑ a ∈ I, ∑ j : Fin n, (1 / (n : ℝ)) * harmonicCharge (w j a) := by
        apply Finset.sum_le_sum
        intro a ha
        exact G.subtwo_floorBundle_normalized_cost_le_local_charge v (neighbor a) (hne a) hn bin hbin
      _ = ∑ j : Fin n, (1 / (n : ℝ)) * ∑ a ∈ I, harmonicCharge (w j a) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hb j) (by positivity)
  have hterm (j : Fin n) : (1 / (n : ℝ)) *
      (if (∃ a, 1 / 2 < w j a) then rank (π j 0) (π j 1) else nr) =
      (1 / (n : ℝ)) * nr +
        (if (∃ a, 1 / 2 < w j a) then
          (1 / (n : ℝ)) * (rank (π j 0) (π j 1) - nr) else 0) := by
    split_ifs <;> ring
  have heq : (∑ j : Fin n, (1 / (n : ℝ)) *
      (if (∃ a, 1 / 2 < w j a) then rank (π j 0) (π j 1) else nr)) =
      nr + ∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyClassMass v neighbor bin i k * (rank i k - nr) := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, subtwo_uniform_bin_mass_sum hn, one_mul]
    rw [G.sum_subtwoHeavyClassMass_weighted v neighbor bin (fun i k => rank i k - nr)]
  rw [heq] at hcost
  exact hcost

/-- The same physical subset inequality in the affine form of the frozen
generator, with every heavy correction on the left. -/
theorem subtwo_physical_subset_cost_certificate_row
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1) (I : Finset (Fin 4)) :
    (∑ a ∈ I, G.subtwoPhysicalBundleCost n v (neighbor a)) +
      (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyClassMass v neighbor bin i k *
        (SubtwoHarmonicRanks.normalRank I.card - SubtwoHarmonicRanks.heavySubsetRank I i k)) ≤
      SubtwoHarmonicRanks.normalRank I.card := by
  have h := G.subtwo_physical_subset_cost_row v neighbor hinj hne hn bin hbin I
  have heq : (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyClassMass v neighbor bin i k *
      (SubtwoHarmonicRanks.normalRank I.card - SubtwoHarmonicRanks.heavySubsetRank I i k)) =
      -(∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyClassMass v neighbor bin i k *
        (SubtwoHarmonicRanks.heavySubsetRank I i k - SubtwoHarmonicRanks.normalRank I.card)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [heq]
  linarith

/-- The singleton upper row has exactly the three coefficients used by
the generator: minus one half, zero, and one quarter. -/
theorem subtwo_physical_singleton_cost_upper
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1) (a : Fin 4) :
    G.subtwoPhysicalBundleCost n v (neighbor a) +
      (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyClassMass v neighbor bin i k *
        (if i = a then (-1 / 2 : ℝ) else if k = a then 0 else 1 / 4)) ≤ 1 / 2 := by
  have hc (i k : Fin 4) : SubtwoHarmonicRanks.normalRank ({a} : Finset (Fin 4)).card -
      SubtwoHarmonicRanks.heavySubsetRank {a} i k =
      (if i = a then (-1 / 2 : ℝ) else if k = a then 0 else 1 / 4) := by
    by_cases hi : i = a <;> by_cases hk : k = a <;>
      norm_num [SubtwoHarmonicRanks.heavySubsetRank, SubtwoHarmonicRanks.normalRank, hi, hk]
  have h := G.subtwo_physical_subset_cost_certificate_row v neighbor hinj hne hn bin hbin {a}
  simp_rw [hc] at h
  simpa [SubtwoHarmonicRanks.normalRank] using h

end
end WeightedEdgeColoring.WeightedMultigraph
