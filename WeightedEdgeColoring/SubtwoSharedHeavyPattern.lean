import WeightedEdgeColoring.SubtwoWeightedPatterns

/-! A physical merge of two feasible local bins containing the same heavy
edge type. All parallel edges on the shared bundle are discarded except
for one copy of the chosen heavy type. This is a construction of a genuine
integer-count weighted-color pattern, not an assumed price inequality. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

def subtwoOffBundleCount (u v : G.V) (n : G.E → ℕ) (f : G.E) : ℕ :=
  if G.Inc u f ∧ G.Inc v f then 0 else n f

theorem subtwoOffBundleCount_le (u v : G.V) (n : G.E → ℕ) (f : G.E) :
    G.subtwoOffBundleCount u v n f ≤ n f := by
  unfold subtwoOffBundleCount
  split <;> simp

theorem subtwoOffBundleCount_shared_zero (e : G.E) (n : G.E → ℕ) :
    G.subtwoOffBundleCount (G.fst e) (G.snd e) n e = 0 := by
  simp [subtwoOffBundleCount, Inc]

/-- The entire off-bundle remainder has load at most one minus the
weight of the one heavy copy. -/
theorem subtwoOffBundleCount_remainder (e : G.E) (n : G.E → ℕ)
    (he : n e = 1) (hload : (∑ f, (n f : ℝ) * G.weight f) ≤ 1) :
    (∑ f, (G.subtwoOffBundleCount (G.fst e) (G.snd e) n f : ℝ) * G.weight f)
      ≤ 1 - G.weight e := by
  classical
  let F := (Finset.univ : Finset G.E).erase e
  have hsum := Finset.sum_erase_add (Finset.univ : Finset G.E)
    (fun f ↦ (n f : ℝ) * G.weight f) (Finset.mem_univ e)
  have hoffsum := Finset.sum_erase_add (Finset.univ : Finset G.E)
    (fun f ↦ (G.subtwoOffBundleCount (G.fst e) (G.snd e) n f : ℝ) * G.weight f)
    (Finset.mem_univ e)
  simp only [subtwoOffBundleCount_shared_zero, Nat.cast_zero, zero_mul, add_zero] at hoffsum
  rw [← hoffsum]
  have hle :
      (∑ f ∈ F, (G.subtwoOffBundleCount (G.fst e) (G.snd e) n f : ℝ) * G.weight f) ≤
        ∑ f ∈ F, (n f : ℝ) * G.weight f := by
    apply Finset.sum_le_sum
    intro f _
    exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (G.subtwoOffBundleCount_le _ _ n f)) (G.weight_nonneg f)
  simp only [he, Nat.cast_one, one_mul] at hsum
  dsimp [F] at hle
  linarith

/-- A bin supported at one endpoint contributes no off-bundle load at
the other endpoint. -/
theorem subtwoOffBundleCount_opposite_zero (u v : G.V) (n : G.E → ℕ)
    (hsupport : ∀ f, ¬G.Inc v f → n f = 0) (f : G.E) (hf : G.Inc u f) :
    G.subtwoOffBundleCount u v n f = 0 := by
  by_cases hv : G.Inc v f
  · simp [subtwoOffBundleCount, hf, hv]
  · simp [subtwoOffBundleCount, hv, hsupport f hv]

def subtwoSharedHeavyCount (e : G.E) (n₀ n₁ : G.E → ℕ) (f : G.E) : ℕ :=
  (if f = e then 1 else 0) +
    G.subtwoOffBundleCount (G.fst e) (G.snd e) n₀ f +
    G.subtwoOffBundleCount (G.fst e) (G.snd e) n₁ f

theorem subtwoSharedHeavyCount_load (e : G.E) (n₀ n₁ : G.E → ℕ) (v : G.V) :
    (∑ f, if G.Inc v f then (G.subtwoSharedHeavyCount e n₀ n₁ f : ℝ) * G.weight f else 0) =
      (if G.Inc v e then G.weight e else 0) +
      (∑ f, if G.Inc v f then
        (G.subtwoOffBundleCount (G.fst e) (G.snd e) n₀ f : ℝ) * G.weight f else 0) +
      (∑ f, if G.Inc v f then
        (G.subtwoOffBundleCount (G.fst e) (G.snd e) n₁ f : ℝ) * G.weight f else 0) := by
  classical
  have hsplit (f : G.E) :
      (if G.Inc v f then (G.subtwoSharedHeavyCount e n₀ n₁ f : ℝ) * G.weight f else 0) =
        (if f = e then (if G.Inc v f then G.weight f else 0) else 0) +
        (if G.Inc v f then
          (G.subtwoOffBundleCount (G.fst e) (G.snd e) n₀ f : ℝ) * G.weight f else 0) +
        (if G.Inc v f then
          (G.subtwoOffBundleCount (G.fst e) (G.snd e) n₁ f : ℝ) * G.weight f else 0) := by
    by_cases he : f = e
    · subst f
      simp [subtwoSharedHeavyCount, subtwoOffBundleCount_shared_zero]
    · by_cases hi : G.Inc v f <;>
        simp [subtwoSharedHeavyCount, hi, he, Nat.cast_add, add_mul]
  simp_rw [hsplit, Finset.sum_add_distrib]
  simp

/-- The merged count vector is a feasible whole-graph weighted color. -/
theorem subtwoSharedHeavyCount_feasible (e : G.E) (n₀ n₁ : G.E → ℕ)
    (hheavy : (1 / 2 : ℝ) < G.weight e)
    (he₀ : n₀ e = 1) (he₁ : n₁ e = 1)
    (hload₀ : (∑ f, (n₀ f : ℝ) * G.weight f) ≤ 1)
    (hload₁ : (∑ f, (n₁ f : ℝ) * G.weight f) ≤ 1)
    (hsupport₀ : ∀ f, ¬G.Inc (G.fst e) f → n₀ f = 0)
    (hsupport₁ : ∀ f, ¬G.Inc (G.snd e) f → n₁ f = 0) :
    ∀ v, (∑ f, if G.Inc v f then
      (G.subtwoSharedHeavyCount e n₀ n₁ f : ℝ) * G.weight f else 0) ≤ 1 := by
  classical
  have hR₀ := G.subtwoOffBundleCount_remainder e n₀ he₀ hload₀
  have hR₁ := G.subtwoOffBundleCount_remainder e n₁ he₁ hload₁
  have hsub (n : G.E → ℕ) (v : G.V) :
      (∑ f, if G.Inc v f then
        (G.subtwoOffBundleCount (G.fst e) (G.snd e) n f : ℝ) * G.weight f else 0) ≤
        ∑ f, (G.subtwoOffBundleCount (G.fst e) (G.snd e) n f : ℝ) * G.weight f := by
    apply Finset.sum_le_sum
    intro f _
    split_ifs
    · rfl
    · exact mul_nonneg (Nat.cast_nonneg _) (G.weight_nonneg f)
  intro v
  rw [G.subtwoSharedHeavyCount_load]
  by_cases hv₀ : v = G.fst e
  · subst v
    have hzero : (∑ f, if G.Inc (G.fst e) f then
        (G.subtwoOffBundleCount (G.fst e) (G.snd e) n₁ f : ℝ) * G.weight f else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro f _
      split_ifs with hf
      · rw [G.subtwoOffBundleCount_opposite_zero _ _ n₁ hsupport₁ f hf]; simp
      · rfl
    have heinc : G.Inc (G.fst e) e := Or.inl rfl
    rw [hzero, if_pos heinc]
    have := hsub n₀ (G.fst e)
    linarith
  by_cases hv₁ : v = G.snd e
  · subst v
    have hzero : (∑ f, if G.Inc (G.snd e) f then
        (G.subtwoOffBundleCount (G.fst e) (G.snd e) n₀ f : ℝ) * G.weight f else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro f _
      split_ifs with hf
      · have hz : G.subtwoOffBundleCount (G.fst e) (G.snd e) n₀ f = 0 := by
          by_cases hu : G.Inc (G.fst e) f
          · simp [subtwoOffBundleCount, hu, hf]
          · simp [subtwoOffBundleCount, hu, hsupport₀ f hu]
        rw [hz]; simp
      · rfl
    have heinc : G.Inc (G.snd e) e := Or.inr rfl
    rw [hzero, if_pos heinc]
    have := hsub n₁ (G.snd e)
    linarith
  · have hn : ¬G.Inc v e := by simpa [Inc, eq_comm] using And.intro hv₀ hv₁
    rw [if_neg hn]
    have h₀ := hsub n₀ v
    have h₁ := hsub n₁ v
    linarith

def subtwoSharedHeavyPattern (e : G.E) (n₀ n₁ : G.E → ℕ)
    (hheavy : (1 / 2 : ℝ) < G.weight e)
    (he₀ : n₀ e = 1) (he₁ : n₁ e = 1)
    (hload₀ : (∑ f, (n₀ f : ℝ) * G.weight f) ≤ 1)
    (hload₁ : (∑ f, (n₁ f : ℝ) * G.weight f) ≤ 1)
    (hsupport₀ : ∀ f, ¬G.Inc (G.fst e) f → n₀ f = 0)
    (hsupport₁ : ∀ f, ¬G.Inc (G.snd e) f → n₁ f = 0) : G.SubtwoWeightedPattern :=
  ⟨G.subtwoSharedHeavyCount e n₀ n₁,
    G.subtwoSharedHeavyCount_feasible e n₀ n₁ hheavy he₀ he₁ hload₀ hload₁ hsupport₀ hsupport₁⟩

theorem subtwoSharedHeavyCount_price (e : G.E) (n₀ n₁ : G.E → ℕ) (price : G.E → ℝ) :
    (∑ f, price f * (G.subtwoSharedHeavyCount e n₀ n₁ f : ℝ)) = price e +
      (∑ f, price f * (G.subtwoOffBundleCount (G.fst e) (G.snd e) n₀ f : ℝ)) +
      ∑ f, price f * (G.subtwoOffBundleCount (G.fst e) (G.snd e) n₁ f : ℝ) := by
  classical
  simp only [subtwoSharedHeavyCount, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  congr 2
  simp

/-- A heavy type occurring in a unit bin occurs exactly once. -/
theorem subtwo_heavy_count_eq_one (e : G.E) (n : G.E → ℕ)
    (hheavy : (1 / 2 : ℝ) < G.weight e) (hne : n e ≠ 0)
    (hload : (∑ f, (n f : ℝ) * G.weight f) ≤ 1) : n e = 1 := by
  have hsingle := Finset.single_le_sum (s := (Finset.univ : Finset G.E))
    (f := fun f ↦ (n f : ℝ) * G.weight f)
    (fun f _ ↦ mul_nonneg (Nat.cast_nonneg _) (G.weight_nonneg f)) (Finset.mem_univ e)
  have hn : n e ≤ 1 := by
    by_contra hn
    have hnR : (2 : ℝ) ≤ n e := by exact_mod_cast (show 2 ≤ n e by omega)
    nlinarith
  omega

/-- The actual merged pattern proves the price inequality used by the
endpoint argument. No compatibility of the two local bin laws is assumed. -/
theorem subtwo_sharedHeavy_price_le (e : G.E) (n₀ n₁ : G.E → ℕ)
    (hheavy : (1 / 2 : ℝ) < G.weight e)
    (he₀ : n₀ e = 1) (he₁ : n₁ e = 1)
    (hload₀ : (∑ f, (n₀ f : ℝ) * G.weight f) ≤ 1)
    (hload₁ : (∑ f, (n₁ f : ℝ) * G.weight f) ≤ 1)
    (hsupport₀ : ∀ f, ¬G.Inc (G.fst e) f → n₀ f = 0)
    (hsupport₁ : ∀ f, ¬G.Inc (G.snd e) f → n₁ f = 0)
    (price : G.E → ℝ) (R : ℝ)
    (hprice : ∀ p : G.SubtwoWeightedPattern, (∑ f, price f * (p.val f : ℝ)) ≤ R) :
    price e +
      (∑ f, price f * (G.subtwoOffBundleCount (G.fst e) (G.snd e) n₀ f : ℝ)) +
      (∑ f, price f * (G.subtwoOffBundleCount (G.fst e) (G.snd e) n₁ f : ℝ)) ≤ R := by
  have hp := hprice (G.subtwoSharedHeavyPattern e n₀ n₁ hheavy he₀ he₁
    hload₀ hload₁ hsupport₀ hsupport₁)
  change (∑ f, price f * (G.subtwoSharedHeavyCount e n₀ n₁ f : ℝ)) ≤ R at hp
  rwa [G.subtwoSharedHeavyCount_price] at hp

end WeightedEdgeColoring.WeightedMultigraph
