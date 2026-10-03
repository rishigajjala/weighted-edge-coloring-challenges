import WeightedEdgeColoring.SubtwoGraphEndpointCertificate

/-! The paired-heavy-bin inequality for actual integer-count graph bins. -/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo.GraphEndpoint

universe u
variable {G : WeightedMultigraph.{u}}

noncomputable def offPrice (G : WeightedMultigraph.{u}) (price : G.E → ℝ)
    (e : G.E) (n : G.E → ℕ) : ℝ :=
  ∑ f, price f * (G.subtwoOffBundleCount (G.fst e) (G.snd e) n f : ℝ)

noncomputable def samePrice (G : WeightedMultigraph.{u}) (price : G.E → ℝ)
    (e : G.E) (n : G.E → ℕ) : ℝ :=
  ∑ f, price f * (G.subtwoSameBundleRemainder e n f : ℝ)

noncomputable def normalizedRemainder (G : WeightedMultigraph.{u}) (price cap : G.E → ℝ)
    (e : G.E) (n : G.E → ℕ) : ℝ :=
  ∑ f, (G.subtwoRemainderCount e n f : ℝ) * (price f / cap f)

theorem Certificate.heavy_bin_decomposition {cap : G.E → ℝ} (C : Certificate G cap)
    (price : G.E → ℝ) (v : G.V) (e : G.E) (n : G.E → ℕ)
    (hheavy : (1 / 2 : ℝ) < G.weight e) (he : n e = 1)
    (hload : (∑ f, (n f : ℝ) * G.weight f) ≤ 1) :
    C.binScore price v n = price e +
      ∑ f, (G.subtwoRemainderCount e n f : ℝ) * (C.z v f * (price f / cap f)) := by
  unfold Certificate.binScore
  rw [G.subtwoRemainderCount_sum e n he (C.itemScore price v)]
  have hi : C.itemScore price v e = price e := by simp only [Certificate.itemScore, if_pos hheavy]
  rw [hi]
  congr 1
  apply Finset.sum_congr rfl
  intro f _
  by_cases hn : G.subtwoRemainderCount e n f = 0
  · simp [hn]
  · have hl := G.subtwoRemainderCount_light e n hload hheavy he f hn
    simp only [Certificate.itemScore, if_neg (not_lt_of_ge hl)]

theorem remainder_off_price (price : G.E → ℝ) (e : G.E) (n : G.E → ℕ) :
    (∑ f, (G.subtwoRemainderCount e n f : ℝ) *
      (if Shared G e f then 0 else price f)) = offPrice G price e n := by
  apply Finset.sum_congr rfl
  intro f _
  by_cases hfe : f = e
  · subst f
    simp [WeightedMultigraph.subtwoRemainderCount,
      WeightedMultigraph.subtwoOffBundleCount_shared_zero]
  · by_cases hs : Shared G e f <;>
      simp [Shared, WeightedMultigraph.subtwoRemainderCount,
        WeightedMultigraph.subtwoOffBundleCount, hfe, hs, mul_comm] at *

theorem remainder_same_price (price : G.E → ℝ) (e : G.E) (n : G.E → ℕ) :
    (∑ f, (G.subtwoRemainderCount e n f : ℝ) *
      (if Shared G e f then price f else 0)) = samePrice G price e n := by
  apply Finset.sum_congr rfl
  intro f _
  by_cases hs : Shared G e f <;>
    simp [Shared, WeightedMultigraph.subtwoSameBundleRemainder, hs, mul_comm] at *

/-- Every light term of a bin is covered by its actual off-bundle price,
its normalized remainder price, and a same-bundle price term. -/
theorem Certificate.heavy_bin_coverage {cap : G.E → ℝ} (C : Certificate G cap)
    (price : G.E → ℝ) (hp : ∀ f, 0 ≤ price f)
    (hcap : ∀ f, G.subtwoSupportedPriceMax {G.fst f, G.snd f} price ≤ cap f)
    (v : G.V) (e : G.E) (n : G.E → ℕ) (hinc : G.Inc v e)
    (hheavy : (1 / 2 : ℝ) < G.weight e) (he : n e = 1)
    (hload : (∑ f, (n f : ℝ) * G.weight f) ≤ 1)
    (hsupport : ∀ f, ¬G.Inc v f → n f = 0) :
    C.binScore price v n ≤ price e + C.rho e * offPrice G price e n +
      C.alpha v e * normalizedRemainder G price cap e n +
      max (C.z v e - C.alpha v e) 0 / cap e * samePrice G price e n := by
  have hnum := EndpointPotential.remainder_coverage price cap (C.z v)
    (fun f ↦ harmonicCharge (G.weight f)) (G.subtwoRemainderCount e n)
    (Shared G e) (cap e) (C.z v e) (C.alpha v e) (C.rho e) hp C.cap_nonneg
    (fun f ↦ (G.subtwo_item_price_le_bundle_harmonic price f).trans
      (mul_le_mul_of_nonneg_right (hcap f) (harmonicCharge_nonneg _)))
    (fun f hf ↦ ⟨C.cap_same e f hf, C.z_same v e f hf⟩) ?_
  · rw [remainder_off_price, remainder_same_price] at hnum
    rw [C.heavy_bin_decomposition price v e n hheavy he hload]
    change _ ≤ price e + C.rho e * offPrice G price e n +
      C.alpha v e * (∑ f, (G.subtwoRemainderCount e n f : ℝ) * (price f / cap f)) +
      max (C.z v e - C.alpha v e) 0 / cap e * samePrice G price e n
    linarith
  · intro f hf hshared
    have hn : n f ≠ 0 := by
      intro hn
      simp [WeightedMultigraph.subtwoRemainderCount, hn] at hf
    exact C.off v e f hinc (by
      by_contra hi
      exact hn (hsupport f hi)) hshared

/-- Pair any two feasible star bins containing the same heavy type.
The resulting estimate uses the genuine merged graph pattern. -/
theorem Certificate.heavy_pair_bound {cap : G.E → ℝ} (C : Certificate G cap)
    (price : G.E → ℝ) (hp : ∀ f, 0 ≤ price f)
    (hcap : ∀ f, G.subtwoSupportedPriceMax {G.fst f, G.snd f} price ≤ cap f)
    (hprice : ∀ p : G.SubtwoWeightedPattern, (∑ f, price f * (p.val f : ℝ)) ≤ 1)
    (e : G.E) (n₀ n₁ : G.E → ℕ) (hheavy : (1 / 2 : ℝ) < G.weight e)
    (he₀ : n₀ e = 1) (he₁ : n₁ e = 1)
    (hload₀ : (∑ f, (n₀ f : ℝ) * G.weight f) ≤ 1)
    (hload₁ : (∑ f, (n₁ f : ℝ) * G.weight f) ≤ 1)
    (hsupport₀ : ∀ f, ¬G.Inc (G.fst e) f → n₀ f = 0)
    (hsupport₁ : ∀ f, ¬G.Inc (G.snd e) f → n₁ f = 0) :
    C.binScore price (G.fst e) n₀ + C.binScore price (G.snd e) n₁ ≤
      C.P (G.fst e) + C.P (G.snd e) := by
  have hi₀ : G.Inc (G.fst e) e := Or.inl rfl
  have hi₁ : G.Inc (G.snd e) e := Or.inr rfl
  have hc₀ := C.heavy_bin_coverage price hp hcap (G.fst e) e n₀ hi₀ hheavy he₀ hload₀ hsupport₀
  have hc₁ := C.heavy_bin_coverage price hp hcap (G.snd e) e n₁ hi₁ hheavy he₁ hload₁ hsupport₁
  have hmerge : price e + offPrice G price e n₀ + offPrice G price e n₁ ≤ 1 :=
    G.subtwo_sharedHeavy_price_le e n₀ n₁ hheavy he₀ he₁ hload₀ hload₁ hsupport₀ hsupport₁
      price 1 hprice
  have hr₀ := G.subtwoHeavyRemainder_normalized e n₀ price cap C.cap_nonneg hcap hheavy he₀ hload₀
  have hr₁ := G.subtwoHeavyRemainder_normalized e n₁ price cap C.cap_nonneg hcap hheavy he₁ hload₁
  have hE₀ := G.subtwoSameBundleRemainder_price_nonneg e n₀ price hp
  have hE₁ := G.subtwoSameBundleRemainder_price_nonneg e n₁ price hp
  have hpack₀ : samePrice G price e n₀ ≤ cap e - price e := by
    have hh := (G.subtwoSameBundleRemainder_packet_price e n₀ price he₀ hload₀).trans (hcap e)
    change price e + samePrice G price e n₀ ≤ cap e at hh
    linarith
  have hpack₁ : samePrice G price e n₁ ≤ cap e - price e := by
    have hh := (G.subtwoSameBundleRemainder_packet_price e n₁ price he₁ hload₁).trans (hcap e)
    change price e + samePrice G price e n₁ ≤ cap e at hh
    linarith
  rcases eq_or_lt_of_le (C.cap_nonneg e) with hz | hm
  · have hz' : cap e = 0 := hz.symm
    have hpz : price e = 0 := by
      change 0 ≤ samePrice G price e n₀ at hE₀
      rw [hz'] at hpack₀
      linarith [hp e]
    simp only [hz', div_zero, zero_mul, hpz, zero_add] at hc₀ hc₁ hmerge
    have hb := EndpointPotential.pairedHeavy_zero_cap
      (C.binScore price (G.fst e) n₀ + C.binScore price (G.snd e) n₁)
      (offPrice G price e n₀) (offPrice G price e n₁)
      (normalizedRemainder G price cap e n₀) (normalizedRemainder G price cap e n₁)
      (C.alpha (G.fst e) e) (C.alpha (G.snd e) e) (C.rho e)
      EndpointPotential.residualCharge (C.rho_nonneg e) (C.alpha_nonneg _ _) (C.alpha_nonneg _ _)
      hmerge hr₀ hr₁ (by linarith)
    have hedge := C.edge e
    rw [hz', mul_zero, zero_add] at hedge
    exact hb.trans hedge
  · have hb := EndpointPotential.pairedHeavy_bound
      (C.binScore price (G.fst e) n₀ + C.binScore price (G.snd e) n₁) (price e)
      (offPrice G price e n₀) (offPrice G price e n₁)
      (samePrice G price e n₀) (samePrice G price e n₁)
      (normalizedRemainder G price cap e n₀) (normalizedRemainder G price cap e n₁)
      (C.z (G.fst e) e) (C.z (G.snd e) e)
      (C.alpha (G.fst e) e) (C.alpha (G.snd e) e) (cap e) (C.rho e)
      EndpointPotential.residualCharge hm (C.rho_nonneg e) (C.rho_le_two e)
      (C.alpha_nonneg _ _) (C.alpha_nonneg _ _) hE₀ hE₁ hpack₀ hpack₁ hmerge hr₀ hr₁
      (C.split e) (C.same _ _ hi₀) (C.same _ _ hi₁) (C.pair e) (by linarith)
    exact hb.trans (C.edge e)

end WeightedEdgeColoring.Subtwo.GraphEndpoint
