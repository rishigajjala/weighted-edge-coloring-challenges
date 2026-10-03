import WeightedEdgeColoring.SubtwoHeavyBinPartition
import WeightedEdgeColoring.SubtwoEndpointBinEstimate

/-! Delete one heavy item and split the remaining counts into the shared
bundle and all other bundles. All counts remain natural numbers. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

def subtwoRemainderCount (e : G.E) (n : G.E → ℕ) (f : G.E) : ℕ :=
  if f = e then 0 else n f

def subtwoSameBundleRemainder (e : G.E) (n : G.E → ℕ) (f : G.E) : ℕ :=
  if G.Inc (G.fst e) f ∧ G.Inc (G.snd e) f then G.subtwoRemainderCount e n f else 0

theorem subtwoRemainderCount_sum (e : G.E) (n : G.E → ℕ) (he : n e = 1)
    (f : G.E → ℝ) :
    (∑ g, (n g : ℝ) * f g) = f e + ∑ g, (G.subtwoRemainderCount e n g : ℝ) * f g := by
  classical
  have hid (g : G.E) : (n g : ℝ) * f g =
      (if g = e then f g else 0) + (G.subtwoRemainderCount e n g : ℝ) * f g := by
    by_cases hg : g = e
    · subst g; simp [subtwoRemainderCount, he]
    · simp [subtwoRemainderCount, hg]
  simp_rw [hid, Finset.sum_add_distrib]
  simp

theorem subtwoRemainderCount_load (e : G.E) (n : G.E → ℕ) (he : n e = 1)
    (hload : (∑ f, (n f : ℝ) * G.weight f) ≤ 1) :
    (∑ f, (G.subtwoRemainderCount e n f : ℝ) * G.weight f) ≤ 1 - G.weight e := by
  rw [G.subtwoRemainderCount_sum e n he G.weight] at hload
  linarith

theorem subtwoRemainderCount_light (e : G.E) (n : G.E → ℕ)
    (hload : (∑ f, (n f : ℝ) * G.weight f) ≤ 1)
    (hheavy : (1 / 2 : ℝ) < G.weight e) (he : n e = 1) :
    ∀ f, G.subtwoRemainderCount e n f ≠ 0 → G.weight f ≤ 1 / 2 := by
  intro f hf
  have hfe : f ≠ e := by intro h; subst f; simp [subtwoRemainderCount] at hf
  have hnf : n f ≠ 0 := by simpa [subtwoRemainderCount, hfe] using hf
  apply le_of_not_gt
  intro hwf
  exact hfe (G.subtwo_heavy_type_unique n hload f e hwf hheavy hnf (by simp [he]))

theorem subtwoRemainderCount_split (e : G.E) (n : G.E → ℕ) (f : G.E) :
    G.subtwoRemainderCount e n f =
      G.subtwoOffBundleCount (G.fst e) (G.snd e) n f + G.subtwoSameBundleRemainder e n f := by
  by_cases hfe : f = e
  · subst f
    simp [subtwoRemainderCount, subtwoSameBundleRemainder, subtwoOffBundleCount_shared_zero]
  · by_cases hs : G.Inc (G.fst e) f ∧ G.Inc (G.snd e) f <;>
      simp [subtwoRemainderCount, subtwoOffBundleCount, subtwoSameBundleRemainder, hfe, hs]

theorem subtwoSameBundleRemainder_price_nonneg (e : G.E) (n : G.E → ℕ)
    (price : G.E → ℝ) (hp : ∀ f, 0 ≤ price f) :
    0 ≤ ∑ f, price f * (G.subtwoSameBundleRemainder e n f : ℝ) := by
  exact Finset.sum_nonneg fun f _ ↦ mul_nonneg (hp f) (Nat.cast_nonneg _)

/-- The remainder after deleting the heavy copy has normalized price at
most 25/36, for caps that dominate the true bundle prices. -/
theorem subtwoHeavyRemainder_normalized (e : G.E) (n : G.E → ℕ)
    (price cap : G.E → ℝ) (hm : ∀ f, 0 ≤ cap f)
    (hcap : ∀ f, G.subtwoSupportedPriceMax {G.fst f, G.snd f} price ≤ cap f)
    (hheavy : (1 / 2 : ℝ) < G.weight e) (he : n e = 1)
    (hload : (∑ f, (n f : ℝ) * G.weight f) ≤ 1) :
    (∑ f, (G.subtwoRemainderCount e n f : ℝ) * (price f / cap f)) ≤
      Subtwo.EndpointPotential.residualCharge := by
  apply Subtwo.EndpointPotential.residual_normalized_price
    G.weight price cap (G.subtwoRemainderCount e n) G.weight_nonneg hm
  · have hl := G.subtwoRemainderCount_load e n he hload
    linarith
  · intro f
    exact (G.subtwo_item_price_le_bundle_harmonic price f).trans
      (mul_le_mul_of_nonneg_right (hcap f) (harmonicCharge_nonneg _))

theorem subtwoSharedBundle_endpoints (e f : G.E)
    (hu : G.Inc (G.fst e) f) (hv : G.Inc (G.snd e) f) :
    G.fst f ∈ ({G.fst e, G.snd e} : Finset G.V) ∧
      G.snd f ∈ ({G.fst e, G.snd e} : Finset G.V) := by
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact False.elim (G.noLoop e (hu.symm.trans hv))
  · simp [hu, hv]
  · simp [hu, hv]
  · exact False.elim (G.noLoop e (hu.symm.trans hv))

/-- The heavy item and all light items on its bundle form an actual
feasible packet, whose price is at most the true bundle maximum. -/
theorem subtwoSameBundleRemainder_packet_price (e : G.E) (n : G.E → ℕ)
    (price : G.E → ℝ) (he : n e = 1)
    (hload : (∑ f, (n f : ℝ) * G.weight f) ≤ 1) :
    price e + (∑ f, price f * (G.subtwoSameBundleRemainder e n f : ℝ)) ≤
      G.subtwoSupportedPriceMax {G.fst e, G.snd e} price := by
  classical
  let count (f : G.E) : ℕ := if G.Inc (G.fst e) f ∧ G.Inc (G.snd e) f then n f else 0
  have hc_le (f : G.E) : count f ≤ n f := by dsimp [count]; split_ifs <;> simp
  have hc_load : (∑ f, (count f : ℝ) * G.weight f) ≤ 1 := by
    refine le_trans (Finset.sum_le_sum ?_) hload
    intro f _
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hc_le f)) (G.weight_nonneg f)
  let packet := SubtwoWeightedPattern.ofTotalLoad G count hc_load
  have hsupport : ∀ f, packet.val f ≠ 0 →
      G.fst f ∈ ({G.fst e, G.snd e} : Finset G.V) ∧
      G.snd f ∈ ({G.fst e, G.snd e} : Finset G.V) := by
    intro f hf
    have hs : G.Inc (G.fst e) f ∧ G.Inc (G.snd e) f := by
      by_contra hs
      exact hf (by simp [packet, SubtwoWeightedPattern.ofTotalLoad, count, hs])
    exact G.subtwoSharedBundle_endpoints e f hs.1 hs.2
  have hp := Subtwo.patternPrice_le_paletteMaxScore
    (G.subtwoSupportedColorPattern {G.fst e, G.snd e}) price () packet
  change (∑ f, price f * ((packet.restrictTo G {G.fst e, G.snd e}).val f : ℝ)) ≤ _ at hp
  rw [SubtwoWeightedPattern.restrictTo_fixed G packet _ hsupport] at hp
  have hid (f : G.E) : (count f : ℝ) =
      (if f = e then (1 : ℝ) else 0) + (G.subtwoSameBundleRemainder e n f : ℝ) := by
    by_cases hfe : f = e
    · subst f
      simp [count, subtwoSameBundleRemainder, subtwoRemainderCount, Inc, he]
    · by_cases hs : G.Inc (G.fst e) f ∧ G.Inc (G.snd e) f <;>
        simp [count, subtwoSameBundleRemainder, subtwoRemainderCount, hfe, hs]
  change (∑ f, price f * (count f : ℝ)) ≤ _ at hp
  simp_rw [hid, mul_add, Finset.sum_add_distrib] at hp
  simpa using hp

end WeightedEdgeColoring.WeightedMultigraph
