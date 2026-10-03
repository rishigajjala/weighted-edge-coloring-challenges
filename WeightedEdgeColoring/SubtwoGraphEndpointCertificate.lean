import WeightedEdgeColoring.SubtwoHeavyRemainder
import WeightedEdgeColoring.SubtwoEndpointLocalDemand

/-!
# Endpoint certificates on an actual multigraph

Edge indices are item types. Parallel types have the same cap and endpoint
coefficient; their weights and prices can be different. This interface
connects the ten-bundle numerical witnesses to actual graph patterns.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo.GraphEndpoint

universe u
variable (G : WeightedMultigraph.{u})

def Shared (e f : G.E) : Prop := G.Inc (G.fst e) f ∧ G.Inc (G.snd e) f

instance (e f : G.E) : Decidable (Shared G e f) := by
  unfold Shared
  infer_instance

structure Certificate (cap : G.E → ℝ) where
  rho : G.E → ℝ
  h : G.V → ℝ
  z : G.V → G.E → ℝ
  c : G.V → ℝ
  alpha : G.V → G.E → ℝ
  P : G.V → ℝ
  cap_nonneg : ∀ e, 0 ≤ cap e
  cap_same : ∀ e f, Shared G e f → cap f = cap e
  z_same : ∀ v e f, Shared G e f → z v f = z v e
  rho_nonneg : ∀ e, 0 ≤ rho e
  rho_le_two : ∀ e, rho e ≤ 2
  h_nonneg : ∀ v, 0 ≤ h v
  z_nonneg : ∀ v e, 0 ≤ z v e
  c_nonneg : ∀ v, 0 ≤ c v
  alpha_nonneg : ∀ v e, 0 ≤ alpha v e
  P_nonneg : ∀ v, 0 ≤ P v
  split : ∀ e, z (G.fst e) e + z (G.snd e) e = 2 * cap e
  light : ∀ v e, G.Inc v e → z v e ≤ c v + h v * cap e
  baseline : ∀ v, EndpointPotential.lightCharge * c v + h v ≤ P v
  off : ∀ v e f, G.Inc v e → G.Inc v f → ¬Shared G e f →
    z v f - rho e * cap f ≤ alpha v e
  same : ∀ v e, G.Inc v e → z v e - (2 - rho e) * cap e ≤ alpha v e
  pair : ∀ e, rho e * cap e ≤ alpha (G.fst e) e + alpha (G.snd e) e
  edge : ∀ e, (2 - rho e) * cap e + rho e +
    EndpointPotential.residualCharge * (alpha (G.fst e) e + alpha (G.snd e) e) ≤
      P (G.fst e) + P (G.snd e)

variable {G}

noncomputable def Certificate.itemScore {cap : G.E → ℝ} (C : Certificate G cap)
    (price : G.E → ℝ) (v : G.V) (e : G.E) : ℝ :=
  if (1 / 2 : ℝ) < G.weight e then price e else C.z v e * (price e / cap e)

noncomputable def Certificate.binScore {cap : G.E → ℝ} (C : Certificate G cap)
    (price : G.E → ℝ) (v : G.V) (n : G.E → ℕ) : ℝ :=
  ∑ e, (n e : ℝ) * C.itemScore price v e

theorem Certificate.itemScore_split {cap : G.E → ℝ} (C : Certificate G cap)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e)
    (hcap : ∀ e, G.subtwoSupportedPriceMax {G.fst e, G.snd e} price ≤ cap e)
    (e : G.E) :
    C.itemScore price (G.fst e) e + C.itemScore price (G.snd e) e = 2 * price e := by
  unfold itemScore
  split_ifs
  · ring
  · have hid := EndpointPotential.normalized_price_identity (price e) (cap e)
      (harmonicCharge (G.weight e)) (hp e) (C.cap_nonneg e)
      ((G.subtwo_item_price_le_bundle_harmonic price e).trans
        (mul_le_mul_of_nonneg_right (hcap e) (harmonicCharge_nonneg _)))
    rw [← add_mul, C.split]
    nlinarith [hid]

theorem Certificate.light_bin_bound {cap : G.E → ℝ} (C : Certificate G cap)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e)
    (hcap : ∀ e, G.subtwoSupportedPriceMax {G.fst e, G.snd e} price ≤ cap e)
    (hprice : ∀ p : G.SubtwoWeightedPattern, (∑ e, price e * (p.val e : ℝ)) ≤ 1)
    (v : G.V) (n : G.E → ℕ)
    (hload : (∑ e, (n e : ℝ) * G.weight e) ≤ 1)
    (hsupport : ∀ e, ¬G.Inc v e → n e = 0)
    (hlight : ∀ e, n e ≠ 0 → G.weight e ≤ 1 / 2) :
    C.binScore price v n ≤ C.P v := by
  have hitem (e : G.E) : price e ≤ cap e * harmonicCharge (G.weight e) :=
    (G.subtwo_item_price_le_bundle_harmonic price e).trans
      (mul_le_mul_of_nonneg_right (hcap e) (harmonicCharge_nonneg _))
  have hprofit : (∑ e, (n e : ℝ) * price e) ≤ 1 := by
    simpa [WeightedMultigraph.SubtwoWeightedPattern.ofTotalLoad, mul_comm] using
      hprice (WeightedMultigraph.SubtwoWeightedPattern.ofTotalLoad G n hload)
  have hnum := EndpointPotential.light_bin_estimate G.weight price cap (C.z v) n
    (C.c v) (C.h v) G.weight_nonneg hp C.cap_nonneg (C.c_nonneg v) (C.h_nonneg v)
    hlight hload hprofit hitem (fun e he ↦ C.light v e (by
      by_contra hi
      exact he (hsupport e hi)))
  have hid : C.binScore price v n = ∑ e, (n e : ℝ) * (C.z v e * (price e / cap e)) := by
    apply Finset.sum_congr rfl
    intro e _
    by_cases hn : n e = 0
    · simp [hn]
    · simp only [itemScore, if_neg (not_lt_of_ge (hlight e hn))]
  rw [hid]
  exact hnum.trans (C.baseline v)

end WeightedEdgeColoring.Subtwo.GraphEndpoint
