import WeightedEdgeColoring.SubtwoGraphEndpointHeavy

/-!
# The graph-level endpoint price bound

A certificate gives a bound for every genuine local fractional packing,
with no hypothesis identifying the endpoint bin distributions. The
proof includes zero caps, arbitrary parallel types, and empty bins.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem subtwo_endpoint_item_mean (demand price : G.E → ℝ)
    (B : G.SubtwoLocalFractionalBins demand) (score : G.V → G.E → ℝ)
    (hsplit : ∀ e, score (G.fst e) e + score (G.snd e) e = 2 * price e) :
    (∑ v, ∑ p, B.mass v p * (∑ e, (B.pattern v p e : ℝ) * score v e)) =
      2 * ∑ e, price e * demand e := by
  classical
  have hv (v : G.V) :
      (∑ p, B.mass v p * (∑ e, (B.pattern v p e : ℝ) * score v e)) =
        ∑ e, if G.Inc v e then score v e * demand e else 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    calc
      _ = score v e * (∑ p, B.mass v p * (B.pattern v p e : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ = _ := by rw [B.covers]; split_ifs <;> simp
  simp_rw [hv]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  calc
    _ = ∑ v, ((if v = G.fst e then score v e * demand e else 0) +
        (if v = G.snd e then score v e * demand e else 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hf : v = G.fst e <;> by_cases hs : v = G.snd e
      · exact False.elim (G.noLoop e (hf.symm.trans hs))
      · simp [Inc, hf, G.noLoop e, eq_comm]
      · simp [Inc, hs, G.noLoop e, eq_comm]
      · simp [Inc, hf, hs, eq_comm]
    _ = (score (G.fst e) e + score (G.snd e) e) * demand e := by
      rw [Finset.sum_add_distrib]
      simp
      ring
    _ = _ := by rw [hsplit]; ring

end WeightedEdgeColoring.WeightedMultigraph

namespace WeightedEdgeColoring.Subtwo.GraphEndpoint

universe u
variable {G : WeightedMultigraph.{u}}

/-- A verified endpoint certificate bounds the price of every demand
with local fractional bin cost at most one. -/
theorem Certificate.demand_price_bound {cap : G.E → ℝ} (C : Certificate G cap)
    (demand price : G.E → ℝ) (B : G.SubtwoLocalFractionalBins demand)
    (hp : ∀ e, 0 ≤ price e)
    (hcap : ∀ e, G.subtwoSupportedPriceMax {G.fst e, G.snd e} price ≤ cap e)
    (hprice : ∀ p : G.SubtwoWeightedPattern, (∑ e, price e * (p.val e : ℝ)) ≤ 1)
    (htotal : ∀ v, (∑ p, B.mass v p) ≤ 1) :
    (∑ e, price e * demand e) ≤ (∑ v, C.P v) / 2 := by
  let B' := B.starRestrict G
  have hsupport : ∀ v p e, ¬G.Inc v e → B'.pattern v p e = 0 :=
    B.starRestrict_support G
  have h := G.subtwo_local_endpoint_score_bound demand B' C.P
    (fun v p ↦ C.binScore price v (B'.pattern v p)) C.P_nonneg htotal hsupport
    (fun v p hl ↦ C.light_bin_bound price hp hcap hprice v (B'.pattern v p)
      (B'.bin_feasible v p) (hsupport v p) hl)
    (fun e p q he hp₀ hp₁ ↦ C.heavy_pair_bound price hp hcap hprice e
      (B'.pattern (G.fst e) p) (B'.pattern (G.snd e) q) he hp₀ hp₁
      (B'.bin_feasible _ _) (B'.bin_feasible _ _) (hsupport _ _) (hsupport _ _))
  have hid := G.subtwo_endpoint_item_mean demand price B' (C.itemScore price)
    (C.itemScore_split price hp hcap)
  change (∑ v, ∑ p, B'.mass v p *
    (∑ e, (B'.pattern v p e : ℝ) * C.itemScore price v e)) ≤ ∑ v, C.P v at h
  rw [hid] at h
  linarith

end WeightedEdgeColoring.Subtwo.GraphEndpoint
