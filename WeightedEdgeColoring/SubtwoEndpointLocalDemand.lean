import WeightedEdgeColoring.SubtwoHeavyBinPartition
import WeightedEdgeColoring.SubtwoEndpointAveraging

/-!
# Applying endpoint estimates to actual fractional local packings

The local packings in these statements have integer type counts and
arbitrary real masses. The hypotheses requiring estimates for single
light bins and pairs of heavy bins are explicit; the numerical
certificate and physical pattern arguments supply them separately.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- The two endpoint coefficients count every demanded type twice. -/
theorem subtwo_endpoint_weighted_mean (demand price : G.E → ℝ)
    (B : G.SubtwoLocalFractionalBins demand) (coeff : G.V → G.E → ℝ)
    (hsplit : ∀ e, coeff (G.fst e) e + coeff (G.snd e) e = 2) :
    (∑ v, ∑ p, B.mass v p *
      (∑ e, coeff v e * price e * (B.pattern v p e : ℝ))) =
      2 * ∑ e, price e * demand e := by
  classical
  have hv (v : G.V) :
      (∑ p, B.mass v p * (∑ e, coeff v e * price e * (B.pattern v p e : ℝ))) =
        ∑ e, if G.Inc v e then coeff v e * price e * demand e else 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    calc
      _ = coeff v e * price e * (∑ p, B.mass v p * (B.pattern v p e : ℝ)) := by
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
    _ = ∑ v, ((if v = G.fst e then coeff v e * price e * demand e else 0) +
        (if v = G.snd e then coeff v e * price e * demand e else 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hf : v = G.fst e <;> by_cases hs : v = G.snd e
      · exact False.elim (G.noLoop e (hf.symm.trans hs))
      · simp [Inc, hf, G.noLoop e, eq_comm]
      · simp [Inc, hs, G.noLoop e, eq_comm]
      · simp [Inc, hf, hs, eq_comm]
    _ = (coeff (G.fst e) e + coeff (G.snd e) e) * price e * demand e := by
      rw [Finset.sum_add_distrib]
      simp
      ring
    _ = _ := by rw [hsplit]; ring

/-- Actual local bins satisfy the full endpoint averaging theorem. -/
theorem subtwo_local_endpoint_score_bound (demand : G.E → ℝ)
    (B : G.SubtwoLocalFractionalBins demand) (P : G.V → ℝ)
    (score : G.V → B.P → ℝ)
    (hP : ∀ v, 0 ≤ P v) (htotal : ∀ v, (∑ p, B.mass v p) ≤ 1)
    (hsupport : ∀ v p e, ¬G.Inc v e → B.pattern v p e = 0)
    (hlight : ∀ v p, (∀ e, B.pattern v p e ≠ 0 → G.weight e ≤ 1 / 2) →
      score v p ≤ P v)
    (hheavy : ∀ e p q, (1 / 2 : ℝ) < G.weight e →
      B.pattern (G.fst e) p e = 1 → B.pattern (G.snd e) q e = 1 →
      score (G.fst e) p + score (G.snd e) q ≤ P (G.fst e) + P (G.snd e)) :
    (∑ v, ∑ p, B.mass v p * score v p) ≤ ∑ v, P v := by
  classical
  apply Subtwo.EndpointAveraging.endpoint_laws_bound
    G.fst G.snd P B.mass (fun v p ↦ G.subtwoHeavyTag (B.pattern v p)) score
    (fun e ↦ if (1 / 2 : ℝ) < G.weight e then demand e else 0)
    G.noLoop hP B.mass_nonneg htotal
  · intro v p e ht
    exact G.subtwoHeavyTag_incident v (B.pattern v p) (B.bin_feasible v p)
      (hsupport v p) e ht
  · intro v e
    by_cases he : (1 / 2 : ℝ) < G.weight e
    · dsimp only
      rw [if_pos he]
      exact B.heavyTag_mass G v e he
    · simp only [he, if_false, ite_self]
      exact B.lightTag_mass G v e (le_of_not_gt he)
  · intro v p ht _
    exact hlight v p ((G.subtwoHeavyTag_none_iff (B.pattern v p)).mp ht)
  · intro e p q htp htq _ _
    have hp := (G.subtwoHeavyTag_some_iff (B.pattern (G.fst e) p)
      (B.bin_feasible _ _) e).mp htp
    have hq := (G.subtwoHeavyTag_some_iff (B.pattern (G.snd e) q)
      (B.bin_feasible _ _) e).mp htq
    exact hheavy e p q hp.1
      (G.subtwo_heavy_count_eq_one e _ hp.1 hp.2 (B.bin_feasible _ _))
      (G.subtwo_heavy_count_eq_one e _ hq.1 hq.2 (B.bin_feasible _ _))

/-- The price objective is bounded by half the endpoint budget once the
two pointwise bin estimates have been supplied. -/
theorem subtwo_local_demand_price_of_endpoint_estimates (demand price : G.E → ℝ)
    (B : G.SubtwoLocalFractionalBins demand) (P : G.V → ℝ)
    (coeff : G.V → G.E → ℝ)
    (hsplit : ∀ e, coeff (G.fst e) e + coeff (G.snd e) e = 2)
    (hP : ∀ v, 0 ≤ P v) (htotal : ∀ v, (∑ p, B.mass v p) ≤ 1)
    (hsupport : ∀ v p e, ¬G.Inc v e → B.pattern v p e = 0)
    (hlight : ∀ v p, (∀ e, B.pattern v p e ≠ 0 → G.weight e ≤ 1 / 2) →
      (∑ e, coeff v e * price e * (B.pattern v p e : ℝ)) ≤ P v)
    (hheavy : ∀ e p q, (1 / 2 : ℝ) < G.weight e →
      B.pattern (G.fst e) p e = 1 → B.pattern (G.snd e) q e = 1 →
      (∑ f, coeff (G.fst e) f * price f * (B.pattern (G.fst e) p f : ℝ)) +
      (∑ f, coeff (G.snd e) f * price f * (B.pattern (G.snd e) q f : ℝ))
        ≤ P (G.fst e) + P (G.snd e)) :
    (∑ e, price e * demand e) ≤ (∑ v, P v) / 2 := by
  have h := G.subtwo_local_endpoint_score_bound demand B P
    (fun v p ↦ ∑ e, coeff v e * price e * (B.pattern v p e : ℝ))
    hP htotal hsupport hlight hheavy
  rw [G.subtwo_endpoint_weighted_mean demand price B coeff hsplit] at h
  linarith

end WeightedEdgeColoring.WeightedMultigraph
