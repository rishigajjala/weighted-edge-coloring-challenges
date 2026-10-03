import WeightedEdgeColoring.SubtwoMixedGraphCandidateColumns

/-!
# Weighted column counts for mixed candidate rows

The packed-word selector needs a column bound independent of the raw number
of tiny edges.  Each tiny coefficient carries its edge weight; a large edge
has weight at least `β`, so its unit coefficient costs at most `weight/β`.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)

theorem sum_sigma_endpointPair_le_coeff
    {A : G.V → Type*} [∀ v, Fintype (A v)]
    (K coeff : ℝ) (hcoeff : 0 ≤ coeff)
    (hcard : ∀ v, (Fintype.card (A v) : ℝ) ≤ K)
    (source : G.V) (e : G.E) (f : (Σ v, A v) → ℝ)
    (hunit : ∀ x, f x ≤ coeff)
    (hsupp : ∀ x, ¬G.EndpointPairMatches x.1 source e → f x = 0) :
    (∑ x, f x) ≤ if G.Inc source e then K * coeff else 0 := by
  classical
  rw [Fintype.sum_sigma]
  by_cases hfst : source = G.fst e
  · subst source
    have hsnd : G.snd e ≠ G.fst e := (G.noLoop e).symm
    simp only [WeightedMultigraph.Inc, eq_self, true_or, if_true]
    calc
      (∑ v, ∑ a : A v, f ⟨v, a⟩) =
          ∑ a : A (G.snd e), f ⟨G.snd e, a⟩ := by
        apply Fintype.sum_eq_single (G.snd e)
        intro v hv
        apply Finset.sum_eq_zero
        intro a _
        exact hsupp ⟨v, a⟩ (by simp [EndpointPairMatches, hv, G.noLoop e])
      _ ≤ ∑ _a : A (G.snd e), coeff :=
        Finset.sum_le_sum fun a _ ↦ hunit ⟨G.snd e, a⟩
      _ = (Fintype.card (A (G.snd e)) : ℝ) * coeff := by simp
      _ ≤ K * coeff := mul_le_mul_of_nonneg_right (hcard _) hcoeff
  · by_cases hsnd : source = G.snd e
    · subst source
      simp only [WeightedMultigraph.Inc, eq_self, or_true, if_true]
      calc
        (∑ v, ∑ a : A v, f ⟨v, a⟩) =
            ∑ a : A (G.fst e), f ⟨G.fst e, a⟩ := by
          apply Fintype.sum_eq_single (G.fst e)
          intro v hv
          apply Finset.sum_eq_zero
          intro a _
          exact hsupp ⟨v, a⟩ (by simp [EndpointPairMatches, hv, hfst])
        _ ≤ ∑ _a : A (G.fst e), coeff :=
          Finset.sum_le_sum fun a _ ↦ hunit ⟨G.fst e, a⟩
        _ = (Fintype.card (A (G.fst e)) : ℝ) * coeff := by simp
        _ ≤ K * coeff := mul_le_mul_of_nonneg_right (hcard _) hcoeff
    · have hnone : ¬G.Inc source e := by
        simp [WeightedMultigraph.Inc, Ne.symm hfst, Ne.symm hsnd]
      rw [if_neg hnone]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro v _
      apply Finset.sum_eq_zero
      intro a _
      exact hsupp ⟨v, a⟩ (by simp [EndpointPairMatches, hfst, hsnd])

end WeightedMultigraph

end

end WeightedEdgeColoring
