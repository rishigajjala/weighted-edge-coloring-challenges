import WeightedEdgeColoring.DyadicWeightBuckets

/-!
# Dyadic extra-edge capture

This file specializes the abstract extra-slot capacity estimate to the
least dyadic bucket map.  The upper weight attached to bucket `i` is
`beta * 2^i`.  It is an upper bound for every edge in the bucket and, on
edges of weight at least `beta`, it is at most twice the edge weight.

The sum of all bucket upper bounds is a finite geometric series.  Thus the
additive reserve in the extra-slot construction is bounded independently of
the number of buckets: it is at most twice the top dyadic scale, times the
per-bucket reserve `1+t`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

/-- The upper weight assigned to a dyadic bucket. -/
def dyadicUpper (beta : ℝ) {L : ℕ} (h : Fin (L + 1)) : ℝ :=
  dyadicScale beta h.1

theorem dyadicUpper_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) {L : ℕ}
    (h : Fin (L + 1)) :
    0 ≤ dyadicUpper beta h := by
  simp [dyadicUpper, dyadicScale, hbeta]

/-- Every weight in `[beta,1]` is below the upper endpoint of its least
dyadic bucket. -/
theorem weight_le_dyadicUpper_bucket {α : Type*} {S : Finset α}
    (beta : ℝ) (L : ℕ) (weight : α → ℝ)
    (hcover : 1 ≤ dyadicScale beta L)
    (hupper : ∀ a ∈ S, weight a ≤ 1)
    {a : α} (ha : a ∈ S) :
    weight a ≤ dyadicUpper beta (dyadicBucket beta L weight a) := by
  exact dyadicBucket_spec beta L weight a
    (exists_dyadic_scale_cover beta L weight hcover a ha hupper)

/-- On weights at least `beta`, a dyadic bucket endpoint is at most twice
the weight assigned to that bucket. -/
theorem dyadicUpper_bucket_le_two_mul {α : Type*} {S : Finset α}
    (beta : ℝ) (L : ℕ) (weight : α → ℝ)
    (hbeta : 0 < beta) (hcover : 1 ≤ dyadicScale beta L)
    (hlower : ∀ a ∈ S, beta ≤ weight a)
    (hupper : ∀ a ∈ S, weight a ≤ 1)
    {a : α} (ha : a ∈ S) :
    dyadicUpper beta (dyadicBucket beta L weight a) ≤ 2 * weight a := by
  have hacover :=
    exists_dyadic_scale_cover beta L weight hcover a ha hupper
  by_cases hzero : (dyadicBucket beta L weight a).val = 0
  · simp [dyadicUpper, dyadicScale, hzero]
    linarith [hlower a ha]
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hjlt : j < (dyadicBucket beta L weight a).val := by
      omega
    have hl := dyadicScale_lt_of_lt_bucket beta L weight a hacover hjlt
    simp only [dyadicUpper, hj, dyadicScale, pow_succ]
    rw [dyadicScale] at hl
    nlinarith

/-- The sum of the dyadic upper endpoints is the usual geometric sum. -/
theorem sum_dyadicUpper_eq (beta : ℝ) (L : ℕ) :
    (∑ h : Fin (L + 1), dyadicUpper beta h) =
      beta * ((2 : ℝ) ^ (L + 1) - 1) := by
  rw [show (∑ h : Fin (L + 1), dyadicUpper beta h) =
      beta * ∑ i ∈ Finset.range (L + 1), (2 : ℝ) ^ i by
    calc
      (∑ h : Fin (L + 1), dyadicUpper beta h) =
          ∑ i ∈ Finset.range (L + 1), beta * (2 : ℝ) ^ i := by
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i hi
        simp [dyadicUpper, dyadicScale, Finset.mem_range.mp hi]
      _ = beta * ∑ i ∈ Finset.range (L + 1), (2 : ℝ) ^ i := by
        rw [Finset.mul_sum]]
  rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
  ring

/-- The whole geometric series is at most twice its last term. -/
theorem sum_dyadicUpper_le_two_mul_top {beta : ℝ} (hbeta : 0 ≤ beta)
    (L : ℕ) :
    (∑ h : Fin (L + 1), dyadicUpper beta h) ≤
      2 * dyadicScale beta L := by
  rw [sum_dyadicUpper_eq]
  unfold dyadicScale
  calc
    beta * ((2 : ℝ) ^ (L + 1) - 1) ≤
        beta * (2 : ℝ) ^ (L + 1) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (by norm_num)) hbeta
    _ = 2 * (beta * (2 : ℝ) ^ L) := by rw [pow_succ]; ring

/-- A positive base scale at most one has a dyadic top scale in `[1,2)`.
This justifies choosing `L` so that the reserve below is an absolute
`O(t+1)` term. -/
theorem exists_dyadic_scale_mem_Ico_one_two (beta : ℝ)
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) :
    ∃ L, 1 ≤ dyadicScale beta L ∧ dyadicScale beta L < 2 := by
  let L := Nat.find (exists_dyadic_scale_ge_one beta hbeta)
  have hcover : 1 ≤ dyadicScale beta L :=
    (Nat.find_spec (exists_dyadic_scale_ge_one beta hbeta))
  refine ⟨L, hcover, ?_⟩
  by_cases hL : L = 0
  · simpa [dyadicScale, hL] using
      lt_of_le_of_lt hbeta1 (by norm_num : (1 : ℝ) < 2)
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hL
    have hprev : dyadicScale beta j < 1 := by
      exact lt_of_not_ge (fun h ↦
        Nat.find_min (exists_dyadic_scale_ge_one beta hbeta)
          (by simpa [L, hj] using Nat.lt_succ_self j) h)
    rw [hj]
    rw [dyadicScale, pow_succ]
    rw [dyadicScale] at hprev
    nlinarith


end

end WeightedEdgeColoring
