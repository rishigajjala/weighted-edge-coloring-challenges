import WeightedEdgeColoring.MultigraphDyadicLargeEdgeExtraCaptureBuckets
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeTotalLoss

/-!
# Filtered local-dyadic extra capture

A Boolean bank in the bucket type separates retained and discarded jobs.
The matching may use both banks, but the estimate below sums only the true
bank.  Consequently its fractional term contains only the correspondingly
masked residual, while the rounding reserve pays for just the true classes.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})
variable {Color : Type*} [Fintype Color] [DecidableEq Color]
variable {Class : Type w} [Fintype Class] [DecidableEq Class]

def boolBucketResidual (bucket : G.E → Bool × Class)
    (residual : G.E → ℝ) (e : G.E) : ℝ :=
  if (bucket e).1 then residual e else 0

/-- If a retained set lies in the large jobs and in the true bucket bank,
then every retained job missed by the ordinary matching is either uncovered
or is a selected extra job in that same true bank. -/
theorem retainedDyadicRemainingStarWeight_le_uncovered_add_trueExtra
    (K N : ℕ) (beta : ℝ) (bucket : G.E → Bool × Class)
    (gamma : ℝ) (reserve : ℕ) (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (hM : ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized
      N (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).IsPartialMatching M)
    (retained : Finset G.E)
    (hlarge : retained ⊆ G.largeEdgeJobs beta)
    (htrue : ∀ e ∈ retained, (bucket e).1 = true)
    (v : G.V) :
    (∑ e ∈ retained \ G.selectedDyadicOrdinaryEdges K N bucket gamma reserve
        residual x M, if G.Inc v e then G.weight e else 0) ≤
      G.uncoveredLargeStarWeight
        ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized
          N (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))
        beta M v +
      ∑ e ∈ (G.selectedDyadicExtraEdges K N bucket gamma reserve
          residual x M).filter
            (fun e ↦ G.Inc v e ∧ (bucket e).1 = true), G.weight e := by
  classical
  let H := (G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized
    N (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)
  let O := G.selectedDyadicOrdinaryEdges K N bucket gamma reserve residual x M
  let U := (G.uncoveredLargeEdges H beta M).filter (G.Inc v)
  let X := (G.selectedDyadicExtraEdges K N bucket gamma reserve residual x M).filter
    (fun e ↦ G.Inc v e ∧ (bucket e).1 = true)
  have hsub : ((retained \ O).filter (G.Inc v)) ⊆ U ∪ X := by
    intro e he
    have he' := Finset.mem_filter.mp he
    have her := Finset.mem_sdiff.mp he'.1
    by_cases hc : H.Covers M e
    · rcases G.mem_selectedDyadicOrdinary_or_extra_of_covers
        K N bucket gamma reserve residual x M hc with ho | hx
      · exact (her.2 ho).elim
      · exact Finset.mem_union_right U (Finset.mem_filter.mpr
          ⟨hx, he'.2, htrue e her.1⟩)
    · exact Finset.mem_union_left X (Finset.mem_filter.mpr
        ⟨(G.mem_uncoveredLargeEdges H).mpr
          ⟨G.mem_largeEdgeJobs.mp (hlarge her.1), hc⟩, he'.2⟩)
  have hdis : Disjoint U X := by
    rw [Finset.disjoint_left]
    intro e heU heX
    have hu := (G.mem_uncoveredLargeEdges H).mp (Finset.mem_filter.mp heU).1
    have hx := (Finset.mem_filter.mp heX).1
    exact hu.2 (G.dyadic_covers_of_mem_selectedExtraEdges
      K N bucket gamma reserve residual x M hx)
  calc
    (∑ e ∈ retained \ O, if G.Inc v e then G.weight e else 0) =
        ∑ e ∈ (retained \ O).filter (G.Inc v), G.weight e := by
          rw [Finset.sum_filter]
    _ ≤ ∑ e ∈ U ∪ X, G.weight e :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun e _ _ ↦ G.weight_nonneg e)
    _ = (∑ e ∈ U, G.weight e) + ∑ e ∈ X, G.weight e := by
      rw [Finset.sum_union hdis]
    _ = G.uncoveredLargeStarWeight H beta M v +
        ∑ e ∈ X, G.weight e := by
      rfl

/-- Selected extra weight in the true bank is controlled only by true-bank
residual mass. -/
theorem selectedDyadicExtraEdges_trueBank_le_weightedResidual
    (K N : ℕ) (bucket : G.E → Bool × Class)
    (gamma ratio : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (hM : ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized
      N (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).IsPartialMatching M)
    (hr0 : ∀ e, 0 ≤ residual e) (hreserve : 0 < reserve)
    (hgamma1 : gamma < 1)
    (upper : Class → ℝ) (hupper0 : ∀ h, 0 ≤ upper h)
    (hweight : ∀ e, G.weight e ≤ upper (bucket e).2)
    (hratio : ∀ e, (bucket e).1 = true → 0 < residual e →
      upper (bucket e).2 ≤ ratio * G.weight e)
    (v : G.V) :
    (∑ e ∈ (G.selectedDyadicExtraEdges K N bucket gamma reserve
        residual x M).filter (fun e ↦ G.Inc v e ∧ (bucket e).1 = true),
      G.weight e) ≤
      2 * ratio * G.weightedResidualStar
        (G.boolBucketResidual bucket residual) v / (1 - gamma) +
      2 * (1 + (reserve : ℝ)) * ∑ h, upper h := by
  classical
  let B := G.boundedDyadicExtraSlotCount bucket residual gamma reserve
  let X := G.selectedDyadicExtraBaseOptions K N bucket gamma reserve
    residual x M
  have hX := G.selectedDyadicExtraBaseOptions_isPartialMatching
    K N bucket gamma reserve residual x M hM
  have hedgeToOption :
      (∑ e ∈ (G.selectedDyadicExtraEdges K N bucket gamma reserve
          residual x M).filter
            (fun e ↦ G.Inc v e ∧ (bucket e).1 = true), G.weight e) =
        ∑ p ∈ X.filter
            (fun p ↦ G.Inc v p.1 ∧ (bucket p.1).1 = true),
          G.weight p.1 := by
    let f : DivisibleLocalExtraChoice G.E G.V (Bool × Class)
        G.fst G.snd bucket B → G.E := fun p ↦ p.1
    have hset :
        (G.selectedDyadicExtraEdges K N bucket gamma reserve residual x M).filter
            (fun e ↦ G.Inc v e ∧ (bucket e).1 = true) =
          (X.filter (fun p ↦
            G.Inc v p.1 ∧ (bucket p.1).1 = true)).image f := by
      ext e
      simp [selectedDyadicExtraEdges, X, f] <;> tauto
    have hinj : Set.InjOn f
        ((X.filter (fun p ↦
          G.Inc v p.1 ∧ (bucket p.1).1 = true) : Finset _) : Set _) := by
      intro p hp q hq hpq
      exact hX.2 (Finset.mem_filter.mp hp).1
        (Finset.mem_filter.mp hq).1 hpq
    rw [hset, Finset.sum_image hinj]
  rw [hedgeToOption]
  have hsplit :
      (∑ p ∈ X.filter
          (fun p ↦ G.Inc v p.1 ∧ (bucket p.1).1 = true),
          G.weight p.1) =
        ∑ h : Class, ∑ p ∈ X.filter (fun p ↦
          G.Inc v p.1 ∧ bucket p.1 = (true, h)), G.weight p.1 := by
    calc
      _ = ∑ p ∈ X, if G.Inc v p.1 ∧ (bucket p.1).1 = true then
          G.weight p.1 else 0 := by rw [Finset.sum_filter]
      _ = ∑ p ∈ X, ∑ h : Class,
          if G.Inc v p.1 ∧ bucket p.1 = (true, h) then
            G.weight p.1 else 0 := by
        apply Finset.sum_congr rfl
        intro p _hp
        rcases hbucket : bucket p.1 with ⟨flag, h⟩
        cases flag with
        | false => simp [hbucket]
        | true =>
            by_cases hinc : G.Inc v p.1 <;> simp [hbucket, hinc]
      _ = ∑ h : Class, ∑ p ∈ X,
          if G.Inc v p.1 ∧ bucket p.1 = (true, h) then
            G.weight p.1 else 0 := by rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h _hh
        rw [← Finset.sum_filter]
  rw [hsplit]
  have hcapacity :
      (∑ h : Class, ∑ p ∈ X.filter (fun p ↦
          G.Inc v p.1 ∧ bucket p.1 = (true, h)), G.weight p.1) ≤
        ∑ h : Class, (B v (true, h) : ℕ) * upper h := by
    apply Finset.sum_le_sum
    intro h _hh
    calc
      (∑ p ∈ X.filter (fun p ↦
          G.Inc v p.1 ∧ bucket p.1 = (true, h)), G.weight p.1) ≤
        ∑ _p ∈ X.filter (fun p ↦
          G.Inc v p.1 ∧ bucket p.1 = (true, h)), upper h := by
            apply Finset.sum_le_sum
            intro p hp
            simpa [(Finset.mem_filter.mp hp).2.2] using hweight p.1
      _ = ((X.filter (fun p ↦
          G.Inc v p.1 ∧ bucket p.1 = (true, h))).card : ℝ) * upper h := by simp
      _ ≤ (B v (true, h) : ℕ) * upper h := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast G.divisibleExtraMatching_card_inc_bucket_le bucket B
            (G.boundedDyadic_left_dvd_support bucket residual gamma reserve)
            (G.boundedDyadic_right_dvd_support bucket residual gamma reserve)
            X hX v (true, h)
        · exact hupper0 h
  apply hcapacity.trans
  have hgap : 0 < 1 - gamma := sub_pos.mpr hgamma1
  have hcount : ∀ h : Class,
      ((B v (true, h) : ℕ) : ℝ) ≤
        2 * (G.boundedClassResidual bucket residual v (true, h) /
          (1 - gamma) + 1 + reserve) := by
    intro h
    exact G.boundedDyadicExtraSlotCount_cast_le bucket residual hr0 gamma
      hreserve hgamma1 v (true, h)
  have hclass :
      (∑ h : Class, upper h *
        G.boundedClassResidual bucket residual v (true, h)) ≤
      ratio * G.weightedResidualStar
        (G.boolBucketResidual bucket residual) v := by
    unfold boundedClassResidual weightedResidualStar boolBucketResidual
    calc
      (∑ h : Class, upper h *
        ∑ e, ((if (G.fst e, bucket e) = (v, (true, h)) then residual e else 0) +
          if (G.snd e, bucket e) = (v, (true, h)) then residual e else 0)) =
        ∑ e, if G.Inc v e ∧ (bucket e).1 = true then
          residual e * upper (bucket e).2 else 0 := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro e _he
            rcases hbucket : bucket e with ⟨flag, h⟩
            cases flag with
            | false => simp [hbucket]
            | true =>
                by_cases hl : G.fst e = v
                · have hs : G.snd e ≠ v := by
                    intro hs
                    exact G.noLoop e (hl.trans hs.symm)
                  simp [hbucket, WeightedMultigraph.Inc, hl, hs, mul_comm]
                · by_cases hs : G.snd e = v
                  · simp [hbucket, WeightedMultigraph.Inc, hl, hs, mul_comm]
                  · simp [hbucket, WeightedMultigraph.Inc, hl, hs]
      _ ≤ ∑ e, if G.Inc v e ∧ (bucket e).1 = true then
          ratio * (residual e * G.weight e) else 0 := by
            apply Finset.sum_le_sum
            intro e _he
            by_cases hboth : G.Inc v e ∧ (bucket e).1 = true
            · simp only [hboth, if_true]
              by_cases hzero : residual e = 0
              · simp [hzero]
              · have hpos : 0 < residual e :=
                  lt_of_le_of_ne (hr0 e) (Ne.symm hzero)
                calc
                  residual e * upper (bucket e).2 ≤
                      residual e * (ratio * G.weight e) :=
                    mul_le_mul_of_nonneg_left
                      (hratio e hboth.2 hpos) (hr0 e)
                  _ = ratio * (residual e * G.weight e) := by ring
            · simp [hboth]
      _ = ratio * ∑ e, if G.Inc v e then
          (if (bucket e).1 then residual e else 0) * G.weight e else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e _he
            by_cases hinc : G.Inc v e <;>
              cases hflag : (bucket e).1 <;> simp [hinc, hflag]
  calc
    (∑ h : Class, (B v (true, h) : ℕ) * upper h) ≤
        ∑ h : Class, 2 *
          (G.boundedClassResidual bucket residual v (true, h) /
            (1 - gamma) + 1 + reserve) * upper h := by
      apply Finset.sum_le_sum
      intro h _hh
      exact mul_le_mul_of_nonneg_right (hcount h) (hupper0 h)
    _ = 2 * (∑ h : Class, upper h *
          G.boundedClassResidual bucket residual v (true, h)) / (1 - gamma) +
        2 * (1 + (reserve : ℝ)) * ∑ h, upper h := by
      calc
        _ = ∑ h : Class,
            (2 * (upper h * G.boundedClassResidual bucket residual v (true, h)) /
                (1 - gamma) + 2 * (1 + (reserve : ℝ)) * upper h) := by
              apply Finset.sum_congr rfl
              intro h _hh
              ring
        _ = _ := by
              rw [Finset.sum_add_distrib, ← Finset.sum_div,
                ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * ratio * G.weightedResidualStar
          (G.boolBucketResidual bucket residual) v / (1 - gamma) +
        2 * (1 + (reserve : ℝ)) * ∑ h, upper h := by
      have hfirst :
          2 * (∑ h : Class, upper h *
              G.boundedClassResidual bucket residual v (true, h)) / (1 - gamma) ≤
            2 * ratio * G.weightedResidualStar
              (G.boolBucketResidual bucket residual) v / (1 - gamma) := by
        apply div_le_div_of_nonneg_right _ hgap.le
        calc
          2 * (∑ h : Class, upper h *
              G.boundedClassResidual bucket residual v (true, h)) ≤
              2 * (ratio * G.weightedResidualStar
                (G.boolBucketResidual bucket residual) v) :=
            mul_le_mul_of_nonneg_left hclass (by norm_num)
          _ = 2 * ratio * G.weightedResidualStar
                (G.boolBucketResidual bucket residual) v := by ring
      linarith

end WeightedMultigraph

end

end WeightedEdgeColoring
