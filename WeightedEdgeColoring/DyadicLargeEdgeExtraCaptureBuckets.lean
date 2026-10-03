import WeightedEdgeColoring.DyadicLargeEdgeExtraCapture
import WeightedEdgeColoring.LargeEdgeExtraCaptureDyadic

/-!
# Dyadic capture for a residual supported on large edges

The local-dyadic construction deliberately sets the residual to zero on
small edges.  The usual comparison between a dyadic bucket endpoint and
twice the edge weight is therefore needed only on the support of the
residual.  This file records that support-sensitive form and specializes it
to the least dyadic bucket map.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

universe u w

variable (G : WeightedSimpleGraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]

/-- A class-upper estimate needs the ratio hypothesis only where the
residual is positive. -/
theorem sum_upper_mul_classResidual_le_weightedResidualStar_of_support
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (hr0 : ∀ e, 0 ≤ residual e)
    (upper : Class → ℝ) (ratio : ℝ)
    (hratio : ∀ e, 0 < residual e →
      upper (bucket e) ≤ ratio * G.weight e)
    (v : G.V) :
    (∑ h, upper h * G.classResidual bucket residual v h) ≤
      ratio * G.weightedResidualStar residual v := by
  rw [G.sum_upper_mul_classResidual_eq bucket residual upper v]
  unfold weightedResidualStar
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _he
  by_cases hinc : G.Inc v e
  · simp only [if_pos hinc]
    by_cases hzero : residual e = 0
    · simp [hzero]
    · have hpos : 0 < residual e := lt_of_le_of_ne (hr0 e) (Ne.symm hzero)
      calc
        residual e * upper (bucket e) ≤
            residual e * (ratio * G.weight e) :=
          mul_le_mul_of_nonneg_left (hratio e hpos) (hr0 e)
        _ = ratio * (residual e * G.weight e) := by ring
  · simp [hinc]

/-- The local power-of-two capture estimate with a support-sensitive ratio
hypothesis. -/
theorem selectedDyadicExtraEdges_starWeight_le_weightedResidual_of_support
    {Color : Type*} [Fintype Color] [DecidableEq Color]
    (K N : ℕ) (bucket : G.E → Class) (gamma ratio : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (hM : ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).IsPartialMatching M)
    (hr0 : ∀ e, 0 ≤ residual e) (hreserve : 0 < reserve)
    (hgamma1 : gamma < 1)
    (upper : Class → ℝ) (hupper0 : ∀ h, 0 ≤ upper h)
    (hweight : ∀ e, G.weight e ≤ upper (bucket e))
    (hratio : ∀ e, 0 < residual e →
      upper (bucket e) ≤ ratio * G.weight e) (v : G.V) :
    (∑ e ∈ (G.selectedDyadicExtraEdges K N bucket gamma reserve residual x M).filter
        (G.Inc v), G.weight e) ≤
      2 * ratio * G.weightedResidualStar residual v / (1 - gamma) +
        2 * (1 + (reserve : ℝ)) * ∑ h, upper h := by
  rw [G.selectedDyadicExtraEdges_starWeight_eq K N bucket gamma reserve
    residual x M hM v]
  have hX := G.selectedDyadicExtraBaseOptions_isPartialMatching
    K N bucket gamma reserve residual x M hM
  have hcapacity := G.divisibleExtraMatching_starWeight_le bucket
    (G.graphDyadicExtraSlotCount bucket residual gamma reserve)
    (G.graphDyadic_left_dvd_support bucket residual gamma reserve)
    (G.graphDyadic_right_dvd_support bucket residual gamma reserve)
    (G.selectedDyadicExtraBaseOptions K N bucket gamma reserve residual x M)
    hX upper hupper0 hweight v
  have hgap : 0 < 1 - gamma := sub_pos.mpr hgamma1
  have hres :=
    G.sum_upper_mul_classResidual_le_weightedResidualStar_of_support
      bucket residual hr0 upper ratio hratio v
  have hdecomp :
      (∑ h, 2 *
        (G.classResidual bucket residual v h / (1 - gamma) +
          1 + reserve) * upper h) =
        2 * (∑ h, upper h * G.classResidual bucket residual v h) /
            (1 - gamma) +
          2 * (1 + (reserve : ℝ)) * ∑ h, upper h := by
    have hterm : ∀ h : Class,
        2 * (G.classResidual bucket residual v h / (1 - gamma) +
          1 + reserve) * upper h =
        2 * (upper h * G.classResidual bucket residual v h) /
            (1 - gamma) +
          2 * (1 + (reserve : ℝ)) * upper h := by
      intro h
      ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_div, ← Finset.mul_sum]
    · rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ h,
        (G.graphDyadicExtraSlotCount bucket residual gamma reserve v h : ℕ) *
          upper h := hcapacity
    _ ≤ ∑ h, 2 *
        (G.classResidual bucket residual v h / (1 - gamma) +
          1 + reserve) * upper h := by
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul_of_nonneg_right
        (G.graphDyadicExtraSlotCount_cast_le bucket residual hr0 gamma
          hreserve hgamma1 v h) (hupper0 h)
    _ = 2 * (∑ h, upper h * G.classResidual bucket residual v h) /
          (1 - gamma) +
        2 * (1 + (reserve : ℝ)) * ∑ h, upper h := hdecomp
    _ ≤ 2 * ratio * G.weightedResidualStar residual v / (1 - gamma) +
        2 * (1 + (reserve : ℝ)) * ∑ h, upper h := by
      apply add_le_add
      · apply div_le_div_of_nonneg_right _ hgap.le
        calc
          2 * (∑ h, upper h * G.classResidual bucket residual v h) ≤
              2 * (ratio * G.weightedResidualStar residual v) :=
            mul_le_mul_of_nonneg_left hres (by norm_num)
          _ = 2 * ratio * G.weightedResidualStar residual v := by ring
      · exact le_rfl

/-- Concrete dyadic estimate for a residual supported on `beta`-large
edges.  The power-of-two local coupling costs the leading factor four and
an additive `8(1+reserve)` when the top dyadic scale is at most two. -/
theorem selectedDyadicExtraEdges_starWeight_le_dyadic_support
    {Color : Type*} [Fintype Color] [DecidableEq Color]
    (K N : ℕ) (beta : ℝ) (L : ℕ) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K (dyadicBucket beta L G.weight) gamma reserve
        residual x)))
    (hM : ((G.dyadicLargeEdgeOptionSystem K
      (dyadicBucket beta L G.weight) gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K (dyadicBucket beta L G.weight) gamma reserve
        residual x)).IsPartialMatching M)
    (hbeta : 0 < beta) (hcover : 1 ≤ dyadicScale beta L)
    (htop : dyadicScale beta L ≤ 2)
    (hr0 : ∀ e, 0 ≤ residual e)
    (hsupport : ∀ e, 0 < residual e → beta ≤ G.weight e)
    (hreserve : 0 < reserve) (hgamma1 : gamma < 1) (v : G.V) :
    (∑ e ∈ (G.selectedDyadicExtraEdges K N
      (dyadicBucket beta L G.weight) gamma reserve residual x M).filter
        (G.Inc v), G.weight e) ≤
      4 * G.weightedResidualStar residual v / (1 - gamma) +
        8 * (1 + (reserve : ℝ)) := by
  have hbase :=
    G.selectedDyadicExtraEdges_starWeight_le_weightedResidual_of_support
      K N (dyadicBucket beta L G.weight) gamma 2 reserve residual x M hM
      hr0 hreserve hgamma1 (dyadicUpper beta)
      (fun h ↦ dyadicUpper_nonneg hbeta.le h)
      (fun e ↦ weight_le_dyadicUpper_bucket beta L G.weight hcover
        (fun f _ ↦ G.weight_le_one f) (Finset.mem_univ e))
      (fun e he ↦ dyadicUpper_bucket_le_two_mul beta L G.weight hbeta
        hcover (fun f hf ↦ by
          have hfe : f = e := Finset.mem_singleton.mp hf
          subst f
          exact hsupport e he)
        (fun f _ ↦ G.weight_le_one f) (by simp : e ∈ ({e} : Finset G.E))) v
  have hsum := sum_dyadicUpper_le_two_mul_top hbeta.le L
  have hsum4 : (∑ h : Fin (L + 1), dyadicUpper beta h) ≤ 4 :=
    hsum.trans (by nlinarith)
  have hreserve0 : 0 ≤ 2 * (1 + (reserve : ℝ)) := by positivity
  have hbase' :
      (∑ e ∈ (G.selectedDyadicExtraEdges K N
        (dyadicBucket beta L G.weight) gamma reserve residual x M).filter
          (G.Inc v), G.weight e) ≤
        4 * G.weightedResidualStar residual v / (1 - gamma) +
          2 * (1 + (reserve : ℝ)) *
            ∑ h : Fin (L + 1), dyadicUpper beta h := by
    convert hbase using 1 <;> ring
  exact hbase'.trans (add_le_add le_rfl (by
    have := mul_le_mul_of_nonneg_left hsum4 hreserve0
    nlinarith))

end WeightedSimpleGraph

end

end WeightedEdgeColoring
