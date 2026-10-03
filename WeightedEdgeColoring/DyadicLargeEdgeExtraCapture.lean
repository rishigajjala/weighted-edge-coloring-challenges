import WeightedEdgeColoring.DyadicLargeEdgeOptions
import WeightedEdgeColoring.LargeEdgeExtraCapture
import WeightedEdgeColoring.QuantizedMatchingProjection
import WeightedEdgeColoring.SumMatchingRestriction

/-!
# Capacity of selected locally dyadic extra options

A selected right-summand option consumes one local extra slot at each
endpoint.  Hence at most `B(v,h)` such jobs can be selected at a fixed
vertex and class.  For the dyadic local count this gives a weighted capture
bound with the fractional residual term and an additive reserve term.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

universe u w₁ w₂

variable (G : WeightedSimpleGraph.{u})
variable {Color : Type w₁} {Class : Type w₂}
  [Fintype Color] [DecidableEq Color]
  [Fintype Class] [DecidableEq Class]

def selectedDyadicExtraBaseOptions
    (K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))) :
    Finset (DivisibleLocalExtraChoice G.E G.V Class G.fst G.snd bucket
      (G.graphDyadicExtraSlotCount bucket residual gamma reserve)) :=
  RankThreeOptionSystem.rightOptionSet
    (RankThreeOptionSystem.baseOptionSet N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M)

theorem selectedDyadicExtraBaseOptions_isPartialMatching
    (K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (hM : ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).IsPartialMatching M) :
    (DivisibleLocalExtraChoice.system G.fst G.snd bucket
      (G.graphDyadicExtraSlotCount bucket residual gamma reserve)
      (G.graphDyadic_left_dvd_support bucket residual gamma reserve)
      (G.graphDyadic_right_dvd_support bucket residual gamma reserve)).IsPartialMatching
      (G.selectedDyadicExtraBaseOptions K N bucket gamma reserve residual x M) := by
  let Hord : RankThreeOptionSystem G.E (OrdinarySlot G.V Color K)
      (OrdinarySlotChoice G.E Color K) :=
    OrdinarySlotChoice.system G.fst G.snd K
  let Hextra := DivisibleLocalExtraChoice.system G.fst G.snd bucket
    (G.graphDyadicExtraSlotCount bucket residual gamma reserve)
    (G.graphDyadic_left_dvd_support bucket residual gamma reserve)
    (G.graphDyadic_right_dvd_support bucket residual gamma reserve)
  let mass := G.dyadicLargeEdgeMass K bucket gamma reserve residual x
  let base := RankThreeOptionSystem.baseOptionSet N mass M
  have hbase : (Hord.separatedSum Hextra).IsPartialMatching base :=
    (Hord.separatedSum Hextra).baseOptionSet_isPartialMatching N mass M hM
  exact Hord.separatedSum_rightOptionSet_isPartialMatching Hextra base hbase

def selectedDyadicExtraEdges
    (K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))) : Finset G.E :=
  (G.selectedDyadicExtraBaseOptions K N bucket gamma reserve residual x M).image
    Sigma.fst

def divisibleExtraSlotAt
    (bucket : G.E → Class) (B : G.V → Class → ℕ) (v : G.V)
    (hleftDiv : ∀ e, B (G.fst e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)
    (hrightDiv : ∀ e, B (G.snd e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)
    (p : DivisibleLocalExtraChoice G.E G.V Class G.fst G.snd bucket B) :
    ExtraSlot G.V Class B :=
  if G.fst p.1 = v then
    DivisibleLocalExtraChoice.leftSlot G.fst G.snd bucket B hleftDiv p
  else
    DivisibleLocalExtraChoice.rightSlot G.fst G.snd bucket B hrightDiv p

theorem divisibleExtraSlotAt_mem_slots
    (bucket : G.E → Class) (B : G.V → Class → ℕ) (v : G.V)
    (hleftDiv : ∀ e, B (G.fst e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)
    (hrightDiv : ∀ e, B (G.snd e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)
    (p : DivisibleLocalExtraChoice G.E G.V Class G.fst G.snd bucket B)
    (hinc : G.Inc v p.1) :
    G.divisibleExtraSlotAt bucket B v hleftDiv hrightDiv p ∈
      (DivisibleLocalExtraChoice.system G.fst G.snd bucket B
        hleftDiv hrightDiv).slots p := by
  rcases hinc with hleft | hright
  · simp [divisibleExtraSlotAt, hleft.symm, DivisibleLocalExtraChoice.system]
  · have hne : G.fst p.1 ≠ v := by
      intro h
      exact G.noLoop p.1 (h.trans hright.symm)
    simp [divisibleExtraSlotAt, hne, DivisibleLocalExtraChoice.system]

theorem divisibleExtraSlotAt_fst
    (bucket : G.E → Class) (B : G.V → Class → ℕ) (v : G.V)
    (hleftDiv : ∀ e, B (G.fst e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)
    (hrightDiv : ∀ e, B (G.snd e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)
    (p : DivisibleLocalExtraChoice G.E G.V Class G.fst G.snd bucket B)
    (hinc : G.Inc v p.1) :
    (G.divisibleExtraSlotAt bucket B v hleftDiv hrightDiv p).1 =
      (v, bucket p.1) := by
  rcases hinc with hleft | hright
  · simp [divisibleExtraSlotAt, hleft.symm,
      DivisibleLocalExtraChoice.leftSlot]
  · have hne : G.fst p.1 ≠ v := by
      intro h
      exact G.noLoop p.1 (h.trans hright.symm)
    simp [divisibleExtraSlotAt, hne, hright,
      DivisibleLocalExtraChoice.rightSlot]

theorem divisibleExtraMatching_card_inc_bucket_le
    (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (hleftDiv : ∀ e, B (G.fst e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)
    (hrightDiv : ∀ e, B (G.snd e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)
    (X : Finset (DivisibleLocalExtraChoice G.E G.V Class
      G.fst G.snd bucket B))
    (hX : (DivisibleLocalExtraChoice.system G.fst G.snd bucket B
      hleftDiv hrightDiv).IsPartialMatching X)
    (v : G.V) (h : Class) :
    (X.filter fun p ↦ G.Inc v p.1 ∧ bucket p.1 = h).card ≤ B v h := by
  classical
  let f := G.divisibleExtraSlotAt bucket B v hleftDiv hrightDiv
  have hcard :
      (X.filter fun p ↦ G.Inc v p.1 ∧ bucket p.1 = h).card ≤
        (G.extraSlotsAt B v h).card := by
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [G.divisibleExtraSlotAt_fst bucket B v hleftDiv hrightDiv p
        hp'.2.1, hp'.2.2]
    · intro p hp q hq hpq
      by_contra hne
      have hp' := Finset.mem_filter.mp hp
      have hq' := Finset.mem_filter.mp hq
      have hdis := hX.1 hp'.1 hq'.1 hne
      have hqmem := G.divisibleExtraSlotAt_mem_slots bucket B v
        hleftDiv hrightDiv q hq'.2.1
      change f q ∈
        (DivisibleLocalExtraChoice.system G.fst G.snd bucket B
          hleftDiv hrightDiv).slots q at hqmem
      rw [← hpq] at hqmem
      have hpmem : f p ∈
          (DivisibleLocalExtraChoice.system G.fst G.snd bucket B
            hleftDiv hrightDiv).slots p := by
        simpa [f] using
          (G.divisibleExtraSlotAt_mem_slots bucket B v hleftDiv hrightDiv p
            hp'.2.1)
      exact Finset.disjoint_left.mp hdis
        hpmem hqmem
  simpa using hcard

theorem divisibleExtraMatching_starWeight_le
    (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (hleftDiv : ∀ e, B (G.fst e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)
    (hrightDiv : ∀ e, B (G.snd e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)
    (X : Finset (DivisibleLocalExtraChoice G.E G.V Class
      G.fst G.snd bucket B))
    (hX : (DivisibleLocalExtraChoice.system G.fst G.snd bucket B
      hleftDiv hrightDiv).IsPartialMatching X)
    (upper : Class → ℝ) (hupper0 : ∀ h, 0 ≤ upper h)
    (hweight : ∀ e, G.weight e ≤ upper (bucket e)) (v : G.V) :
    (∑ p ∈ X.filter (fun p ↦ G.Inc v p.1), G.weight p.1) ≤
      ∑ h, (B v h : ℕ) * upper h := by
  classical
  have hsplit :
      (∑ p ∈ X.filter (fun p ↦ G.Inc v p.1), G.weight p.1) =
        ∑ h, ∑ p ∈ X.filter
          (fun p ↦ G.Inc v p.1 ∧ bucket p.1 = h), G.weight p.1 := by
    calc
      _ = ∑ p ∈ X, if G.Inc v p.1 then G.weight p.1 else 0 := by
        rw [Finset.sum_filter]
      _ = ∑ p ∈ X, ∑ h,
          if G.Inc v p.1 ∧ bucket p.1 = h then G.weight p.1 else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hinc : G.Inc v p.1 <;> simp [hinc]
      _ = ∑ h, ∑ p ∈ X,
          if G.Inc v p.1 ∧ bucket p.1 = h then G.weight p.1 else 0 := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [← Finset.sum_filter]
  rw [hsplit]
  apply Finset.sum_le_sum
  intro h _
  calc
    (∑ p ∈ X.filter (fun p ↦ G.Inc v p.1 ∧ bucket p.1 = h),
        G.weight p.1) ≤
        ∑ _p ∈ X.filter (fun p ↦ G.Inc v p.1 ∧ bucket p.1 = h),
          upper h := by
      apply Finset.sum_le_sum
      intro p hp
      simpa [(Finset.mem_filter.mp hp).2.2] using hweight p.1
    _ = ((X.filter fun p ↦ G.Inc v p.1 ∧ bucket p.1 = h).card : ℝ) *
        upper h := by simp
    _ ≤ (B v h : ℕ) * upper h := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast G.divisibleExtraMatching_card_inc_bucket_le bucket B
          hleftDiv hrightDiv X hX v h
      · exact hupper0 h

theorem selectedDyadicExtraEdges_starWeight_eq
    (K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (hM : ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).IsPartialMatching M)
    (v : G.V) :
    (∑ e ∈ (G.selectedDyadicExtraEdges K N bucket gamma reserve residual x M).filter
        (G.Inc v), G.weight e) =
      ∑ p ∈ (G.selectedDyadicExtraBaseOptions K N bucket gamma reserve
        residual x M).filter (fun p ↦ G.Inc v p.1), G.weight p.1 := by
  classical
  let X := G.selectedDyadicExtraBaseOptions K N bucket gamma reserve residual x M
  have hX := G.selectedDyadicExtraBaseOptions_isPartialMatching
    K N bucket gamma reserve residual x M hM
  have hset :
      (G.selectedDyadicExtraEdges K N bucket gamma reserve residual x M).filter
          (G.Inc v) =
        (X.filter fun p ↦ G.Inc v p.1).image
          (fun p : DivisibleLocalExtraChoice G.E G.V Class G.fst G.snd bucket
            (G.graphDyadicExtraSlotCount bucket residual gamma reserve) ↦ p.1) := by
    ext e
    simp [selectedDyadicExtraEdges, X]
  have hinj : Set.InjOn
      (fun p : DivisibleLocalExtraChoice G.E G.V Class G.fst G.snd bucket
        (G.graphDyadicExtraSlotCount bucket residual gamma reserve) ↦ p.1)
      ((X.filter fun p ↦ G.Inc v p.1 : Finset _) : Set _) := by
    intro p hp q hq hpq
    exact hX.2 (Finset.mem_filter.mp hp).1
      (Finset.mem_filter.mp hq).1 hpq
  rw [hset, Finset.sum_image hinj]

/-- Final local-dyadic capture estimate.  The factor two is the harmless
rounding to a power of two. -/
theorem selectedDyadicExtraEdges_starWeight_le_weightedResidual
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
    (hratio : ∀ e, upper (bucket e) ≤ ratio * G.weight e) (v : G.V) :
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
  have hres := G.sum_upper_mul_classResidual_le_weightedResidualStar
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

end WeightedSimpleGraph

end

end WeightedEdgeColoring
