import WeightedEdgeColoring.MultigraphDyadicLargeEdgeMatchingExtraction
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeExtraCapture
import WeightedEdgeColoring.BoundedMultiplicityLargeEdgeLossBridge

/-!
# Total large-edge loss for local dyadic extra options
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

universe u w₁ w₂

variable (G : WeightedMultigraph.{u})
variable {Color : Type w₁} {Class : Type w₂}
  [Fintype Color] [DecidableEq Color]
  [Fintype Class] [DecidableEq Class]

def selectedDyadicOrdinaryEdges
    (K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ) (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))) : Finset G.E :=
  (RankThreeOptionSystem.leftOptionSet
    (RankThreeOptionSystem.baseOptionSet N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M)).image
        OrdinarySlotChoice.job

@[simp] theorem mem_selectedDyadicOrdinaryEdges_iff
    (K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ) (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))) (e : G.E) :
    e ∈ G.selectedDyadicOrdinaryEdges K N bucket gamma reserve residual x M ↔
      ∃ o : OrdinarySlotChoice G.E Color K,
        Sum.inl o ∈ RankThreeOptionSystem.baseOptionSet N
          (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M ∧
        o.job = e := by
  simp [selectedDyadicOrdinaryEdges,
    RankThreeOptionSystem.mem_leftOptionSet_iff]

theorem dyadic_covers_of_mem_selectedOrdinaryEdges
    (K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ) (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))) {e : G.E}
    (he : e ∈ G.selectedDyadicOrdinaryEdges K N bucket gamma reserve
      residual x M) :
    ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).Covers M e := by
  rcases (G.mem_selectedDyadicOrdinaryEdges_iff K N bucket gamma reserve
    residual x M e).mp he with ⟨o, ho, rfl⟩
  rcases (RankThreeOptionSystem.mem_baseOptionSet_iff N
    (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M
    (Sum.inl o)).mp ho with ⟨q, hqM, hq⟩
  refine ⟨q, hqM, ?_⟩
  change (G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).owner
    q.1 = o.job
  rw [hq]
  rfl

theorem dyadic_covers_of_mem_selectedExtraEdges
    (K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ) (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))) {e : G.E}
    (he : e ∈ G.selectedDyadicExtraEdges K N bucket gamma reserve
      residual x M) :
    ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).Covers M e := by
  rcases Finset.mem_image.mp he with ⟨p, hp, rfl⟩
  have hpBase : Sum.inr p ∈ RankThreeOptionSystem.baseOptionSet N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M :=
    (RankThreeOptionSystem.mem_rightOptionSet_iff _ p).mp hp
  rcases (RankThreeOptionSystem.mem_baseOptionSet_iff N
    (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M
    (Sum.inr p)).mp hpBase with ⟨q, hqM, hq⟩
  refine ⟨q, hqM, ?_⟩
  change (G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).owner
    q.1 = p.1
  rw [hq]
  rfl

theorem mem_selectedDyadicOrdinary_or_extra_of_covers
    (K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ) (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))) {e : G.E}
    (he : ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).Covers M e) :
    e ∈ G.selectedDyadicOrdinaryEdges K N bucket gamma reserve residual x M ∨
      e ∈ G.selectedDyadicExtraEdges K N bucket gamma reserve residual x M := by
  rcases he with ⟨q, hqM, howner⟩
  have hbase : q.1 ∈ RankThreeOptionSystem.baseOptionSet N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M :=
    (RankThreeOptionSystem.mem_baseOptionSet_iff N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M q.1).mpr
        ⟨q, hqM, rfl⟩
  cases hq : q.1 with
  | inl o =>
      left
      apply (G.mem_selectedDyadicOrdinaryEdges_iff K N bucket gamma reserve
        residual x M e).mpr
      refine ⟨o, by simpa [hq] using hbase, ?_⟩
      change (G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).owner
        q.1 = e at howner
      simpa [hq] using howner
  | inr p =>
      right
      apply Finset.mem_image.mpr
      refine ⟨p, ?_, ?_⟩
      · apply (RankThreeOptionSystem.mem_rightOptionSet_iff _ p).mpr
        simpa [hq] using hbase
      · change (G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).owner
          q.1 = e at howner
        simpa [hq] using howner

theorem selectedDyadicOrdinaryEdges_disjoint_extra
    (K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ) (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (hM : ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).IsPartialMatching M) :
    Disjoint
      (G.selectedDyadicOrdinaryEdges K N bucket gamma reserve residual x M)
      (G.selectedDyadicExtraEdges K N bucket gamma reserve residual x M) := by
  rw [Finset.disjoint_left]
  intro e heOrd heExtra
  rcases (G.mem_selectedDyadicOrdinaryEdges_iff K N bucket gamma reserve
    residual x M e).mp heOrd with ⟨o, hoBase, hoe⟩
  rcases Finset.mem_image.mp heExtra with ⟨p, hpExtra, hpe⟩
  have hpBase : Sum.inr p ∈ RankThreeOptionSystem.baseOptionSet N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M :=
    (RankThreeOptionSystem.mem_rightOptionSet_iff _ p).mp hpExtra
  have hbaseM :=
    (G.dyadicLargeEdgeOptionSystem (Color := Color) K bucket gamma reserve
      residual).baseOptionSet_isPartialMatching N
        (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M hM
  have howner :
      (G.dyadicLargeEdgeOptionSystem (Color := Color) K bucket gamma reserve
        residual).owner
          (Sum.inl o) =
        (G.dyadicLargeEdgeOptionSystem (Color := Color) K bucket gamma reserve
          residual).owner
          (Sum.inr p) := by
    change o.job = p.1
    exact hoe.trans hpe.symm
  have := hbaseM.2 hoBase hpBase howner
  exact Sum.inl_ne_inr this

def dyadicLargeEdgesRemainingAfterOrdinary
    (K N : ℕ) (beta : ℝ) (bucket : G.E → Class) (gamma : ℝ)
    (reserve : ℕ) (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))) : Finset G.E :=
  G.largeEdgeJobs beta \
    G.selectedDyadicOrdinaryEdges K N bucket gamma reserve residual x M

theorem dyadicLargeEdgesRemainingAfterOrdinary_eq
    (K N : ℕ) (beta : ℝ) (bucket : G.E → Class) (gamma : ℝ)
    (reserve : ℕ) (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (hM : ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).IsPartialMatching M) :
    G.dyadicLargeEdgesRemainingAfterOrdinary K N beta bucket gamma reserve
        residual x M =
      G.uncoveredLargeEdges
        ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
          (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))
        beta M ∪
      (G.selectedDyadicExtraEdges K N bucket gamma reserve residual x M).filter
        (fun e ↦ beta ≤ G.weight e) := by
  classical
  ext e
  simp only [dyadicLargeEdgesRemainingAfterOrdinary, Finset.mem_sdiff,
    G.mem_largeEdgeJobs, G.mem_uncoveredLargeEdges, Finset.mem_union,
    Finset.mem_filter]
  let H := (G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
    (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)
  constructor
  · rintro ⟨heLarge, heNotOrdinary⟩
    by_cases heCovered : H.Covers M e
    · rcases G.mem_selectedDyadicOrdinary_or_extra_of_covers
        K N bucket gamma reserve residual x M heCovered with heOrd | heExtra
      · exact (heNotOrdinary heOrd).elim
      · exact Or.inr ⟨heExtra, heLarge⟩
    · exact Or.inl ⟨heLarge, heCovered⟩
  · rintro (⟨heLarge, heUncovered⟩ | ⟨heExtra, heLarge⟩)
    · refine ⟨heLarge, ?_⟩
      intro heOrd
      exact heUncovered (G.dyadic_covers_of_mem_selectedOrdinaryEdges
        K N bucket gamma reserve residual x M heOrd)
    · refine ⟨heLarge, ?_⟩
      intro heOrd
      exact Finset.disjoint_left.mp
        (G.selectedDyadicOrdinaryEdges_disjoint_extra
          K N bucket gamma reserve residual x M hM) heOrd heExtra

def dyadicLargeRemainingStarWeight
    (K N : ℕ) (beta : ℝ) (bucket : G.E → Class) (gamma : ℝ)
    (reserve : ℕ) (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (v : G.V) : ℝ :=
  ∑ e ∈ (G.dyadicLargeEdgesRemainingAfterOrdinary K N beta bucket gamma
    reserve residual x M).filter (G.Inc v), G.weight e

theorem dyadicLargeRemainingStarWeight_le_uncovered_add_extra
    (K N : ℕ) (beta : ℝ) (bucket : G.E → Class) (gamma : ℝ)
    (reserve : ℕ) (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (hM : ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).IsPartialMatching M)
    (v : G.V) :
    G.dyadicLargeRemainingStarWeight K N beta bucket gamma reserve residual x
        M v ≤
      G.uncoveredLargeStarWeight
        ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
          (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))
        beta M v +
      ∑ e ∈ (G.selectedDyadicExtraEdges K N bucket gamma reserve residual x M).filter
        (G.Inc v), G.weight e := by
  classical
  let H := (G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
    (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)
  let U := G.uncoveredLargeEdges H beta M
  let X := (G.selectedDyadicExtraEdges K N bucket gamma reserve residual x M).filter
    (fun e ↦ beta ≤ G.weight e)
  have hUX : Disjoint U X := by
    rw [Finset.disjoint_left]
    intro e heU heX
    exact (G.mem_uncoveredLargeEdges H).mp heU |>.2
      (G.dyadic_covers_of_mem_selectedExtraEdges K N bucket gamma reserve
        residual x M (Finset.mem_filter.mp heX).1)
  have hfilter : Disjoint (U.filter (G.Inc v)) (X.filter (G.Inc v)) := by
    rw [Finset.disjoint_left]
    intro e heU heX
    exact Finset.disjoint_left.mp hUX
      (Finset.mem_filter.mp heU).1 (Finset.mem_filter.mp heX).1
  rw [dyadicLargeRemainingStarWeight,
    G.dyadicLargeEdgesRemainingAfterOrdinary_eq K N beta bucket gamma reserve
      residual x M hM, Finset.filter_union, Finset.sum_union hfilter]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    have he' := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp he'.1).1, he'.2⟩
  · intro e _ _
    exact G.weight_nonneg e

end WeightedMultigraph

end

end WeightedEdgeColoring
