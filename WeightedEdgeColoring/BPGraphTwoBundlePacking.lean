import WeightedEdgeColoring.BPGraphEdgeBinPacking
import WeightedEdgeColoring.BPGeneralPatternTwoBagMinimumExtraction
import WeightedEdgeColoring.FiniteFractionalPatternCoverOfPacking

/-!
# Joint local packing of two graph edge bundles

Two disjoint edge sets incident with the same vertex inherit one joint bin
packing from that vertex.  Their disjoint-sum bin-packing instance therefore
has a fractional cover whose cost is the local number of bins.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- Two disjoint incident edge sets pack jointly into every packing of their
common vertex star. -/
theorem sum_edgeSetBinPackingInstance_packsInto_of_packsStarInto
    (F H : Finset G.E) (v : G.V) {n : ℕ}
    (hdisj : Disjoint F H)
    (hincF : ∀ e ∈ F, G.Inc v e)
    (hincH : ∀ e ∈ H, G.Inc v e)
    (hpack : G.PacksStarInto v n) :
    ((G.edgeSetBinPackingInstance F).sum
      (G.edgeSetBinPackingInstance H)).PacksInto n := by
  classical
  rcases hpack with ⟨starBin, hstarBin⟩
  let A := G.edgeSetBinPackingInstance F
  let B := G.edgeSetBinPackingInstance H
  let itemToStar : (A.sum B).Item → G.StarEdge v
    | Sum.inl e => ⟨e.1, hincF e.1 e.2⟩
    | Sum.inr e => ⟨e.1, hincH e.1 e.2⟩
  let bin : (A.sum B).Item → Fin n := fun e ↦ starBin (itemToStar e)
  refine ⟨⟨bin, ?_⟩⟩
  intro j
  let f : G.E → ℝ := fun e ↦
    if he : G.Inc v e then
      if starBin ⟨e, he⟩ = j then G.weight e else 0
    else 0
  have hUnionSub : F ∪ H ⊆
      (Finset.univ : Finset G.E).filter (G.Inc v) := by
    intro e he
    rcases Finset.mem_union.mp he with heF | heH
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hincF e heF⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hincH e heH⟩
  calc
    (A.sum B).binLoad bin j =
        (∑ e ∈ F, f e) + ∑ e ∈ H, f e := by
      unfold BinPackingInstance.binLoad
      change
        (∑ i : Sum A.Item B.Item,
          if bin i = j then Sum.elim A.weight B.weight i else 0) = _
      rw [Fintype.sum_sum_type]
      congr 1
      · calc
          (∑ e : A.Item,
              if bin (Sum.inl e) = j then (A.sum B).weight (Sum.inl e)
              else 0) = ∑ e : A.Item, f e.1 := by
            apply Finset.sum_congr rfl
            intro e _he
            simp [A, B, bin, itemToStar, f, BinPackingInstance.sum,
              hincF e.1 e.2]
          _ = ∑ e ∈ F, f e :=
            (Finset.sum_subtype (p := fun e : G.E ↦ e ∈ F) F
              (by intro e; simp) f).symm
      · calc
          (∑ e : B.Item,
              if bin (Sum.inr e) = j then (A.sum B).weight (Sum.inr e)
              else 0) = ∑ e : B.Item, f e.1 := by
            apply Finset.sum_congr rfl
            intro e _he
            simp [A, B, bin, itemToStar, f, BinPackingInstance.sum,
              hincH e.1 e.2]
          _ = ∑ e ∈ H, f e :=
            (Finset.sum_subtype (p := fun e : G.E ↦ e ∈ H) H
              (by intro e; simp) f).symm
    _ = ∑ e ∈ F ∪ H, f e := (Finset.sum_union hdisj).symm
    _ ≤ ∑ e ∈ (Finset.univ : Finset G.E).filter (G.Inc v), f e := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hUnionSub
        (fun e _heStar _heUnion ↦ by
          by_cases hve : G.Inc v e
          · by_cases hbin : starBin ⟨e, hve⟩ = j
            · simp [f, hve, hbin, G.weight_nonneg]
            · simp [f, hve, hbin]
          · simp [f, hve])
    _ = G.starBinLoad starBin j := by
      calc
        (∑ e ∈ (Finset.univ : Finset G.E).filter (G.Inc v), f e) =
            ∑ e : G.StarEdge v, f e.1 :=
          Finset.sum_subtype
            (p := G.Inc v) ((Finset.univ : Finset G.E).filter (G.Inc v))
            (by intro e; simp) f
        _ = G.starBinLoad starBin j := by
          unfold starBinLoad
          apply Finset.sum_congr rfl
          intro e _he
          simp [f, e.2]
    _ ≤ 1 := hstarBin j

/-- The joint instance of two disjoint incident edge sets has a fractional
pattern cover of cost exactly the number of local bins. -/
theorem exists_sum_edgeSet_fractionalPatternCover_cost_eq_of_packsStarInto
    (F H : Finset G.E) (v : G.V) {n : ℕ}
    (hdisj : Disjoint F H)
    (hincF : ∀ e ∈ F, G.Inc v e)
    (hincH : ∀ e ∈ H, G.Inc v e)
    (hpack : G.PacksStarInto v n) :
    ∃ C : ((G.edgeSetBinPackingInstance F).sum
        (G.edgeSetBinPackingInstance H)).FractionalPatternCover,
      C.cost = n := by
  apply BinPackingInstance.exists_fractionalPatternCover_cost_eq_of_packsInto
  exact G.sum_edgeSetBinPackingInstance_packsInto_of_packsStarInto
    F H v hdisj hincF hincH hpack

end

end WeightedMultigraph
end WeightedEdgeColoring
