import WeightedEdgeColoring.FiniteFractionalPatternCoverHeavy
import WeightedEdgeColoring.WeightedMultigraph

/-!
# Bin-packing instances carried by graph edge sets

A finite edge set is a finite bin-packing instance with the inherited edge
weights.  If every edge of the set is incident with one vertex, any packing
of that vertex star restricts to a packing of the edge set.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- The bin-packing instance whose indexed items are the edges in `F`. -/
def edgeSetBinPackingInstance (F : Finset G.E) : BinPackingInstance where
  Item := {e : G.E // e ∈ F}
  instFintypeItem := inferInstance
  instDecidableEqItem := inferInstance
  weight := fun e ↦ G.weight e.1
  weight_pos := fun e ↦ G.weight_pos e.1
  weight_le_one := fun e ↦ G.weight_le_one e.1

@[simp] theorem edgeSetBinPackingInstance_weight
    (F : Finset G.E) (e : (G.edgeSetBinPackingInstance F).Item) :
    (G.edgeSetBinPackingInstance F).weight e = G.weight e.1 := rfl

/-- A local star packing restricts to every incident edge subset. -/
theorem edgeSetBinPackingInstance_packsInto_of_packsStarInto
    (F : Finset G.E) (v : G.V) {n : ℕ}
    (hinc : ∀ e ∈ F, G.Inc v e)
    (hpack : G.PacksStarInto v n) :
    (G.edgeSetBinPackingInstance F).PacksInto n := by
  classical
  rcases hpack with ⟨starBin, hstarBin⟩
  let itemToStar : (G.edgeSetBinPackingInstance F).Item → G.StarEdge v :=
    fun e ↦ ⟨e.1, hinc e.1 e.2⟩
  let bin : (G.edgeSetBinPackingInstance F).Item → Fin n :=
    fun e ↦ starBin (itemToStar e)
  refine ⟨⟨bin, ?_⟩⟩
  intro j
  let f : G.E → ℝ := fun e ↦
    if he : G.Inc v e then
      if starBin ⟨e, he⟩ = j then G.weight e else 0
    else 0
  have hFsub : F ⊆ (Finset.univ : Finset G.E).filter (G.Inc v) := by
    intro e heF
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc e heF⟩
  calc
    (G.edgeSetBinPackingInstance F).binLoad bin j =
        ∑ e ∈ F, f e := by
      unfold BinPackingInstance.binLoad
      calc
        (∑ e : (G.edgeSetBinPackingInstance F).Item,
            if bin e = j then
              (G.edgeSetBinPackingInstance F).weight e else 0) =
            ∑ e : (G.edgeSetBinPackingInstance F).Item, f e.1 := by
          apply Finset.sum_congr rfl
          intro e _he
          simp [bin, itemToStar, f, hinc e.1 e.2]
        _ = ∑ e ∈ F, f e :=
          (Finset.sum_subtype (p := fun e : G.E ↦ e ∈ F) F
            (by intro e; simp) f).symm
    _ ≤ ∑ e ∈ (Finset.univ : Finset G.E).filter (G.Inc v), f e := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hFsub
        (fun e _heStar _heNotF ↦ by
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

/-- If every edge of `F` is heavier than one half, the number of edges is
bounded by the cost of every fractional pattern cover of the inherited edge
instance. -/
theorem edgeSet_card_le_fractionalPatternCover_cost_of_half_lt
    (F : Finset G.E)
    (hhalf : ∀ e ∈ F, (1 / 2 : ℝ) < G.weight e)
    (C : (G.edgeSetBinPackingInstance F).FractionalPatternCover) :
    (F.card : ℝ) ≤ C.cost := by
  have h :=
    BinPackingInstance.FractionalPatternCover.card_le_cost_of_half_lt
      (G.edgeSetBinPackingInstance F)
      (fun e ↦ hhalf e.1 e.2) C
  simpa [edgeSetBinPackingInstance] using h

end

end WeightedMultigraph
end WeightedEdgeColoring
