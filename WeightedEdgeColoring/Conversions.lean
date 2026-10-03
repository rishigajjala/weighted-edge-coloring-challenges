import WeightedEdgeColoring.GreedyCleanup

namespace WeightedEdgeColoring
namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph)

/-- Forget that an indexed graph has no parallel edges. -/
def toMultigraph : WeightedMultigraph where
  V := G.V
  E := G.E
  instFintypeV := G.instFintypeV
  instFintypeE := G.instFintypeE
  instDecidableEqV := G.instDecidableEqV
  instDecidableEqE := G.instDecidableEqE
  fst := G.fst
  snd := G.snd
  noLoop := G.noLoop
  weight := G.weight
  weight_pos := G.weight_pos
  weight_le_one := G.weight_le_one

@[simp] theorem toMultigraph_inc (v : G.V) (e : G.E) :
    G.toMultigraph.Inc v e ↔ G.Inc v e := Iff.rfl

@[simp] theorem toMultigraph_colorLoad {q : ℕ} (color : G.E → Fin q)
    (v : G.V) (i : Fin q) :
    G.toMultigraph.colorLoad color v i = G.colorLoad color v i := rfl

@[simp] theorem toMultigraph_isWeightedColoring {q : ℕ} (color : G.E → Fin q) :
    G.toMultigraph.IsWeightedColoring color ↔ G.IsWeightedColoring color := Iff.rfl

@[simp] theorem toMultigraph_hasWeightedColoring (q : ℕ) :
    G.toMultigraph.HasWeightedColoring q ↔ G.HasWeightedColoring q := Iff.rfl

@[simp] theorem toMultigraph_starBinLoad {n : ℕ} {v : G.V}
    (bin : G.StarEdge v → Fin n) (i : Fin n) :
    G.toMultigraph.starBinLoad bin i = G.starBinLoad bin i := rfl

@[simp] theorem toMultigraph_packsStarInto (v : G.V) (n : ℕ) :
    G.toMultigraph.PacksStarInto v n ↔ G.PacksStarInto v n := Iff.rfl

@[simp] theorem toMultigraph_locallyPacksInto (n : ℕ) :
    G.toMultigraph.LocallyPacksInto n ↔ G.LocallyPacksInto n := Iff.rfl

@[simp] theorem toMultigraph_starWeight (v : G.V) :
    G.toMultigraph.starWeight v = G.starWeight v := rfl

/-- The two minimum-color definitions agree after forgetting simplicity. -/
theorem toMultigraph_chiW_eq :
    G.toMultigraph.chiW = G.weightedChromaticIndex := by
  apply le_antisymm
  · apply G.toMultigraph.chiW_le_of_hasWeightedColoring
    exact G.hasWeightedColoring_weightedChromaticIndex
  · apply G.weightedChromaticIndex_le_of_hasWeightedColoring
    exact G.toMultigraph.hasWeightedColoring_chiW

/-- The two local-bin definitions agree after forgetting simplicity. -/
theorem toMultigraph_bp_eq :
    G.toMultigraph.bp = G.localBinNumber := by
  apply le_antisymm
  · apply G.toMultigraph.bp_le_of_locallyPacksInto
    exact G.locallyPacksInto_localBinNumber
  · apply G.localBinNumber_le_of_locallyPacksInto
    exact G.toMultigraph.locallyPacksInto_bp

/-- The simple graph's total load is bounded by its local bin number. -/
theorem toMultigraph_deltaW_le_localBinNumber :
    G.toMultigraph.deltaW ≤ G.localBinNumber := by
  rw [← G.toMultigraph_bp_eq]
  exact G.toMultigraph.deltaW_le_bp

/-- Unconditional deterministic cleanup for simple graphs. -/
theorem weightedChromaticIndex_le_four_localBinNumber_add_one :
    G.weightedChromaticIndex ≤ 4 * G.localBinNumber + 1 := by
  rw [← G.toMultigraph_chiW_eq]
  apply G.toMultigraph.chiW_le_of_hasWeightedColoring
  exact G.toMultigraph.hasWeightedColoring_four_add_one G.localBinNumber
    G.toMultigraph_deltaW_le_localBinNumber

end WeightedSimpleGraph
end WeightedEdgeColoring
