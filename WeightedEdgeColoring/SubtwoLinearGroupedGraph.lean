import WeightedEdgeColoring.SubtwoPatternOccurrenceTransfer
import WeightedEdgeColoring.FiniteKeyedLinearGroupingRemainder
import WeightedEdgeColoring.SubtwoBoundedPatternMenu

/-!
# Linear grouping inside one restored block

The grouping key is the ordered endpoint pair. Each nonempty later group
has one rounded type. Its retained physical edges are no heavier than the
representative, and distinct predecessor edges pay for its occurrences.
Thus any proved reserved palette transfers to at most |V|² M types.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 160000
open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G : WeightedMultigraph.{u})

namespace SubtwoLinearGrouping

abbrev EdgeInstance : BinPackingInstance.{u} where
  Item := G.E
  instFintypeItem := inferInstance
  instDecidableEqItem := inferInstance
  weight := G.weight
  weight_pos := G.weight_pos
  weight_le_one := G.weight_le_one

abbrev key (e : (EdgeInstance G).Item) : G.V × G.V := (G.fst e, G.snd e)
abbrev GroupType (M : ℕ) :=
  BinPackingInstance.KeyedLinearRoundedCover.RoundedItem (key G) M
abbrev OccurrenceAt (M : ℕ) (j : GroupType G M) :=
  {i : Fin (BinPackingInstance.KeyedLinearRoundedCover.cell (key G) j.keyValue).card //
    i ∈ BinPackingInstance.KeyedLinearRoundedCover.laterIndices (key G) M j.keyValue j.number}
abbrev Occurrence (M : ℕ) := Σ j : GroupType G M, OccurrenceAt G M j
abbrev source (M : ℕ) : Occurrence G M → G.E :=
  BinPackingInstance.KeyedLinearRoundedCover.predecessorItem (key G) M
abbrev target (M : ℕ) : Occurrence G M → G.E :=
  BinPackingInstance.KeyedLinearRoundedCover.targetItem (key G) M

noncomputable def typeGraph (M : ℕ) : WeightedMultigraph.{u} := by
  classical
  exact {
    V := G.V
    E := GroupType G M
    instFintypeV := inferInstance
    instFintypeE := inferInstance
    instDecidableEqV := inferInstance
    instDecidableEqE := inferInstance
    fst := fun j => j.keyValue.1
    snd := fun j => j.keyValue.2
    noLoop := by
      intro j h
      have hk := BinPackingInstance.KeyedLinearRoundedCover.RoundedItem.key_representative
        (key G) M j
      exact G.noLoop j.representative (by
        have hf := congrArg Prod.fst hk
        have hs := congrArg Prod.snd hk
        exact hf.trans (h.trans hs.symm))
    weight := BinPackingInstance.KeyedLinearRoundedCover.roundedWeight (key G) M
    weight_pos := (BinPackingInstance.KeyedLinearRoundedCover.roundedInstance (key G) M).weight_pos
    weight_le_one := (BinPackingInstance.KeyedLinearRoundedCover.roundedInstance (key G) M).weight_le_one }

noncomputable def targetGraph (M : ℕ) : WeightedMultigraph.{u} := by
  classical
  exact {
    V := G.V
    E := Occurrence G M
    instFintypeV := inferInstance
    instFintypeE := inferInstance
    instDecidableEqV := inferInstance
    instDecidableEqE := inferInstance
    fst := fun o => G.fst (target G M o)
    snd := fun o => G.snd (target G M o)
    noLoop := fun o => G.noLoop (target G M o)
    weight := fun o => G.weight (target G M o)
    weight_pos := fun o => G.weight_pos (target G M o)
    weight_le_one := fun o => G.weight_le_one (target G M o) }

theorem source_inc (M : ℕ) (v : G.V) (o : Occurrence G M) :
    G.Inc v (source G M o) ↔ (typeGraph G M).Inc v o.1 := by
  have hk := BinPackingInstance.KeyedLinearRoundedCover.key_predecessorItem (key G) M o
  have hf := congrArg Prod.fst hk
  have hs := congrArg Prod.snd hk
  dsimp only [key] at hf hs
  change (G.fst (source G M o) = v ∨ G.snd (source G M o) = v) ↔
    (o.1.keyValue.1 = v ∨ o.1.keyValue.2 = v)
  rw [hf, hs]

theorem target_inc (M : ℕ) (v : G.V) (o : Occurrence G M) :
    (targetGraph G M).Inc v o ↔ (typeGraph G M).Inc v o.1 := by
  have hk := BinPackingInstance.KeyedLinearRoundedCover.key_targetItem (key G) M o
  have hf := congrArg Prod.fst hk
  have hs := congrArg Prod.snd hk
  dsimp only [key] at hf hs
  change (G.fst (target G M o) = v ∨ G.snd (target G M o) = v) ↔
    (o.1.keyValue.1 = v ∨ o.1.keyValue.2 = v)
  rw [hf, hs]

/-- All retained occurrences are paid for by their distinct predecessors. -/
theorem paletteAttainable (M : ℕ) (hM : 0 < M)
    (budget : Option G.V → ℝ) (demand : G.E → ℝ)
    (hd : demand ∈ Subtwo.PaletteAttainable budget G.subtwoReservedColorPattern) :
    (fun j : (typeGraph G M).E => ∑ o : OccurrenceAt G M j,
      demand (source G M ⟨j,o⟩)) ∈
      Subtwo.PaletteAttainable budget (typeGraph G M).subtwoReservedColorPattern := by
  have h := G.subtwoOccurrence_paletteAttainable (typeGraph G M) (fun v : G.V => v)
    (OccurrenceAt G M) (source G M) (fun v => ⟨v,rfl⟩)
    (BinPackingInstance.KeyedLinearRoundedCover.predecessorItem_injective (key G) M hM)
    (source_inc G M)
    (BinPackingInstance.KeyedLinearRoundedCover.roundedWeight_le_predecessorItem (key G) M hM)
    budget demand hd
  obtain ⟨hnonneg, a, ha, hcover⟩ := h
  refine ⟨hnonneg, a, ha, ?_⟩
  intro j
  convert hcover j using 1
  unfold Subtwo.paletteCoverage
  apply Finset.sum_congr rfl
  intro l _
  cases l <;> rfl

theorem card_types_le (M : ℕ) :
    Fintype.card (typeGraph G M).E ≤ (Fintype.card G.V)^2 * M := by
  have h := Fintype.card_le_of_injective
    (fun j : GroupType G M => j.val) Subtype.val_injective
  have hm : M - 1 ≤ M := Nat.sub_le _ _
  calc
    _ ≤ Fintype.card ((G.V × G.V) × Fin (M-1)) := h
    _ = (Fintype.card G.V)^2 * (M-1) := by simp [pow_two, Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ hm

theorem type_weight_ge (M S : ℕ)
    (hweight : ∀ e, (1 : ℝ) / S ≤ G.weight e)
    (j : (typeGraph G M).E) :
    (1 : ℝ) / S ≤ (typeGraph G M).weight j :=
  hweight j.representative

theorem target_weight_le (M : ℕ) (o : Occurrence G M) :
    (targetGraph G M).weight o ≤ (typeGraph G M).weight o.1 :=
  BinPackingInstance.KeyedLinearRoundedCover.targetItem_weight_le_roundedWeight (key G) M o

theorem card_patterns_le (M S : ℕ) (hS : 0 < S)
    (hweight : ∀ e, (1 : ℝ) / S ≤ G.weight e) :
    Fintype.card (typeGraph G M).SubtwoWeightedPattern ≤
      (S+1)^((Fintype.card G.V)^2 * M) :=
  ((typeGraph G M).card_subtwoWeightedPattern_le_uniform S hS
    (type_weight_ge G M S hweight)).trans
    (Nat.pow_le_pow_right (by omega) (card_types_le G M))

end SubtwoLinearGrouping
end
end WeightedEdgeColoring.WeightedMultigraph
