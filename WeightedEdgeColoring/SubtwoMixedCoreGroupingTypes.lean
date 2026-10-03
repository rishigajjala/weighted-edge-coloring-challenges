import WeightedEdgeColoring.SubtwoMixedCoreGrouping

/-! A uniform finite weight menu after grouping only the finite core. -/

set_option maxHeartbeats 4000000
open scoped BigOperators Sym2
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u

theorem endpoints_eq_of_floorKey_eq (G : WeightedMultigraph.{u}) {e f : G.E}
    (h : G.floorKey e = G.floorKey f) : s(G.fst e,G.snd e) = s(G.fst f,G.snd f) := by
  have hh : ∀ e : G.E, s(G.fst e,G.snd e) = s((G.floorKey e).1,(G.floorKey e).2) := by
    intro e
    unfold floorKey floorTail floorHead
    split_ifs
    · rfl
    · exact Sym2.eq_swap
  rw [hh e, hh f, h]

namespace SubtwoMixedCoreGrouping
variable (G : WeightedMultigraph.{u}) (F : Finset G.E) (M : ℕ)

def smallPair (k : G.V × G.V) : Finset {e : G.E // e ∉ F} :=
  Finset.univ.filter fun e => (graph G F M).floorKey (Sum.inr e) = k

theorem smallPair_card_le_one
    (hsmall : Function.Injective (fun e : {e : G.E // e ∉ F} => s(G.fst e.val, G.snd e.val)))
    (k : G.V × G.V) : (smallPair G F M k).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro e he f hf
  apply hsmall
  exact (graph G F M).endpoints_eq_of_floorKey_eq
    ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)

theorem exists_pair_weight_menu
    (hsmall : Function.Injective (fun e : {e : G.E // e ∉ F} => s(G.fst e.val, G.snd e.val)))
    (k : G.V × G.V) :
    ∃ W : Finset ℝ, W.card ≤ 2*M+1 ∧
      ∀ e : (graph G F M).E, e ∈ (graph G F M).floorBundle k →
        (graph G F M).weight e ∈ W := by
  classical
  obtain ⟨W,hW,hw⟩ := SubtwoGlobalLinearGrouping.exists_pair_weight_menu (G.edgeRestriction F) M k
  let T := (smallPair G F M k).image (fun e => G.weight e.val)
  have hT : T.card ≤ 1 := Finset.card_image_le.trans (smallPair_card_le_one G F M hsmall k)
  refine ⟨W ∪ T, (Finset.card_union_le _ _).trans (Nat.add_le_add hW hT), ?_⟩
  intro e he
  cases e with
  | inl e =>
      have hk := (graph G F M).floorKey_eq_of_mem_floorBundle he
      have he' : e ∈ (Core G F M).floorBundle k := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, hk⟩
      exact Finset.mem_union_left _ (hw e he')
  | inr e =>
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (graph G F M).floorKey_eq_of_mem_floorBundle he⟩, rfl⟩

theorem card_bundle_weight_types_le
    (hsmall : Function.Injective (fun e : {e : G.E // e ∉ F} => s(G.fst e.val, G.snd e.val)))
    (k : G.V × G.V) :
    Fintype.card ((graph G F M).EdgeSetWeightType ((graph G F M).floorBundle k)) ≤ 2*M+1 := by
  classical
  obtain ⟨W,hW,hw⟩ := exists_pair_weight_menu G F M hsmall k
  change Fintype.card {w : ℝ // w ∈ ((graph G F M).floorBundle k).image (graph G F M).weight} ≤ _
  rw [Fintype.card_coe]
  apply (Finset.card_le_card ?_).trans hW
  intro w hw'
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hw'
  exact hw e he

end SubtwoMixedCoreGrouping
end
end WeightedEdgeColoring.WeightedMultigraph
