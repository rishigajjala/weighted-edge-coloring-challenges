import WeightedEdgeColoring.SubtwoGlobalLinearGrouping
import WeightedEdgeColoring.SubtwoInjectiveLocalPacking
import WeightedEdgeColoring.BPGeneralFloorPacketization

/-! Every grouped endpoint pair uses a fixed finite menu of weights. -/

set_option maxHeartbeats 4000000
open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
namespace SubtwoGlobalLinearGrouping
open SubtwoLinearGrouping
open BinPackingInstance.KeyedLinearRoundedCover
variable (G : WeightedMultigraph.{u}) (M : ℕ)

theorem locallyPacksInto (hM : 0 < M) {n : ℕ}
    (hlocal : G.LocallyPacksInto n) : (graph G M).LocallyPacksInto n :=
  G.locallyPacksInto_of_injective_heavier_edges (graph G M) id (source G M)
    (source_injective G M hM) (fun v e h => (source_inc G M v e).mpr h)
    (weight_le_source G M hM) hlocal

def groupTypesAt (k : G.V × G.V) : Finset (GroupType G M) :=
  Finset.univ.filter fun j => j.keyValue = k

theorem card_groupTypesAt_le (k : G.V × G.V) :
    (groupTypesAt G M k).card ≤ M-1 := by
  classical
  have hinj : Set.InjOn (fun j : GroupType G M => j.number) (groupTypesAt G M k) := by
    intro a ha b hb hab
    apply Subtype.ext
    apply Prod.ext
    · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    · exact hab
  calc
    _ = ((groupTypesAt G M k).image fun j => j.number).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Fin (M-1))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = M-1 := by simp

def weightMenu (k : G.V × G.V) : Finset ℝ := by
  classical
  exact if M ≤ (cell (key G) k).card then
    (groupTypesAt G M k).image ((typeGraph G M).weight)
  else (cell (key G) k).image G.weight

theorem card_weightMenu_le (k : G.V × G.V) : (weightMenu G M k).card ≤ M := by
  classical
  unfold weightMenu
  split_ifs with ha
  · exact (Finset.card_image_le).trans ((card_groupTypesAt_le G M k).trans (Nat.sub_le _ _))
  · exact Finset.card_image_le.trans (Nat.le_of_lt (Nat.lt_of_not_ge ha))

theorem weight_mem_menu (e : (graph G M).E) :
    (graph G M).weight e ∈ weightMenu G M (key G (target G M e)) := by
  classical
  cases e with
  | inl e =>
      change G.weight e.val ∈ weightMenu G M (key G e.val)
      rw [weightMenu, if_neg (Nat.not_le.mpr e.property)]
      apply Finset.mem_image.mpr
      exact ⟨e.val, by simp [cell], rfl⟩
  | inr o =>
      have hk := key_targetItem (key G) M o
      change (typeGraph G M).weight o.1 ∈ weightMenu G M (key G (SubtwoLinearGrouping.target G M o))
      rw [hk, weightMenu, if_pos o.1.active]
      exact Finset.mem_image.mpr ⟨o.1, by simp [groupTypesAt], rfl⟩

theorem exists_pair_weight_menu (k : G.V × G.V) :
    ∃ W : Finset ℝ, W.card ≤ 2*M ∧
      ∀ e : (graph G M).E, e ∈ (graph G M).floorBundle k → (graph G M).weight e ∈ W := by
  classical
  refine ⟨weightMenu G M k ∪ weightMenu G M k.swap, ?_, ?_⟩
  · exact (Finset.card_union_le _ _).trans (by
      have h := card_weightMenu_le G M k
      have h' := card_weightMenu_le G M k.swap
      omega)
  · intro e he
    have hk := (graph G M).floorKey_eq_of_mem_floorBundle he
    rw [floorKey_eq_floorPairKey, floorPairKey] at hk
    have hm := weight_mem_menu G M e
    split_ifs at hk with ho
    · have heq : key G (target G M e) = k := hk
      exact Finset.mem_union_left _ (heq ▸ hm)
    · have heq : key G (target G M e) = k.swap := by
        exact congrArg Prod.swap hk
      exact Finset.mem_union_right _ (heq ▸ hm)

theorem card_bundle_weight_types_le (k : G.V × G.V) :
    Fintype.card ((graph G M).EdgeSetWeightType ((graph G M).floorBundle k)) ≤ 2*M := by
  classical
  obtain ⟨W,hW,hw⟩ := exists_pair_weight_menu G M k
  change Fintype.card {w : ℝ // w ∈ ((graph G M).floorBundle k).image (graph G M).weight} ≤ _
  rw [Fintype.card_coe]
  apply (Finset.card_le_card ?_).trans hW
  intro w hw'
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hw'
  exact hw e he

end SubtwoGlobalLinearGrouping
end
end WeightedEdgeColoring.WeightedMultigraph
