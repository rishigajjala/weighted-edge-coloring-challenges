import WeightedEdgeColoring.SubtwoMixedCoreGroupingTypes
import WeightedEdgeColoring.SubtwoMixedOneTinyFloorResidual

/-! The actual grouped graph supplies the one-tiny floor remainder premise. -/

set_option maxHeartbeats 4000000
open scoped BigOperators Sym2
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u

theorem floorBundleAtMostOneTiny_of_below_endpoint_injective
    (G : WeightedMultigraph.{u}) (D S : ℕ) (hS : 0 < S)
    (hD : ∀ k, Fintype.card (G.EdgeSetWeightType (G.floorBundle k)) ≤ D+1)
    (hsmall : Function.Injective
      (fun e : {e : G.E // G.weight e < (1 : ℝ)/S} => s(G.fst e.val,G.snd e.val))) :
    G.FloorBundleAtMostOneTiny D S := by
  classical
  intro k
  refine ⟨hD k, ?_⟩
  have hflo : ∀ x : G.EdgeSetWeightType (G.floorBundle k), (1 : ℝ)/S ≤ x.val →
      Nat.floor (1/x.val) ≤ S := by
    intro x hx
    have hpos : 0 < x.val := (G.edgeSetWeightBinPackingInstance (G.floorBundle k)).weight_pos x
    have hSR : (0 : ℝ) < S := by exact_mod_cast hS
    have hr : (1 : ℝ)/x.val ≤ S := by
      apply (div_le_iff₀ hpos).2
      have h := (div_le_iff₀ hSR).1 hx
      nlinarith
    have hfloor := (Nat.floor_le (one_div_nonneg.mpr hpos.le)).trans hr
    exact_mod_cast hfloor
  have hunique : ∀ x y : G.EdgeSetWeightType (G.floorBundle k),
      x.val < (1 : ℝ)/S → y.val < (1 : ℝ)/S → x = y := by
    intro x y hx hy
    obtain ⟨e,he,hxe⟩ := Finset.mem_image.mp x.property
    obtain ⟨f,hf,hyf⟩ := Finset.mem_image.mp y.property
    have eh : G.weight e < (1 : ℝ)/S := hxe ▸ hx
    have fh : G.weight f < (1 : ℝ)/S := hyf ▸ hy
    have hends := G.endpoints_eq_of_floorKey_eq
      ((G.floorKey_eq_of_mem_floorBundle he).trans (G.floorKey_eq_of_mem_floorBundle hf).symm)
    have hef : e = f := congrArg Subtype.val (hsmall (a₁ := ⟨e,eh⟩) (a₂ := ⟨f,fh⟩) hends)
    apply Subtype.ext
    exact hxe.symm.trans ((congrArg G.weight hef).trans hyf)
  by_cases ht : ∃ x : G.EdgeSetWeightType (G.floorBundle k), x.val < (1 : ℝ)/S
  · obtain ⟨tiny,htiny⟩ := ht
    right
    refine ⟨tiny, ?_, ?_⟩
    · unfold edgeSetWeightDemand
      rw [Finset.card_le_one]
      intro e he f hf
      obtain ⟨he,hwe⟩ := Finset.mem_filter.mp he
      obtain ⟨hf,hwf⟩ := Finset.mem_filter.mp hf
      have eh : G.weight e < (1 : ℝ)/S := hwe ▸ htiny
      have fh : G.weight f < (1 : ℝ)/S := hwf ▸ htiny
      exact congrArg Subtype.val (hsmall (a₁ := ⟨e,eh⟩) (a₂ := ⟨f,fh⟩)
        (G.endpoints_eq_of_floorKey_eq ((G.floorKey_eq_of_mem_floorBundle he).trans
          (G.floorKey_eq_of_mem_floorBundle hf).symm)))
    · intro p x hxt
      have hx : (1 : ℝ)/S ≤ x.val := le_of_not_gt (fun h => hxt (hunique x tiny h htiny))
      exact (BinPackingInstance.Pattern.multiplicity_le_floor
        (G.edgeSetWeightBinPackingInstance (G.floorBundle k)) p x).trans (hflo x hx)
  · left
    intro x
    exact hflo x (le_of_not_gt (fun hx => ht ⟨x,hx⟩))

namespace SubtwoMixedCoreGrouping

theorem floorBundleAtMostOneTiny
    (G : WeightedMultigraph.{u}) (F : Finset G.E) (M S : ℕ) (hS : 0 < S)
    (hlower : ∀ e ∈ F, (1 : ℝ)/S ≤ G.weight e)
    (hsmall : Function.Injective (fun e : {e : G.E // e ∉ F} => s(G.fst e.val,G.snd e.val))) :
    (graph G F M).FloorBundleAtMostOneTiny (2*M) S :=
  (graph G F M).floorBundleAtMostOneTiny_of_below_endpoint_injective (2*M) S hS
    (card_bundle_weight_types_le G F M hsmall)
    (below_endpoint_injective G F M ((1 : ℝ)/S) hlower hsmall)

end SubtwoMixedCoreGrouping
end
end WeightedEdgeColoring.WeightedMultigraph
