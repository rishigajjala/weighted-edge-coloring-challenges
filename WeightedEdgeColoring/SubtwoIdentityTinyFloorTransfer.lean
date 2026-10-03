import WeightedEdgeColoring.SubtwoIdentityTinyPacketization
import WeightedEdgeColoring.SubtwoGroupedOneTinyFloor

/-! Floor-bundle type menus are unchanged by singleton tiny packetization. -/

open scoped BigOperators Sym2
namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u

variable (G : WeightedMultigraph.{u}) (τ : ℝ)
  (hτ : 0 ≤ τ)
  (hpair : Function.Injective
    (fun e : (G.belowRestriction τ).E => s(G.fst e.1, G.snd e.1)))

private abbrev P := G.identityTinyPacketization τ hτ hpair
private abbrev H := (P G τ hτ hpair).mixedObjectGraph

theorem identityTinyPacketization_floorBundle_weight_image
    (k : G.V × G.V) :
    ((H G τ hτ hpair).floorBundle k).image (H G τ hτ hpair).weight =
      (G.floorBundle k).image G.weight := by
  classical
  let P := G.identityTinyPacketization τ hτ hpair
  let H := P.mixedObjectGraph
  ext w
  constructor
  · intro hw
    obtain ⟨p,hp,hpw⟩ := Finset.mem_image.mp hw
    obtain ⟨e,he⟩ := P.mixedPacketization.onto p
    subst p
    apply Finset.mem_image.mpr
    refine ⟨e, ?_, ?_⟩
    · have hk : H.floorKey (P.mixedPacketization.packetOf e) = k :=
        (Finset.mem_filter.mp hp).2
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,
        (G.identityTinyPacketization_floorKey hτ hpair e).symm.trans hk⟩
    · exact (G.identityTinyPacketization_mixedWeight hτ hpair e).symm.trans hpw
  · intro hw
    obtain ⟨e,he,hew⟩ := Finset.mem_image.mp hw
    apply Finset.mem_image.mpr
    refine ⟨P.mixedPacketization.packetOf e, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,
        (G.identityTinyPacketization_floorKey hτ hpair e).trans
          (Finset.mem_filter.mp he).2⟩
    · exact (G.identityTinyPacketization_mixedWeight hτ hpair e).trans hew

theorem identityTinyPacketization_card_floorBundle_weight_types
    (k : G.V × G.V) :
    Fintype.card ((H G τ hτ hpair).EdgeSetWeightType
      ((H G τ hτ hpair).floorBundle k)) =
    Fintype.card (G.EdgeSetWeightType (G.floorBundle k)) := by
  classical
  change Fintype.card {w : ℝ // w ∈
      ((H G τ hτ hpair).floorBundle k).image (H G τ hτ hpair).weight} =
    Fintype.card {w : ℝ // w ∈ (G.floorBundle k).image G.weight}
  simp only [Fintype.card_coe]
  exact congrArg Finset.card
    (G.identityTinyPacketization_floorBundle_weight_image τ hτ hpair k)

theorem identityTinyPacketization_below_endpoint_injective :
    Function.Injective
      (fun p : {p : (H G τ hτ hpair).E //
          (H G τ hτ hpair).weight p < τ} =>
        s((H G τ hτ hpair).fst p.1,
          (H G τ hτ hpair).snd p.1)) := by
  classical
  let P := G.identityTinyPacketization τ hτ hpair
  let H := P.mixedObjectGraph
  intro p q hpq
  obtain ⟨e,he⟩ := P.mixedPacketization.onto p.1
  obtain ⟨f,hf⟩ := P.mixedPacketization.onto q.1
  have heTiny : G.weight e < τ := by
    rw [← G.identityTinyPacketization_mixedWeight hτ hpair e, he]
    exact p.2
  have hfTiny : G.weight f < τ := by
    rw [← G.identityTinyPacketization_mixedWeight hτ hpair f, hf]
    exact q.2
  have hends : s(G.fst e,G.snd e) = s(G.fst f,G.snd f) := by
    rw [← G.identityTinyPacketization_mixedEndpoints hτ hpair e,
      ← G.identityTinyPacketization_mixedEndpoints hτ hpair f]
    have hpq' := hpq
    change s(H.fst p.1,H.snd p.1) = s(H.fst q.1,H.snd q.1) at hpq'
    rw [←he, ←hf] at hpq'
    exact hpq'
  have hsub : (⟨e,(G.mem_edgesBelow_iff τ e).2 heTiny⟩ :
      (G.belowRestriction τ).E) =
      ⟨f,(G.mem_edgesBelow_iff τ f).2 hfTiny⟩ := hpair hends
  have hef : e = f := congrArg Subtype.val hsub
  apply Subtype.ext
  calc
    p.1 = P.mixedPacketization.packetOf e := he.symm
    _ = P.mixedPacketization.packetOf f := congrArg _ hef
    _ = q.1 := hf

/-- The one-tiny floor residual premise survives the identity mixed-object
adapter, with exactly the original finite type-menu bound. -/
theorem identityTinyPacketization_floorBundleAtMostOneTiny
    (D S : ℕ) (hS : 0 < S) (hτeq : τ = (1 : ℝ)/S)
    (hD : ∀ k, Fintype.card (G.EdgeSetWeightType (G.floorBundle k)) ≤ D+1) :
    (H G τ hτ hpair).FloorBundleAtMostOneTiny D S := by
  subst τ
  apply (H G ((1:ℝ)/S) hτ hpair).floorBundleAtMostOneTiny_of_below_endpoint_injective
    D S hS
  · intro k
    rw [G.identityTinyPacketization_card_floorBundle_weight_types
      ((1:ℝ)/S) hτ hpair k]
    exact hD k
  · exact G.identityTinyPacketization_below_endpoint_injective
      ((1:ℝ)/S) hτ hpair

end
end WeightedEdgeColoring.WeightedMultigraph
