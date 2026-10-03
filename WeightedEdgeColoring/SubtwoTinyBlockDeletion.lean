import WeightedEdgeColoring.GeneralTinyThresholdMixedObjects

/-! A block of at most five vertices loses only a bounded number of
endpoint-simple tiny objects when these objects are omitted after block
selection. The statement is independent of the number of original edges. -/

open scoped BigOperators Sym2

namespace WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization

universe u
variable {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {tau : ℝ}
  (P : G.GeneralTinyThresholdPacketization tau)

noncomputable def smallInternalObjects (S : Finset G.V) :
    Finset {o : P.Object // o ∈ P.smallObjects} :=
  Finset.univ.filter (fun o =>
    P.mixedObjectGraph.fst o.1 ∈ S ∧ P.mixedObjectGraph.snd o.1 ∈ S)

theorem smallInternalObjects_card_le_square (S : Finset G.V) :
    (P.smallInternalObjects S).card ≤ S.card * S.card := by
  classical
  let endpoint : {o : P.Object // o ∈ P.smallObjects} → Sym2 G.V :=
    fun o => s(P.mixedObjectGraph.fst o.1, P.mixedObjectGraph.snd o.1)
  let pairs : Finset (Sym2 G.V) :=
    (S.product S).image (fun ab => s(ab.1, ab.2))
  have hsubset : (P.smallInternalObjects S).image endpoint ⊆ pairs := by
    intro p hp
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hp
    have hi := (Finset.mem_filter.mp ho).2
    exact Finset.mem_image.mpr ⟨(P.mixedObjectGraph.fst o.1,
      P.mixedObjectGraph.snd o.1), Finset.mem_product.mpr hi, rfl⟩
  have hinj : Function.Injective endpoint := P.smallObjects_endpoint_injective
  calc
    (P.smallInternalObjects S).card =
        ((P.smallInternalObjects S).image endpoint).card :=
          (Finset.card_image_of_injective _ hinj).symm
    _ ≤ pairs.card := Finset.card_le_card hsubset
    _ ≤ (S.product S).card := Finset.card_image_le
    _ = S.card * S.card := Finset.card_product _ _

theorem smallInternalObjects_card_le_twenty_five (S : Finset G.V)
    (hS : S.card ≤ 5) :
    (P.smallInternalObjects S).card ≤ 25 := by
  have h := P.smallInternalObjects_card_le_square S
  nlinarith

theorem smallInternalObjects_weight_le (S : Finset G.V)
    (hS : S.card ≤ 5) (htau : 0 ≤ tau) :
    (∑ o ∈ P.smallInternalObjects S,
      P.mixedObjectGraph.weight o.1) ≤ 25 * tau := by
  calc
    _ ≤ ∑ _o ∈ P.smallInternalObjects S, tau := by
      apply Finset.sum_le_sum
      intro o ho
      exact P.smallObject_weight_le o.2
    _ = (P.smallInternalObjects S).card * tau := by simp
    _ ≤ 25 * tau := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast P.smallInternalObjects_card_le_twenty_five S hS) htau

theorem smallInternalObjects_starWeight_le (S : Finset G.V)
    (hS : S.card ≤ 5) (htau : 0 ≤ tau) (v : G.V) :
    (∑ o ∈ P.smallInternalObjects S,
      if P.mixedObjectGraph.Inc v o.1 then P.mixedObjectGraph.weight o.1 else 0) ≤
        25 * tau := by
  calc
    _ ≤ ∑ o ∈ P.smallInternalObjects S,
        P.mixedObjectGraph.weight o.1 := by
      apply Finset.sum_le_sum
      intro o _
      split_ifs
      · rfl
      · exact P.mixedObjectGraph.weight_pos o.1 |>.le
    _ ≤ 25 * tau := P.smallInternalObjects_weight_le S hS htau

end WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
