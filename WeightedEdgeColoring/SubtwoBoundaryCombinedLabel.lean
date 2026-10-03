import WeightedEdgeColoring.SubtwoMixedGraphJointSelectedSupport

/-! A boundary color used by a full packet has its unique original endpoint;
otherwise the selected residual word supplies the endpoint label.  This
module is independent of the quantitative charge estimates. -/

namespace WeightedEdgeColoring
open scoped BigOperators
noncomputable section

namespace WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})
variable {B L : Type*} [Fintype B] [DecidableEq B] [DecidableEq L]
variable {K : ℕ}

/-- A base color is present at a block exactly when one of its selected
physical edges meets the block. -/
def boundaryBaseUses (Fbase : Finset G.E) (block : G.V → B)
    (baseColor : G.E → Fin K) (b : B) (c : Fin K) : Prop :=
  ∃ v : G.V, block v = b ∧
    ∃ e ∈ Fbase, G.Inc v e ∧ baseColor e = c

/-- The endpoint label of a used base color, or the selected residual label
when that base color is absent from the block. -/
def combinedBoundaryLabel (Fbase : Finset G.E) (block : G.V → B)
    (baseColor : G.E → Fin K) (vertexLabel : B → G.V → L)
    (selectedLabel : B → Fin K → Option L) (b : B) (c : Fin K) : Option L := by
  classical
  exact if h : G.boundaryBaseUses Fbase block baseColor b c then
    some (vertexLabel b (Classical.choose h))
  else selectedLabel b c

theorem combinedBoundaryLabel_base
    (Fbase : Finset G.E) (block : G.V → B)
    (baseColor : G.E → Fin K) (vertexLabel : B → G.V → L)
    (selectedLabel : B → Fin K → Option L)
    (hunique : ∀ e ∈ Fbase, ∀ f ∈ Fbase,
      ∀ v w, G.Inc v e → G.Inc w f → block v = block w →
        baseColor e = baseColor f → v = w)
    {e : G.E} (he : e ∈ Fbase) {v : G.V} (hv : G.Inc v e) :
    G.combinedBoundaryLabel Fbase block baseColor vertexLabel selectedLabel
      (block v) (baseColor e) = some (vertexLabel (block v) v) := by
  classical
  let h : G.boundaryBaseUses Fbase block baseColor (block v) (baseColor e) :=
    ⟨v, rfl, e, he, hv, rfl⟩
  simp only [combinedBoundaryLabel, dif_pos h]
  rcases (Classical.choose_spec h) with ⟨hb, e', he', hv', hc'⟩
  have hveq : Classical.choose h = v :=
    hunique e' he' e he (Classical.choose h) v hv' hv hb hc'
  simp [hveq]

theorem combinedBoundaryLabel_residual
    (Fbase Fres : Finset G.E) (block : G.V → B)
    (baseColor residualColor : G.E → Fin K)
    (vertexLabel : B → G.V → L)
    (selectedLabel : B → Fin K → Option L)
    (hmissing : ∀ e ∈ Fres, ∀ v, G.Inc v e →
      ¬ G.boundaryBaseUses Fbase block baseColor
          (block v) (residualColor e))
    (hselected : ∀ e ∈ Fres, ∀ v, G.Inc v e →
      selectedLabel (block v) (residualColor e) =
        some (vertexLabel (block v) v))
    {e : G.E} (he : e ∈ Fres) {v : G.V} (hv : G.Inc v e) :
    G.combinedBoundaryLabel Fbase block baseColor vertexLabel selectedLabel
      (block v) (residualColor e) = some (vertexLabel (block v) v) := by
  simp only [combinedBoundaryLabel, dif_neg (hmissing e he v hv)]
  exact hselected e he v hv

/-- The label class of the combined boundary palette is contained in the
union of the base and selected-word classes. -/
theorem combinedBoundaryLabel_class_card_le
    (Fbase : Finset G.E) (block : G.V → B)
    (baseColor : G.E → Fin K) (vertexLabel : B → G.V → L)
    (selectedLabel : B → Fin K → Option L)
    (b : B) (label : L) :
    (Finset.univ.filter fun c : Fin K ↦
      G.combinedBoundaryLabel Fbase block baseColor vertexLabel
        selectedLabel b c = some label).card ≤
      (Finset.univ.filter fun c : Fin K ↦
        ∃ v, block v = b ∧
          (∃ e ∈ Fbase, G.Inc v e ∧ baseColor e = c) ∧
          vertexLabel b v = label).card +
      (Finset.univ.filter fun c : Fin K ↦
        selectedLabel b c = some label).card := by
  classical
  let A : Finset (Fin K) := Finset.univ.filter fun c ↦
    ∃ v, block v = b ∧
      (∃ e ∈ Fbase, G.Inc v e ∧ baseColor e = c) ∧
      vertexLabel b v = label
  let D : Finset (Fin K) := Finset.univ.filter fun c ↦
    selectedLabel b c = some label
  have hsubset :
      (Finset.univ.filter fun c : Fin K ↦
        G.combinedBoundaryLabel Fbase block baseColor vertexLabel
          selectedLabel b c = some label) ⊆ A ∪ D := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    by_cases h : G.boundaryBaseUses Fbase block baseColor b c
    · have hh : vertexLabel b (Classical.choose h) = label := by
        simpa [combinedBoundaryLabel, h] using hc
      exact Finset.mem_union.mpr (Or.inl (by
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨Classical.choose h, (Classical.choose_spec h).1,
          (Classical.choose_spec h).2, hh⟩))
    · exact Finset.mem_union.mpr (Or.inr (by
        simpa [D, combinedBoundaryLabel, h] using hc))
  calc
    _ ≤ (A ∪ D).card := Finset.card_le_card hsubset
    _ ≤ A.card + D.card := Finset.card_union_le A D
    _ = _ := rfl

/-- Injective labels within a block turn the base part of a label class
into the used colors at that one original vertex. -/
theorem boundaryBaseLabelClass_subset_vertexColors
    (Fbase : Finset G.E) (block : G.V → B)
    (baseColor : G.E → Fin K) (vertexLabel : B → G.V → L)
    (hinj : ∀ b v w, block v = b → block w = b →
      vertexLabel b v = vertexLabel b w → v = w)
    (v : G.V) :
    (Finset.univ.filter fun c : Fin K ↦
      ∃ w, block w = block v ∧
        (∃ e ∈ Fbase, G.Inc w e ∧ baseColor e = c) ∧
        vertexLabel (block v) w = vertexLabel (block v) v) ⊆
      (Finset.univ.filter fun c : Fin K ↦
        ∃ e ∈ Fbase, G.Inc v e ∧ baseColor e = c) := by
  classical
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  obtain ⟨w, hw, he, hlabel⟩ := hc
  have hwv := hinj (block v) w v hw rfl hlabel
  simpa [hwv] using he

end WeightedMultigraph
end
end WeightedEdgeColoring
