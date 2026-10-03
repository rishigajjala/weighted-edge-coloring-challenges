import WeightedEdgeColoring.SubtwoPaletteAllocation

/-! A finite injection prescribed on a subset extends to a full bijection.
This lets the restoration step pad the boundary color classes without
changing the labels on colors that are already used. -/

namespace WeightedEdgeColoring.Subtwo
noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Extend an injective assignment on a prescribed subset of a finite set.
Equal total cardinalities supply exactly enough unused target elements. -/
theorem exists_equiv_extending_subtype
    (p : A → Prop) [DecidablePred p]
    (f : {a // p a} → B) (hf : Function.Injective f)
    (hcard : Fintype.card A = Fintype.card B) :
    ∃ e : A ≃ B, ∀ a : {a // p a}, e a.val = f a := by
  classical
  let ef : {a // p a} ≃ {b // b ∈ Set.range f} := Equiv.ofInjective f hf
  have hsubcard : Fintype.card {a // p a} = Fintype.card {b // b ∈ Set.range f} :=
    Fintype.card_congr ef
  have hcompcard : Fintype.card {a // ¬p a} =
      Fintype.card {b // ¬b ∈ Set.range f} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hcard, hsubcard]
  let ec : {a // ¬p a} ≃ {b // ¬b ∈ Set.range f} := Fintype.equivOfCardEq hcompcard
  let e : A ≃ B := (Equiv.sumCompl p).symm.trans
    ((Equiv.sumCongr ef ec).trans (Equiv.sumCompl fun b => b ∈ Set.range f))
  refine ⟨e, ?_⟩
  intro a
  simp [e, ef, Equiv.sumCompl, a.property]

end
end WeightedEdgeColoring.Subtwo
