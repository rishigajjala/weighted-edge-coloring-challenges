import WeightedEdgeColoring.ExtraSlotOptions
import WeightedEdgeColoring.PairUniqueOptions
import WeightedEdgeColoring.WeightedGraph

namespace WeightedEdgeColoring

/-!
# Pair uniqueness of extra-slot choices in a simple graph

Two distinct concrete endpoint slots identify the unordered endpoint pair of
their edge.  Simplicity then identifies the edge, and the slot labels identify
the two Cartesian coordinates.
-/

noncomputable section

universe u w

namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]
variable (bucket : G.E → Class) (B : G.V → Class → ℕ)

/-- The Cartesian leave-uncoloured option family of a simple graph is
pair-unique. -/
theorem extraSlotChoice_pairUnique :
    (ExtraSlotChoice.system G.fst G.snd bucket B).PairUnique := by
  intro s t hst q p hsq htq hsp htp
  have hqorient :
      (s = ExtraSlotChoice.leftSlot G.fst G.snd bucket B q ∧
        t = ExtraSlotChoice.rightSlot G.fst G.snd bucket B q) ∨
      (s = ExtraSlotChoice.rightSlot G.fst G.snd bucket B q ∧
        t = ExtraSlotChoice.leftSlot G.fst G.snd bucket B q) := by
    simp only [ExtraSlotChoice.system, Finset.mem_insert,
      Finset.mem_singleton] at hsq htq
    rcases hsq with hs | hs <;> rcases htq with ht | ht
    · exact (hst (hs.trans ht.symm)).elim
    · exact Or.inl ⟨hs, ht⟩
    · exact Or.inr ⟨hs, ht⟩
    · exact (hst (hs.trans ht.symm)).elim
  have hporient :
      (s = ExtraSlotChoice.leftSlot G.fst G.snd bucket B p ∧
        t = ExtraSlotChoice.rightSlot G.fst G.snd bucket B p) ∨
      (s = ExtraSlotChoice.rightSlot G.fst G.snd bucket B p ∧
        t = ExtraSlotChoice.leftSlot G.fst G.snd bucket B p) := by
    simp only [ExtraSlotChoice.system, Finset.mem_insert,
      Finset.mem_singleton] at hsp htp
    rcases hsp with hs | hs <;> rcases htp with ht | ht
    · exact (hst (hs.trans ht.symm)).elim
    · exact Or.inl ⟨hs, ht⟩
    · exact Or.inr ⟨hs, ht⟩
    · exact (hst (hs.trans ht.symm)).elim
  rcases q with ⟨e, a, b⟩
  rcases p with ⟨f, c, d⟩
  rcases hqorient with hq | hq <;> rcases hporient with hp | hp
  · have hleft :
        ExtraSlotChoice.leftSlot G.fst G.snd bucket B ⟨e, (a, b)⟩ =
          ExtraSlotChoice.leftSlot G.fst G.snd bucket B ⟨f, (c, d)⟩ :=
      hq.1.symm.trans hp.1
    have hright :
        ExtraSlotChoice.rightSlot G.fst G.snd bucket B ⟨e, (a, b)⟩ =
          ExtraSlotChoice.rightSlot G.fst G.snd bucket B ⟨f, (c, d)⟩ :=
      hq.2.symm.trans hp.2
    have heFst : G.fst e = G.fst f :=
      congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hleft
    have heSnd : G.snd e = G.snd f :=
      congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hright
    have hef : e = f := G.endpoints_injective
      ((Sym2.eq_iff).2 (Or.inl ⟨heFst, heSnd⟩))
    subst f
    have hac : a = c := Fin.ext
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.2.val) hleft)
    have hbd : b = d := Fin.ext
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.2.val) hright)
    subst c
    subst d
    rfl
  · have hleftRight :
        ExtraSlotChoice.leftSlot G.fst G.snd bucket B ⟨e, (a, b)⟩ =
          ExtraSlotChoice.rightSlot G.fst G.snd bucket B ⟨f, (c, d)⟩ :=
      hq.1.symm.trans hp.1
    have hrightLeft :
        ExtraSlotChoice.rightSlot G.fst G.snd bucket B ⟨e, (a, b)⟩ =
          ExtraSlotChoice.leftSlot G.fst G.snd bucket B ⟨f, (c, d)⟩ :=
      hq.2.symm.trans hp.2
    have heFst : G.fst e = G.snd f :=
      congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hleftRight
    have heSnd : G.snd e = G.fst f :=
      congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hrightLeft
    have hef : e = f := G.endpoints_injective
      ((Sym2.eq_iff).2 (Or.inr ⟨heFst, heSnd⟩))
    subst f
    exact (G.noLoop e heFst).elim
  · have hrightLeft :
        ExtraSlotChoice.rightSlot G.fst G.snd bucket B ⟨e, (a, b)⟩ =
          ExtraSlotChoice.leftSlot G.fst G.snd bucket B ⟨f, (c, d)⟩ :=
      hq.1.symm.trans hp.1
    have hleftRight :
        ExtraSlotChoice.leftSlot G.fst G.snd bucket B ⟨e, (a, b)⟩ =
          ExtraSlotChoice.rightSlot G.fst G.snd bucket B ⟨f, (c, d)⟩ :=
      hq.2.symm.trans hp.2
    have heFst : G.fst e = G.snd f :=
      congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hleftRight
    have heSnd : G.snd e = G.fst f :=
      congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hrightLeft
    have hef : e = f := G.endpoints_injective
      ((Sym2.eq_iff).2 (Or.inr ⟨heFst, heSnd⟩))
    subst f
    exact (G.noLoop e heFst).elim
  · have hleft :
        ExtraSlotChoice.leftSlot G.fst G.snd bucket B ⟨e, (a, b)⟩ =
          ExtraSlotChoice.leftSlot G.fst G.snd bucket B ⟨f, (c, d)⟩ :=
      hq.2.symm.trans hp.2
    have hright :
        ExtraSlotChoice.rightSlot G.fst G.snd bucket B ⟨e, (a, b)⟩ =
          ExtraSlotChoice.rightSlot G.fst G.snd bucket B ⟨f, (c, d)⟩ :=
      hq.1.symm.trans hp.1
    have heFst : G.fst e = G.fst f :=
      congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hleft
    have heSnd : G.snd e = G.snd f :=
      congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hright
    have hef : e = f := G.endpoints_injective
      ((Sym2.eq_iff).2 (Or.inl ⟨heFst, heSnd⟩))
    subst f
    have hac : a = c := Fin.ext
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.2.val) hleft)
    have hbd : b = d := Fin.ext
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.2.val) hright)
    subst c
    subst d
    rfl

end WeightedSimpleGraph

end

end WeightedEdgeColoring
