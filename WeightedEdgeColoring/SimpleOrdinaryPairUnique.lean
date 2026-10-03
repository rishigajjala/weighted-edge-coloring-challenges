import WeightedEdgeColoring.OrdinarySlotOptions
import WeightedEdgeColoring.PairUniqueOptions
import WeightedEdgeColoring.WeightedGraph

namespace WeightedEdgeColoring

/-!
# Pair uniqueness of ordinary choices in a simple graph

Two distinct ordinary slots record the two endpoints of an edge and a common
colour.  Their vertex labels determine the unordered endpoint pair.  In a
simple graph that determines the edge, after which the colour and numbered
places determine the whole option.
-/

noncomputable section

universe u w

namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph.{u})
variable {Color : Type w} [Fintype Color] [DecidableEq Color]

/-- Ordinary colour/place choices are pair-unique on a simple graph. -/
theorem ordinarySlotChoice_pairUnique (K : ℕ) :
    (OrdinarySlotChoice.system (Job := G.E) (Vertex := G.V)
      (Color := Color) G.fst G.snd K).PairUnique := by
  intro s t hst q p hsq htq hsp htp
  have hqorient :
      (s = OrdinarySlotChoice.leftSlot G.fst K q ∧
        t = OrdinarySlotChoice.rightSlot G.snd K q) ∨
      (s = OrdinarySlotChoice.rightSlot G.snd K q ∧
        t = OrdinarySlotChoice.leftSlot G.fst K q) := by
    simp only [OrdinarySlotChoice.system, Finset.mem_insert,
      Finset.mem_singleton] at hsq htq
    rcases hsq with hs | hs <;> rcases htq with ht | ht
    · exact (hst (hs.trans ht.symm)).elim
    · exact Or.inl ⟨hs, ht⟩
    · exact Or.inr ⟨hs, ht⟩
    · exact (hst (hs.trans ht.symm)).elim
  have hporient :
      (s = OrdinarySlotChoice.leftSlot G.fst K p ∧
        t = OrdinarySlotChoice.rightSlot G.snd K p) ∨
      (s = OrdinarySlotChoice.rightSlot G.snd K p ∧
        t = OrdinarySlotChoice.leftSlot G.fst K p) := by
    simp only [OrdinarySlotChoice.system, Finset.mem_insert,
      Finset.mem_singleton] at hsp htp
    rcases hsp with hs | hs <;> rcases htp with ht | ht
    · exact (hst (hs.trans ht.symm)).elim
    · exact Or.inl ⟨hs, ht⟩
    · exact Or.inr ⟨hs, ht⟩
    · exact (hst (hs.trans ht.symm)).elim
  rcases q with ⟨e, c, i, j⟩
  rcases p with ⟨f, d, k, l⟩
  rcases hqorient with hq | hq <;> rcases hporient with hp | hp
  · have hleft :
        OrdinarySlotChoice.leftSlot G.fst K
            (⟨e, c, i, j⟩ : OrdinarySlotChoice G.E Color K) =
          OrdinarySlotChoice.leftSlot G.fst K ⟨f, d, k, l⟩ :=
      hq.1.symm.trans hp.1
    have hright :
        OrdinarySlotChoice.rightSlot G.snd K
            (⟨e, c, i, j⟩ : OrdinarySlotChoice G.E Color K) =
          OrdinarySlotChoice.rightSlot G.snd K ⟨f, d, k, l⟩ :=
      hq.2.symm.trans hp.2
    have heFst : G.fst e = G.fst f :=
      congrArg OrdinarySlot.vertex hleft
    have heSnd : G.snd e = G.snd f :=
      congrArg OrdinarySlot.vertex hright
    have hef : e = f := G.endpoints_injective
      ((Sym2.eq_iff).2 (Or.inl ⟨heFst, heSnd⟩))
    subst f
    have hcd : c = d := congrArg OrdinarySlot.color hleft
    subst d
    have hik : i = k := congrArg OrdinarySlot.place hleft
    have hjl : j = l := congrArg OrdinarySlot.place hright
    subst k
    subst l
    rfl
  · have hleftRight :
        OrdinarySlotChoice.leftSlot G.fst K
            (⟨e, c, i, j⟩ : OrdinarySlotChoice G.E Color K) =
          OrdinarySlotChoice.rightSlot G.snd K ⟨f, d, k, l⟩ :=
      hq.1.symm.trans hp.1
    have hrightLeft :
        OrdinarySlotChoice.rightSlot G.snd K
            (⟨e, c, i, j⟩ : OrdinarySlotChoice G.E Color K) =
          OrdinarySlotChoice.leftSlot G.fst K ⟨f, d, k, l⟩ :=
      hq.2.symm.trans hp.2
    have heFst : G.fst e = G.snd f :=
      congrArg OrdinarySlot.vertex hleftRight
    have heSnd : G.snd e = G.fst f :=
      congrArg OrdinarySlot.vertex hrightLeft
    have hef : e = f := G.endpoints_injective
      ((Sym2.eq_iff).2 (Or.inr ⟨heFst, heSnd⟩))
    subst f
    exact (G.noLoop e heFst).elim
  · have hrightLeft :
        OrdinarySlotChoice.rightSlot G.snd K
            (⟨e, c, i, j⟩ : OrdinarySlotChoice G.E Color K) =
          OrdinarySlotChoice.leftSlot G.fst K ⟨f, d, k, l⟩ :=
      hq.1.symm.trans hp.1
    have hleftRight :
        OrdinarySlotChoice.leftSlot G.fst K
            (⟨e, c, i, j⟩ : OrdinarySlotChoice G.E Color K) =
          OrdinarySlotChoice.rightSlot G.snd K ⟨f, d, k, l⟩ :=
      hq.2.symm.trans hp.2
    have heFst : G.fst e = G.snd f :=
      congrArg OrdinarySlot.vertex hleftRight
    have heSnd : G.snd e = G.fst f :=
      congrArg OrdinarySlot.vertex hrightLeft
    have hef : e = f := G.endpoints_injective
      ((Sym2.eq_iff).2 (Or.inr ⟨heFst, heSnd⟩))
    subst f
    exact (G.noLoop e heFst).elim
  · have hleft :
        OrdinarySlotChoice.leftSlot G.fst K
            (⟨e, c, i, j⟩ : OrdinarySlotChoice G.E Color K) =
          OrdinarySlotChoice.leftSlot G.fst K ⟨f, d, k, l⟩ :=
      hq.2.symm.trans hp.2
    have hright :
        OrdinarySlotChoice.rightSlot G.snd K
            (⟨e, c, i, j⟩ : OrdinarySlotChoice G.E Color K) =
          OrdinarySlotChoice.rightSlot G.snd K ⟨f, d, k, l⟩ :=
      hq.1.symm.trans hp.1
    have heFst : G.fst e = G.fst f :=
      congrArg OrdinarySlot.vertex hleft
    have heSnd : G.snd e = G.snd f :=
      congrArg OrdinarySlot.vertex hright
    have hef : e = f := G.endpoints_injective
      ((Sym2.eq_iff).2 (Or.inl ⟨heFst, heSnd⟩))
    subst f
    have hcd : c = d := congrArg OrdinarySlot.color hleft
    subst d
    have hik : i = k := congrArg OrdinarySlot.place hleft
    have hjl : j = l := congrArg OrdinarySlot.place hright
    subst k
    subst l
    rfl

end WeightedSimpleGraph

end

end WeightedEdgeColoring
