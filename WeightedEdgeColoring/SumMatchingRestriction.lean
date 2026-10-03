import WeightedEdgeColoring.SeparatedOptionSystems

/-!
# Restricting a matching to one option summand
-/

namespace WeightedEdgeColoring

noncomputable section

namespace RankThreeOptionSystem

universe u v v₁ v₂ w₁ w₂

variable {Job : Type u} {Slot : Type v} {Slot₁ : Type v₁} {Slot₂ : Type v₂}
  {Option₁ : Type w₁} {Option₂ : Type w₂}
  [Fintype Job] [Fintype Slot] [Fintype Slot₁] [Fintype Slot₂]
  [Fintype Option₁] [Fintype Option₂]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Slot₁] [DecidableEq Slot₂]
  [DecidableEq Option₁] [DecidableEq Option₂]

/-- Keep just the left options in a finite set of sum options. -/
def leftOptionSet (M : Finset (Option₁ ⊕ Option₂)) : Finset Option₁ :=
  M.biUnion fun z ↦ match z with
    | Sum.inl o => {o}
    | Sum.inr _ => ∅

@[simp] theorem mem_leftOptionSet_iff
    (M : Finset (Option₁ ⊕ Option₂)) (o : Option₁) :
    o ∈ leftOptionSet M ↔ Sum.inl o ∈ M := by
  constructor
  · intro ho
    rcases Finset.mem_biUnion.mp ho with ⟨z, hzM, hzo⟩
    cases z with
    | inl p =>
        simp only [Finset.mem_singleton] at hzo
        subst p
        exact hzM
    | inr p => simp at hzo
  · intro ho
    apply Finset.mem_biUnion.mpr
    exact ⟨Sum.inl o, ho, by simp⟩

/-- Restricting a matching in an ordinary sum preserves a matching on the
left option system. -/
theorem sum_leftOptionSet_isPartialMatching
    (H : RankThreeOptionSystem Job Slot Option₁)
    (K : RankThreeOptionSystem Job Slot Option₂)
    (M : Finset (Option₁ ⊕ Option₂))
    (hM : (H.sum K).IsPartialMatching M) :
    H.IsPartialMatching (leftOptionSet M) := by
  constructor
  · intro o ho p hp hop
    exact hM.1 ((mem_leftOptionSet_iff M o).mp ho)
      ((mem_leftOptionSet_iff M p).mp hp)
      (fun h ↦ hop (Sum.inl.inj h))
  · intro o ho p hp howner
    exact Sum.inl.inj (hM.2 ((mem_leftOptionSet_iff M o).mp ho)
      ((mem_leftOptionSet_iff M p).mp hp) howner)

/-- The same restriction theorem for systems whose two slot types were
embedded into a disjoint sum. -/
theorem separatedSum_leftOptionSet_isPartialMatching
    (H : RankThreeOptionSystem Job Slot₁ Option₁)
    (K : RankThreeOptionSystem Job Slot₂ Option₂)
    (M : Finset (Option₁ ⊕ Option₂))
    (hM : (H.separatedSum K).IsPartialMatching M) :
    H.IsPartialMatching (leftOptionSet M) := by
  have hLift :
      (H.liftSlotsLeft (Slot₂ := Slot₂)).IsPartialMatching
        (leftOptionSet M) :=
    sum_leftOptionSet_isPartialMatching
      (H.liftSlotsLeft (Slot₂ := Slot₂))
      (K.liftSlotsRight (Slot₁ := Slot₁)) M hM
  constructor
  · intro o ho p hp hop
    rw [Compatible, Finset.disjoint_left]
    intro s hso hsp
    have hc := hLift.1 ho hp hop
    exact Finset.disjoint_left.mp hc
      ((H.mem_liftSlotsLeft_inl o s).mpr hso)
      ((H.mem_liftSlotsLeft_inl p s).mpr hsp)
  · exact hLift.2

end RankThreeOptionSystem

end

end WeightedEdgeColoring
