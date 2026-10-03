import WeightedEdgeColoring.DivisibleLocalExtraSlotOptions
import WeightedEdgeColoring.PairUniqueOptions
import WeightedEdgeColoring.WeightedGraph

namespace WeightedEdgeColoring

noncomputable section

universe u w

namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]
variable (bucket : G.E → Class) (B : G.V → Class → ℕ)
variable
  (hleftDiv : ∀ e, B (G.fst e) (bucket e) ∣
    DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)
  (hrightDiv : ∀ e, B (G.snd e) (bucket e) ∣
    DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)

theorem divisibleLocalExtraChoice_pairUnique
    (hleft : ∀ e, 0 < B (G.fst e) (bucket e))
    (hright : ∀ e, 0 < B (G.snd e) (bucket e)) :
    (DivisibleLocalExtraChoice.system G.fst G.snd bucket B
      hleftDiv hrightDiv).PairUnique := by
  intro s t hst q p hsq htq hsp htp
  have orient (x : DivisibleLocalExtraChoice G.E G.V Class
      G.fst G.snd bucket B)
      (hsx : s ∈ (DivisibleLocalExtraChoice.system G.fst G.snd bucket B
        hleftDiv hrightDiv).slots x)
      (htx : t ∈ (DivisibleLocalExtraChoice.system G.fst G.snd bucket B
        hleftDiv hrightDiv).slots x) :
      (s = DivisibleLocalExtraChoice.leftSlot G.fst G.snd bucket B
          hleftDiv x ∧
        t = DivisibleLocalExtraChoice.rightSlot G.fst G.snd bucket B
          hrightDiv x) ∨
      (s = DivisibleLocalExtraChoice.rightSlot G.fst G.snd bucket B
          hrightDiv x ∧
        t = DivisibleLocalExtraChoice.leftSlot G.fst G.snd bucket B
          hleftDiv x) := by
    simp only [DivisibleLocalExtraChoice.system, Finset.mem_insert,
      Finset.mem_singleton] at hsx htx
    rcases hsx with hs | hs <;> rcases htx with ht | ht
    · exact (hst (hs.trans ht.symm)).elim
    · exact Or.inl ⟨hs, ht⟩
    · exact Or.inr ⟨hs, ht⟩
    · exact (hst (hs.trans ht.symm)).elim
  rcases q with ⟨e, i⟩
  rcases p with ⟨f, k⟩
  have hq := orient ⟨e, i⟩ hsq htq
  have hp := orient ⟨f, k⟩ hsp htp
  rcases hq with hq | hq <;> rcases hp with hp | hp
  · have hl := hq.1.symm.trans hp.1
    have hr := hq.2.symm.trans hp.2
    have hef : e = f := G.endpoints_injective ((Sym2.eq_iff).2 (Or.inl
      ⟨congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hl,
        congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hr⟩))
    subst f
    have hiLeft :
        DivisibleLocalExtraChoice.leftIndex G.fst G.snd bucket B hleftDiv
            ⟨e, i⟩ =
          DivisibleLocalExtraChoice.leftIndex G.fst G.snd bucket B hleftDiv
            ⟨e, k⟩ := Fin.ext
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.2.val) hl)
    have hiRight :
        DivisibleLocalExtraChoice.rightIndex G.fst G.snd bucket B hrightDiv
            ⟨e, i⟩ =
          DivisibleLocalExtraChoice.rightIndex G.fst G.snd bucket B hrightDiv
            ⟨e, k⟩ := Fin.ext
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.2.val) hr)
    have hik : i = k := by
      rcases le_total (B (G.fst e) (bucket e))
          (B (G.snd e) (bucket e)) with hle | hle
      · exact DivisibleLocalExtraChoice.rightIndex_injective_of_left_le
          G.fst G.snd bucket B hrightDiv hright e hle hiRight
      · exact DivisibleLocalExtraChoice.leftIndex_injective_of_right_le
          G.fst G.snd bucket B hleftDiv hleft e hle hiLeft
    subst k
    rfl

  · have hlr := hq.1.symm.trans hp.1
    have hrl := hq.2.symm.trans hp.2
    have hef : e = f := G.endpoints_injective ((Sym2.eq_iff).2 (Or.inr
      ⟨congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hlr,
        congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hrl⟩))
    subst f
    exact (G.noLoop e
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hlr)).elim
  · have hrl := hq.1.symm.trans hp.1
    have hlr := hq.2.symm.trans hp.2
    have hef : e = f := G.endpoints_injective ((Sym2.eq_iff).2 (Or.inr
      ⟨congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hlr,
        congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hrl⟩))
    subst f
    exact (G.noLoop e
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hlr)).elim
  · have hr := hq.1.symm.trans hp.1
    have hl := hq.2.symm.trans hp.2
    have hef : e = f := G.endpoints_injective ((Sym2.eq_iff).2 (Or.inl
      ⟨congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hl,
        congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hr⟩))
    subst f
    have hiLeft :
        DivisibleLocalExtraChoice.leftIndex G.fst G.snd bucket B hleftDiv
            ⟨e, i⟩ =
          DivisibleLocalExtraChoice.leftIndex G.fst G.snd bucket B hleftDiv
            ⟨e, k⟩ := Fin.ext
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.2.val) hl)
    have hiRight :
        DivisibleLocalExtraChoice.rightIndex G.fst G.snd bucket B hrightDiv
            ⟨e, i⟩ =
          DivisibleLocalExtraChoice.rightIndex G.fst G.snd bucket B hrightDiv
            ⟨e, k⟩ := Fin.ext
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.2.val) hr)
    have hik : i = k := by
      rcases le_total (B (G.fst e) (bucket e))
          (B (G.snd e) (bucket e)) with hle | hle
      · exact DivisibleLocalExtraChoice.rightIndex_injective_of_left_le
          G.fst G.snd bucket B hrightDiv hright e hle hiRight
      · exact DivisibleLocalExtraChoice.leftIndex_injective_of_right_le
          G.fst G.snd bucket B hleftDiv hleft e hle hiLeft
    subst k
    rfl

theorem quantized_divisibleLocalExtraSlotPairCodegree_le_reserve
    (residual : G.E → ℝ) (hr0 : ∀ e, 0 ≤ residual e)
    (hr1 : ∀ e, residual e ≤ 1)
    (hleft : ∀ e, 0 < B (G.fst e) (bucket e))
    (hright : ∀ e, 0 < B (G.snd e) (bucket e))
    {reserve : ℕ} (hreserve0 : 0 < reserve)
    (hreserve : ∀ v h, reserve ≤ B v h) (N : ℕ)
    {s t : ExtraSlot G.V Class B} (hst : s ≠ t) :
    ((((DivisibleLocalExtraChoice.system G.fst G.snd bucket B
      hleftDiv hrightDiv).quantized N
      (DivisibleLocalExtraChoice.mass G.fst G.snd bucket B residual)).slotPairCodegree
        s t : ℕ) : ℝ) ≤ (N : ℝ) / reserve := by
  have hrpos : (0 : ℝ) < reserve := by exact_mod_cast hreserve0
  calc
    _ ≤ (N : ℝ) * (1 / (reserve : ℝ)) := by
      apply (DivisibleLocalExtraChoice.system G.fst G.snd bucket B
        hleftDiv hrightDiv).quantized_slotPairCodegree_le
          (G.divisibleLocalExtraChoice_pairUnique bucket B hleftDiv hrightDiv
            hleft hright)
          N (DivisibleLocalExtraChoice.mass G.fst G.snd bucket B residual)
          (1 / (reserve : ℝ))
      · exact le_of_lt (one_div_pos.mpr hrpos)
      · exact DivisibleLocalExtraChoice.mass_nonneg
          G.fst G.snd bucket B residual hr0
      · intro p
        have hT : reserve ≤
            DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B p.1 :=
          (hreserve (G.fst p.1) (bucket p.1)).trans
            (Nat.le_max_left _ _)
        exact residual_div_count_le_inv_reserve (residual p.1) (hr1 p.1)
          hreserve0 hT
      · exact hst
    _ = (N : ℝ) / reserve := by ring

end WeightedSimpleGraph

end

end WeightedEdgeColoring
