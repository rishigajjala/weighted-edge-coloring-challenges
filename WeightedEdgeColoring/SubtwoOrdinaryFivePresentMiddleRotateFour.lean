import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleOppositeForced

/-!
# Rotate the omitted edge four times around the critical pentagon

The last state omits the former `XZ₁` edge. Its ordered critical path is
`X,Y,Z₃,Z₂,Z₁`, so the two middle vertices occur in the opposite order.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

private theorem FivePathState.shift_paint_stable_outside
    {F : Finset G.E} {k : ℕ} {a b : Fin k}
    (s t : G.FivePathState F k a b)
    (hpaint : t.paint = G.assignEdgeColor s.paint s.omitted a)
    {v : G.V} (hv : v ∉ s.path.1.support.toFinset)
    {r : G.E} (hrInc : G.Inc v r) :
    t.paint r = s.paint r := by
  have hrNe : r ≠ s.omitted := by
    intro heq
    subst r
    have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc
      s.left_ne_right s.left_inc s.right_inc
    have hvLR : v = s.left ∨ v = s.right := by
      rcases hends with ⟨hf,hs⟩ | ⟨hf,hs⟩
      · rcases hrInc with hfV | hsV
        · exact Or.inl (hfV.symm.trans hf)
        · exact Or.inr (hsV.symm.trans hs)
      · rcases hrInc with hfV | hsV
        · exact Or.inr (hfV.symm.trans hf)
        · exact Or.inl (hsV.symm.trans hs)
    rcases hvLR with hL | hR
    · have hm : v ∈ s.path.1.support.toFinset := by
        rw [hL]
        simpa only [List.mem_toFinset] using s.path.1.start_mem_support
      exact hv hm
    · have hm : v ∈ s.path.1.support.toFinset := by
        rw [hR]
        simpa only [List.mem_toFinset] using s.path.1.end_mem_support
      exact hv hm
  rw [hpaint, G.assignEdgeColor_of_ne s.paint hrNe a]

theorem FivePathState.exists_four_shift_rotation
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hca : c ≠ a) (hcb : c ≠ b) :
    ∃ t : G.FivePathState F k b a,
      t.left = s.left ∧
      t.right = s.path.1.getVert 1 ∧
      t.path.1.getVert 1 = s.right ∧
      t.path.1.getVert 2 = s.path.1.getVert 3 ∧
      t.path.1.getVert 3 = s.path.1.getVert 2 ∧
      t.path.1.support.toFinset = s.path.1.support.toFinset ∧
      (∀ v, v ∉ s.path.1.support.toFinset →
        ∀ r, G.Inc v r → t.paint r = s.paint r) ∧
      (∀ v, FivePathState.HasExternalColorAt G s c v →
        FivePathState.HasExternalColorAt G t c v) ∧
      (FivePathState.NotTwoInternalColor G s c →
        FivePathState.NotTwoInternalColor G t c) := by
  obtain ⟨s₁,h₁F,h₁I,h₁P,h₁L,h₁R,h₁S,h₁V1,h₁V2,h₁V3⟩ :=
    FivePathState.exists_shiftLast G s hcritical
  let r₁ := s₁.reverse
  obtain ⟨s₂,h₂F,h₂I,h₂P,h₂L,h₂R,h₂S,h₂V1,h₂V2,h₂V3⟩ :=
    FivePathState.exists_shiftLast G r₁ hcritical
  let r₂ := s₂.reverse
  obtain ⟨s₃,h₃F,h₃I,h₃P,h₃L,h₃R,h₃S,h₃V1,h₃V2,h₃V3⟩ :=
    FivePathState.exists_shiftLast G r₂ hcritical
  let r₃ := s₃.reverse
  obtain ⟨t,h₄F,h₄I,h₄P,h₄L,h₄R,h₄S,h₄V1,h₄V2,h₄V3⟩ :=
    FivePathState.exists_shiftLast G r₃ hcritical
  have hr₁V1 : r₁.path.1.getVert 1 = s.left := by
    rw [FivePathState.reverse_getVert G s₁ 1]
    simpa using h₁V3
  have hr₁V2 : r₁.path.1.getVert 2 = s.path.1.getVert 1 := by
    rw [FivePathState.reverse_getVert G s₁ 2]
    simpa using h₁V2
  have hr₁V3 : r₁.path.1.getVert 3 = s.path.1.getVert 2 := by
    rw [FivePathState.reverse_getVert G s₁ 3]
    simpa using h₁V1
  have hs₂L : s₂.left = s.path.1.getVert 2 := h₂L.trans hr₁V3
  have hs₂R : s₂.right = s.path.1.getVert 3 := h₂R.trans h₁L
  have hs₂V1 : s₂.path.1.getVert 1 = s.path.1.getVert 1 :=
    h₂V1.trans hr₁V2
  have hs₂V2 : s₂.path.1.getVert 2 = s.left := by
    rw [h₂V2, FivePathState.reverse_getVert G s₁ 1]
    exact h₁V3
  have hs₂V3 : s₂.path.1.getVert 3 = s.right := by
    rw [h₂V3]
    exact h₁R
  have hr₂V1 : r₂.path.1.getVert 1 = s.right := by
    rw [FivePathState.reverse_getVert G s₂ 1]
    exact hs₂V3
  have hr₂V2 : r₂.path.1.getVert 2 = s.left := by
    rw [FivePathState.reverse_getVert G s₂ 2]
    exact hs₂V2
  have hr₂V3 : r₂.path.1.getVert 3 = s.path.1.getVert 1 := by
    rw [FivePathState.reverse_getVert G s₂ 3]
    exact hs₂V1
  have hs₃L : s₃.left = s.path.1.getVert 1 := h₃L.trans hr₂V3
  have hs₃R : s₃.right = s.path.1.getVert 2 := h₃R.trans hs₂L
  have hs₃V1 : s₃.path.1.getVert 1 = s.left := h₃V1.trans hr₂V2
  have hs₃V2 : s₃.path.1.getVert 2 = s.right := h₃V2.trans hr₂V1
  have hs₃V3 : s₃.path.1.getVert 3 = s.path.1.getVert 3 := by
    rw [h₃V3]
    exact hs₂R
  have hr₃V1 : r₃.path.1.getVert 1 = s.path.1.getVert 3 := by
    rw [FivePathState.reverse_getVert G s₃ 1]
    exact hs₃V3
  have hr₃V2 : r₃.path.1.getVert 2 = s.right := by
    rw [FivePathState.reverse_getVert G s₃ 2]
    exact hs₃V2
  have hr₃V3 : r₃.path.1.getVert 3 = s.left := by
    rw [FivePathState.reverse_getVert G s₃ 3]
    exact hs₃V1
  have htL : t.left = s.left := h₄L.trans hr₃V3
  have htR : t.right = s.path.1.getVert 1 := h₄R.trans hs₃L
  have htV1 : t.path.1.getVert 1 = s.right := h₄V1.trans hr₃V2
  have htV2 : t.path.1.getVert 2 = s.path.1.getVert 3 :=
    h₄V2.trans hr₃V1
  have htV3 : t.path.1.getVert 3 = s.path.1.getVert 2 := by
    rw [h₄V3]
    exact hs₃R
  have htS : t.path.1.support.toFinset = s.path.1.support.toFinset := by
    rw [h₄S, FivePathState.reverse_support G s₃, h₃S,
      FivePathState.reverse_support G s₂, h₂S,
      FivePathState.reverse_support G s₁, h₁S]
  have hStable : ∀ v, v ∉ s.path.1.support.toFinset →
      ∀ r, G.Inc v r → t.paint r = s.paint r := by
    intro v hv r hr
    have hS₁ : v ∉ s₁.path.1.support.toFinset := by simpa [h₁S] using hv
    have hr₁ : v ∉ r₁.path.1.support.toFinset := by
      change v ∉ s₁.reverse.path.1.support.toFinset
      simpa [FivePathState.reverse_support G s₁] using hS₁
    have hS₂ : v ∉ s₂.path.1.support.toFinset := by simpa [h₂S] using hr₁
    have hr₂ : v ∉ r₂.path.1.support.toFinset := by
      change v ∉ s₂.reverse.path.1.support.toFinset
      simpa [FivePathState.reverse_support G s₂] using hS₂
    have hS₃ : v ∉ s₃.path.1.support.toFinset := by simpa [h₃S] using hr₂
    have hr₃ : v ∉ r₃.path.1.support.toFinset := by
      change v ∉ s₃.reverse.path.1.support.toFinset
      simpa [FivePathState.reverse_support G s₃] using hS₃
    calc
      t.paint r = r₃.paint r :=
        FivePathState.shift_paint_stable_outside G r₃ t h₄P hr₃ hr
      _ = s₃.paint r := rfl
      _ = r₂.paint r :=
        FivePathState.shift_paint_stable_outside G r₂ s₃ h₃P hr₂ hr
      _ = s₂.paint r := rfl
      _ = r₁.paint r :=
        FivePathState.shift_paint_stable_outside G r₁ s₂ h₂P hr₁ hr
      _ = s₁.paint r := rfl
      _ = s.paint r :=
        FivePathState.shift_paint_stable_outside G s s₁ h₁P hv hr
  have hExt : ∀ v, FivePathState.HasExternalColorAt G s c v →
      FivePathState.HasExternalColorAt G t c v := by
    intro v hv
    have hv₁ := FivePathState.external_preserved_of_shiftLast
      G s s₁ h₁I h₁P h₁S hv
    have hvr₁ := FivePathState.reverse_external G s₁ hv₁
    have hv₂ := FivePathState.external_preserved_of_shiftLast
      G r₁ s₂ h₂I h₂P h₂S hvr₁
    have hvr₂ := FivePathState.reverse_external G s₂ hv₂
    have hv₃ := FivePathState.external_preserved_of_shiftLast
      G r₂ s₃ h₃I h₃P h₃S hvr₂
    have hvr₃ := FivePathState.reverse_external G s₃ hv₃
    exact FivePathState.external_preserved_of_shiftLast
      G r₃ t h₄I h₄P h₄S hvr₃
  have hNot : FivePathState.NotTwoInternalColor G s c →
      FivePathState.NotTwoInternalColor G t c := by
    intro hn
    have hn₁ := FivePathState.not_two_internal_preserved_of_shiftLast
      G s s₁ hca h₁P h₁S hn
    have hnr₁ := FivePathState.reverse_not_two_internal G s₁ hn₁
    have hn₂ := FivePathState.not_two_internal_preserved_of_shiftLast
      G r₁ s₂ hcb h₂P h₂S hnr₁
    have hnr₂ := FivePathState.reverse_not_two_internal G s₂ hn₂
    have hn₃ := FivePathState.not_two_internal_preserved_of_shiftLast
      G r₂ s₃ hca h₃P h₃S hnr₂
    have hnr₃ := FivePathState.reverse_not_two_internal G s₃ hn₃
    exact FivePathState.not_two_internal_preserved_of_shiftLast
      G r₃ t hcb h₄P h₄S hnr₃
  exact ⟨t,htL,htR,htV1,htV2,htV3,htS,hStable,hExt,hNot⟩

end WeightedEdgeColoring.WeightedMultigraph
