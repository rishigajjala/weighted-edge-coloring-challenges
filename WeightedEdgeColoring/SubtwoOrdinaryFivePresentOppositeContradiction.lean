import WeightedEdgeColoring.SubtwoOrdinaryFivePresentOppositeFirstHitTransport

/-!
# The opposite middle order reduces to the first order

This is the missing symmetry step in Andersen's five-vertex argument.
After shifting the omitted edge once, the old exterior prefix and suffix
force the new rooted `(b,c)` path to meet its middle pair in the first
order.  The already proved circuit contradiction then applies.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.false_of_vz1_no_middle_c_z3_first
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hZ1 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 1))
    (hnoMiddle : ¬∃ g, g ∈ F.erase s.omitted ∧
      G.Inc (s.path.1.getVert 2) g ∧
      G.Inc (s.path.1.getVert 3) g ∧ s.paint g = c)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ1 : p.1.getVert i = s.path.1.getVert 1)
    (q₂ : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right (s.path.1.getVert 2))
    (hqLen : p.1.length ≤ q₂.1.length)
    (hX : q₂.1.getVert p.1.length = s.left)
    (hpen : q₂.1.getVert (q₂.1.length-1) =
      s.path.1.getVert 3) : False := by
  obtain ⟨u, huL, huR, hu1, hu2, hu3, _, huPaint,
    huNot, huExtL, huExtR, huExt1,
    pre, hpreCap, r, hrCap⟩ :=
    FivePathState.exists_first_shift_transported_exterior_routes
      G s hcritical hnot hleft hright hZ1
      p hi hiLe hfirst hiZ1 q₂ hqLen hX hpen
  obtain ⟨p',i',hi',hiLe',hfirst',hi1',
    q₃,hqLen',hX',hpen'⟩ :=
    FivePathState.exists_first_order_middle_path_of_exterior_routes
      G u hcritical hdk hdegree hthreshold
      huExtL huExtR pre hpreCap r hrCap
  have hcb := (FivePathState.external_endpoint_color_ne_missing
    G s hleft hright).2
  have hnoMiddleU : ¬∃ g, g ∈ F.erase u.omitted ∧
      G.Inc (u.path.1.getVert 2) g ∧
      G.Inc (u.path.1.getVert 3) g ∧ u.paint g = c := by
    intro h
    obtain ⟨g,hgF,hg2,hg3,hgc⟩ := h
    have hgNe : g ≠ s.omitted := by
      intro heq
      have hnew : u.paint g = b := by
        rw [huPaint, heq]
        simp [assignEdgeColor]
      exact hcb (hgc.symm.trans hnew)
    have hgOld : g ∈ F.erase s.omitted :=
      Finset.mem_erase.mpr ⟨hgNe,(Finset.mem_erase.mp hgF).2⟩
    have hgcOld : s.paint g = c := by
      rw [huPaint, G.assignEdgeColor_of_ne s.paint hgNe b] at hgc
      exact hgc
    exact hnoMiddle ⟨g,hgOld,hu3 ▸ hg3,hu2 ▸ hg2,hgcOld⟩
  exact FivePathState.false_of_vz1_no_middle_c_z2_first
    G u hcritical hdk hdegree hthreshold huNot
      huExtL huExtR huExt1 hnoMiddleU
      p' hi' hiLe' hfirst' hi1' q₃ hqLen' hX' hpen'

/-- The two possible orders of the middle pair are both impossible. -/
theorem FivePathState.false_of_vz1_no_middle_c
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hZ1 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 1))
    (hnoMiddle : ¬∃ g, g ∈ F.erase s.omitted ∧
      G.Inc (s.path.1.getVert 2) g ∧
      G.Inc (s.path.1.getVert 3) g ∧ s.paint g = c)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ1 : p.1.getVert i = s.path.1.getVert 1) : False := by
  obtain ⟨q₂,hqLen,hX,hpen⟩ :=
    FivePathState.exists_middle_pair_opposite_order
      G s hcritical hdk hdegree hthreshold hnot
      hleft hright hZ1 p hi hiLe hfirst hiZ1 hnoMiddle
  exact FivePathState.false_of_vz1_no_middle_c_z3_first
    G s hcritical hdk hdegree hthreshold hnot
      hleft hright hZ1 hnoMiddle p hi hiLe hfirst hiZ1
      q₂ hqLen hX hpen

end WeightedEdgeColoring.WeightedMultigraph
