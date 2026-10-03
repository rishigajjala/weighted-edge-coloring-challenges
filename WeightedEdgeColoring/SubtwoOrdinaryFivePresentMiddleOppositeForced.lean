import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleFirstOrderContradiction

/-!
# The only surviving order on the middle pair

The first order has already been eliminated by the actual circuit and
second-switch contradiction. Thus any remaining five-path witness has
the opposite middle-pair order on its rooted two-color chain.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.exists_middle_pair_opposite_order
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
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ1 : p.1.getVert i = s.path.1.getVert 1)
    (hnoMiddle : ¬∃ g, g ∈ F.erase s.omitted ∧
      G.Inc (s.path.1.getVert 2) g ∧
      G.Inc (s.path.1.getVert 3) g ∧ s.paint g = c) :
    ∃ q₂ : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
        s.right (s.path.1.getVert 2),
      p.1.length ≤ q₂.1.length ∧
      q₂.1.getVert p.1.length = s.left ∧
      q₂.1.getVert (q₂.1.length - 1) =
        s.path.1.getVert 3 := by
  obtain ⟨q₂,q₃,hq₂Len,hq₃Len,hX₂,hX₃,horder⟩ :=
    FivePathState.exists_middle_pair_penultimate_order
      G s hcritical hdk hdegree hthreshold hnot
        hleft hright hZ1 p hi hiLe hfirst hiZ1 hnoMiddle
  rcases horder with hZ2First | hZ3First
  · exact False.elim (FivePathState.false_of_vz1_no_middle_c_z2_first
      G s hcritical hdk hdegree hthreshold hnot
        hleft hright hZ1 hnoMiddle p hi hiLe hfirst hiZ1
        q₃ hq₃Len hX₃ hZ2First)
  · exact ⟨q₂,hq₂Len,hX₂,hZ3First⟩

end WeightedEdgeColoring.WeightedMultigraph
