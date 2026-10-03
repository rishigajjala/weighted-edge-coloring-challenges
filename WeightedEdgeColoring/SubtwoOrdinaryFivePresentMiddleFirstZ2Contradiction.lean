import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleFirstExternalContradiction

/-!
# Both structural alternatives at a first return to `Z₂`
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.false_of_middle_first_z2
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hZ2 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 2))
    {z : G.V}
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right z)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ2 : p.1.getVert i = s.path.1.getVert 2) : False := by
  rcases FivePathState.middle_first_z2_external_or_cross_chord
      G s hcritical hdk hdegree hthreshold hnot
      hleft hright hZ2 with hZ3 | ⟨g,hgF,hg3,hg1,hgc⟩
  · exact FivePathState.false_of_middle_first_z2_external_z3
      G s hcritical hdk hdegree hthreshold hnot
      hleft hright hZ2 hZ3 p hi hiLe hfirst hiZ2
  · exact FivePathState.false_of_middle_first_z2_cross_chord
      G s hcritical hdk hdegree hthreshold
      hleft hright hZ2 p hiLe hfirst hiZ2
      hgF hg1 hg3 hgc

end WeightedEdgeColoring.WeightedMultigraph
