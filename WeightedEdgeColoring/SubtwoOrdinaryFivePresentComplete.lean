import WeightedEdgeColoring.SubtwoOrdinaryFivePresentReverseComponent

/-!
# The normalized present-color branch is impossible
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.false_of_external_ends_not_two_internal
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right) : False := by
  let H := G.twoColorGraph (F.erase s.omitted) s.paint b c
  by_cases hsame : H.connectedComponentMk s.right =
      H.connectedComponentMk s.left
  · exact FivePathState.false_of_same_bc_component_with_external_ends
      G s hcritical hdk hdegree hthreshold hnot
        hleft hright hsame
  have hseparate : H.connectedComponentMk s.left ≠
      H.connectedComponentMk s.right := by
    intro h
    exact hsame h.symm
  have hAC := FivePathState.same_ac_component_of_separate_bc
    G s hcritical hdk hdegree hthreshold hnot
      hleft hright hseparate
  let sr := s.reverse
  have hnotR := FivePathState.reverse_not_two_internal G s hnot
  have hleftR : FivePathState.HasExternalColorAt G sr c sr.left :=
    FivePathState.reverse_external G s hright
  have hrightR : FivePathState.HasExternalColorAt G sr c sr.right :=
    FivePathState.reverse_external G s hleft
  have hcompR :
      (G.twoColorGraph (F.erase sr.omitted) sr.paint a c).connectedComponentMk
        sr.right =
      (G.twoColorGraph (F.erase sr.omitted) sr.paint a c).connectedComponentMk
        sr.left := by
    simpa [sr, FivePathState.reverse] using hAC
  exact FivePathState.false_of_same_bc_component_with_external_ends
    G sr hcritical hdk hdegree hthreshold hnotR
      hleftR hrightR hcompR

end WeightedEdgeColoring.WeightedMultigraph
