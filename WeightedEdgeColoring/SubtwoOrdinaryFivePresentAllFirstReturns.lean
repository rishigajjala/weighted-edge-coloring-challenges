import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleFirstZ3Contradiction

/-!
# All three possible first returns are impossible
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.false_of_same_bc_component_with_external_ends
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hcomp : (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.right =
      (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.left) : False := by
  obtain ⟨p,i,hi,hiLe,hfirst,hExt,hcase⟩ :=
    FivePathState.same_component_first_return_external
      G s hcritical hdk hdegree hthreshold hleft hright hcomp
  rcases hcase with hZ1 | hZ2 | hZ3
  · have hZ1Ext : FivePathState.HasExternalColorAt G s c
        (s.path.1.getVert 1) := hZ1 ▸ hExt
    by_cases hmiddle : ∃ g, g ∈ F.erase s.omitted ∧
        G.Inc (s.path.1.getVert 2) g ∧
        G.Inc (s.path.1.getVert 3) g ∧ s.paint g = c
    · obtain ⟨g,hgF,hg2,hg3,hgc⟩ := hmiddle
      exact FivePathState.false_of_vz1_internal_c
        G s hcritical hdk hdegree hthreshold
          hleft hright hZ1Ext p hi hiLe hfirst hZ1
          hgF hg2 hg3 hgc
    · exact FivePathState.false_of_vz1_no_middle_c
        G s hcritical hdk hdegree hthreshold hnot
          hleft hright hZ1Ext hmiddle p hi hiLe hfirst hZ1
  · have hZ2Ext : FivePathState.HasExternalColorAt G s c
        (s.path.1.getVert 2) := hZ2 ▸ hExt
    exact FivePathState.false_of_middle_first_z2
      G s hcritical hdk hdegree hthreshold hnot
        hleft hright hZ2Ext p hi hiLe hfirst hZ2
  · have hZ3Ext : FivePathState.HasExternalColorAt G s c
        (s.path.1.getVert 3) := hZ3 ▸ hExt
    exact FivePathState.false_of_middle_first_z3
      G s hcritical hdk hdegree hthreshold
        hleft hright hZ3Ext p hi hiLe hfirst hZ3

end WeightedEdgeColoring.WeightedMultigraph
