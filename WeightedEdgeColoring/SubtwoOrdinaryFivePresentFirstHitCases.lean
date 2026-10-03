import WeightedEdgeColoring.SubtwoOrdinaryFivePresentFirstHitPair

/-!
# Exact ordered first-return cases in the connected present-color branch
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.same_component_first_return_cases
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hcomp : (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.right =
      (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.left) :
    ∃ p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left,
      ∃ i : ℕ, 1 < i ∧ i ≤ p.1.length ∧
        (∀ j, 0 < j → j < i →
          p.1.getVert j ∉ s.path.1.support.toFinset) ∧
        FivePathState.HasExternalColorAt G s c (p.1.getVert i) ∧
        ((p.1.getVert i = s.path.1.getVert 1 ∧
            p.1.getVert (i + 1) = s.left ∧ i + 1 = p.1.length) ∨
          (p.1.getVert i = s.path.1.getVert 2 ∧
            p.1.getVert (i + 1) = s.path.1.getVert 3) ∨
          (p.1.getVert i = s.path.1.getVert 3 ∧
            p.1.getVert (i + 1) = s.path.1.getVert 2)) := by
  obtain ⟨p, i, hi, hiLe, hfirst, hExt, hcase⟩ :=
    FivePathState.same_component_first_return_external G s
      hcritical hdk hdegree hthreshold hleft hright hcomp
  refine ⟨p, i, hi, hiLe, hfirst, hExt, ?_⟩
  rcases hcase with hZ1 | hZ2 | hZ3
  · have hshape := FivePathState.first_return_at_z1_then_left
      G s p hi hiLe hfirst hZ1
    exact Or.inl ⟨hZ1, hshape.1, hshape.2⟩
  · have hshape := FivePathState.first_return_middle_pair
      G s p hi hiLe hfirst (Or.inl hZ2)
    rcases hshape with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · have hshape := FivePathState.first_return_middle_pair
      G s p hi hiLe hfirst (Or.inr hZ3)
    rcases hshape with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

end WeightedEdgeColoring.WeightedMultigraph
