import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleExternal

/-!
# The exact exceptional chord in a middle-first return

If `c` leaves the old five vertices at `X`, `Y`, and `Z₂`, then either it
also leaves at `Z₃`, or its edge at `Z₃` is the internal `Z₁Z₃` chord.
This is the missing alternative in a one-edge shift normalization.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.middle_first_z2_external_or_cross_chord
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hZ2 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 2)) :
    FivePathState.HasExternalColorAt G s c
        (s.path.1.getVert 3) ∨
      ∃ g, g ∈ F.erase s.omitted ∧
        G.Inc (s.path.1.getVert 3) g ∧
        G.Inc (s.path.1.getVert 1) g ∧ s.paint g = c := by
  classical
  by_cases hZ3 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 3)
  · exact Or.inl hZ3
  right
  by_contra hnoChord
  let S := s.path.1.support.toFinset
  have hother : ∀ w ∈ S,
      w ≠ s.path.1.getVert 3 → w ≠ s.path.1.getVert 1 →
      FivePathState.HasExternalColorAt G s c w := by
    intro w hwS hwNe3 hwNe1
    have hS := FivePathState.support_eq_five_vertices G s
    change w ∈ s.path.1.support.toFinset at hwS
    rw [hS] at hwS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwS
    rcases hwS with hX | hZ1 | hZ2eq | hZ3eq | hY
    · simpa [hX] using hleft
    · exact False.elim (hwNe1 hZ1)
    · simpa [hZ2eq] using hZ2
    · exact False.elim (hwNe3 hZ3eq)
    · simpa [hY] using hright
  have hpresent := FivePathState.present_at_every_vertex_of_not_two_internal
    G s hcritical hdk hdegree hthreshold hnot
  have hpresent3 : c ∉ G.missingColorsAt
      (F.erase s.omitted) s.paint (s.path.1.getVert 3) :=
    hpresent _ (s.path.1.getVert_mem_support 3)
  exact hZ3 (G.external_color_at_of_present_no_middle_edge
    s.proper hpresent3
    (fun w hwS hwNe3 hwNe1 ↦ hother w hwS hwNe3 hwNe1)
    hnoChord)

end WeightedEdgeColoring.WeightedMultigraph
