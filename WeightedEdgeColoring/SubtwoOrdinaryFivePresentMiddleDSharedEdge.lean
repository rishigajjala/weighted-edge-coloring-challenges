import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleCAPathShape

/-! # The d edge at Y after the no-middle-c second switch -/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.right_d_edge_to_common_middle
    {F : Finset G.E} {k D : ℕ} {a b c d : Fin k}
    (s : G.FivePathState F k b a)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hdX : d ∈ G.missingColorsAt (F.erase s.omitted) s.paint s.left)
    (hdY : d ∉ G.missingColorsAt (F.erase s.omitted) s.paint s.right)
    {paint₂ : G.E → Fin k}
    (hproper₂ : G.IsProperOn (F.erase s.omitted) paint₂)
    (hcX₂ : c ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.left)
    (haY₂ : a ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.right)
    (hdX₂ : d ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.left)
    (hkeep : ∀ g ∈ F.erase s.omitted,
      s.paint g = d → paint₂ g = d)
    (q : (G.twoColorGraph (F.erase s.omitted) paint₂ c a).Path
      s.left s.right)
    (hqLen : q.1.length = 4)
    {z w u : G.V}
    (hqSupport : q.1.support.toFinset = {s.left,z,w,u,s.right})
    (hwOut : w ∉ s.path.1.support.toFinset)
    (huOut : u ∉ s.path.1.support.toFinset) :
    ∃ g ∈ F.erase s.omitted,
      G.Inc s.right g ∧ G.Inc z g ∧ s.paint g = d := by
  let s₂ : G.FivePathState F k c a := {
    omitted := s.omitted
    paint := paint₂
    left := s.left
    right := s.right
    omitted_mem := s.omitted_mem
    left_ne_right := s.left_ne_right
    left_inc := s.left_inc
    right_inc := s.right_inc
    proper := hproper₂
    left_missing := hcX₂
    right_missing := haY₂
    path := q
    path_len := hqLen
  }
  obtain ⟨g, hgF, hgY, hgD⟩ :=
    G.exists_edge_of_not_missingColor hdY
  have hgS : g ∈ G.internalEdges (F.erase s.omitted)
      s.path.1.support.toFinset :=
    FivePathState.right_color_edge_internal_of_missing_left
      G s hcritical hdk hdegree hthreshold hdX hgF hgY hgD
  have hg₂D : paint₂ g = d := hkeep g hgF hgD
  have hgT : g ∈ G.internalEdges (F.erase s.omitted)
      q.1.support.toFinset := by
    have h := FivePathState.right_color_edge_internal_of_missing_left
      G s₂ hcritical hdk hdegree hthreshold hdX₂ hgF hgY hg₂D
    simpa [s₂] using h
  have hgNotX : ¬G.Inc s.left g := by
    intro hgX
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.left d hdX hgF hgX) hgD
  have hinter := G.old_new_five_support_intersection
    hwOut huOut q hqSupport
  have hgZ : G.Inc z g :=
    G.internal_edge_in_two_supports_at_right
      hinter hgS hgT hgY hgNotX
  exact ⟨g, hgF, hgY, hgZ, hgD⟩

end WeightedEdgeColoring.WeightedMultigraph
