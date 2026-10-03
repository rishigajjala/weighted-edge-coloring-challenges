import WeightedEdgeColoring.SubtwoOrdinaryFiveOutside

/-!
# Local saturation of a five-vertex critical chain

At its last internal vertex, every edge in a colour missing at either
endpoint stays inside the five-vertex path. This is the local exclusion
used in the first part of Andersen's five-vertex saturation argument.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- An edge of a colour missing at either endpoint, incident to the last
internal vertex of a five-vertex critical path, stays inside its support. -/
theorem last_internal_missingColor_edge_internal_fivePath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {g : G.E} (hgF : g ∈ F.erase e)
    (hgZ : G.Inc (p.1.getVert 3) g)
    (hgMissing : color g ∈
      G.missingColorsAt (F.erase e) color (G.fst e) ∪
      G.missingColorsAt (F.erase e) color (G.snd e)) :
    g ∈ G.internalEdges (F.erase e) p.1.support.toFinset := by
  have hZ : p.1.getVert 3 ∈ p.1.support :=
    p.1.getVert_mem_support 3
  have hother (w : G.V) (hwout : w ∉ p.1.support)
      (hgW : G.Inc w g) : False := by
    rcases Finset.mem_union.mp hgMissing with hcX | hcY
    · exact G.no_outside_last_neighbor_of_missing_first_color
        hcritical heF hproper ha hb hcX p hpLen hdk hdegree hthreshold
        hwout hgF hgZ hgW rfl
    · exact G.no_outside_last_neighbor_of_missing_second_color
        hcritical heF hproper ha hb hcY p hpLen hdk hdegree hthreshold
        hwout hgF hgZ hgW rfl
  apply Finset.mem_filter.mpr
  refine ⟨hgF, ?_⟩
  constructor
  · by_contra hfst
    exact hother (G.fst g) (by simpa using hfst) (Or.inl rfl)
  · by_contra hsnd
    exact hother (G.snd g) (by simpa using hsnd) (Or.inr rfl)

end WeightedEdgeColoring.WeightedMultigraph
