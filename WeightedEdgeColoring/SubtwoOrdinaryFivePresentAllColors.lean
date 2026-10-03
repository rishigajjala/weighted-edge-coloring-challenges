import WeightedEdgeColoring.SubtwoOrdinaryFivePresentComplete
import WeightedEdgeColoring.SubtwoOrdinaryFivePresentEndpoint

/-!
# Every palette color saturates a critical five-path

Endpoint normalization and the complete present-color contradiction imply
Andersen's five-path saturation statement for every color, including colors
present at all five vertices.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem two_internal_edges_of_any_color_fivePath
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
    (c : Fin k) :
    ∃ r s, r ≠ s ∧
      r ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      s ∈ G.internalEdges (F.erase e) p.1.support.toFinset ∧
      color r = c ∧ color s = c := by
  by_contra hnot
  obtain ⟨a', b', t, _, hleft, hright, hnotT⟩ :=
    G.unsaturated_color_has_recolored_external_endpoint_pair
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold hnot
  exact FivePathState.false_of_external_ends_not_two_internal
    G t hcritical hdk hdegree hthreshold hnotT hleft hright

end WeightedEdgeColoring.WeightedMultigraph
