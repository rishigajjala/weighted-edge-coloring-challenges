import WeightedEdgeColoring.SubtwoOrdinaryFivePresentAllColors
import WeightedEdgeColoring.SubtwoOrdinaryChainSeven

/-!
# The five-vertex odd-set obstruction

Every palette color occurs twice among the internal edges of a critical
five-path. Restoring the omitted edge then violates the odd-set density
inequality at the palette size.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem oddSetCertificate_of_critical_fivePath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2) :
    ∃ S : Finset G.V, Odd S.card ∧ 3 ≤ S.card ∧
      (k : ℝ) * ((S.card : ℝ) - 1) <
        (2 : ℝ) * (G.internalEdges F S).card := by
  classical
  let S := p.1.support.toFinset
  have hS : S.card = 5 := by
    dsimp [S]
    rw [List.toFinset_card_of_nodup p.property.support_nodup,
      p.1.length_support, hpLen]
  have heS : G.fst e ∈ S ∧ G.snd e ∈ S := by
    constructor
    · simpa [S] using p.1.start_mem_support
    · simpa [S] using p.1.end_mem_support
  have hall : ∀ c : Fin k,
      2 ≤ ((G.internalEdges (F.erase e) S).filter
        (fun g ↦ color g = c)).card := by
    intro c
    obtain ⟨r, s, hrs, hr, hs, hrc, hsc⟩ :=
      G.two_internal_edges_of_any_color_fivePath
        hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold c
    have hpair : ({r, s} : Finset G.E) ⊆
        (G.internalEdges (F.erase e) S).filter (fun g ↦ color g = c) := by
      intro g hg
      rcases Finset.mem_insert.mp hg with hgr | hgs
      · subst g
        exact Finset.mem_filter.mpr ⟨hr, hrc⟩
      · have hgs' : g = s := by simpa using hgs
        subst g
        exact Finset.mem_filter.mpr ⟨hs, hsc⟩
    have hcard := Finset.card_le_card hpair
    simpa [hrs] using hcard
  exact ⟨S, G.oddSetCertificate_of_allColors_twice_internal_five
    color hS heF heS hall⟩

end WeightedEdgeColoring.WeightedMultigraph
