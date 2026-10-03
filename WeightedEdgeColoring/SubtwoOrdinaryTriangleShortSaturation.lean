import WeightedEdgeColoring.SubtwoOrdinaryTriangleShortPresent
import WeightedEdgeColoring.BPOrdinaryCriticalTriangleSaturation

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem allColors_internal_criticalTriangle_short
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    (hdk : d + 1 < k) (hdegree : ∀ v, G.degreeOn F v ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hno : G.NoOddSetCertificateAt F k) :
    ∃ S : Finset G.V, S.card = 3 ∧
      G.fst e ∈ S ∧ G.snd e ∈ S ∧
      ∀ c : Fin k, ∃ g,
        g ∈ G.internalEdges (F.erase e) S ∧ color g = c := by
  have hdegreeErase : ∀ v, G.degreeOn (F.erase e) v < k := by
    intro v
    exact (G.degreeOn_mono_critical (Finset.erase_subset e F) v).trans_lt
      ((hdegree v).trans_lt (by omega))
  obtain ⟨a, ha⟩ :=
    G.exists_mem_missingColorsAt_of_degreeOn_lt hproper
      (hdegreeErase (G.fst e))
  obtain ⟨b, hb⟩ :=
    G.exists_mem_missingColorsAt_of_degreeOn_lt hproper
      (hdegreeErase (G.snd e))
  obtain ⟨p, _⟩ := G.exists_criticalEndpointPath
    hcritical heF hproper ha hb
  have hpLength := G.criticalPath_length_eq_two_of_no_oddSetCertificate
    hcritical heF hproper ha hb p hdk hdegree hthreshold hno
  let x := G.fst e
  let y := G.snd e
  let z := p.1.getVert 1
  let S : Finset G.V := {x, y, z}
  have hxy : x ≠ y := G.noLoop e
  have hxz : x ≠ z := by
    have hAdj : (G.twoColorGraph (F.erase e) color a b).Adj x z := by
      simpa [x, z] using p.1.adj_getVert_succ (i := 0) (by omega)
    exact hAdj.ne
  have hyz : y ≠ z := by
    have hend : p.1.getVert 2 = G.snd e := by
      simpa [hpLength] using p.1.getVert_length
    have hAdj : (G.twoColorGraph (F.erase e) color a b).Adj z y := by
      simpa [y, z, hend] using
        p.1.adj_getVert_succ (i := 1) (by omega)
    exact hAdj.ne.symm
  have hScard : S.card = 3 := by
    simp [S, hxy, hxz, hyz]
  refine ⟨S, hScard, by simp [S, x], by simp [S, y], ?_⟩
  intro c
  by_cases hcx : c ∈ G.missingColorsAt (F.erase e) color x
  · rcases G.exists_oppositeEdge_of_mem_missing_first_of_threeChain_short
        hcritical heF hproper ha hb p hdk hdegree hthreshold hno
        (by simpa [x] using hcx) with
      ⟨g, hgF, hgz, hgy, hgc⟩
    refine ⟨g, ?_, hgc⟩
    exact G.mem_internalEdges_of_mem_of_inc_inc hgF hyz.symm
      (by simp [S, z]) (by simp [S, y]) hgz hgy
  · by_cases hcy : c ∈ G.missingColorsAt (F.erase e) color y
    · rcases G.exists_oppositeEdge_of_mem_missing_second_of_threeChain_short
          hcritical heF hproper ha hb p hdk hdegree hthreshold hno
          (by simpa [y] using hcy) with
        ⟨g, hgF, hgx, hgz, hgc⟩
      refine ⟨g, ?_, hgc⟩
      exact G.mem_internalEdges_of_mem_of_inc_inc hgF hxz
        (by simp [S, x]) (by simp [S, z]) hgx hgz
    · by_cases hcz : c ∈ G.missingColorsAt (F.erase e) color z
      · rcases G.exists_endpointEdge_of_mem_missing_middle_of_threeChain_short
            hcritical heF hproper ha hb p hdk hdegree hthreshold hno
            (by simpa [z] using hcz) with
          ⟨g, hgF, hgx, hgy, hgc⟩
        refine ⟨g, ?_, hgc⟩
        exact G.mem_internalEdges_of_mem_of_inc_inc hgF hxy
          (by simp [S, x]) (by simp [S, y]) hgx hgy
      · rcases G.exists_triangleEdge_of_not_missing_middle_of_threeChain_short
            hcritical heF hproper ha hb p hdk hdegree hthreshold hno
            (by simpa [z] using hcz) with
          ⟨g, hgF, hgc, hpair⟩
        refine ⟨g, ?_, hgc⟩
        rcases hpair with hxyEdge | hxzEdge | hyzEdge
        · exact G.mem_internalEdges_of_mem_of_inc_inc hgF hxy
            (by simp [S, x]) (by simp [S, y]) hxyEdge.1 hxyEdge.2
        · exact G.mem_internalEdges_of_mem_of_inc_inc hgF hxz
            (by simp [S, x]) (by simp [S, z]) hxzEdge.1 hxzEdge.2
        · exact G.mem_internalEdges_of_mem_of_inc_inc hgF hyz
            (by simp [S, y]) (by simp [S, z]) hyzEdge.1 hyzEdge.2

/-- A critical graph with the seven-sixths chain bound and at least two
unused colors at every vertex has an odd-set density violation. A five-chain
produces a five-set violation; if none exists, all chains are triangles and
the triangle recoloring argument produces a three-set violation. -/
theorem false_of_colorCritical_noOddSetCertificate_sevenSixths
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    (hk : 0 < k)
    (hdk : d + 1 < k) (hdegree : ∀ v, G.degreeOn F v ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hno : G.NoOddSetCertificateAt F k) : False := by
  obtain ⟨e, heF⟩ := IsColorCriticalOn.nonempty G hk hcritical
  obtain ⟨color, hproper⟩ := hcritical.2 e heF
  obtain ⟨S, hScard, heX, heY, hall⟩ :=
    G.allColors_internal_criticalTriangle_short
      hcritical heF hproper hdk hdegree hthreshold hno
  exact hno ⟨S, G.oddSetCertificate_at_of_allColors_internal_three
    color hScard heF ⟨heX, heY⟩ hall⟩



end WeightedMultigraph
end WeightedEdgeColoring
