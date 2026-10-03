import WeightedEdgeColoring.BPOrdinaryCriticalTrianglePresent
import WeightedEdgeColoring.BPOrdinaryCriticalTriangleCertificate

/-!
# Saturation of an Andersen critical triangle

The three missing-colour inclusions and the present-colour lemma together
say that every palette colour occurs on an edge of the critical triangle.
This file packages that conclusion and immediately turns it into the
strict odd-set certificate.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- An edge incident with two distinct members of a vertex set is internal
to that set. -/
theorem mem_internalEdges_of_mem_of_inc_inc
    {F : Finset G.E} {S : Finset G.V} {g : G.E}
    (hgF : g ∈ F) {u v : G.V} (huv : u ≠ v)
    (huS : u ∈ S) (hvS : v ∈ S)
    (hgu : G.Inc u g) (hgv : G.Inc v g) :
    g ∈ G.internalEdges F S := by
  apply Finset.mem_filter.mpr
  refine ⟨hgF, ?_⟩
  rcases G.endpoint_eq_or_endpoint_eq_swap_of_inc huv hgu hgv with
    hdirect | hswap
  · exact ⟨by simpa [hdirect.1] using huS,
      by simpa [hdirect.2] using hvS⟩
  · exact ⟨by simpa [hswap.1] using hvS,
      by simpa [hswap.2] using huS⟩

/-- Every colour occurs on an internal edge of the three-vertex critical
triangle. -/
theorem allColors_internal_criticalTriangle
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    (hdk : d < k) (hdegree : ∀ v, G.degreeOn F v ≤ d)
    (hthreshold : 5 * d < 4 * k + 2) :
    ∃ S : Finset G.V, S.card = 3 ∧
      G.fst e ∈ S ∧ G.snd e ∈ S ∧
      ∀ c : Fin k, ∃ g,
        g ∈ G.internalEdges (F.erase e) S ∧ color g = c := by
  have hdegreeErase : ∀ v, G.degreeOn (F.erase e) v < k := by
    intro v
    exact (G.degreeOn_mono_critical (Finset.erase_subset e F) v).trans_lt
      ((hdegree v).trans_lt hdk)
  obtain ⟨a, ha⟩ :=
    G.exists_mem_missingColorsAt_of_degreeOn_lt hproper
      (hdegreeErase (G.fst e))
  obtain ⟨b, hb⟩ :=
    G.exists_mem_missingColorsAt_of_degreeOn_lt hproper
      (hdegreeErase (G.snd e))
  obtain ⟨p, _⟩ := G.exists_criticalEndpointPath
    hcritical heF hproper ha hb
  have hpLength := G.criticalPath_length_eq_two
    hcritical heF hproper ha hb p hdk hdegree hthreshold
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
  · rcases G.exists_oppositeEdge_of_mem_missing_first_of_threeChain
        hcritical heF hproper ha hb p hdk hdegree hthreshold
        (by simpa [x] using hcx) with
      ⟨g, hgF, hgz, hgy, hgc⟩
    refine ⟨g, ?_, hgc⟩
    exact G.mem_internalEdges_of_mem_of_inc_inc hgF hyz.symm
      (by simp [S, z]) (by simp [S, y]) hgz hgy
  · by_cases hcy : c ∈ G.missingColorsAt (F.erase e) color y
    · rcases G.exists_oppositeEdge_of_mem_missing_second_of_threeChain
          hcritical heF hproper ha hb p hdk hdegree hthreshold
          (by simpa [y] using hcy) with
        ⟨g, hgF, hgx, hgz, hgc⟩
      refine ⟨g, ?_, hgc⟩
      exact G.mem_internalEdges_of_mem_of_inc_inc hgF hxz
        (by simp [S, x]) (by simp [S, z]) hgx hgz
    · by_cases hcz : c ∈ G.missingColorsAt (F.erase e) color z
      · rcases G.exists_endpointEdge_of_mem_missing_middle_of_threeChain
            hcritical heF hproper ha hb p hdk hdegree hthreshold
            (by simpa [z] using hcz) with
          ⟨g, hgF, hgx, hgy, hgc⟩
        refine ⟨g, ?_, hgc⟩
        exact G.mem_internalEdges_of_mem_of_inc_inc hgF hxy
          (by simp [S, x]) (by simp [S, y]) hgx hgy
      · rcases G.exists_triangleEdge_of_not_missing_middle_of_threeChain
            hcritical heF hproper ha hb p hdk hdegree hthreshold
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

/-- A critical graph in the strict five-fourths range has a violating
three-vertex odd set. -/
theorem exists_oddSetCertificate_of_colorCritical_fiveFourth
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    (hk : 0 < k)
    (hdk : d < k) (hdegree : ∀ v, G.degreeOn F v ≤ d)
    (hthreshold : 5 * d < 4 * k + 2) :
    ∃ S : Finset G.V, Odd S.card ∧ 3 ≤ S.card ∧
      (k : ℝ) * ((S.card : ℝ) - 1) <
        (2 : ℝ) * (G.internalEdges F S).card := by
  obtain ⟨e, heF⟩ := IsColorCriticalOn.nonempty G hk hcritical
  obtain ⟨color, hproper⟩ := hcritical.2 e heF
  obtain ⟨S, hScard, heX, heY, hall⟩ :=
    G.allColors_internal_criticalTriangle
      hcritical heF hproper hdk hdegree hthreshold
  exact G.exists_oddSetCertificate_of_allColors_internal_three
    color hScard heF ⟨heX, heY⟩ hall

end WeightedMultigraph
end WeightedEdgeColoring
