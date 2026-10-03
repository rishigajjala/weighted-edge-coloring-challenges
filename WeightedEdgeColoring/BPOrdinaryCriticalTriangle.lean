import WeightedEdgeColoring.BPOrdinaryCriticalChainThree

/-!
# The first triangle consequences of three-vertex critical chains

Let `x-z-y` be a critical chain for an omitted edge `xy`.  If every
critical chain has three vertices, then every colour missing at `x` occurs
on an edge `zy`, and every colour missing at `y` occurs on an edge `xz`.
These are two of the three elementary inclusions used in Andersen's
three-vertex ring argument.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- A concrete critical endpoint path exists for every pair of endpoint
missing colours. -/
theorem exists_criticalEndpointPath
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e)) :
    ∃ p : (G.twoColorGraph (F.erase e) color a b).Path
        (G.fst e) (G.snd e), True := by
  have hcomponent := G.critical_endpoints_same_twoColorComponent
    hcritical heF hproper ha hb
  have hreach :
      (G.twoColorGraph (F.erase e) color a b).Reachable
        (G.fst e) (G.snd e) :=
    SimpleGraph.ConnectedComponent.exact hcomponent
  rcases hreach with ⟨w⟩
  exact ⟨w.toPath, trivial⟩

/-- A colour missing at the first endpoint is realized on the opposite
side of the critical triangle. -/
theorem exists_oppositeEdge_of_mem_missing_first_of_threeChain
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hdk : d < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 5 * d < 4 * k + 2)
    {c : Fin k}
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.fst e)) :
    ∃ g, g ∈ F.erase e ∧
      G.Inc (p.1.getVert 1) g ∧ G.Inc (G.snd e) g ∧ color g = c := by
  have hpLength := G.criticalPath_length_eq_two
    hcritical heF hproper ha hb p hdk hdegree hthreshold
  let z := p.1.getVert 1
  have hp0 : (G.twoColorGraph (F.erase e) color a b).Adj
      (G.fst e) z := by
    simpa [z] using p.1.adj_getVert_succ (i := 0) (by omega)
  rcases G.exists_twoColorWitnessEdge
      (F.erase e) color a b hp0 with
    ⟨gB, hgBF, hgBx, hgBz, hgBcolor⟩
  have hgBneA : color gB ≠ a :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase e) color (G.fst e) a ha hgBF hgBx
  have hgBB : color gB = b := hgBcolor.resolve_left hgBneA
  obtain ⟨q, _⟩ := G.exists_criticalEndpointPath
    hcritical heF hproper hc hb
  have hqLength := G.criticalPath_length_eq_two
    hcritical heF hproper hc hb q hdk hdegree hthreshold
  let w := q.1.getVert 1
  have hq0 : (G.twoColorGraph (F.erase e) color c b).Adj
      (G.fst e) w := by
    simpa [w] using q.1.adj_getVert_succ (i := 0) (by omega)
  have hq1 : (G.twoColorGraph (F.erase e) color c b).Adj
      w (G.snd e) := by
    have hend : q.1.getVert 2 = G.snd e := by
      simpa [hqLength] using q.1.getVert_length
    simpa [w, hend] using q.1.adj_getVert_succ (i := 1) (by omega)
  rcases G.exists_twoColorWitnessEdge
      (F.erase e) color c b hq0 with
    ⟨rB, hrBF, hrBx, hrBw, hrBcolor⟩
  have hrBneC : color rB ≠ c :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase e) color (G.fst e) c hc hrBF hrBx
  have hrBB : color rB = b := hrBcolor.resolve_left hrBneC
  have hwz : w = z := by
    by_contra hwz
    have hcolors : color rB ≠ color gB :=
      G.color_ne_of_isProperOn_of_incident_otherEndpoints_ne hproper
        hq0.ne hp0.ne hwz hrBF hgBF hrBx hrBw hgBx hgBz
    exact hcolors (hrBB.trans hgBB.symm)
  rcases G.exists_twoColorWitnessEdge
      (F.erase e) color c b hq1 with
    ⟨gC, hgCF, hgCw, hgCy, hgCcolor⟩
  have hgCneB : color gC ≠ b :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase e) color (G.snd e) b hb hgCF hgCy
  have hgCC : color gC = c := hgCcolor.resolve_right hgCneB
  refine ⟨gC, hgCF, ?_, hgCy, hgCC⟩
  simpa [z, hwz] using hgCw

/-- A colour missing at the second endpoint is realized on the opposite
side of the critical triangle. -/
theorem exists_oppositeEdge_of_mem_missing_second_of_threeChain
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hdk : d < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 5 * d < 4 * k + 2)
    {c : Fin k}
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.snd e)) :
    ∃ g, g ∈ F.erase e ∧
      G.Inc (G.fst e) g ∧ G.Inc (p.1.getVert 1) g ∧ color g = c := by
  have hpLength := G.criticalPath_length_eq_two
    hcritical heF hproper ha hb p hdk hdegree hthreshold
  let z := p.1.getVert 1
  have hp1 : (G.twoColorGraph (F.erase e) color a b).Adj
      z (G.snd e) := by
    have hend : p.1.getVert 2 = G.snd e := by
      simpa [hpLength] using p.1.getVert_length
    simpa [z, hend] using p.1.adj_getVert_succ (i := 1) (by omega)
  rcases G.exists_twoColorWitnessEdge
      (F.erase e) color a b hp1 with
    ⟨gA, hgAF, hgAz, hgAy, hgAcolor⟩
  have hgAneB : color gA ≠ b :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase e) color (G.snd e) b hb hgAF hgAy
  have hgAA : color gA = a := hgAcolor.resolve_right hgAneB
  obtain ⟨q, _⟩ := G.exists_criticalEndpointPath
    hcritical heF hproper ha hc
  have hqLength := G.criticalPath_length_eq_two
    hcritical heF hproper ha hc q hdk hdegree hthreshold
  let w := q.1.getVert 1
  have hq0 : (G.twoColorGraph (F.erase e) color a c).Adj
      (G.fst e) w := by
    simpa [w] using q.1.adj_getVert_succ (i := 0) (by omega)
  have hq1 : (G.twoColorGraph (F.erase e) color a c).Adj
      w (G.snd e) := by
    have hend : q.1.getVert 2 = G.snd e := by
      simpa [hqLength] using q.1.getVert_length
    simpa [w, hend] using q.1.adj_getVert_succ (i := 1) (by omega)
  rcases G.exists_twoColorWitnessEdge
      (F.erase e) color a c hq1 with
    ⟨rA, hrAF, hrAw, hrAy, hrAcolor⟩
  have hrAneC : color rA ≠ c :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase e) color (G.snd e) c hc hrAF hrAy
  have hrAA : color rA = a := hrAcolor.resolve_right hrAneC
  have hwz : w = z := by
    by_contra hwz
    have hcolors : color rA ≠ color gA :=
      G.color_ne_of_isProperOn_of_incident_otherEndpoints_ne hproper
        hq1.ne.symm hp1.ne.symm hwz hrAF hgAF hrAy hrAw hgAy hgAz
    exact hcolors (hrAA.trans hgAA.symm)
  rcases G.exists_twoColorWitnessEdge
      (F.erase e) color a c hq0 with
    ⟨gC, hgCF, hgCx, hgCw, hgCcolor⟩
  have hgCneA : color gC ≠ a :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase e) color (G.fst e) a ha hgCF hgCx
  have hgCC : color gC = c := hgCcolor.resolve_left hgCneA
  refine ⟨gC, hgCF, hgCx, ?_, hgCC⟩
  simpa [z, hwz] using hgCw

end WeightedMultigraph
end WeightedEdgeColoring
