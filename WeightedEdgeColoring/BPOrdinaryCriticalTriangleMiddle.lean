import WeightedEdgeColoring.BPOrdinaryCriticalShift

/-!
# Colours missing at the middle vertex of a critical triangle

The omitted edge can be shifted to the first edge of the three-vertex
critical chain.  Applying the three-vertex result again shows that every
colour missing at the middle vertex occurs on an edge joining the two old
endpoints.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Two distinct incident vertices are the two endpoints of the edge, in
one of the two possible orders. -/
theorem endpoint_eq_or_endpoint_eq_swap_of_inc
    {g : G.E} {u v : G.V} (huv : u ≠ v)
    (hgu : G.Inc u g) (hgv : G.Inc v g) :
    (G.fst g = u ∧ G.snd g = v) ∨
      (G.fst g = v ∧ G.snd g = u) := by
  rcases hgu with hfu | hsu <;> rcases hgv with hfv | hsv
  · exact False.elim (huv (hfu.symm.trans hfv))
  · exact Or.inl ⟨hfu, hsv⟩
  · exact Or.inr ⟨hfv, hsu⟩
  · exact False.elim (huv (hsu.symm.trans hsv))

/-- A colour missing at the middle vertex is realized between the two
endpoints of the critical triangle. -/
theorem exists_endpointEdge_of_mem_missing_middle_of_threeChain
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
    (hc : c ∈ G.missingColorsAt (F.erase e) color (p.1.getVert 1)) :
    ∃ g, g ∈ F.erase e ∧ G.Inc (G.fst e) g ∧
      G.Inc (G.snd e) g ∧ color g = c := by
  have hpLength := G.criticalPath_length_eq_two
    hcritical heF hproper ha hb p hdk hdegree hthreshold
  let z := p.1.getVert 1
  have hp0 : (G.twoColorGraph (F.erase e) color a b).Adj
      (G.fst e) z := by
    simpa [z] using p.1.adj_getVert_succ (i := 0) (by omega)
  have hp1 : (G.twoColorGraph (F.erase e) color a b).Adj
      z (G.snd e) := by
    have hend : p.1.getVert 2 = G.snd e := by
      simpa [hpLength] using p.1.getVert_length
    simpa [z, hend] using p.1.adj_getVert_succ (i := 1) (by omega)
  rcases G.exists_twoColorWitnessEdge
      (F.erase e) color a b hp0 with
    ⟨gB, hgBF, hgBx, hgBz, hgBcolor⟩
  rcases G.exists_twoColorWitnessEdge
      (F.erase e) color a b hp1 with
    ⟨gA, hgAF, hgAz, hgAy, hgAcolor⟩
  have hgBneA : color gB ≠ a :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase e) color (G.fst e) a ha hgBF hgBx
  have hgBB : color gB = b := hgBcolor.resolve_left hgBneA
  have hgAneB : color gA ≠ b :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase e) color (G.snd e) b hb hgAF hgAy
  have hgAA : color gA = a := hgAcolor.resolve_right hgAneB
  have hab : a ≠ b :=
    G.critical_endpoint_missingColors_ne hcritical heF hproper ha hb
  have hcb : c ≠ b := by
    have hne : color gB ≠ c :=
      G.color_ne_of_mem_missingColorsAt
        (F.erase e) color z c (by simpa [z] using hc) hgBF hgBz
    intro h
    exact hne (hgBB.trans h.symm)
  have hca : c ≠ a := by
    have hne : color gA ≠ c :=
      G.color_ne_of_mem_missingColorsAt
        (F.erase e) color z c (by simpa [z] using hc) hgAF hgAz
    intro h
    exact hne (hgAA.trans h.symm)
  let shifted := G.assignEdgeColor color e b
  have hproperShift : G.IsProperOn (F.erase gB) shifted := by
    exact G.isProperOn_shiftOmittedEdge heF hgBF hproper hgBB hgBx hb
  have haShift :
      a ∈ G.missingColorsAt (F.erase gB) shifted (G.fst e) := by
    exact G.mem_missingColorsAt_shiftOmitted_of_ne hab
      ha
  have hcShift :
      c ∈ G.missingColorsAt (F.erase gB) shifted z := by
    exact G.mem_missingColorsAt_shiftOmitted_of_ne hcb
      (by simpa [z] using hc)
  have hgBF' : gB ∈ F := (Finset.mem_erase.mp hgBF).2
  have hxz : G.fst e ≠ z := hp0.ne
  rcases G.endpoint_eq_or_endpoint_eq_swap_of_inc
      hxz hgBx hgBz with hdirect | hswap
  · have haFst :
        a ∈ G.missingColorsAt (F.erase gB) shifted (G.fst gB) := by
      simpa [hdirect.1] using haShift
    have hcSnd :
        c ∈ G.missingColorsAt (F.erase gB) shifted (G.snd gB) := by
      simpa [hdirect.2] using hcShift
    obtain ⟨q, _⟩ := G.exists_criticalEndpointPath
      hcritical hgBF' hproperShift haFst hcSnd
    have hqLength := G.criticalPath_length_eq_two
      hcritical hgBF' hproperShift haFst hcSnd q hdk hdegree hthreshold
    let w := q.1.getVert 1
    have hq0 : (G.twoColorGraph (F.erase gB) shifted a c).Adj
        (G.fst gB) w := by
      simpa [w] using q.1.adj_getVert_succ (i := 0) (by omega)
    have hq1 : (G.twoColorGraph (F.erase gB) shifted a c).Adj
        w (G.snd gB) := by
      have hend : q.1.getVert 2 = G.snd gB := by
        simpa [hqLength] using q.1.getVert_length
      simpa [w, hend] using q.1.adj_getVert_succ (i := 1) (by omega)
    rcases G.exists_twoColorWitnessEdge
        (F.erase gB) shifted a c hq1 with
      ⟨rA, hrAF, hrAw, hrAz, hrAcolor⟩
    have hrAneC : shifted rA ≠ c :=
      G.color_ne_of_mem_missingColorsAt
        (F.erase gB) shifted (G.snd gB) c hcSnd hrAF hrAz
    have hrAA : shifted rA = a := hrAcolor.resolve_right hrAneC
    have hgAinShift : gA ∈ F.erase gB := by
      apply Finset.mem_erase.mpr
      refine ⟨?_, (Finset.mem_erase.mp hgAF).2⟩
      intro h
      subst gA
      exact hab (hgAA.symm.trans hgBB)
    have hgAShift : shifted gA = a := by
      have hgAneE : gA ≠ e := (Finset.mem_erase.mp hgAF).1
      simpa [shifted, G.assignEdgeColor_of_ne color hgAneE b] using hgAA
    have hwY : w = G.snd e := by
      by_contra hwY
      have hcolors : shifted rA ≠ shifted gA :=
        G.color_ne_of_isProperOn_of_incident_otherEndpoints_ne hproperShift
          (u := w) (v := z) (w := G.snd e)
          (by simpa [hdirect.2] using hq1.ne.symm) hp1.ne hwY
          hrAF hgAinShift (by simpa [hdirect.2] using hrAz) hrAw hgAz hgAy
      exact hcolors (hrAA.trans hgAShift.symm)
    rcases G.exists_twoColorWitnessEdge
        (F.erase gB) shifted a c hq0 with
      ⟨gC, hgCF, hgCx, hgCw, hgCcolor⟩
    have hgCneA : shifted gC ≠ a :=
      G.color_ne_of_mem_missingColorsAt
        (F.erase gB) shifted (G.fst gB) a haFst hgCF hgCx
    have hgCC : shifted gC = c := hgCcolor.resolve_left hgCneA
    have hgCneE : gC ≠ e := by
      intro h
      subst gC
      have hbc : b = c := by simpa [shifted, assignEdgeColor] using hgCC
      exact hcb hbc.symm
    have hgCFe : gC ∈ F.erase e :=
      Finset.mem_erase.mpr ⟨hgCneE, (Finset.mem_erase.mp hgCF).2⟩
    have hgCOld : color gC = c := by
      simpa [shifted, G.assignEdgeColor_of_ne color hgCneE b] using hgCC
    refine ⟨gC, hgCFe, ?_, ?_, hgCOld⟩
    · simpa [hdirect.1] using hgCx
    · simpa [w, hwY] using hgCw
  · have hcFst :
        c ∈ G.missingColorsAt (F.erase gB) shifted (G.fst gB) := by
      simpa [hswap.1] using hcShift
    have haSnd :
        a ∈ G.missingColorsAt (F.erase gB) shifted (G.snd gB) := by
      simpa [hswap.2] using haShift
    obtain ⟨q, _⟩ := G.exists_criticalEndpointPath
      hcritical hgBF' hproperShift hcFst haSnd
    have hqLength := G.criticalPath_length_eq_two
      hcritical hgBF' hproperShift hcFst haSnd q hdk hdegree hthreshold
    let w := q.1.getVert 1
    have hq0 : (G.twoColorGraph (F.erase gB) shifted c a).Adj
        (G.fst gB) w := by
      simpa [w] using q.1.adj_getVert_succ (i := 0) (by omega)
    have hq1 : (G.twoColorGraph (F.erase gB) shifted c a).Adj
        w (G.snd gB) := by
      have hend : q.1.getVert 2 = G.snd gB := by
        simpa [hqLength] using q.1.getVert_length
      simpa [w, hend] using q.1.adj_getVert_succ (i := 1) (by omega)
    rcases G.exists_twoColorWitnessEdge
        (F.erase gB) shifted c a hq0 with
      ⟨rA, hrAF, hrAz, hrAw, hrAcolor⟩
    have hrAneC : shifted rA ≠ c :=
      G.color_ne_of_mem_missingColorsAt
        (F.erase gB) shifted (G.fst gB) c hcFst hrAF hrAz
    have hrAA : shifted rA = a := hrAcolor.resolve_left hrAneC
    have hgAinShift : gA ∈ F.erase gB := by
      apply Finset.mem_erase.mpr
      refine ⟨?_, (Finset.mem_erase.mp hgAF).2⟩
      intro h
      subst gA
      exact hab (hgAA.symm.trans hgBB)
    have hgAShift : shifted gA = a := by
      have hgAneE : gA ≠ e := (Finset.mem_erase.mp hgAF).1
      simpa [shifted, G.assignEdgeColor_of_ne color hgAneE b] using hgAA
    have hwY : w = G.snd e := by
      by_contra hwY
      have hcolors : shifted rA ≠ shifted gA :=
        G.color_ne_of_isProperOn_of_incident_otherEndpoints_ne hproperShift
          (u := w) (v := z) (w := G.snd e)
          (by simpa [hswap.1] using hq0.ne) hp1.ne hwY
          hrAF hgAinShift (by simpa [hswap.1] using hrAz) hrAw hgAz hgAy
      exact hcolors (hrAA.trans hgAShift.symm)
    rcases G.exists_twoColorWitnessEdge
        (F.erase gB) shifted c a hq1 with
      ⟨gC, hgCF, hgCw, hgCx, hgCcolor⟩
    have hgCneA : shifted gC ≠ a :=
      G.color_ne_of_mem_missingColorsAt
        (F.erase gB) shifted (G.snd gB) a haSnd hgCF hgCx
    have hgCC : shifted gC = c := hgCcolor.resolve_right hgCneA
    have hgCneE : gC ≠ e := by
      intro h
      subst gC
      have hbc : b = c := by simpa [shifted, assignEdgeColor] using hgCC
      exact hcb hbc.symm
    have hgCFe : gC ∈ F.erase e :=
      Finset.mem_erase.mpr ⟨hgCneE, (Finset.mem_erase.mp hgCF).2⟩
    have hgCOld : color gC = c := by
      simpa [shifted, G.assignEdgeColor_of_ne color hgCneE b] using hgCC
    refine ⟨gC, hgCFe, ?_, ?_, hgCOld⟩
    · simpa [hswap.2] using hgCx
    · simpa [w, hwY] using hgCw

end WeightedMultigraph
end WeightedEdgeColoring
