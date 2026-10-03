import WeightedEdgeColoring.SubtwoOrdinaryTriangleShortMiddle
import WeightedEdgeColoring.BPOrdinaryCriticalTrianglePresentComponent

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem presentColor_first_mem_second_twoColorComponent_short
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (hcX : c ∉ G.missingColorsAt (F.erase e) color (G.fst e))
    (hcY : c ∉ G.missingColorsAt (F.erase e) color (G.snd e))
    {z : G.V} (hxz : G.fst e ≠ z) (hyz : G.snd e ≠ z)
    {gA : G.E} (hgAF : gA ∈ F.erase e)
    (hgAz : G.Inc z gA) (hgAy : G.Inc (G.snd e) gA)
    (hgAA : color gA = a)
    (hnoCXZ : ∀ r, r ∈ F.erase e → G.Inc (G.fst e) r →
      G.Inc z r → color r ≠ c)
    (hdk : d + 1 < k) (hdegree : ∀ v, G.degreeOn F v ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hno : G.NoOddSetCertificateAt F k) :
    (G.twoColorGraph (F.erase e) color b c).connectedComponentMk
        (G.fst e) =
      (G.twoColorGraph (F.erase e) color b c).connectedComponentMk
        (G.snd e) := by
  classical
  let R := F.erase e
  let H := G.twoColorGraph R color b c
  let CY : H.ConnectedComponent := H.connectedComponentMk (G.snd e)
  let flip : H.ConnectedComponent → Prop := fun C ↦ C = CY
  by_contra hxComp
  have hxNotFlip : ¬flip (H.connectedComponentMk (G.fst e)) := by
    simpa [flip, CY, H, R] using hxComp
  have hyFlip : flip (H.connectedComponentMk (G.snd e)) := by
    rfl
  let switched : G.E → Fin k :=
    G.kempeComponentSwitch R color b c flip
  have hproperSwitched : G.IsProperOn R switched := by
    exact G.isProperOn_kempeComponentSwitch R color hproper b c flip
  have hcb : c ≠ b := by
    intro h
    subst c
    exact hcY hb
  have hab : a ≠ b :=
    G.critical_endpoint_missingColors_ne hcritical heF hproper ha hb
  have hac : a ≠ c := by
    intro h
    subst c
    exact hcX ha
  have haSwitched :
      a ∈ G.missingColorsAt R switched (G.fst e) := by
    exact (G.mem_missingColorsAt_kempeComponentSwitch_of_fixedColor_iff
      color b c flip (G.fst e) a hab hac).mpr ha
  have hcSwitched :
      c ∈ G.missingColorsAt R switched (G.snd e) := by
    exact (G.mem_missingColorsAt_kempeComponentSwitch_of_flip
      R color b c flip (G.snd e) hyFlip).1.mpr hb
  obtain ⟨q, _⟩ := G.exists_criticalEndpointPath
    hcritical heF hproperSwitched haSwitched hcSwitched
  have hqLength := G.criticalPath_length_eq_two_of_no_oddSetCertificate
    hcritical heF hproperSwitched haSwitched hcSwitched q
      hdk hdegree hthreshold hno
  let w := q.1.getVert 1
  have hq0 : (G.twoColorGraph R switched a c).Adj (G.fst e) w := by
    simpa [w] using q.1.adj_getVert_succ (i := 0) (by omega)
  have hq1 : (G.twoColorGraph R switched a c).Adj w (G.snd e) := by
    have hend : q.1.getVert 2 = G.snd e := by
      simpa [hqLength] using q.1.getVert_length
    simpa [w, hend] using q.1.adj_getVert_succ (i := 1) (by omega)
  rcases G.exists_twoColorWitnessEdge R switched a c hq1 with
    ⟨rA, hrAF, hrAw, hrAy, hrAcolor⟩
  have hrAneC : switched rA ≠ c :=
    G.color_ne_of_mem_missingColorsAt
      R switched (G.snd e) c hcSwitched hrAF hrAy
  have hrAA : switched rA = a := hrAcolor.resolve_right hrAneC
  have hgASwitched : switched gA = a := by
    exact (G.kempeComponentSwitch_eq_fixedColor_iff
      color b c flip a hab hac gA).mpr hgAA
  have hwz : w = z := by
    by_contra hwz
    have hcolors : switched rA ≠ switched gA :=
      G.color_ne_of_isProperOn_of_incident_otherEndpoints_ne hproperSwitched
        hq1.ne.symm hyz hwz hrAF hgAF hrAy hrAw hgAy hgAz
    exact hcolors (hrAA.trans hgASwitched.symm)
  rcases G.exists_twoColorWitnessEdge R switched a c hq0 with
    ⟨rC, hrCF, hrCx, hrCw, hrCcolor⟩
  have hrCneA : switched rC ≠ a :=
    G.color_ne_of_mem_missingColorsAt
      R switched (G.fst e) a haSwitched hrCF hrCx
  have hrCC : switched rC = c := hrCcolor.resolve_left hrCneA
  have hrCOld : switched rC = color rC := by
    have hlocal := G.kempeComponentSwitch_eq_localPerm
      R color b c flip hrCF hrCx
    have hnot : ¬flip
        ((G.twoColorGraph R color b c).connectedComponentMk (G.fst e)) := by
      simpa [H] using hxNotFlip
    simpa [switched, kempeLocalPerm, hnot] using hlocal
  exact (hnoCXZ rC hrCF hrCx (by simpa [w, hwz] using hrCw))
    (hrCOld.symm.trans hrCC)

/-- Endpoint-free form of the preceding component claim. -/
theorem presentColor_x_mem_y_twoColorComponent_short
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {x y z : G.V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxe : G.Inc x e) (hye : G.Inc y e)
    {a b c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color x)
    (hb : b ∈ G.missingColorsAt (F.erase e) color y)
    (hcX : c ∉ G.missingColorsAt (F.erase e) color x)
    (hcY : c ∉ G.missingColorsAt (F.erase e) color y)
    {gA : G.E} (hgAF : gA ∈ F.erase e)
    (hgAz : G.Inc z gA) (hgAy : G.Inc y gA) (hgAA : color gA = a)
    (hnoCXZ : ∀ r, r ∈ F.erase e → G.Inc x r →
      G.Inc z r → color r ≠ c)
    (hdk : d + 1 < k) (hdegree : ∀ v, G.degreeOn F v ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hno : G.NoOddSetCertificateAt F k) :
    (G.twoColorGraph (F.erase e) color b c).connectedComponentMk x =
      (G.twoColorGraph (F.erase e) color b c).connectedComponentMk y := by
  classical
  let R := F.erase e
  let H := G.twoColorGraph R color b c
  let CY : H.ConnectedComponent := H.connectedComponentMk y
  let flip : H.ConnectedComponent → Prop := fun C ↦ C = CY
  by_contra hxComp
  have hxNotFlip : ¬flip (H.connectedComponentMk x) := by
    simpa [flip, CY, H, R] using hxComp
  have hyFlip : flip (H.connectedComponentMk y) := by rfl
  let switched : G.E → Fin k :=
    G.kempeComponentSwitch R color b c flip
  have hproperSwitched : G.IsProperOn R switched :=
    G.isProperOn_kempeComponentSwitch R color hproper b c flip
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc hxy hxe hye
  have hcb : c ≠ b := by intro h; subst c; exact hcY hb
  have hab : a ≠ b := by
    intro h
    subst b
    rcases hends with hdirect | hswap
    · exact G.not_both_mem_missingColorsAt_endpoints_of_colorCritical
        hcritical heF hproper a
          ⟨by simpa [hdirect.1] using ha,
            by simpa [hdirect.2] using hb⟩
    · exact G.not_both_mem_missingColorsAt_endpoints_of_colorCritical
        hcritical heF hproper a
          ⟨by simpa [hswap.1] using hb,
            by simpa [hswap.2] using ha⟩
  have hac : a ≠ c := by intro h; subst c; exact hcX ha
  have haSwitched : a ∈ G.missingColorsAt R switched x :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_fixedColor_iff
      color b c flip x a hab hac).mpr ha
  have hcSwitched : c ∈ G.missingColorsAt R switched y :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_flip
      R color b c flip y hyFlip).1.mpr hb
  rcases hends with hdirect | hswap
  · have haFst : a ∈ G.missingColorsAt R switched (G.fst e) := by
      simpa [hdirect.1] using haSwitched
    have hcSnd : c ∈ G.missingColorsAt R switched (G.snd e) := by
      simpa [hdirect.2] using hcSwitched
    obtain ⟨q, _⟩ := G.exists_criticalEndpointPath
      hcritical heF hproperSwitched haFst hcSnd
    have hqLength := G.criticalPath_length_eq_two_of_no_oddSetCertificate
      hcritical heF hproperSwitched haFst hcSnd q hdk hdegree hthreshold hno
    let w := q.1.getVert 1
    have hq0 : (G.twoColorGraph R switched a c).Adj x w := by
      simpa [w, hdirect.1] using q.1.adj_getVert_succ (i := 0) (by omega)
    have hq1 : (G.twoColorGraph R switched a c).Adj w y := by
      have hend : q.1.getVert 2 = G.snd e := by
        simpa [hqLength] using q.1.getVert_length
      simpa [w, hend, hdirect.2] using
        q.1.adj_getVert_succ (i := 1) (by omega)
    rcases G.exists_twoColorWitnessEdge R switched a c hq1 with
      ⟨rA, hrAF, hrAw, hrAy, hrAcolor⟩
    have hrAneC : switched rA ≠ c :=
      G.color_ne_of_mem_missingColorsAt R switched y c hcSwitched hrAF hrAy
    have hrAA : switched rA = a := hrAcolor.resolve_right hrAneC
    have hgASwitched : switched gA = a :=
      (G.kempeComponentSwitch_eq_fixedColor_iff
        color b c flip a hab hac gA).mpr hgAA
    have hwz : w = z := by
      by_contra hwz
      have hcolors : switched rA ≠ switched gA :=
        G.color_ne_of_isProperOn_of_incident_otherEndpoints_ne
          hproperSwitched hq1.ne.symm hyz hwz
            hrAF hgAF hrAy hrAw hgAy hgAz
      exact hcolors (hrAA.trans hgASwitched.symm)
    rcases G.exists_twoColorWitnessEdge R switched a c hq0 with
      ⟨rC, hrCF, hrCx, hrCw, hrCcolor⟩
    have hrCneA : switched rC ≠ a :=
      G.color_ne_of_mem_missingColorsAt R switched x a haSwitched hrCF hrCx
    have hrCC : switched rC = c := hrCcolor.resolve_left hrCneA
    have hrCOld : switched rC = color rC := by
      have hlocal := G.kempeComponentSwitch_eq_localPerm
        R color b c flip hrCF hrCx
      have hnot : ¬flip
          ((G.twoColorGraph R color b c).connectedComponentMk x) := by
        simpa [H] using hxNotFlip
      simpa [switched, kempeLocalPerm, hnot] using hlocal
    exact (hnoCXZ rC hrCF hrCx (by simpa [w, hwz] using hrCw))
      (hrCOld.symm.trans hrCC)
  · have hcFst : c ∈ G.missingColorsAt R switched (G.fst e) := by
      simpa [hswap.1] using hcSwitched
    have haSnd : a ∈ G.missingColorsAt R switched (G.snd e) := by
      simpa [hswap.2] using haSwitched
    obtain ⟨q, _⟩ := G.exists_criticalEndpointPath
      hcritical heF hproperSwitched hcFst haSnd
    have hqLength := G.criticalPath_length_eq_two_of_no_oddSetCertificate
      hcritical heF hproperSwitched hcFst haSnd q hdk hdegree hthreshold hno
    let w := q.1.getVert 1
    have hq0 : (G.twoColorGraph R switched c a).Adj y w := by
      simpa [w, hswap.1] using q.1.adj_getVert_succ (i := 0) (by omega)
    have hq1 : (G.twoColorGraph R switched c a).Adj w x := by
      have hend : q.1.getVert 2 = G.snd e := by
        simpa [hqLength] using q.1.getVert_length
      simpa [w, hend, hswap.2] using
        q.1.adj_getVert_succ (i := 1) (by omega)
    rcases G.exists_twoColorWitnessEdge R switched c a hq0 with
      ⟨rA, hrAF, hrAy, hrAw, hrAcolor⟩
    have hrAneC : switched rA ≠ c :=
      G.color_ne_of_mem_missingColorsAt R switched y c hcSwitched hrAF hrAy
    have hrAA : switched rA = a := hrAcolor.resolve_left hrAneC
    have hgASwitched : switched gA = a :=
      (G.kempeComponentSwitch_eq_fixedColor_iff
        color b c flip a hab hac gA).mpr hgAA
    have hwz : w = z := by
      by_contra hwz
      have hcolors : switched rA ≠ switched gA :=
        G.color_ne_of_isProperOn_of_incident_otherEndpoints_ne
          hproperSwitched hq0.ne hyz hwz
            hrAF hgAF hrAy hrAw hgAy hgAz
      exact hcolors (hrAA.trans hgASwitched.symm)
    rcases G.exists_twoColorWitnessEdge R switched c a hq1 with
      ⟨rC, hrCF, hrCw, hrCx, hrCcolor⟩
    have hrCneA : switched rC ≠ a :=
      G.color_ne_of_mem_missingColorsAt R switched x a haSwitched hrCF hrCx
    have hrCC : switched rC = c := hrCcolor.resolve_right hrCneA
    have hrCOld : switched rC = color rC := by
      have hlocal := G.kempeComponentSwitch_eq_localPerm
        R color b c flip hrCF hrCx
      have hnot : ¬flip
          ((G.twoColorGraph R color b c).connectedComponentMk x) := by
        simpa [H] using hxNotFlip
      simpa [switched, kempeLocalPerm, hnot] using hlocal
    exact (hnoCXZ rC hrCF hrCx (by simpa [w, hwz] using hrCw))
      (hrCOld.symm.trans hrCC)


end WeightedMultigraph
end WeightedEdgeColoring
