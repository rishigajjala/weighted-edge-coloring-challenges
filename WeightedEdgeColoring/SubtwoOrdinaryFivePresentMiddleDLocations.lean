import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleCAPathLength

/-!
# The two d edges of the second no-middle-c circuit
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.middle_d_edge_locations_of_forced_geometry
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (u : G.FivePathState F k b a)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hleftExt : FivePathState.HasExternalColorAt G u c u.left)
    (hrightExt : FivePathState.HasExternalColorAt G u c u.right)
    {paint₂ : G.E → Fin k}
    (hproper₂ : G.IsProperOn (F.erase u.omitted) paint₂)
    (hcLeft : c ∈ G.missingColorsAt (F.erase u.omitted) paint₂ u.left)
    (haRight : a ∈ G.missingColorsAt (F.erase u.omitted) paint₂ u.right)
    (hother : ∀ r, u.paint r ≠ b → u.paint r ≠ c →
      paint₂ r = u.paint r)
    (hfixed : ∀ d', d' ≠ b → d' ≠ c →
      (d' ∈ G.missingColorsAt (F.erase u.omitted) paint₂ u.left ↔
        d' ∈ G.missingColorsAt (F.erase u.omitted) u.paint u.left))
    (qCA : (G.twoColorGraph (F.erase u.omitted) paint₂ c a).Path
      u.left u.right)
    (hqCard : qCA.1.support.toFinset.card ≤ 5)
    {outY outZ : G.V}
    (hne : outY ≠ outZ)
    (hYout : outY ∉ u.path.1.support.toFinset)
    (hZout : outZ ∉ u.path.1.support.toFinset)
    {gY gZ : G.E}
    (hgYF : gY ∈ F.erase u.omitted)
    (hgYY : G.Inc u.right gY) (hgYOut : G.Inc outY gY)
    (hgYC : paint₂ gY = c)
    (hgZF : gZ ∈ F.erase u.omitted)
    (hgZ1 : G.Inc (u.path.1.getVert 1) gZ)
    (hgZOut : G.Inc outZ gZ)
    (hgZC : paint₂ gZ = c) :
    ∃ d : Fin k, d ≠ a ∧ d ≠ b ∧ d ≠ c ∧
      d ∈ G.missingColorsAt (F.erase u.omitted) u.paint u.left ∧
      d ∈ G.missingColorsAt (F.erase u.omitted) paint₂ u.left ∧
      qCA.1.length = 4 ∧
      qCA.1.support.toFinset =
        {u.left,u.path.1.getVert 1,outZ,outY,u.right} ∧
      ∃ gD₁ gD₂ : G.E,
        gD₁ ∈ F.erase u.omitted ∧ gD₂ ∈ F.erase u.omitted ∧
        G.Inc u.right gD₁ ∧
        G.Inc (u.path.1.getVert 1) gD₁ ∧
        G.Inc (u.path.1.getVert 2) gD₂ ∧
        G.Inc (u.path.1.getVert 3) gD₂ ∧
        u.paint gD₁ = d ∧ u.paint gD₂ = d ∧
        paint₂ gD₁ = d ∧ paint₂ gD₂ = d := by
  obtain ⟨d,hdLeft,hdb⟩ :=
    FivePathState.exists_second_missing_left_color
      (c := b) G u hdk hdegree
  obtain ⟨g₀,hg₀F,hg₀L,hg₀1,hg₀A⟩ :=
    FivePathState.exists_first_b_edge G u
  have hab : a ≠ b := by
    intro heq
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase u.omitted) u.paint u.left b u.left_missing hg₀F hg₀L)
      (hg₀A.trans heq)
  have hcne := FivePathState.external_endpoint_color_ne_missing
    G u hleftExt hrightExt
  have hda : d ≠ a := by
    intro heq
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase u.omitted) u.paint u.left d hdLeft hg₀F hg₀L)
      (hg₀A.trans heq.symm)
  obtain ⟨gC,hgCF,hgCL,hgCC,_⟩ := hleftExt
  have hdc : d ≠ c := by
    intro heq
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase u.omitted) u.paint u.left d hdLeft hgCF hgCL)
      (hgCC.trans heq.symm)
  have hdLeft₂ := (hfixed d hdb hdc).mpr hdLeft
  have hg₀₂ : paint₂ g₀ = a :=
    (hother g₀ (by simpa [hg₀A] using hab)
      (by simpa [hg₀A] using hcne.2.symm)).trans hg₀A
  have hqSupport := FivePathState.middle_ca_path_support_of_exterior_edges
    G u hcritical hproper₂ hcLeft haRight hne hYout hZout
      hg₀F hg₀L hg₀1 hg₀₂
      hgYF hgYY hgYOut hgYC
      hgZF hgZ1 hgZOut hgZC qCA hqCard
  have hqLen := FivePathState.middle_ca_path_length_of_support
    G u hne hYout hZout qCA hqSupport
  have hdRight := FivePathState.missing_left_color_present_right
    G u hcritical hdLeft
  have hkeep : ∀ r ∈ F.erase u.omitted,
      u.paint r = d → paint₂ r = d := by
    intro r hrF hrD
    exact (hother r (by simpa [hrD] using hdb)
      (by simpa [hrD] using hdc)).trans hrD
  obtain ⟨gD₁,hgD₁F,hgD₁Y,hgD₁Z,hgD₁D⟩ :=
    FivePathState.right_d_edge_to_common_middle
      G u hcritical hdk hdegree hthreshold hdLeft hdRight
      hproper₂ hcLeft haRight hdLeft₂ hkeep qCA hqLen
      hqSupport hZout hYout
  obtain ⟨gD₂,hgD₂F,hgD₂2,hgD₂3,hgD₂D⟩ :=
    FivePathState.middle_d_edge_of_right_z1_edge
      G u hcritical hdk hdegree hthreshold hdLeft
      hgD₁F hgD₁Y hgD₁Z hgD₁D
  exact ⟨d,hda,hdb,hdc,hdLeft,hdLeft₂,hqLen,hqSupport,
    gD₁,gD₂,hgD₁F,hgD₂F,hgD₁Y,hgD₁Z,
    hgD₂2,hgD₂3,hgD₁D,hgD₂D,
    hkeep gD₁ hgD₁F hgD₁D,hkeep gD₂ hgD₂F hgD₂D⟩

end WeightedEdgeColoring.WeightedMultigraph
