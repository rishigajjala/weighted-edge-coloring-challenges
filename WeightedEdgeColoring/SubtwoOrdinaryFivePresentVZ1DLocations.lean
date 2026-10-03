import WeightedEdgeColoring.SubtwoOrdinaryFivePresentVZ1Refined

/-!
# The two d-edge locations in Andersen's V=Z1 middle-c case
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- In the actual V=Z₁ middle-`c` configuration, choose a further
color `d` missing at `X`. Its two internal edges are forced to be
`Y–Z₁` and `Z₂–Z₃`. The first edge also belongs to the switched
critical `(c,a)` five-path support. -/
theorem FivePathState.exists_vz1_internal_c_d_edge_locations
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hZ1external : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 1))
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ1 : p.1.getVert i = s.path.1.getVert 1)
    {t : G.E} (htF : t ∈ F.erase s.omitted)
    (ht2 : G.Inc (s.path.1.getVert 2) t)
    (ht3 : G.Inc (s.path.1.getVert 3) t)
    (htC : s.paint t = c) :
    ∃ d : Fin k, d ≠ a ∧ d ≠ b ∧ d ≠ c ∧
      d ∈ G.missingColorsAt (F.erase s.omitted) s.paint s.left ∧
      ∃ paint₂ : G.E → Fin k,
        G.IsProperOn (F.erase s.omitted) paint₂ ∧
        c ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.left ∧
        a ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.right ∧
        d ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.left ∧
        ∃ qCA : (G.twoColorGraph (F.erase s.omitted) paint₂ c a).Path
          s.left s.right,
          qCA.1.length = 4 ∧
          ∃ w u, w ∉ s.path.1.support.toFinset ∧
            u ∉ s.path.1.support.toFinset ∧ w ≠ u ∧
            qCA.1.support.toFinset =
              {s.left, s.path.1.getVert 1, w, u, s.right} ∧
            ∃ gY gM, gY ∈ F.erase s.omitted ∧
              gM ∈ F.erase s.omitted ∧
              G.Inc s.right gY ∧
              G.Inc (s.path.1.getVert 1) gY ∧
              G.Inc (s.path.1.getVert 2) gM ∧
              G.Inc (s.path.1.getVert 3) gM ∧
              s.paint gY = d ∧ s.paint gM = d ∧
              paint₂ gY = d ∧ paint₂ gM = d := by
  obtain ⟨d, hdX, hda⟩ :=
    FivePathState.exists_second_missing_left_color
      (c := a) G s hdk hdegree
  obtain ⟨g₀, hg₀F, hg₀X, _, hg₀B⟩ :=
    FivePathState.exists_first_b_edge G s
  have hdb : d ≠ b := by
    intro h
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.left d hdX hg₀F hg₀X)
      (hg₀B.trans h.symm)
  have hleft' := hleft
  obtain ⟨gC, hgCF, hgCX, hgCC, _⟩ := hleft'
  have hdc : d ≠ c := by
    intro h
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.left d hdX hgCF hgCX)
      (hgCC.trans h.symm)
  obtain ⟨paint₂, hproper₂, hcX₂, haY₂, hkeep, hfixed,
    qCA, hqLen, w, u, hwOut, huOut, hwu, hqSupport,
    gWU, hgWUF, hgw, hgu, hgWUA⟩ :=
    FivePathState.exists_vz1_internal_c_refined_second_switch
      G s hcritical hdk hdegree hthreshold hleft hright hZ1external
      p hi hiLe hfirst hiZ1 htF ht2 ht3 htC
  have hdX₂ := (hfixed d hda hdb hdc).mpr hdX
  have hdY := FivePathState.missing_left_color_present_right
    G s hcritical hdX
  have hkeepD : ∀ g ∈ F.erase s.omitted,
      s.paint g = d → paint₂ g = d := by
    intro g hgF hgD
    exact (hkeep g (by simpa [hgD] using hda)
      (by simpa [hgD] using hdb)
      (by simpa [hgD] using hdc)).trans hgD
  obtain ⟨gY, hgYF, hgYY, hgYZ, hgYD⟩ :=
    FivePathState.right_d_edge_to_common_z1
      G s hcritical hdk hdegree hthreshold hdX hdY
      hproper₂ hcX₂ haY₂ hdX₂ hkeepD qCA hqLen
      hqSupport hwOut huOut
  obtain ⟨gM, hgMF, hgM2, hgM3, hgMD⟩ :=
    FivePathState.middle_d_edge_of_right_z1_edge
      G s hcritical hdk hdegree hthreshold hdX
      hgYF hgYY hgYZ hgYD
  exact ⟨d, hda, hdb, hdc, hdX, paint₂, hproper₂,
    hcX₂, haY₂, hdX₂, qCA, hqLen,
    w, u, hwOut, huOut, hwu, hqSupport,
    gY, gM, hgYF, hgMF, hgYY, hgYZ, hgM2, hgM3,
    hgYD, hgMD, hkeepD gY hgYF hgYD, hkeepD gM hgMF hgMD⟩

end WeightedEdgeColoring.WeightedMultigraph
