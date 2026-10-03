import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleForcedOutside

/-!
# Actual exterior a edge in the Z₂-first branch
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.exists_actual_middle_forced_outside_a_edge
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hZ1 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 1))
    (hnoMiddle : ¬∃ g, g ∈ F.erase s.omitted ∧
      G.Inc (s.path.1.getVert 2) g ∧
      G.Inc (s.path.1.getVert 3) g ∧ s.paint g = c)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ1 : p.1.getVert i = s.path.1.getVert 1)
    (q₃ : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right (s.path.1.getVert 3))
    (hqLen : p.1.length ≤ q₃.1.length)
    (hX : q₃.1.getVert p.1.length = s.left)
    (hpen : q₃.1.getVert (q₃.1.length-1) =
      s.path.1.getVert 2) :
    ∃ u : G.FivePathState F k b a,
      u.left = s.path.1.getVert 3 ∧ u.right = s.right ∧
      ∃ paint₂ : G.E → Fin k,
        G.IsProperOn (F.erase u.omitted) paint₂ ∧
        c ∈ G.missingColorsAt (F.erase u.omitted) paint₂ u.left ∧
        a ∈ G.missingColorsAt (F.erase u.omitted) paint₂ u.right ∧
        ∃ outY outZ : G.V,
          outY ≠ outZ ∧
          outY ∉ s.path.1.support.toFinset ∧
          outZ ∉ s.path.1.support.toFinset ∧
          ∃ gY gZ gA : G.E,
            gY ∈ F.erase u.omitted ∧
            gZ ∈ F.erase u.omitted ∧
            gA ∈ F.erase u.omitted ∧
            G.Inc s.right gY ∧ G.Inc outY gY ∧ paint₂ gY = c ∧
            G.Inc (s.path.1.getVert 2) gZ ∧ G.Inc outZ gZ ∧
              paint₂ gZ = c ∧
            G.Inc outY gA ∧ G.Inc outZ gA ∧ paint₂ gA = a := by
  obtain ⟨u,huL,huR,hu1,hu2,hu3,hZ2Ext,hZ3Ext,hYExt,
    paint₂,hproper,hcLeft,haRight,hother,hstable,_,qCA,hqCard⟩ :=
    FivePathState.exists_actual_middle_second_switch
      G s hcritical hdk hdegree hthreshold hnot
        hleft hright hZ1 hnoMiddle p hi hiLe hfirst hiZ1
        q₃ hqLen hX hpen
  obtain ⟨outY,outZ,hne,hYout,hZout,gY,gZ,gA,
    hgYF,hgZF,hgAF,hgYY,hgYOut,hgYC,
    hgZZ2,hgZOut,hgZC,hgAY,hgAZ,hgAA⟩ :=
    FivePathState.forced_middle_outside_a_edge
      G s u hcritical huL huR hu1 hu2 hu3
        hZ2Ext hZ3Ext hYExt
        hproper hcLeft haRight hother hstable qCA hqCard
  exact ⟨u,huL,huR,paint₂,hproper,hcLeft,haRight,
    outY,outZ,hne,hYout,hZout,
    gY,gZ,gA,hgYF,hgZF,hgAF,hgYY,hgYOut,hgYC,
    hgZZ2,hgZOut,hgZC,hgAY,hgAZ,hgAA⟩

end WeightedEdgeColoring.WeightedMultigraph
