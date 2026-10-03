import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddlePairExternalActual

/-!
# Actual second BC switch in the no-middle-c, Z₂-first branch
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.exists_actual_middle_second_switch
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
      u.path.1.getVert 1 = s.path.1.getVert 2 ∧
      u.path.1.getVert 2 = s.path.1.getVert 1 ∧
      u.path.1.getVert 3 = s.left ∧
      FivePathState.HasExternalColorAt G u c (s.path.1.getVert 2) ∧
      FivePathState.HasExternalColorAt G u c (s.path.1.getVert 3) ∧
      FivePathState.HasExternalColorAt G u c s.right ∧
      ∃ paint₂ : G.E → Fin k,
        G.IsProperOn (F.erase u.omitted) paint₂ ∧
        c ∈ G.missingColorsAt (F.erase u.omitted) paint₂ u.left ∧
        a ∈ G.missingColorsAt (F.erase u.omitted) paint₂ u.right ∧
        (∀ r, u.paint r ≠ b → u.paint r ≠ c →
          paint₂ r = u.paint r) ∧
        (∀ v ∈ s.path.1.support, v ≠ s.path.1.getVert 3 →
          ∀ r ∈ F.erase u.omitted, G.Inc v r →
            paint₂ r = u.paint r) ∧
        (∀ d', d' ≠ b → d' ≠ c →
          (d' ∈ G.missingColorsAt (F.erase u.omitted) paint₂ u.left ↔
            d' ∈ G.missingColorsAt (F.erase u.omitted) u.paint u.left)) ∧
        ∃ qCA : (G.twoColorGraph (F.erase u.omitted) paint₂ c a).Path
            u.left u.right,
          qCA.1.support.toFinset.card ≤ 5 := by
  obtain ⟨hZ2Ext,hZ3Ext⟩ :=
    FivePathState.external_middle_pair_of_no_middle_c
      G s hcritical hdk hdegree hthreshold hnot
        hleft hright hZ1 hnoMiddle
  obtain ⟨t,u,_,huL,huR,_,hu1,hu2,hu3,hExt,
    qpre,qsuf,hpreCap,hsufCap,hZ3outPre,hZ3outSuf,_⟩ :=
    FivePathState.exists_actual_middle_exterior_pair_with_external_after_switch_shift
      G s hcritical hleft hright p hi hiLe hfirst hiZ1
        q₃ hqLen hX hpen
  obtain ⟨paint₂,hproper,hcLeft,haRight,hother,hstable,hfixed,qCA,hcard⟩ :=
    FivePathState.exists_second_switch_from_middle_route
      G s u hcritical hdk hdegree hthreshold
        huL huR hu1 hu2 hu3 qpre qsuf
          hpreCap hsufCap hZ3outPre hZ3outSuf
  exact ⟨u,huL,huR,hu1,hu2,hu3,
    hExt _ hZ2Ext,hExt _ hZ3Ext,hExt _ hright,
    paint₂,hproper,hcLeft,haRight,hother,hstable,hfixed,qCA,hcard⟩

end WeightedEdgeColoring.WeightedMultigraph
