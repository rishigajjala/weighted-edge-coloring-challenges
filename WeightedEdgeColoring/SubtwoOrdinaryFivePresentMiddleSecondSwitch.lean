import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleCircuitRoute

/-!
# Switch Z₃'s BC component and recover the short critical CA path
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable local instance middleSecondFiniteNeighborSet
    (H : SimpleGraph G.V) (v : G.V) : Fintype (H.neighborSet v) :=
  @Subtype.fintype G.V (fun w ↦ w ∈ H.neighborSet v)
    (Classical.decPred _) G.instFintypeV

private theorem cast_middle_route_endpoints
    {H : SimpleGraph G.V} {x x' y y' : G.V}
    (hx : x = x') (hy : y = y') (q : H.Path x y) :
    ∃ q' : H.Path x' y',
      q'.1.support = q.1.support ∧ q'.1.length = q.1.length := by
  subst x'
  subst y'
  exact ⟨q,rfl,rfl⟩

theorem FivePathState.exists_second_switch_from_middle_route
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (u : G.FivePathState F k b a)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (huL : u.left = s.path.1.getVert 3)
    (huR : u.right = s.right)
    (hu1 : u.path.1.getVert 1 = s.path.1.getVert 2)
    (hu2 : u.path.1.getVert 2 = s.path.1.getVert 1)
    (hu3 : u.path.1.getVert 3 = s.left)
    (qpre : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
      s.right (s.path.1.getVert 1))
    (qsuf : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
      s.left (s.path.1.getVert 2))
    (hpreCap : ∀ v ∈ qpre.1.support,
      v ∈ s.path.1.support →
        v = s.right ∨ v = s.path.1.getVert 1)
    (hsufCap : ∀ v ∈ qsuf.1.support,
      v ∈ s.path.1.support →
        v = s.left ∨ v = s.path.1.getVert 2)
    (hZ3outPre : s.path.1.getVert 3 ∉ qpre.1.support)
    (hZ3outSuf : s.path.1.getVert 3 ∉ qsuf.1.support) :
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
  obtain ⟨route,hlen,hclose,hZ3out⟩ :=
    FivePathState.exists_middle_bc_route_avoiding_xy
      G s u hu1 hu2 hu3 huR qpre qsuf
      hpreCap hsufCap hZ3outPre hZ3outSuf
  obtain ⟨route',hRouteS,hRouteL⟩ :=
    G.cast_middle_route_endpoints huR.symm hu3.symm route
  have hlen' : 2 ≤ route'.1.length := by simpa [hRouteL] using hlen
  have hclose' : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Adj
      (u.path.1.getVert 3) u.right := by
    simpa [hu3,huR] using hclose
  have hleftOut : u.left ∉ route'.1.support := by
    simpa [huL,hRouteS] using hZ3out
  let H := G.twoColorGraph (F.erase u.omitted) u.paint b c
  have hmax : ∀ z,
      (G.twoColorGraph (F.erase u.omitted) u.paint b c).degree z ≤ 2 := by
    intro z
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase u.omitted) u.paint u.proper b c z
  have hsep : H.connectedComponentMk
      u.left ≠
      H.connectedComponentMk
        u.right := by
    intro heq
    have hmem := G.mem_closedPath_support_of_same_component
      H
      route' hlen' hclose'.symm hmax heq
    exact hleftOut hmem
  let flip : H.ConnectedComponent → Prop :=
    fun C ↦ C = H.connectedComponentMk u.left
  letI : DecidablePred flip := Classical.decPred _
  let paint₂ := G.kempeComponentSwitch
    (F.erase u.omitted) u.paint b c flip
  have hproper : G.IsProperOn (F.erase u.omitted) paint₂ :=
    G.isProperOn_kempeComponentSwitch
      (F.erase u.omitted) u.paint u.proper b c flip
  have hcLeft : c ∈ G.missingColorsAt
      (F.erase u.omitted) paint₂ u.left :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_flip
      (F.erase u.omitted) u.paint b c flip u.left rfl).1.mpr
      u.left_missing
  have hRightNot : ¬flip (H.connectedComponentMk u.right) := by
    intro h
    exact hsep h.symm
  have haRight : a ∈ G.missingColorsAt
      (F.erase u.omitted) paint₂ u.right :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_not_flip_iff
      (F.erase u.omitted) u.paint b c flip u.right hRightNot a).mpr
      u.right_missing
  have hother : ∀ r, u.paint r ≠ b → u.paint r ≠ c →
      paint₂ r = u.paint r := by
    intro r hrb hrc
    exact G.kempeComponentSwitch_eq_of_color_ne
      u.paint b c flip r hrb hrc
  have hfixed : ∀ d', d' ≠ b → d' ≠ c →
      (d' ∈ G.missingColorsAt (F.erase u.omitted) paint₂ u.left ↔
        d' ∈ G.missingColorsAt (F.erase u.omitted) u.paint u.left) := by
    intro d' hdb hdc
    exact G.mem_missingColorsAt_kempeComponentSwitch_of_fixedColor_iff
      (F := F.erase u.omitted) u.paint b c flip u.left d' hdb hdc
  have hstableOld : ∀ v ∈ s.path.1.support,
      v ≠ s.path.1.getVert 3 →
        ∀ r ∈ F.erase u.omitted, G.Inc v r → paint₂ r = u.paint r := by
    intro v hv hvNe r hrF hrV
    have hvComp : (G.twoColorGraph (F.erase u.omitted) u.paint b c).connectedComponentMk v =
        (G.twoColorGraph (F.erase u.omitted) u.paint b c).connectedComponentMk u.right := by
      have hOld : v ∈ s.path.1.support.toFinset := by simpa using hv
      rw [FivePathState.support_eq_five_vertices G s] at hOld
      simp only [Finset.mem_insert,Finset.mem_singleton] at hOld
      have hYcomp : (G.twoColorGraph (F.erase u.omitted) u.paint b c).connectedComponentMk
          s.right =
          (G.twoColorGraph (F.erase u.omitted) u.paint b c).connectedComponentMk
            (s.path.1.getVert 1) :=
        SimpleGraph.ConnectedComponent.sound ⟨qpre.1⟩
      have hXcomp : (G.twoColorGraph (F.erase u.omitted) u.paint b c).connectedComponentMk
          s.left =
          (G.twoColorGraph (F.erase u.omitted) u.paint b c).connectedComponentMk
            (s.path.1.getVert 2) :=
        SimpleGraph.ConnectedComponent.sound ⟨qsuf.1⟩
      have h12 : (G.twoColorGraph (F.erase u.omitted) u.paint b c).connectedComponentMk
          (s.path.1.getVert 1) =
          (G.twoColorGraph (F.erase u.omitted) u.paint b c).connectedComponentMk
            (s.path.1.getVert 2) := by
        obtain ⟨_,_,h12Adj,_,_,_,_⟩ :=
          FivePathState.exists_middle_bc_circuit_of_exterior_pair
            G s u hu1 hu2 hu3 huR qpre qsuf
              hpreCap hsufCap hZ3outPre hZ3outSuf
        exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h12Adj
      rcases hOld with hX | hZ1 | hZ2 | hZ3 | hY
      · rw [hX,hXcomp,←h12,←hYcomp,←huR]
      · rw [hZ1,←hYcomp,←huR]
      · rw [hZ2,←h12,←hYcomp,←huR]
      · exact False.elim (hvNe hZ3)
      · rw [hY,←huR]
    have hnotFlip : ¬flip (H.connectedComponentMk v) := by
      intro h
      exact hsep (h.symm.trans hvComp)
    change G.kempeComponentSwitch (F.erase u.omitted)
      u.paint b c flip r = u.paint r
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase u.omitted) u.paint b c flip hrF hrV]
    simp [kempeLocalPerm, flip, H, hnotFlip]
  have hcompCA := G.critical_endpoints_same_twoColorComponent_at
    hcritical u.omitted_mem hproper u.left_ne_right
      u.left_inc u.right_inc hcLeft haRight
  have hreachCA : (G.twoColorGraph (F.erase u.omitted) paint₂ c a).Reachable
      u.left u.right := SimpleGraph.ConnectedComponent.exact hcompCA
  obtain ⟨walk⟩ := hreachCA
  let qCA := walk.toPath
  have hcard := G.criticalPath_support_card_le_five_at
    hcritical u.omitted_mem hproper u.left_ne_right
      u.left_inc u.right_inc hcLeft haRight qCA
      hdk hdegree hthreshold
  exact ⟨paint₂,hproper,hcLeft,haRight,hother,hstableOld,
    hfixed,qCA,hcard⟩

end WeightedEdgeColoring.WeightedMultigraph
