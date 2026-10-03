import WeightedEdgeColoring.SubtwoOrdinaryFivePresentVZ1SecondSwitch

/-!
# Five-vertex critical-chain geometry forces an exterior `a` edge
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- If a critical `(c,a)` path has at most five vertices and already
contains the five distinct vertices `X,Z₁,W,U,Y`, then its middle edge
joins `W` to `U` and has color `a`. -/
theorem forced_outside_a_edge_of_five_critical_path
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {paint : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) paint)
    {x y z w u : G.V} (hxy : x ≠ y) (hxz : x ≠ z) (hzy : z ≠ y)
    (hxe : G.Inc x e) (hye : G.Inc y e)
    {a c : Fin k}
    (hcX : c ∈ G.missingColorsAt (F.erase e) paint x)
    (haY : a ∈ G.missingColorsAt (F.erase e) paint y)
    {S : Finset G.V} (hxS : x ∈ S) (hzS : z ∈ S) (hyS : y ∈ S)
    (hwOut : w ∉ S) (huOut : u ∉ S) (hwu : w ≠ u)
    {g₀ gW gU : G.E}
    (hg₀F : g₀ ∈ F.erase e) (hg₀X : G.Inc x g₀)
    (hg₀Z : G.Inc z g₀) (hg₀A : paint g₀ = a)
    (hgWF : gW ∈ F.erase e) (hgWZ : G.Inc z gW)
    (hgWW : G.Inc w gW) (hgWC : paint gW = c)
    (hgUF : gU ∈ F.erase e) (hgUY : G.Inc y gU)
    (hgUU : G.Inc u gU) (hgUC : paint gU = c)
    (q : (G.twoColorGraph (F.erase e) paint c a).Path x y)
    (hqCard : q.1.support.toFinset.card ≤ 5) :
    ∃ g ∈ F.erase e, G.Inc w g ∧ G.Inc u g ∧ paint g = a := by
  classical
  let H := G.twoColorGraph (F.erase e) paint c a
  have hwx : w ≠ x := by intro h; exact hwOut (h ▸ hxS)
  have hwz : w ≠ z := by intro h; exact hwOut (h ▸ hzS)
  have hwy : w ≠ y := by intro h; exact hwOut (h ▸ hyS)
  have hux : u ≠ x := by intro h; exact huOut (h ▸ hxS)
  have huz : u ≠ z := by intro h; exact huOut (h ▸ hzS)
  have huy : u ≠ y := by intro h; exact huOut (h ▸ hyS)
  have hXZ : H.Adj x z :=
    G.twoColorGraph_adj_of_witness_inc hxz hg₀F hg₀X hg₀Z
      (Or.inr hg₀A)
  have hZW : H.Adj z w :=
    G.twoColorGraph_adj_of_witness_inc hwz.symm hgWF hgWZ hgWW
      (Or.inl hgWC)
  have hYU : H.Adj y u :=
    G.twoColorGraph_adj_of_witness_inc huy.symm hgUF hgUY hgUU
      (Or.inl hgUC)
  have hCompXY := G.critical_endpoints_same_twoColorComponent_at
    hcritical heF hproper hxy hxe hye hcX haY
  have hCompXZ := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hXZ
  have hCompZW := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hZW
  have hCompYU := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hYU
  have hzComp : H.connectedComponentMk z = H.connectedComponentMk x :=
    hCompXZ.symm
  have hwComp : H.connectedComponentMk w = H.connectedComponentMk x :=
    hCompZW.symm.trans hzComp
  have huComp : H.connectedComponentMk u = H.connectedComponentMk x :=
    hCompYU.symm.trans hCompXY.symm
  have hzMem : z ∈ q.1.support :=
    G.mem_criticalPath_support_of_same_twoColorComponent_at
      hcritical heF hproper hxy hxe hye hcX haY q hzComp
  have hwMem : w ∈ q.1.support :=
    G.mem_criticalPath_support_of_same_twoColorComponent_at
      hcritical heF hproper hxy hxe hye hcX haY q hwComp
  have huMem : u ∈ q.1.support :=
    G.mem_criticalPath_support_of_same_twoColorComponent_at
      hcritical heF hproper hxy hxe hye hcX haY q huComp
  have hTsub : ({x,z,w,u,y} : Finset G.V) ⊆
      q.1.support.toFinset := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · simpa only [List.mem_toFinset] using q.1.start_mem_support
    · simpa only [List.mem_toFinset] using hzMem
    · simpa only [List.mem_toFinset] using hwMem
    · simpa only [List.mem_toFinset] using huMem
    · simpa only [List.mem_toFinset] using q.1.end_mem_support
  have hTcard : ({x,z,w,u,y} : Finset G.V).card = 5 := by
    have hnodup : [x,z,w,u,y].Nodup := by
      simp [hxz, hxy, hzy, hwx.symm, hwz.symm, hwy, hux.symm,
        huz.symm, huy, hwu]
    have heq : ([x,z,w,u,y] : List G.V).toFinset =
        ({x,z,w,u,y} : Finset G.V) := by
      ext v
      simp
    rw [← heq]
    rw [List.toFinset_card_of_nodup hnodup]
    simp
  have hqLen : q.1.length = 4 := by
    have hlarge := Finset.card_le_card hTsub
    have hsupportCard : q.1.support.toFinset.card = q.1.length + 1 := by
      rw [List.toFinset_card_of_nodup q.property.support_nodup,
        q.1.length_support]
    omega
  have hfirstAdj : H.Adj x (q.1.getVert 1) := by
    simpa using q.1.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨r₀, hr₀F, hr₀X, hr₀Q, hr₀Color⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) paint c a hfirstAdj
  have hr₀NeC : paint r₀ ≠ c :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase e) paint x c hcX hr₀F hr₀X
  have hr₀A : paint r₀ = a := hr₀Color.resolve_left hr₀NeC
  have hr₀eq : r₀ = g₀ := by
    apply hproper x
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hr₀F, hr₀X⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hg₀F, hg₀X⟩)
    · exact hr₀A.trans hg₀A.symm
  have hqFirst : q.1.getVert 1 = z := by
    have hqOther := G.kempeOtherEndpoint_eq_of_incident
      hr₀X hr₀Q hfirstAdj.ne
    have hgOther := G.kempeOtherEndpoint_eq_of_incident
      hg₀X hg₀Z hxz
    rw [hr₀eq] at hqOther
    exact hqOther.symm.trans hgOther
  have hlastAdj : H.Adj (q.1.getVert 3) y := by
    have hidx : 3 + 1 = q.1.length := by omega
    simpa [hidx] using q.1.adj_getVert_succ (i := 3) (by omega)
  obtain ⟨r₃, hr₃F, hr₃Q, hr₃Y, hr₃Color⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) paint c a hlastAdj
  have hr₃NeA : paint r₃ ≠ a :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase e) paint y a haY hr₃F hr₃Y
  have hr₃C : paint r₃ = c := hr₃Color.resolve_right hr₃NeA
  have hr₃eq : r₃ = gU := by
    apply hproper y
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hr₃F, hr₃Y⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgUF, hgUY⟩)
    · exact hr₃C.trans hgUC.symm
  have hqThird : q.1.getVert 3 = u := by
    have hqOther := G.kempeOtherEndpoint_eq_of_incident
      hr₃Y hr₃Q hlastAdj.ne.symm
    have hgOther := G.kempeOtherEndpoint_eq_of_incident
      hgUY hgUU huy.symm
    rw [hr₃eq] at hqOther
    exact hqOther.symm.trans hgOther
  have hqMiddle : q.1.getVert 2 = w := by
    obtain ⟨j, hj, hjLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hwMem
    have hj4 : j ≤ 4 := by omega
    interval_cases j
    · exact False.elim (hwx (by simpa using hj.symm))
    · exact False.elim (hwz (by simpa [hqFirst] using hj.symm))
    · exact hj
    · exact False.elim (hwu (by simpa [hqThird] using hj.symm))
    · exact False.elim (hwy (by
        have hend : q.1.getVert 4 = y := by
          simpa [hqLen] using q.1.getVert_length
        simpa [hend] using hj.symm))
  have hmidAdj : H.Adj w u := by
    simpa [hqMiddle, hqThird] using
      q.1.adj_getVert_succ (i := 2) (by omega)
  obtain ⟨g, hgF, hgw, hgu, hgColor⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) paint c a hmidAdj
  have hgNeC : paint g ≠ c := by
    intro hgC
    have hgeq : g = gU := by
      apply hproper u
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgu⟩)
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgUF, hgUU⟩)
      · exact hgC.trans hgUC.symm
    have hqOther := G.kempeOtherEndpoint_eq_of_incident
      hgu hgw hwu.symm
    have hgOther := G.kempeOtherEndpoint_eq_of_incident
      hgUU hgUY huy
    rw [hgeq] at hqOther
    exact hwy (hqOther.symm.trans hgOther)
  exact ⟨g, hgF, hgw, hgu, hgColor.resolve_left hgNeC⟩

end WeightedEdgeColoring.WeightedMultigraph
