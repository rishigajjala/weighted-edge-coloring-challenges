import WeightedEdgeColoring.SubtwoOrdinaryFivePresentRightSwitchStable

/-!
# Symmetry when the right `(b,c)` component is separate from the left
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.same_ac_component_of_separate_bc
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hnot : FivePathState.NotTwoInternalColor G s c)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hseparate : (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.left ≠
      (G.twoColorGraph (F.erase s.omitted) s.paint b c).connectedComponentMk
        s.right) :
    (G.twoColorGraph (F.erase s.omitted) s.paint a c).connectedComponentMk
      s.left =
    (G.twoColorGraph (F.erase s.omitted) s.paint a c).connectedComponentMk
      s.right := by
  classical
  let H := G.twoColorGraph (F.erase s.omitted) s.paint b c
  have hZ3not : H.connectedComponentMk (s.path.1.getVert 3) ≠
      H.connectedComponentMk s.right := by
    intro h
    exact FivePathState.false_of_right_bc_component_reaches_z3
      G s hcritical hdk hdegree hthreshold hnot
        hleft hright hseparate h
  obtain ⟨switched,hproper,ha,hc,hother,hstable,
    q,hqCard,hq1Out,hq3⟩ :=
    FivePathState.first_switched_critical_path_vertex_outside_with_stability
      G s hcritical hdk hdegree hthreshold
        hleft hright hseparate
  have hqLen : q.1.length = 4 := by
    have hcardLen : q.1.support.toFinset.card = q.1.length + 1 := by
      rw [List.toFinset_card_of_nodup q.property.support_nodup,
        q.1.length_support]
    omega
  have hq0 : q.1.getVert 0 = s.left := q.1.getVert_zero
  have hq4 : q.1.getVert 4 = s.right := by
    simpa [hqLen] using q.1.getVert_length
  let K := G.twoColorGraph (F.erase s.omitted) switched a c
  have hadj01 : K.Adj s.left (q.1.getVert 1) := by
    simpa [hq0] using q.1.adj_getVert_succ
      (i := 0) (by omega : 0 < q.1.length)
  have hadj12 : K.Adj (q.1.getVert 1) (q.1.getVert 2) :=
    q.1.adj_getVert_succ (i := 1) (by omega)
  have hadj23 : K.Adj (q.1.getVert 2)
      (s.path.1.getVert 3) := by
    simpa [hq3] using q.1.adj_getVert_succ (i := 2) (by omega)
  have hadj34 : K.Adj (s.path.1.getVert 3) s.right := by
    simpa [hq3,hq4] using q.1.adj_getVert_succ (i := 3) (by omega)
  obtain ⟨r₀,hr₀F,hr₀X,hr₀1,hr₀Col⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) switched a c hadj01
  obtain ⟨r₁,hr₁F,hr₁1,hr₁2,hr₁Col⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) switched a c hadj12
  obtain ⟨r₂,hr₂F,hr₂2,hr₂3,hr₂Col⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) switched a c hadj23
  obtain ⟨r₃,hr₃F,hr₃3,hr₃Y,hr₃Col⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) switched a c hadj34
  have hr₀NeA : switched r₀ ≠ a :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) switched s.left a ha hr₀F hr₀X
  have hr₀C : switched r₀ = c := hr₀Col.resolve_left hr₀NeA
  have hr₃NeC : switched r₃ ≠ c :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) switched s.right c hc hr₃F hr₃Y
  have hr₃A : switched r₃ = a := hr₃Col.resolve_right hr₃NeC
  have hr₁NeC : switched r₁ ≠ c := by
    intro h
    have heq := hproper (q.1.getVert 1)
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hr₀F,hr₀1⟩))
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hr₁F,hr₁1⟩))
      (hr₀C.trans h.symm)
    have hEndNe : s.left ≠ q.1.getVert 2 := by
      intro heqV
      have hidx := q.property.getVert_injOn
        (Set.mem_Iic.mpr (by omega : 0 ≤ q.1.length))
        (Set.mem_Iic.mpr (by omega : 2 ≤ q.1.length))
        (hq0.trans heqV)
      omega
    have hother₀ := G.kempeOtherEndpoint_eq_of_incident
      hr₀1 hr₀X hadj01.ne.symm
    have hother₁ := G.kempeOtherEndpoint_eq_of_incident
      hr₁1 hr₁2 hadj12.ne
    rw [heq] at hother₀
    exact hEndNe (hother₀.symm.trans hother₁)
  have hr₁A : switched r₁ = a := hr₁Col.resolve_right hr₁NeC
  have hr₂NeA : switched r₂ ≠ a := by
    intro h
    have heq := hproper (s.path.1.getVert 3)
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hr₂F,hr₂3⟩))
      (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hr₃F,hr₃3⟩))
      (h.trans hr₃A.symm)
    have hEndNe : q.1.getVert 2 ≠ s.right := by
      intro heqV
      have hidx := q.property.getVert_injOn
        (Set.mem_Iic.mpr (by omega : 2 ≤ q.1.length))
        (Set.mem_Iic.mpr (by omega : 4 ≤ q.1.length))
        (heqV.trans hq4.symm)
      omega
    have hother₂ := G.kempeOtherEndpoint_eq_of_incident
      hr₂3 hr₂2 hadj23.ne.symm
    have hother₃ := G.kempeOtherEndpoint_eq_of_incident
      hr₃3 hr₃Y hadj34.ne
    rw [heq] at hother₂
    exact hEndNe (hother₂.symm.trans hother₃)
  have hr₂C : switched r₂ = c := hr₂Col.resolve_left hr₂NeA
  have hr₀Old : s.paint r₀ = c :=
    (hstable s.left hseparate r₀ hr₀F hr₀X).symm.trans hr₀C
  have hX1old : H.Adj s.left (q.1.getVert 1) :=
    G.twoColorGraph_adj_of_witness_inc hadj01.ne
      hr₀F hr₀X hr₀1 (Or.inr hr₀Old)
  have hq1Comp : H.connectedComponentMk (q.1.getVert 1) =
      H.connectedComponentMk s.left :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hX1old).symm
  have hq1Not : H.connectedComponentMk (q.1.getVert 1) ≠
      H.connectedComponentMk s.right := by
    intro h
    exact hseparate (hq1Comp.symm.trans h)
  have hr₁Old : s.paint r₁ = a :=
    (hstable _ hq1Not r₁ hr₁F hr₁1).symm.trans hr₁A
  have hr₂Old : s.paint r₂ = c :=
    (hstable _ hZ3not r₂ hr₂F hr₂3).symm.trans hr₂C
  have hr₃Old : s.paint r₃ = a :=
    (hstable _ hZ3not r₃ hr₃F hr₃3).symm.trans hr₃A
  have h23old : H.Adj (q.1.getVert 2)
      (s.path.1.getVert 3) :=
    G.twoColorGraph_adj_of_witness_inc hadj23.ne
      hr₂F hr₂2 hr₂3 (Or.inr hr₂Old)
  let A := G.twoColorGraph (F.erase s.omitted) s.paint a c
  have h01 : A.Adj s.left (q.1.getVert 1) :=
    G.twoColorGraph_adj_of_witness_inc hadj01.ne
      hr₀F hr₀X hr₀1 (Or.inr hr₀Old)
  have h12 : A.Adj (q.1.getVert 1) (q.1.getVert 2) :=
    G.twoColorGraph_adj_of_witness_inc hadj12.ne
      hr₁F hr₁1 hr₁2 (Or.inl hr₁Old)
  have h23 : A.Adj (q.1.getVert 2)
      (s.path.1.getVert 3) :=
    G.twoColorGraph_adj_of_witness_inc hadj23.ne
      hr₂F hr₂2 hr₂3 (Or.inr hr₂Old)
  have h34 : A.Adj (s.path.1.getVert 3) s.right :=
    G.twoColorGraph_adj_of_witness_inc hadj34.ne
      hr₃F hr₃3 hr₃Y (Or.inl hr₃Old)
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h01).trans
    ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h12).trans
      ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h23).trans
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h34)))

end WeightedEdgeColoring.WeightedMultigraph
