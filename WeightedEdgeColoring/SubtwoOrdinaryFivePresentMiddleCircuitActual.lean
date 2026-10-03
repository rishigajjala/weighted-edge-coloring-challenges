import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleCircuit

/-!
# The actual switched circuit separates Z₃ from the other old vertices
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable local instance middleCircuitFiniteNeighborSet
    (H : SimpleGraph G.V) (v : G.V) : Fintype (H.neighborSet v) :=
  @Subtype.fintype G.V (fun w ↦ w ∈ H.neighborSet v)
    (Classical.decPred _) G.instFintypeV

theorem FivePathState.exists_actual_middle_bc_circuit_separation
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
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
      ∀ v ∈ s.path.1.support,
        v ≠ s.path.1.getVert 3 →
          (G.twoColorGraph (F.erase u.omitted) u.paint b c).connectedComponentMk v ≠
          (G.twoColorGraph (F.erase u.omitted) u.paint b c).connectedComponentMk
            (s.path.1.getVert 3) := by
  obtain ⟨t,u,_,huL,huR,_,hu1,hu2,hu3,
    qpre,qsuf,hpreCap,hsufCap,hZ3outPre,hZ3outSuf,_⟩ :=
    FivePathState.exists_actual_middle_exterior_pair_after_switch_shift
      G s hcritical hleft hright p hi hiLe hfirst hiZ1
      q₃ hqLen hX hpen
  let H := G.twoColorGraph (F.erase u.omitted) u.paint b c
  obtain ⟨qcycle,hlen,h12,hZ3out,_,_,_⟩ :=
    FivePathState.exists_middle_bc_circuit_of_exterior_pair
      G s u hu1 hu2 hu3 huR qpre qsuf
      hpreCap hsufCap hZ3outPre hZ3outSuf
  have hmax : ∀ z, H.degree z ≤ 2 := by
    intro z
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase u.omitted) u.paint u.proper b c z
  have hZ3sep : H.connectedComponentMk
        (s.path.1.getVert 3) ≠
      H.connectedComponentMk (s.path.1.getVert 1) := by
    intro heq
    exact hZ3out (G.mem_closedPath_support_of_same_component
      H qcycle hlen h12 hmax heq)
  have hY1 : H.connectedComponentMk s.right =
      H.connectedComponentMk (s.path.1.getVert 1) :=
    SimpleGraph.ConnectedComponent.sound ⟨qpre.1⟩
  have hX2 : H.connectedComponentMk s.left =
      H.connectedComponentMk (s.path.1.getVert 2) :=
    SimpleGraph.ConnectedComponent.sound ⟨qsuf.1⟩
  have h12Comp : H.connectedComponentMk (s.path.1.getVert 1) =
      H.connectedComponentMk (s.path.1.getVert 2) :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h12
  refine ⟨u,huL,huR,?_⟩
  intro v hv hvNe
  have hvS : v ∈ s.path.1.support.toFinset := by simpa using hv
  rw [FivePathState.support_eq_five_vertices G s] at hvS
  simp only [Finset.mem_insert,Finset.mem_singleton] at hvS
  rcases hvS with hX | hZ1 | hZ2 | hZ3 | hY
  · rw [hX,hX2,←h12Comp]
    exact Ne.symm hZ3sep
  · rw [hZ1]
    exact Ne.symm hZ3sep
  · rw [hZ2,←h12Comp]
    exact Ne.symm hZ3sep
  · exact False.elim (hvNe hZ3)
  · rw [hY,hY1]
    exact Ne.symm hZ3sep

end WeightedEdgeColoring.WeightedMultigraph
