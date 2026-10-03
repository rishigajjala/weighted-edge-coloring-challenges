import WeightedEdgeColoring.SubtwoOrdinaryFivePresentOppositeFirstShift
import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleRotateTransport
import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleNoChordThird

/-!
# Exterior routes survive the first-edge shift

Only the old omitted edge changes paint.  Its endpoints belong to the
five-path support, so paint is unchanged at each outside endpoint.  This
is exactly the hypothesis of the existing exterior-path transport lemma.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.first_edge_shift_paint_stable_outside
    {F : Finset G.E} {k : ℕ} {a b : Fin k}
    (s : G.FivePathState F k a b)
    (u : G.FivePathState F k a b)
    (hpaint : u.paint = G.assignEdgeColor s.paint s.omitted b)
    {v : G.V} (hv : v ∉ s.path.1.support.toFinset)
    {r : G.E} (hrInc : G.Inc v r) :
    u.paint r = s.paint r := by
  have hrNe : r ≠ s.omitted := by
    intro heq
    subst r
    have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc
      s.left_ne_right s.left_inc s.right_inc
    have hvLR : v = s.left ∨ v = s.right := by
      rcases hends with ⟨hf,hs⟩ | ⟨hf,hs⟩
      · rcases hrInc with hfV | hsV
        · exact Or.inl (hfV.symm.trans hf)
        · exact Or.inr (hsV.symm.trans hs)
      · rcases hrInc with hfV | hsV
        · exact Or.inr (hfV.symm.trans hf)
        · exact Or.inl (hsV.symm.trans hs)
    rcases hvLR with hL | hR
    · apply hv
      rw [hL]
      simpa only [List.mem_toFinset] using s.path.1.start_mem_support
    · apply hv
      rw [hR]
      simpa only [List.mem_toFinset] using s.path.1.end_mem_support
  rw [hpaint, G.assignEdgeColor_of_ne s.paint hrNe b]

theorem FivePathState.exists_first_shift_transported_exterior_routes
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hnot : FivePathState.NotTwoInternalColor G s c)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (hZ1 : FivePathState.HasExternalColorAt G s c
      (s.path.1.getVert 1))
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ1 : p.1.getVert i = s.path.1.getVert 1)
    (q₂ : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right (s.path.1.getVert 2))
    (hqLen : p.1.length ≤ q₂.1.length)
    (hX : q₂.1.getVert p.1.length = s.left)
    (hpen : q₂.1.getVert (q₂.1.length-1) =
      s.path.1.getVert 3) :
    ∃ u : G.FivePathState F k a b,
      u.left = s.left ∧
      u.right = s.path.1.getVert 1 ∧
      u.path.1.getVert 1 = s.right ∧
      u.path.1.getVert 2 = s.path.1.getVert 3 ∧
      u.path.1.getVert 3 = s.path.1.getVert 2 ∧
      u.path.1.support.toFinset = s.path.1.support.toFinset ∧
      u.paint = G.assignEdgeColor s.paint s.omitted b ∧
      FivePathState.NotTwoInternalColor G u c ∧
      FivePathState.HasExternalColorAt G u c u.left ∧
      FivePathState.HasExternalColorAt G u c u.right ∧
      FivePathState.HasExternalColorAt G u c (u.path.1.getVert 1) ∧
      ∃ pre : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
          u.right (u.path.1.getVert 1),
        (∀ v ∈ pre.1.support,
          v ∈ u.path.1.support →
            v = u.right ∨ v = u.path.1.getVert 1) ∧
      ∃ r : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
          u.left (u.path.1.getVert 2),
        (∀ v ∈ r.1.support,
          v ∈ u.path.1.support →
            v = u.left ∨ v = u.path.1.getVert 2) := by
  have hcb := (FivePathState.external_endpoint_color_ne_missing
    G s hleft hright).2
  obtain ⟨u, huL, huR, hu1, hu2, hu3, huS,
    huPaint, huNot, huExt⟩ :=
    FivePathState.exists_first_edge_shift_for_opposite_order
      G s hcritical hcb hnot
  have hStable : ∀ v, v ∉ s.path.1.support.toFinset →
      ∀ r, G.Inc v r → u.paint r = s.paint r := by
    intro v hv r hr
    exact FivePathState.first_edge_shift_paint_stable_outside
      G s u huPaint hv hr
  obtain ⟨old, hcap, _, _⟩ :=
    FivePathState.exists_actual_middle_opposite_exterior_suffix
      G s hright p hi hiLe hfirst hiZ1 q₂ hqLen hX hpen
  obtain ⟨oldPre, _, hpreCap⟩ :=
    FivePathState.first_return_z1_prefix_support
      G s p hi hiLe hfirst hiZ1
  have hno : ¬(G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj
      s.left (s.path.1.getVert 3) :=
    FivePathState.no_left_bc_adj_middle_third G s hleft
  have hExterior := G.exterior_edges_of_endpoint_only_support
    (G.twoColorGraph (F.erase s.omitted) s.paint b c)
    (fun v ↦ v ∈ s.path.1.support) old hcap hno
  obtain ⟨r, hrS, _, _⟩ :=
    FivePathState.transfer_exterior_path_of_outside_stability
      G s u huS hStable old hExterior
  have hZ1S : s.path.1.getVert 1 ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 1
  have hnoPre : ¬(G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj
      s.right (s.path.1.getVert 1) :=
    FivePathState.no_right_bc_adj_old_vertex G s hright hZ1S
  have hpreCapSet : ∀ v ∈ oldPre.1.support,
      v ∈ s.path.1.support →
        v = s.right ∨ v = s.path.1.getVert 1 := by
    intro v hv hvS
    exact hpreCap v hv (by simpa using hvS)
  have hpreExterior := G.exterior_edges_of_endpoint_only_support
    (G.twoColorGraph (F.erase s.omitted) s.paint b c)
    (fun v ↦ v ∈ s.path.1.support) oldPre hpreCapSet hnoPre
  obtain ⟨preForward, hpreS, _, _⟩ :=
    FivePathState.transfer_exterior_path_of_outside_stability
      G s u huS hStable oldPre hpreExterior
  let pre := preForward.reverse
  let pre' := G.pathEndpointsCast huR hu1 pre
  let r' := G.pathEndpointsCast huL hu2 r
  refine ⟨u, huL, huR, hu1, hu2, hu3, huS,
    huPaint, huNot, ?_, ?_, ?_, pre', ?_, r', ?_⟩
  · exact huL.symm ▸ huExt _ hleft
  · exact huR.symm ▸ huExt _ hZ1
  · exact hu1 ▸ huExt _ hright
  · intro v hv hvU
    have hvOld : v ∈ oldPre.1.support := by
      simpa [pre', pre, G.pathEndpointsCast_support,
        SimpleGraph.Walk.support_reverse, hpreS] using hv
    have hvUf : v ∈ u.path.1.support.toFinset := by simpa using hvU
    have hvSf : v ∈ s.path.1.support.toFinset := by
      rw [← huS]
      exact hvUf
    rcases hpreCapSet v hvOld (by simpa using hvSf) with hY | hZ1eq
    · exact Or.inr (hY.trans hu1.symm)
    · exact Or.inl (hZ1eq.trans huR.symm)
  · intro v hv hvU
    have hvOld : v ∈ old.1.support := by
      simpa [r', G.pathEndpointsCast_support, hrS] using hv
    have hvUf : v ∈ u.path.1.support.toFinset := by simpa using hvU
    have hvSf : v ∈ s.path.1.support.toFinset := by
      rw [← huS]
      exact hvUf
    rcases hcap v hvOld (by simpa using hvSf) with hX | hZ3
    · exact Or.inl (hX.trans huL.symm)
    · exact Or.inr (hZ3.trans hu2.symm)

end WeightedEdgeColoring.WeightedMultigraph
