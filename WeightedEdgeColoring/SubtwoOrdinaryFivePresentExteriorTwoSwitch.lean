import WeightedEdgeColoring.SubtwoOrdinaryFivePresentExteriorTransport

/-!
# Exterior BC paths survive the AB switch and omitted-edge shift
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

private theorem cast_path_graph
    {H K : SimpleGraph G.V} {x y : G.V}
    (h : H = K) (q : H.Path x y) :
    ∃ q' : K.Path x y,
      q'.1.support = q.1.support ∧ q'.1.length = q.1.length ∧
      q'.1.edges = q.1.edges := by
  subst K
  exact ⟨q,rfl,rfl,rfl⟩

theorem FivePathState.exists_exterior_bc_path_after_ab_then_shift
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hca : c ≠ a) (hcb : c ≠ b)
    {x y : G.V}
    (q : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path x y)
    (hcap : ∀ v ∈ q.1.support,
      v ∈ s.path.1.support → v = x ∨ v = y)
    (hno : ¬(G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj x y)
    (hZ3out : s.path.1.getVert 3 ∉ q.1.support) :
    ∃ t u : G.FivePathState F k b a,
      t.omitted = s.omitted ∧
      u.left = s.path.1.getVert 3 ∧ u.right = s.right ∧
      u.paint = G.assignEdgeColor t.paint s.omitted b ∧
      ∃ q' : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path x y,
        q'.1.support = q.1.support ∧ q'.1.length = q.1.length ∧
        q'.1.edges = q.1.edges := by
  obtain ⟨t,htOmit,_,htRight,_,htVerts,htOther,_,htStable⟩ :=
    FivePathState.exists_ab_switched_state G s hcritical
  obtain ⟨u,_,_,huPaint,huLeft,huRight,_,_,_,_⟩ :=
    FivePathState.exists_shiftLast G t hcritical
  have hexterior := G.exterior_edges_of_endpoint_only_support
    (G.twoColorGraph (F.erase s.omitted) s.paint b c)
    (fun v ↦ v ∈ s.path.1.support) q hcap hno
  obtain ⟨q₁,hq₁S,hq₁L,hq₁E⟩ :=
    FivePathState.transfer_exterior_bc_path_after_ab_switch
      G s hca hcb htOther htStable q hexterior
  have hGraph₁ : G.twoColorGraph (F.erase s.omitted) t.paint b c =
      G.twoColorGraph (F.erase t.omitted) t.paint b c := by
    rw [htOmit]
  obtain ⟨q₁',hq₁'S,hq₁'L,hq₁'E⟩ :=
    G.cast_path_graph hGraph₁ q₁
  have hZ3out₁ : s.path.1.getVert 3 ∉ q₁'.1.support := by
    simpa [hq₁'S,hq₁S] using hZ3out
  have hZ3Inc : G.Inc (s.path.1.getVert 3) u.omitted := by
    rw [← htVerts 3, ← huLeft]
    exact u.left_inc
  obtain ⟨q₂,hq₂S,hq₂L,hq₂E⟩ :=
    G.twoColorPath_after_shift_avoiding_removed_endpoint
      (F := F) (paint := t.paint)
      (e := t.omitted) (g := u.omitted) (a := b)
      (b := b) (c := c) hZ3Inc
      q₁' hZ3out₁
  have hGraph₂ : G.twoColorGraph (F.erase u.omitted)
      (G.assignEdgeColor t.paint t.omitted b) b c =
      G.twoColorGraph (F.erase u.omitted) u.paint b c := by
    rw [huPaint]
  obtain ⟨q₂',hq₂'S,hq₂'L,hq₂'E⟩ :=
    G.cast_path_graph hGraph₂ q₂
  refine ⟨t,u,htOmit,huLeft.trans (htVerts 3),huRight.trans htRight,?_,?_⟩
  · simpa [htOmit] using huPaint
  · refine ⟨q₂', ?_, ?_, ?_⟩
    · exact hq₂'S.trans (hq₂S.trans (hq₁'S.trans hq₁S))
    · exact hq₂'L.trans (hq₂L.trans (hq₁'L.trans hq₁L))
    · exact hq₂'E.trans (hq₂E.trans (hq₁'E.trans hq₁E))

end WeightedEdgeColoring.WeightedMultigraph
