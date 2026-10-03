import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleSuffixActual

/-!
# Two exterior BC segments through one common AB switch and shift
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

private theorem cast_pair_path_graph
    {H K : SimpleGraph G.V} {x y : G.V}
    (h : H = K) (q : H.Path x y) :
    ∃ q' : K.Path x y,
      q'.1.support = q.1.support ∧ q'.1.length = q.1.length ∧
      q'.1.edges = q.1.edges := by
  subst K
  exact ⟨q,rfl,rfl,rfl⟩

theorem FivePathState.exists_pair_exterior_bc_paths_after_ab_then_shift
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hca : c ≠ a) (hcb : c ≠ b)
    {x₁ y₁ x₂ y₂ : G.V}
    (q₁ : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path x₁ y₁)
    (q₂ : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path x₂ y₂)
    (hcap₁ : ∀ v ∈ q₁.1.support,
      v ∈ s.path.1.support → v = x₁ ∨ v = y₁)
    (hcap₂ : ∀ v ∈ q₂.1.support,
      v ∈ s.path.1.support → v = x₂ ∨ v = y₂)
    (hno₁ : ¬(G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj x₁ y₁)
    (hno₂ : ¬(G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj x₂ y₂)
    (hZ3out₁ : s.path.1.getVert 3 ∉ q₁.1.support)
    (hZ3out₂ : s.path.1.getVert 3 ∉ q₂.1.support) :
    ∃ t u : G.FivePathState F k b a,
      t.omitted = s.omitted ∧
      u.left = s.path.1.getVert 3 ∧ u.right = s.right ∧
      u.paint = G.assignEdgeColor t.paint s.omitted b ∧
      u.path.1.getVert 1 = s.path.1.getVert 2 ∧
      u.path.1.getVert 2 = s.path.1.getVert 1 ∧
      u.path.1.getVert 3 = s.left ∧
      ∃ q₁' : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path x₁ y₁,
        q₁'.1.support = q₁.1.support ∧
        q₁'.1.length = q₁.1.length ∧
        q₁'.1.edges = q₁.1.edges ∧
        ∃ q₂' : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path x₂ y₂,
          q₂'.1.support = q₂.1.support ∧
          q₂'.1.length = q₂.1.length ∧
          q₂'.1.edges = q₂.1.edges := by
  obtain ⟨t,htOmit,htLeft,htRight,_,htVerts,htOther,_,htStable⟩ :=
    FivePathState.exists_ab_switched_state G s hcritical
  obtain ⟨u,_,_,huPaint,huLeft,huRight,_,hu1,hu2,hu3⟩ :=
    FivePathState.exists_shiftLast G t hcritical
  have hZ3Inc : G.Inc (s.path.1.getVert 3) u.omitted := by
    rw [← htVerts 3, ← huLeft]
    exact u.left_inc
  have transport {x y : G.V}
      (q : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path x y)
      (hcap : ∀ v ∈ q.1.support,
        v ∈ s.path.1.support → v = x ∨ v = y)
      (hno : ¬(G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj x y)
      (hZ3out : s.path.1.getVert 3 ∉ q.1.support) :
      ∃ q' : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path x y,
        q'.1.support = q.1.support ∧ q'.1.length = q.1.length ∧
          q'.1.edges = q.1.edges := by
    have hexterior := G.exterior_edges_of_endpoint_only_support
      (G.twoColorGraph (F.erase s.omitted) s.paint b c)
      (fun v ↦ v ∈ s.path.1.support) q hcap hno
    obtain ⟨r,hrS,hrL,hrE⟩ :=
      FivePathState.transfer_exterior_bc_path_after_ab_switch
        G s hca hcb htOther htStable q hexterior
    have hGraph₁ : G.twoColorGraph (F.erase s.omitted) t.paint b c =
        G.twoColorGraph (F.erase t.omitted) t.paint b c := by
      rw [htOmit]
    obtain ⟨r',hr'S,hr'L,hr'E⟩ := G.cast_pair_path_graph hGraph₁ r
    have hZ3out' : s.path.1.getVert 3 ∉ r'.1.support := by
      simpa [hr'S,hrS] using hZ3out
    obtain ⟨r₂,hr₂S,hr₂L,hr₂E⟩ :=
      G.twoColorPath_after_shift_avoiding_removed_endpoint
        (F := F) (paint := t.paint) (e := t.omitted)
        (g := u.omitted) (a := b) (b := b) (c := c)
        hZ3Inc r' hZ3out'
    have hGraph₂ : G.twoColorGraph (F.erase u.omitted)
        (G.assignEdgeColor t.paint t.omitted b) b c =
        G.twoColorGraph (F.erase u.omitted) u.paint b c := by
      rw [huPaint]
    obtain ⟨r₃,hr₃S,hr₃L,hr₃E⟩ := G.cast_pair_path_graph hGraph₂ r₂
    exact ⟨r₃,
      hr₃S.trans (hr₂S.trans (hr'S.trans hrS)),
      hr₃L.trans (hr₂L.trans (hr'L.trans hrL)),
      hr₃E.trans (hr₂E.trans (hr'E.trans hrE))⟩
  obtain ⟨q₁',h₁S,h₁L,h₁E⟩ := transport q₁ hcap₁ hno₁ hZ3out₁
  obtain ⟨q₂',h₂S,h₂L,h₂E⟩ := transport q₂ hcap₂ hno₂ hZ3out₂
  exact ⟨t,u,htOmit,huLeft.trans (htVerts 3),
    huRight.trans htRight,by simpa [htOmit] using huPaint,
    hu1.trans (htVerts 2),hu2.trans (htVerts 1),
    hu3.trans htLeft,
    q₁',h₁S,h₁L,h₁E,q₂',h₂S,h₂L,h₂E⟩

end WeightedEdgeColoring.WeightedMultigraph
