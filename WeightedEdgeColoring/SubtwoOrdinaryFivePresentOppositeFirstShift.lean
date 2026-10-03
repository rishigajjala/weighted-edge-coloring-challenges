import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleOppositeForced

/-!
# Shift the omitted edge once in the opposite-order case

The old omitted edge `XY` is painted `b`, and the first old path edge
`XZ₁` becomes omitted.  The new ordered critical path is
`X,Y,Z₃,Z₂,Z₁`.  This is the symmetry needed in Andersen's final case:
the two middle vertices exchange order without losing the original
five-vertex support or any external edge of color `c`.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem FivePathState.exists_first_edge_shift_for_opposite_order
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hcb : c ≠ b)
    (hnot : FivePathState.NotTwoInternalColor G s c) :
    ∃ u : G.FivePathState F k a b,
      u.left = s.left ∧
      u.right = s.path.1.getVert 1 ∧
      u.path.1.getVert 1 = s.right ∧
      u.path.1.getVert 2 = s.path.1.getVert 3 ∧
      u.path.1.getVert 3 = s.path.1.getVert 2 ∧
      u.path.1.support.toFinset = s.path.1.support.toFinset ∧
      u.paint = G.assignEdgeColor s.paint s.omitted b ∧
      FivePathState.NotTwoInternalColor G u c ∧
      (∀ v, FivePathState.HasExternalColorAt G s c v →
        FivePathState.HasExternalColorAt G u c v) := by
  let sr := s.reverse
  obtain ⟨t, _, hinternal, hpaint, htL, htR,
    htSupport, ht1, ht2, ht3⟩ :=
    FivePathState.exists_shiftLast G sr hcritical
  let u := t.reverse
  have hsr1 : sr.path.1.getVert 1 = s.path.1.getVert 3 := by
    rw [FivePathState.reverse_getVert G s 1]
  have hsr2 : sr.path.1.getVert 2 = s.path.1.getVert 2 := by
    rw [FivePathState.reverse_getVert G s 2]
  have hsr3 : sr.path.1.getVert 3 = s.path.1.getVert 1 := by
    rw [FivePathState.reverse_getVert G s 3]
  have huL : u.left = s.left := htR
  have huR : u.right = s.path.1.getVert 1 := htL.trans hsr3
  have hu1 : u.path.1.getVert 1 = s.right := by
    rw [FivePathState.reverse_getVert G t 1]
    exact ht3
  have hu2 : u.path.1.getVert 2 = s.path.1.getVert 3 := by
    rw [FivePathState.reverse_getVert G t 2]
    exact ht2.trans hsr1
  have hu3 : u.path.1.getVert 3 = s.path.1.getVert 2 := by
    rw [FivePathState.reverse_getVert G t 3]
    exact ht1.trans hsr2
  have huSupport : u.path.1.support.toFinset =
      s.path.1.support.toFinset :=
    (FivePathState.reverse_support G t).trans
      (htSupport.trans (FivePathState.reverse_support G s))
  have huPaint : u.paint = G.assignEdgeColor s.paint s.omitted b := hpaint
  have hnSr : FivePathState.NotTwoInternalColor G sr c :=
    FivePathState.reverse_not_two_internal G s hnot
  have hnT : FivePathState.NotTwoInternalColor G t c :=
    FivePathState.not_two_internal_preserved_of_shiftLast
      G sr t hcb hpaint htSupport hnSr
  have hnU : FivePathState.NotTwoInternalColor G u c :=
    FivePathState.reverse_not_two_internal G t hnT
  have hExt : ∀ v, FivePathState.HasExternalColorAt G s c v →
      FivePathState.HasExternalColorAt G u c v := by
    intro v hv
    have hsr : FivePathState.HasExternalColorAt G sr c v :=
      FivePathState.reverse_external G s hv
    have ht : FivePathState.HasExternalColorAt G t c v :=
      FivePathState.external_preserved_of_shiftLast
        G sr t hinternal hpaint htSupport hsr
    exact FivePathState.reverse_external G t ht
  exact ⟨u, huL, huR, hu1, hu2, hu3,
    huSupport, huPaint, hnU, hExt⟩

end WeightedEdgeColoring.WeightedMultigraph
