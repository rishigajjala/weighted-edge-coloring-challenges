import WeightedEdgeColoring.SubtwoOrdinaryFivePresentABShiftState

/-!
# Switch the old critical chain, then shift the omitted edge to Z3Y
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Andersen's first switch and omitted-edge shift are available as
actual five-path states: the new omitted edge is `Z₃Y`, the formerly
omitted `XY` edge receives `b`, and the new critical path runs
`Z₃,Z₂,Z₁,X,Y`. External edges of a third color survive both moves. -/
theorem FivePathState.exists_ab_switch_then_shift_last
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hca : c ≠ a) (hcb : c ≠ b) :
    ∃ t u : G.FivePathState F k b a,
      t.omitted = s.omitted ∧
      u.omitted ∈ F.erase s.omitted ∧
      u.left = s.path.1.getVert 3 ∧ u.right = s.right ∧
      u.paint = G.assignEdgeColor t.paint s.omitted b ∧
      u.path.1.support.toFinset = s.path.1.support.toFinset ∧
      u.path.1.getVert 1 = s.path.1.getVert 2 ∧
      u.path.1.getVert 2 = s.path.1.getVert 1 ∧
      u.path.1.getVert 3 = s.left ∧
      (∀ v, FivePathState.HasExternalColorAt G s c v →
        FivePathState.HasExternalColorAt G u c v) := by
  obtain ⟨t,htOmit,htLeft,htRight,htSupport,htVerts,
    htOther,htExternal,htStable⟩ :=
    FivePathState.exists_ab_switched_state G s hcritical
  obtain ⟨u,huF,huInternal,huPaint,huLeft,huRight,
    huSupport,hu1,hu2,hu3⟩ :=
    FivePathState.exists_shiftLast G t hcritical
  have huF' : u.omitted ∈ F.erase s.omitted := by
    simpa [htOmit] using huF
  have huLeft' : u.left = s.path.1.getVert 3 := by
    rw [huLeft]
    exact htVerts 3
  have huRight' : u.right = s.right := huRight.trans htRight
  have huPaint' : u.paint = G.assignEdgeColor t.paint s.omitted b := by
    simpa [htOmit] using huPaint
  have huSupport' : u.path.1.support.toFinset =
      s.path.1.support.toFinset := by
    rw [huSupport, htSupport]
  have hu1' : u.path.1.getVert 1 = s.path.1.getVert 2 :=
    hu1.trans (htVerts 2)
  have hu2' : u.path.1.getVert 2 = s.path.1.getVert 1 :=
    hu2.trans (htVerts 1)
  have hu3' : u.path.1.getVert 3 = s.left := by
    exact hu3.trans htLeft
  have huExternal : ∀ v,
      FivePathState.HasExternalColorAt G s c v →
      FivePathState.HasExternalColorAt G u c v := by
    intro v hExt
    have htExt := htExternal c hca hcb v hExt
    exact FivePathState.external_preserved_of_shiftLast
      G t u huInternal huPaint huSupport htExt
  exact ⟨t,u,htOmit,huF',huLeft',huRight',huPaint',
    huSupport',hu1',hu2',hu3',huExternal⟩

end WeightedEdgeColoring.WeightedMultigraph
