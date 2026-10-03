import WeightedEdgeColoring.SubtwoOrdinaryFivePresentFirstHitCases

/-!
# The critical `(a,b)` component is exactly the old five-path
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Every vertex of the critical `(a,b)` component is on the chosen
five-path, and conversely every vertex of that path is in the
component. This gives exact support control for switching the old
critical chain in Andersen's remaining `V = Z₁` case. -/
theorem FivePathState.mem_path_support_iff_ab_component
    {F : Finset G.E} {k : ℕ} {a b : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (v : G.V) :
    v ∈ s.path.1.support ↔
      (G.twoColorGraph (F.erase s.omitted) s.paint a b).connectedComponentMk v =
        (G.twoColorGraph (F.erase s.omitted) s.paint a b).connectedComponentMk
          s.left := by
  let H := G.twoColorGraph (F.erase s.omitted) s.paint a b
  constructor
  · intro hv
    have hreach : H.Reachable s.left v :=
      ⟨s.path.1.takeUntil v hv⟩
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  · intro hcomp
    exact G.mem_criticalPath_support_of_same_twoColorComponent_at
      hcritical s.omitted_mem s.proper s.left_ne_right
      s.left_inc s.right_inc s.left_missing s.right_missing s.path hcomp

/-- Switching just the critical `(a,b)` path leaves all incident
colors unchanged outside its five vertices. -/
theorem FivePathState.exists_ab_path_switch_stable_outside
    {F : Finset G.E} {k : ℕ} {a b : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k) :
    ∃ switched : G.E → Fin k,
      G.IsProperOn (F.erase s.omitted) switched ∧
      (∀ v ∈ s.path.1.support,
        ∀ r ∈ F.erase s.omitted, G.Inc v r →
          s.paint r = a → switched r = b) ∧
      (∀ v ∈ s.path.1.support,
        ∀ r ∈ F.erase s.omitted, G.Inc v r →
          s.paint r = b → switched r = a) ∧
      (∀ r, s.paint r ≠ a → s.paint r ≠ b →
        switched r = s.paint r) ∧
      (∀ v, v ∉ s.path.1.support →
        ∀ r ∈ F.erase s.omitted, G.Inc v r →
          switched r = s.paint r) := by
  classical
  let H := G.twoColorGraph (F.erase s.omitted) s.paint a b
  let flip : H.ConnectedComponent → Prop :=
    fun C ↦ C = H.connectedComponentMk s.left
  letI : DecidablePred flip := Classical.decPred _
  let switched := G.kempeComponentSwitch
    (F.erase s.omitted) s.paint a b flip
  have hproper : G.IsProperOn (F.erase s.omitted) switched :=
    G.isProperOn_kempeComponentSwitch
      (F.erase s.omitted) s.paint s.proper a b flip
  have hswapA : ∀ v ∈ s.path.1.support,
      ∀ r ∈ F.erase s.omitted, G.Inc v r →
        s.paint r = a → switched r = b := by
    intro v hv r hrF hrV hrA
    have hflip : flip (H.connectedComponentMk v) :=
      (FivePathState.mem_path_support_iff_ab_component
        G s hcritical v).mp hv
    change G.kempeComponentSwitch (F.erase s.omitted)
      s.paint a b flip r = b
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase s.omitted) s.paint a b flip hrF hrV]
    simp [kempeLocalPerm, flip, H, hflip, hrA]
  have hswapB : ∀ v ∈ s.path.1.support,
      ∀ r ∈ F.erase s.omitted, G.Inc v r →
        s.paint r = b → switched r = a := by
    intro v hv r hrF hrV hrB
    have hflip : flip (H.connectedComponentMk v) :=
      (FivePathState.mem_path_support_iff_ab_component
        G s hcritical v).mp hv
    change G.kempeComponentSwitch (F.erase s.omitted)
      s.paint a b flip r = a
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase s.omitted) s.paint a b flip hrF hrV]
    simp [kempeLocalPerm, flip, H, hflip, hrB]
  have hother : ∀ r, s.paint r ≠ a → s.paint r ≠ b →
      switched r = s.paint r := by
    intro r hra hrb
    exact G.kempeComponentSwitch_eq_of_color_ne
      s.paint a b flip r hra hrb
  have hstable : ∀ v, v ∉ s.path.1.support →
      ∀ r ∈ F.erase s.omitted, G.Inc v r →
        switched r = s.paint r := by
    intro v hvOut r hrF hrV
    have hnot : ¬flip (H.connectedComponentMk v) := by
      intro h
      exact hvOut ((FivePathState.mem_path_support_iff_ab_component
        G s hcritical v).mpr h)
    change G.kempeComponentSwitch (F.erase s.omitted)
      s.paint a b flip r = s.paint r
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase s.omitted) s.paint a b flip hrF hrV]
    simp [kempeLocalPerm, flip, H, hnot]
  exact ⟨switched, hproper, hswapA, hswapB, hother, hstable⟩

end WeightedEdgeColoring.WeightedMultigraph
