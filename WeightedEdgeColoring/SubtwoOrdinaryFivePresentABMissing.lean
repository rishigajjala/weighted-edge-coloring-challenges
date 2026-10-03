import WeightedEdgeColoring.SubtwoOrdinaryFivePresentABComponent

/-!
# Endpoint palettes after switching the old critical chain
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- The checked edgewise behavior of the old-chain switch suffices to
transport the missing endpoint colors: `b` becomes absent at `X`, and
`a` becomes absent at `Y`. -/
theorem FivePathState.ab_path_switch_missing_endpoints
    {F : Finset G.E} {k : ℕ} {a b : Fin k}
    (s : G.FivePathState F k a b)
    {switched : G.E → Fin k}
    (hswapA : ∀ v ∈ s.path.1.support,
      ∀ r ∈ F.erase s.omitted, G.Inc v r →
        s.paint r = a → switched r = b)
    (hswapB : ∀ v ∈ s.path.1.support,
      ∀ r ∈ F.erase s.omitted, G.Inc v r →
        s.paint r = b → switched r = a)
    (hother : ∀ r, s.paint r ≠ a → s.paint r ≠ b →
      switched r = s.paint r) :
    b ∈ G.missingColorsAt (F.erase s.omitted) switched s.left ∧
      a ∈ G.missingColorsAt (F.erase s.omitted) switched s.right := by
  have hab : a ≠ b := by
    obtain ⟨g, hgF, hgL, _, hgB⟩ :=
      FivePathState.exists_first_b_edge G s
    intro h
    have hne := G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.left a s.left_missing hgF hgL
    exact hne (hgB.trans h.symm)
  have hLmem : s.left ∈ s.path.1.support :=
    s.path.1.start_mem_support
  have hRmem : s.right ∈ s.path.1.support :=
    s.path.1.end_mem_support
  constructor
  · simp only [missingColorsAt, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_image]
    intro hused
    obtain ⟨r, hr, hrSw⟩ := hused
    have hrData := Finset.mem_filter.mp hr
    by_cases hra : s.paint r = a
    · exact (G.color_ne_of_mem_missingColorsAt
        (F.erase s.omitted) s.paint s.left a s.left_missing
        hrData.1 hrData.2) hra
    by_cases hrb : s.paint r = b
    · have hswA := hswapB s.left hLmem r hrData.1 hrData.2 hrb
      exact hab (hswA.symm.trans hrSw)
    · have hsw := hother r hra hrb
      exact hrb (hsw.symm.trans hrSw)
  · simp only [missingColorsAt, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_image]
    intro hused
    obtain ⟨r, hr, hrSw⟩ := hused
    have hrData := Finset.mem_filter.mp hr
    by_cases hrb : s.paint r = b
    · exact (G.color_ne_of_mem_missingColorsAt
        (F.erase s.omitted) s.paint s.right b s.right_missing
        hrData.1 hrData.2) hrb
    by_cases hra : s.paint r = a
    · have hswB := hswapA s.right hRmem r hrData.1 hrData.2 hra
      exact hab (hrSw.symm.trans hswB)
    · have hsw := hother r hra hrb
      exact hra (hsw.symm.trans hrSw)

end WeightedEdgeColoring.WeightedMultigraph
