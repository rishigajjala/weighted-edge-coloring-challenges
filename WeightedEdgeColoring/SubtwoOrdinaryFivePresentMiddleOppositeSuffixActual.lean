import WeightedEdgeColoring.SubtwoOrdinaryFivePresentMiddleOppositeSuffix

/-!
# Extract the actual X-to-Z₃ exterior segment from the Y-rooted chain
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable local instance middleOppositeSuffixFiniteNeighborSet
    (H : SimpleGraph G.V) (v : G.V) : Fintype (H.neighborSet v) :=
  @Subtype.fintype G.V (fun w ↦ w ∈ H.neighborSet v)
    (Classical.decPred _) G.instFintypeV

theorem FivePathState.exists_actual_middle_opposite_exterior_suffix
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ1 : p.1.getVert i = s.path.1.getVert 1)
    (q₃ : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right (s.path.1.getVert 2))
    (hqLen : p.1.length ≤ q₃.1.length)
    (hX : q₃.1.getVert p.1.length = s.left)
    (hpen : q₃.1.getVert (q₃.1.length-1) =
      s.path.1.getVert 3) :
    ∃ r : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
        s.left (s.path.1.getVert 3),
      (∀ v ∈ r.1.support,
        v ∈ s.path.1.support →
          v = s.left ∨ v = s.path.1.getVert 3) ∧
      s.path.1.getVert 2 ∉ r.1.support ∧
      (∀ hXmem : s.left ∈ q₃.1.support,
        ∀ v ∈ r.1.support,
          v ∈ (q₃.1.takeUntil s.left hXmem).support →
            v = s.left) := by
  let H := G.twoColorGraph (F.erase s.omitted) s.paint b c
  have hmax : ∀ v, H.degree v ≤ 2 := by
    intro v
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase s.omitted) s.paint s.proper b c v
  have hcYpresent : c ∉ G.missingColorsAt
      (F.erase s.omitted) s.paint s.right := by
    obtain ⟨g,hgF,hgY,hgC,_⟩ := hright
    intro hmiss
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.right c hmiss hgF hgY) hgC
  have hYactive : G.IsTwoColorActive
      (F.erase s.omitted) s.paint b c s.right :=
    Or.inl ⟨s.right_missing, hcYpresent⟩
  have hroot : H.degree s.right ≤ 1 :=
    G.twoColorGraph_degree_le_one_of_active
      (F.erase s.omitted) s.paint s.proper b c s.right hYactive
  have hshape := FivePathState.first_return_at_z1_then_left
    G s p hi hiLe hfirst hiZ1
  have hpLen : p.1.length = i+1 := hshape.2.symm
  have hqZ1 : q₃.1.getVert i = s.path.1.getVert 1 := by
    have hsame := G.rooted_paths_agree_until_shorter_ends
      p q₃ hmax hroot i hiLe (by omega)
    exact hsame.symm.trans hiZ1
  have hZ2neX : s.path.1.getVert 2 ≠ s.left :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 2) (by omega : 2 < 4)).1
  have hZ3neX : s.path.1.getVert 3 ≠ s.left :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 3) (by omega : 3 < 4)).1
  have horder : i+1 < q₃.1.length-1 := by
    have hlenLt : p.1.length < q₃.1.length := by
      by_contra h
      have heq : p.1.length = q₃.1.length := by omega
      have hX3 : s.left = s.path.1.getVert 2 := by
        exact (heq ▸ hX).symm.trans q₃.1.getVert_length
      exact hZ2neX hX3.symm
    have hne : p.1.length ≠ q₃.1.length-1 := by
      intro heq
      have hX2 : s.left = s.path.1.getVert 3 := by
        exact (heq ▸ hX).symm.trans hpen
      exact hZ3neX hX2.symm
    omega
  have hXmem : s.left ∈ q₃.1.support := by
    simpa only [hX] using q₃.1.getVert_mem_support p.1.length
  obtain ⟨r,hrCap,hZ2out,hdisj⟩ :=
    FivePathState.exists_middle_opposite_exterior_suffix
      G s q₃ i hqZ1 (by simpa [←hpLen] using hX)
        hpen horder hXmem
  refine ⟨r,hrCap,hZ2out,?_⟩
  intro hXmem' v hv hvPre
  have hPreEq : q₃.1.takeUntil s.left hXmem' =
      q₃.1.takeUntil s.left hXmem := rfl
  exact hdisj v hv (by simpa [hPreEq] using hvPre)

end WeightedEdgeColoring.WeightedMultigraph
