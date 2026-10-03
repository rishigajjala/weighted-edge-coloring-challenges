import WeightedEdgeColoring.SubtwoOrdinaryFivePresentExteriorPair

/-!
# Actual exterior qpre and qsuf through one common switch and shift
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable local instance middlePairFiniteNeighborSet
    (H : SimpleGraph G.V) (v : G.V) : Fintype (H.neighborSet v) :=
  @Subtype.fintype G.V (fun w ↦ w ∈ H.neighborSet v)
    (Classical.decPred _) G.instFintypeV

theorem FivePathState.exists_actual_middle_exterior_pair_after_switch_shift
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
    ∃ t u : G.FivePathState F k b a,
      t.omitted = s.omitted ∧
      u.left = s.path.1.getVert 3 ∧ u.right = s.right ∧
      u.paint = G.assignEdgeColor t.paint s.omitted b ∧
      u.path.1.getVert 1 = s.path.1.getVert 2 ∧
      u.path.1.getVert 2 = s.path.1.getVert 1 ∧
      u.path.1.getVert 3 = s.left ∧
      ∃ qpre : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
          s.right (s.path.1.getVert 1),
        ∃ qsuf : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
            s.left (s.path.1.getVert 2),
          (∀ v ∈ qpre.1.support,
            v ∈ s.path.1.support →
              v = s.right ∨ v = s.path.1.getVert 1) ∧
          (∀ v ∈ qsuf.1.support,
            v ∈ s.path.1.support →
              v = s.left ∨ v = s.path.1.getVert 2) ∧
          s.path.1.getVert 3 ∉ qpre.1.support ∧
          s.path.1.getVert 3 ∉ qsuf.1.support ∧
          (∀ v ∈ qpre.1.support, v ∉ qsuf.1.support) := by
  obtain ⟨q₁,hq₁Len,hq₁Cap⟩ :=
    FivePathState.first_return_z1_prefix_support
      G s p hi hiLe hfirst hiZ1
  obtain ⟨q₂,hq₂Cap,hZ3out₂,hq₂Disj⟩ :=
    FivePathState.exists_actual_middle_exterior_suffix
      G s hright p hi hiLe hfirst hiZ1
      q₃ hqLen hX hpen
  have hcap₁ : ∀ v ∈ q₁.1.support,
      v ∈ s.path.1.support →
        v = s.right ∨ v = s.path.1.getVert 1 := by
    intro v hv hvS
    exact hq₁Cap v hv (by simpa using hvS)
  have hZ3neY : s.path.1.getVert 3 ≠ s.right :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 3) (by omega : 3 < 4)).2
  have hZ3neZ1 : s.path.1.getVert 3 ≠
      s.path.1.getVert 1 := by
    intro h
    have hinj := s.path.property.getVert_injOn
      (Set.mem_Iic.mpr (by have := s.path_len; omega : 3 ≤ s.path.1.length))
      (Set.mem_Iic.mpr (by have := s.path_len; omega : 1 ≤ s.path.1.length)) h
    omega
  have hZ3out₁ : s.path.1.getVert 3 ∉ q₁.1.support := by
    intro hmem
    have hS : s.path.1.getVert 3 ∈ s.path.1.support :=
      s.path.1.getVert_mem_support 3
    rcases hcap₁ _ hmem hS with hY | hZ1
    · exact hZ3neY hY
    · exact hZ3neZ1 hZ1
  have hcne := FivePathState.external_endpoint_color_ne_missing
    G s hleft hright
  have hZ1S : s.path.1.getVert 1 ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 1
  have hno₁ : ¬(G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj
      s.right (s.path.1.getVert 1) :=
    FivePathState.no_right_bc_adj_old_vertex G s hright hZ1S
  have hno₂ : ¬(G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj
      s.left (s.path.1.getVert 2) :=
    FivePathState.no_left_bc_adj_middle_second G s hleft
  obtain ⟨t,u,htO,huL,huR,huP,hu1,hu2,hu3,
    qpre,hpreS,_,_,qsuf,hsufS,_,_⟩ :=
    FivePathState.exists_pair_exterior_bc_paths_after_ab_then_shift
      G s hcritical hcne.1 hcne.2
      q₁ q₂ hcap₁ hq₂Cap hno₁ hno₂ hZ3out₁ hZ3out₂
  refine ⟨t,u,htO,huL,huR,huP,hu1,hu2,hu3,
    qpre,qsuf,?_,?_,?_,?_,?_⟩
  · intro v hv hvS
    exact hcap₁ v (by simpa [hpreS] using hv) hvS
  · intro v hv hvS
    exact hq₂Cap v (by simpa [hsufS] using hv) hvS
  · simpa [hpreS] using hZ3out₁
  · simpa [hsufS] using hZ3out₂
  · intro v hvPre hvSuf
    let H := G.twoColorGraph (F.erase s.omitted) s.paint b c
    have hmax : ∀ z, H.degree z ≤ 2 := by
      intro z
      exact G.twoColorGraph_degree_le_two_of_isProperOn
        (F.erase s.omitted) s.paint s.proper b c z
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
    have hXmem : s.left ∈ q₃.1.support := by
      simpa only [hX] using q₃.1.getVert_mem_support p.1.length
    have hpreLen : (q₃.1.takeUntil s.left hXmem).length =
        p.1.length := by
      have hget := q₃.1.getVert_length_takeUntil hXmem
      have hlen := q₃.1.length_takeUntil_le hXmem
      exact q₃.property.getVert_injOn
        (Set.mem_Iic.mpr hlen)
        (Set.mem_Iic.mpr hqLen)
        (hget.trans hX.symm)
    have hvQ₁ : v ∈ q₁.1.support := by simpa [hpreS] using hvPre
    obtain ⟨j,hj,hjLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvQ₁
    have hjQ₃ : q₃.1.getVert j = v := by
      have hsame := G.rooted_paths_agree_until_shorter_ends
        q₁ q₃ hmax hroot j hjLe (by omega)
      exact hsame.symm.trans hj
    have hvPreX : v ∈ (q₃.1.takeUntil s.left hXmem).support := by
      have hjLePre : j ≤ (q₃.1.takeUntil s.left hXmem).length := by omega
      have hget := q₃.1.getVert_takeUntil hXmem hjLePre
      exact (hget.trans hjQ₃) ▸
        (q₃.1.takeUntil s.left hXmem).getVert_mem_support j
    have hvQ₂ : v ∈ q₂.1.support := by simpa [hsufS] using hvSuf
    have hvX : v = s.left := hq₂Disj hXmem v hvQ₂ hvPreX
    have hvOld : v ∈ s.path.1.support := by
      rw [hvX]
      exact s.path.1.start_mem_support
    rcases hcap₁ v hvQ₁ hvOld with hvY | hvZ1
    · exact s.left_ne_right (hvX.symm.trans hvY)
    · exact (FivePathState.internal_vertex_ne_endpoints G s
        (by omega : 0 < 1) (by omega : 1 < 4)).1
        (hvZ1.symm.trans hvX)

end WeightedEdgeColoring.WeightedMultigraph
