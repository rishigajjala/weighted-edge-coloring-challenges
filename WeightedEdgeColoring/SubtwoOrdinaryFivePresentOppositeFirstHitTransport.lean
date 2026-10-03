import WeightedEdgeColoring.SubtwoOrdinaryFivePresentOppositeFirstShiftTransport
import WeightedEdgeColoring.SubtwoOrdinaryFivePresentFirstHitCases

/-!
# A degree-two rooted path must keep its exterior prefix

This graph lemma turns the transported `Z₁→Y` exterior route into the
exact first-return order needed after the single-edge shift.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable local instance oppositeFirstHitFiniteNeighborSet
    (H : SimpleGraph G.V) (v : G.V) : Fintype (H.neighborSet v) :=
  @Subtype.fintype G.V (fun w ↦ w ∈ H.neighborSet v)
    (Classical.decPred _) G.instFintypeV

theorem rooted_first_return_at_exterior_prefix_end
    {H : SimpleGraph G.V} {x y z : G.V}
    (pre : H.Path x z) (p : H.Path x y)
    (hmax : ∀ v, H.degree v ≤ 2)
    (hroot : H.degree x ≤ 1)
    (S : G.V → Prop)
    (hzS : S z) (hyS : S y)
    (hxy : y ≠ x) (hyz : y ≠ z) (hxz : x ≠ z)
    (hpreCap : ∀ v ∈ pre.1.support, S v → v = x ∨ v = z)
    {i : ℕ} (hi : 0 < i) (hiLe : i ≤ p.1.length)
    (hiS : S (p.1.getVert i))
    (hfirst : ∀ j, 0 < j → j < i → ¬S (p.1.getVert j)) :
    i = pre.1.length ∧ p.1.getVert i = z := by
  have hprePos : 0 < pre.1.length := by
    by_contra h
    have hz : pre.1.length = 0 := by omega
    exact hxz (SimpleGraph.Walk.eq_of_length_eq_zero hz)
  have hpreLt : pre.1.length < p.1.length := by
    by_contra h
    have hpLe : p.1.length ≤ pre.1.length := by omega
    have hsame := G.rooted_paths_agree_until_shorter_ends
      p pre hmax hroot p.1.length le_rfl hpLe
    have hyPre : y ∈ pre.1.support := by
      have hyVert : pre.1.getVert p.1.length = y := by
        simpa using hsame.symm
      exact hyVert ▸ pre.1.getVert_mem_support p.1.length
    rcases hpreCap y hyPre hyS with h | h
    · exact hxy h
    · exact hyz h
  have hsameAt := G.rooted_paths_agree_until_shorter_ends
    p pre hmax hroot pre.1.length (by omega) le_rfl
  have hpZ : p.1.getVert pre.1.length = z := by
    simpa using hsameAt.trans pre.1.getVert_length
  have hiLePre : i ≤ pre.1.length := by
    by_contra h
    exact hfirst pre.1.length hprePos (by omega)
      (by simpa [hpZ] using hzS)
  have hpreLeI : pre.1.length ≤ i := by
    by_contra h
    have hsameI := G.rooted_paths_agree_until_shorter_ends
      p pre hmax hroot i hiLe (by omega)
    have hmem : pre.1.getVert i ∈ pre.1.support :=
      pre.1.getVert_mem_support i
    rcases hpreCap _ hmem (hsameI ▸ hiS) with hx | hz
    · have hpre0 := pre.1.getVert_zero
      have hinj := pre.property.getVert_injOn
        (Set.mem_Iic.mpr (by omega : i ≤ pre.1.length))
        (Set.mem_Iic.mpr (by omega : 0 ≤ pre.1.length))
        (hx.trans hpre0.symm)
      omega
    · have hinj := pre.property.getVert_injOn
        (Set.mem_Iic.mpr (by omega : i ≤ pre.1.length))
        (Set.mem_Iic.mpr (by omega : pre.1.length ≤ pre.1.length))
        (hz.trans pre.1.getVert_length.symm)
      omega
  constructor
  · omega
  · simpa [show i = pre.1.length by omega] using hpZ

/-- If the rooted degree-two component reaches `y` without visiting
the adjacent target `z`, every rooted path to `z` ends through `y`. -/
theorem rooted_path_penultimate_of_avoiding_route
    {H : SimpleGraph G.V} {x y z : G.V}
    (r : H.Path x y) (q : H.Path x z)
    (hmax : ∀ v, H.degree v ≤ 2)
    (hroot : H.degree x ≤ 1)
    (hzOut : z ∉ r.1.support)
    (hyx : y ≠ x) (hyz : y ≠ z)
    (hyzAdj : H.Adj y z) :
    q.1.getVert (q.1.length - 1) = y := by
  have hrLt : r.1.length < q.1.length := by
    by_contra h
    have hqLe : q.1.length ≤ r.1.length := by omega
    have hsame := G.rooted_paths_agree_until_shorter_ends
      r q hmax hroot q.1.length hqLe le_rfl
    have hzMem : z ∈ r.1.support := by
      have h : r.1.getVert q.1.length = z :=
        hsame.trans q.1.getVert_length
      exact h ▸ r.1.getVert_mem_support q.1.length
    exact hzOut hzMem
  have hsame := G.rooted_paths_agree_until_shorter_ends
    r q hmax hroot r.1.length le_rfl (by omega)
  have hyMem : y ∈ q.1.support := by
    have h : q.1.getVert r.1.length = y :=
      hsame.symm.trans r.1.getVert_length
    exact h ▸ q.1.getVert_mem_support r.1.length
  exact G.path_penultimate_of_internal_adj_endpoint
    q hmax hyMem hyx hyz hyzAdj

/-- The single-edge shift makes the transported exterior prefix the first
return of the new right-rooted `(b,c)` path. -/
theorem FivePathState.exists_first_return_at_one_of_exterior_prefix
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (u : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G u c u.left)
    (hright : FivePathState.HasExternalColorAt G u c u.right)
    (pre : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
      u.right (u.path.1.getVert 1))
    (hpreCap : ∀ v ∈ pre.1.support,
      v ∈ u.path.1.support →
        v = u.right ∨ v = u.path.1.getVert 1) :
    ∃ p : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
        u.right u.left,
      ∃ i : ℕ, 1 < i ∧ i ≤ p.1.length ∧
        (∀ j, 0 < j → j < i →
          p.1.getVert j ∉ u.path.1.support.toFinset) ∧
        p.1.getVert i = u.path.1.getVert 1 := by
  let H := G.twoColorGraph (F.erase u.omitted) u.paint b c
  obtain ⟨g, hgF, hgL, hg1, hgB⟩ :=
    FivePathState.exists_first_b_edge G u
  have hne : u.left ≠ u.path.1.getVert 1 :=
    (FivePathState.internal_vertex_ne_endpoints G u
      (by omega : 0 < 1) (by omega : 1 < 4)).1.symm
  have hAdj : H.Adj u.left (u.path.1.getVert 1) :=
    G.twoColorGraph_adj_of_witness_inc hne hgF hgL hg1 (Or.inl hgB)
  have hpreComp : H.connectedComponentMk u.right =
      H.connectedComponentMk (u.path.1.getVert 1) :=
    SimpleGraph.ConnectedComponent.sound ⟨pre.1⟩
  have hfirstComp : H.connectedComponentMk (u.path.1.getVert 1) =
      H.connectedComponentMk u.left :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hAdj.symm
  have hcomp : H.connectedComponentMk u.right =
      H.connectedComponentMk u.left := hpreComp.trans hfirstComp
  obtain ⟨p,i,hi,hiLe,hfirst,_,hcase⟩ :=
    FivePathState.same_component_first_return_cases G u
      hcritical hdk hdegree hthreshold hleft hright hcomp
  have hmax : ∀ v, H.degree v ≤ 2 := by
    intro v
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase u.omitted) u.paint u.proper b c v
  have hcPresent : c ∉ G.missingColorsAt
      (F.erase u.omitted) u.paint u.right := by
    obtain ⟨h,hF,hInc,hC,_⟩ := hright
    intro hm
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase u.omitted) u.paint u.right c hm hF hInc) hC
  have hactive : G.IsTwoColorActive
      (F.erase u.omitted) u.paint b c u.right :=
    Or.inl ⟨u.right_missing, hcPresent⟩
  have hroot : H.degree u.right ≤ 1 :=
    G.twoColorGraph_degree_le_one_of_active
      (F.erase u.omitted) u.paint u.proper b c u.right hactive
  have hfirstS : u.path.1.getVert 1 ∈ u.path.1.support :=
    u.path.1.getVert_mem_support 1
  have hleftS : u.left ∈ u.path.1.support :=
    u.path.1.start_mem_support
  have hiS : p.1.getVert i ∈ u.path.1.support := by
    rcases hcase with h1 | h2 | h3
    · rw [h1.1]
      exact u.path.1.getVert_mem_support 1
    · rw [h2.1]
      exact u.path.1.getVert_mem_support 2
    · rw [h3.1]
      exact u.path.1.getVert_mem_support 3
  have hfirstEq := G.rooted_first_return_at_exterior_prefix_end
    pre p hmax hroot (fun v ↦ v ∈ u.path.1.support)
    hfirstS hleftS u.left_ne_right hne
    (FivePathState.internal_vertex_ne_endpoints G u
      (by omega : 0 < 1) (by omega : 1 < 4)).2.symm
    hpreCap (by omega) hiLe hiS
    (by intro j hj hji
        simpa only [List.mem_toFinset] using hfirst j hj hji)
  exact ⟨p,i,hi,hiLe,hfirst,hfirstEq.2⟩

theorem FivePathState.exists_first_order_middle_path_of_exterior_routes
    {F : Finset G.E} {k D : ℕ} {a b c : Fin k}
    (u : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G u c u.left)
    (hright : FivePathState.HasExternalColorAt G u c u.right)
    (pre : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
      u.right (u.path.1.getVert 1))
    (hpreCap : ∀ v ∈ pre.1.support,
      v ∈ u.path.1.support →
        v = u.right ∨ v = u.path.1.getVert 1)
    (r : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
      u.left (u.path.1.getVert 2))
    (hrCap : ∀ v ∈ r.1.support,
      v ∈ u.path.1.support →
        v = u.left ∨ v = u.path.1.getVert 2) :
    ∃ p : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
        u.right u.left,
      ∃ i : ℕ, 1 < i ∧ i ≤ p.1.length ∧
        (∀ j, 0 < j → j < i →
          p.1.getVert j ∉ u.path.1.support.toFinset) ∧
        p.1.getVert i = u.path.1.getVert 1 ∧
      ∃ q₃ : (G.twoColorGraph (F.erase u.omitted) u.paint b c).Path
          u.right (u.path.1.getVert 3),
        p.1.length ≤ q₃.1.length ∧
        q₃.1.getVert p.1.length = u.left ∧
        q₃.1.getVert (q₃.1.length - 1) =
          u.path.1.getVert 2 := by
  let H := G.twoColorGraph (F.erase u.omitted) u.paint b c
  obtain ⟨p,i,hi,hiLe,hfirst,hi1⟩ :=
    FivePathState.exists_first_return_at_one_of_exterior_prefix
      G u hcritical hdk hdegree hthreshold
      hleft hright pre hpreCap
  obtain ⟨g₀,hg₀F,hg₀L,hg₀1,hg₀B⟩ :=
    FivePathState.exists_first_b_edge G u
  obtain ⟨_,g₂,_,_,_,_,_,hg₂F,hg₂2,hg₂3,hg₂B,_,_,_,_⟩ :=
    FivePathState.exists_three_surviving_path_edges G u
  have hne01 : u.left ≠ u.path.1.getVert 1 :=
    (FivePathState.internal_vertex_ne_endpoints G u
      (by omega : 0 < 1) (by omega : 1 < 4)).1.symm
  have hne23 : u.path.1.getVert 2 ≠ u.path.1.getVert 3 :=
    (u.path.1.adj_getVert_succ
      (i := 2) (by have := u.path_len; omega)).ne
  have hAdj01 : H.Adj (u.path.1.getVert 1) u.left :=
    (G.twoColorGraph_adj_of_witness_inc hne01
      hg₀F hg₀L hg₀1 (Or.inl hg₀B)).symm
  have hAdj23 : H.Adj (u.path.1.getVert 2)
      (u.path.1.getVert 3) :=
    G.twoColorGraph_adj_of_witness_inc hne23
      hg₂F hg₂2 hg₂3 (Or.inl hg₂B)
  let walk : H.Walk u.right (u.path.1.getVert 2) :=
    (pre.1.concat hAdj01).append r.1
  let route : H.Path u.right (u.path.1.getVert 2) := walk.toPath
  have hne31 : u.path.1.getVert 3 ≠ u.path.1.getVert 1 := by
    intro h
    have hinj := u.path.property.getVert_injOn
      (Set.mem_Iic.mpr (by have := u.path_len; omega : 3 ≤ u.path.1.length))
      (Set.mem_Iic.mpr (by have := u.path_len; omega : 1 ≤ u.path.1.length)) h
    omega
  have hne3R : u.path.1.getVert 3 ≠ u.right :=
    (FivePathState.internal_vertex_ne_endpoints G u
      (by omega : 0 < 3) (by omega : 3 < 4)).2
  have hne3L : u.path.1.getVert 3 ≠ u.left :=
    (FivePathState.internal_vertex_ne_endpoints G u
      (by omega : 0 < 3) (by omega : 3 < 4)).1
  have hne32 : u.path.1.getVert 3 ≠ u.path.1.getVert 2 :=
    hne23.symm
  have hZ3S : u.path.1.getVert 3 ∈ u.path.1.support :=
    u.path.1.getVert_mem_support 3
  have hZ3notWalk : u.path.1.getVert 3 ∉ walk.support := by
    intro hm
    have hparts : u.path.1.getVert 3 ∈
        (pre.1.concat hAdj01).support ∨
        u.path.1.getVert 3 ∈ r.1.support := by
      simpa only [walk, SimpleGraph.Walk.mem_support_append_iff] using hm
    rcases hparts with hfirst | hlast
    · have hparts' : u.path.1.getVert 3 ∈ pre.1.support ∨
          u.path.1.getVert 3 = u.left := by
        simpa [SimpleGraph.Walk.support_concat,
          List.concat_eq_append] using hfirst
      rcases hparts' with hpre | hL
      · rcases hpreCap _ hpre hZ3S with hR | h1
        · exact hne3R hR
        · exact hne31 h1
      · exact hne3L hL
    · rcases hrCap _ hlast hZ3S with hL | h2
      · exact hne3L hL
      · exact hne32 h2
  have hZ3notRoute : u.path.1.getVert 3 ∉ route.1.support := by
    intro hm
    exact hZ3notWalk (walk.support_toPath_subset hm)
  have hrootComp : H.connectedComponentMk u.right =
      H.connectedComponentMk (u.path.1.getVert 2) :=
    SimpleGraph.ConnectedComponent.sound ⟨route.1⟩
  have h23Comp : H.connectedComponentMk (u.path.1.getVert 2) =
      H.connectedComponentMk (u.path.1.getVert 3) :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hAdj23
  have hreach : H.Reachable u.right (u.path.1.getVert 3) :=
    SimpleGraph.ConnectedComponent.exact (hrootComp.trans h23Comp)
  obtain ⟨walk₃⟩ := hreach
  let q₃ : H.Path u.right (u.path.1.getVert 3) := walk₃.toPath
  have hmax : ∀ v, H.degree v ≤ 2 := by
    intro v
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase u.omitted) u.paint u.proper b c v
  have hcPresent : c ∉ G.missingColorsAt
      (F.erase u.omitted) u.paint u.right := by
    obtain ⟨h,hF,hInc,hC,_⟩ := hright
    intro hm
    exact (G.color_ne_of_mem_missingColorsAt
      (F.erase u.omitted) u.paint u.right c hm hF hInc) hC
  have hactive : G.IsTwoColorActive
      (F.erase u.omitted) u.paint b c u.right :=
    Or.inl ⟨u.right_missing, hcPresent⟩
  have hroot : H.degree u.right ≤ 1 :=
    G.twoColorGraph_degree_le_one_of_active
      (F.erase u.omitted) u.paint u.proper b c u.right hactive
  have hpen : q₃.1.getVert (q₃.1.length - 1) =
      u.path.1.getVert 2 :=
    G.rooted_path_penultimate_of_avoiding_route
      route q₃ hmax hroot hZ3notRoute
      (FivePathState.internal_vertex_ne_endpoints G u
        (by omega : 0 < 2) (by omega : 2 < 4)).2
      hne23 hAdj23
  have hshape := FivePathState.first_return_at_z1_then_left
    G u p hi hiLe hfirst hi1
  have hZ2outP : u.path.1.getVert 2 ∉ p.1.support :=
    (FivePathState.first_return_z1_path_avoids_middle
      G u p hi hiLe hfirst hi1).1
  have hpLeQ : p.1.length ≤ q₃.1.length := by
    by_contra h
    have hqLt : q₃.1.length < p.1.length := by omega
    have hsame := G.rooted_paths_agree_until_shorter_ends
      p q₃ hmax hroot q₃.1.length (by omega) le_rfl
    have hZ3mem : u.path.1.getVert 3 ∈ p.1.support := by
      have h : p.1.getVert q₃.1.length = u.path.1.getVert 3 :=
        hsame.trans q₃.1.getVert_length
      exact h ▸ p.1.getVert_mem_support q₃.1.length
    exact (FivePathState.first_return_z1_path_avoids_middle
      G u p hi hiLe hfirst hi1).2 hZ3mem
  have hXat : q₃.1.getVert p.1.length = u.left := by
    have hsame := G.rooted_paths_agree_until_shorter_ends
      p q₃ hmax hroot p.1.length le_rfl hpLeQ
    exact hsame.symm.trans p.1.getVert_length
  exact ⟨p,i,hi,hiLe,hfirst,hi1,q₃,hpLeQ,hXat,hpen⟩

end WeightedEdgeColoring.WeightedMultigraph
