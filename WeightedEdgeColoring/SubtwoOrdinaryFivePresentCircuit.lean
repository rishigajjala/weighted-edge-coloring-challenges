import WeightedEdgeColoring.SubtwoOrdinaryFivePresentKempe

/-!
# Transporting an ordered two-color component across an omitted-edge shift

The first path edge is deleted and the previously omitted edge receives a
color. A path avoiding one endpoint of the deleted edge remains a path in
the shifted two-color graph. This is the graph-theoretic transport needed
before closing Andersen's `(b,c)` component into a circuit.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable local instance fiveCircuitFiniteNeighborSet
    (H : SimpleGraph G.V) (v : G.V) : Fintype (H.neighborSet v) :=
  @Subtype.fintype G.V (fun w ↦ w ∈ H.neighborSet v)
    (Classical.decPred _) G.instFintypeV

theorem twoColorGraph_adj_after_shift_avoiding_removed_endpoint
    {F : Finset G.E} {k : ℕ} {paint : G.E → Fin k}
    {e g : G.E} {a b c : Fin k} {w x y : G.V}
    (hwg : G.Inc w g)
    (hxy : (G.twoColorGraph (F.erase e) paint b c).Adj x y)
    (hwx : w ≠ x) (hwy : w ≠ y) :
    (G.twoColorGraph (F.erase g)
      (G.assignEdgeColor paint e a) b c).Adj x y := by
  obtain ⟨r, hrF, hrX, hrY, hrColor⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) paint b c hxy
  have hrNeG : r ≠ g := by
    intro hrg
    have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc
      hxy.ne hrX hrY
    rw [hrg] at hends
    rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
    · rcases hwg with hwfst | hwsnd
      · exact hwx (hwfst.symm.trans hfst)
      · exact hwy (hwsnd.symm.trans hsnd)
    · rcases hwg with hwfst | hwsnd
      · exact hwy (hwfst.symm.trans hfst)
      · exact hwx (hwsnd.symm.trans hsnd)
  have hrNeE : r ≠ e := (Finset.mem_erase.mp hrF).1
  have hrNew : r ∈ F.erase g :=
    Finset.mem_erase.mpr ⟨hrNeG, (Finset.mem_erase.mp hrF).2⟩
  have hrColorNew : G.assignEdgeColor paint e a r = b ∨
      G.assignEdgeColor paint e a r = c := by
    simpa [G.assignEdgeColor_of_ne paint hrNeE a] using hrColor
  exact G.twoColorGraph_adj_of_witness_inc hxy.ne
    hrNew hrX hrY hrColorNew

/-- A two-color path avoiding one endpoint of the newly omitted edge
survives the shift, with exactly the same ordered support. -/
theorem twoColorPath_after_shift_avoiding_removed_endpoint
    {F : Finset G.E} {k : ℕ} {paint : G.E → Fin k}
    {e g : G.E} {a b c : Fin k} {w x y : G.V}
    (hwg : G.Inc w g)
    (p : (G.twoColorGraph (F.erase e) paint b c).Path x y)
    (hwout : w ∉ p.1.support) :
    ∃ q : (G.twoColorGraph (F.erase g)
        (G.assignEdgeColor paint e a) b c).Path x y,
      q.1.support = p.1.support ∧ q.1.length = p.1.length ∧
        q.1.edges = p.1.edges := by
  let H := G.twoColorGraph (F.erase g)
    (G.assignEdgeColor paint e a) b c
  have hedges : ∀ z ∈ p.1.edges, z ∈ H.edgeSet := by
    intro z hz
    induction z using Sym2.inductionOn with
    | _ u v =>
      have huv : (G.twoColorGraph (F.erase e) paint b c).Adj u v :=
        p.1.edges_subset_edgeSet hz
      have hu : w ≠ u := by
        intro h
        exact hwout (h ▸ p.1.fst_mem_support_of_mem_edges hz)
      have hv : w ≠ v := by
        intro h
        exact hwout (h ▸ p.1.snd_mem_support_of_mem_edges hz)
      exact G.twoColorGraph_adj_after_shift_avoiding_removed_endpoint
        hwg huv hu hv
  let qWalk := p.1.transfer H hedges
  let q : H.Path x y := ⟨qWalk, p.property.transfer hedges⟩
  refine ⟨q, ?_, ?_, ?_⟩
  · change (p.1.transfer H hedges).support = p.1.support
    exact p.1.support_transfer hedges
  · change (p.1.transfer H hedges).length = p.1.length
    exact p.1.length_transfer hedges
  · change (p.1.transfer H hedges).edges = p.1.edges
    exact p.1.edges_transfer hedges

/-- Replacing the first `(b,c)` edge by the omitted edge closes any
`Y`-to-`X` component segment that avoids the other endpoint of the
deleted edge. The resulting circuit keeps the segment's vertex order. -/
theorem twoColorPath_closes_to_cycle_after_shift
    {F : Finset G.E} {k : ℕ} {paint : G.E → Fin k}
    {e g : G.E} {b c : Fin k} {w x y : G.V}
    (heF : e ∈ F) (hgFe : g ∈ F.erase e)
    (hxe : G.Inc x e) (hye : G.Inc y e) (hxy : x ≠ y)
    (hwg : G.Inc w g)
    (p : (G.twoColorGraph (F.erase e) paint b c).Path y x)
    (hwout : w ∉ p.1.support)
    (hnoXY : ¬(G.twoColorGraph (F.erase e) paint b c).Adj x y) :
    ∃ q : (G.twoColorGraph (F.erase g)
        (G.assignEdgeColor paint e b) b c).Path y x,
      q.1.support = p.1.support ∧ q.1.length = p.1.length ∧
      ∃ circuit : (G.twoColorGraph (F.erase g)
          (G.assignEdgeColor paint e b) b c).Walk x x,
        circuit.IsCycle ∧ circuit.support = x :: p.1.support := by
  let H := G.twoColorGraph (F.erase g)
    (G.assignEdgeColor paint e b) b c
  obtain ⟨q, hsupport, hlength, hqEdges⟩ :=
    G.twoColorPath_after_shift_avoiding_removed_endpoint
      (a := b) hwg p hwout
  have heFg : e ∈ F.erase g :=
    Finset.mem_erase.mpr ⟨Ne.symm (Finset.mem_erase.mp hgFe).1, heF⟩
  have hnewE : G.assignEdgeColor paint e b e = b := by
    simp [assignEdgeColor]
  have hXY : H.Adj x y :=
    G.twoColorGraph_adj_of_witness_inc hxy heFg hxe hye
      (Or.inl hnewE)
  have hnoEdge : s(x, y) ∉ q.1.edges := by
    rw [hqEdges]
    intro he
    exact hnoXY (p.1.edges_subset_edgeSet he)
  let circuit : H.Walk x x := .cons hXY q.1
  have hcycle : circuit.IsCycle := q.cons_isCycle hXY hnoEdge
  exact ⟨q, hsupport, hlength,
    circuit, hcycle, by simp [circuit, hsupport]⟩

/-- The boundary `c` edge at the right endpoint excludes a direct
`(b,c)` edge between the omitted-edge endpoints. -/
theorem FivePathState.no_endpoint_bc_edge_of_external_right
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hright : FivePathState.HasExternalColorAt G s c s.right) :
    ¬(G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj
      s.left s.right := by
  obtain ⟨g, hgF, hgR, hgc, hgExt⟩ := hright
  have hR : s.right ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.end_mem_support
  obtain ⟨w, hgw, hwOut, hwNeR⟩ :=
    FivePathState.outside_neighbor_of_external_edge G s hR hgF hgExt
  intro hadj
  obtain ⟨r, hrF, hrL, hrR, hrColor⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) s.paint b c hadj
  have hrNeB : s.paint r ≠ b :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.right b s.right_missing hrF hrR
  have hrC : s.paint r = c := hrColor.resolve_left hrNeB
  have hrg : r = g := by
    apply s.proper s.right
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hrR⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgR⟩)
    · exact hrC.trans hgc.symm
  have hotherR := G.kempeOtherEndpoint_eq_of_incident
    hrR hrL s.left_ne_right.symm
  have hotherG := G.kempeOtherEndpoint_eq_of_incident
    hgR hgw hwNeR.symm
  rw [hrg] at hotherR
  have hLw : s.left = w := hotherR.symm.trans hotherG
  have hL : s.left ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.start_mem_support
  exact hwOut (hLw ▸ hL)

/-- In the `V = X` branch of Andersen's proof, the right `(b,c)`
component reaches `X` before visiting `Z₁`. Moving `b` from `XZ₁` to
the omitted edge turns that ordered component segment into a circuit. -/
theorem FivePathState.first_hit_left_component_closes_after_shift
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    (hfirstHit : s.path.1.getVert 1 ∉ p.1.support) :
    ∃ g : G.E, g ∈ F.erase s.omitted ∧
      G.Inc s.left g ∧ G.Inc (s.path.1.getVert 1) g ∧
      s.paint g = b ∧
      G.IsProperOn (F.erase g)
        (G.assignEdgeColor s.paint s.omitted b) ∧
      ∃ q : (G.twoColorGraph (F.erase g)
          (G.assignEdgeColor s.paint s.omitted b) b c).Path
          s.right s.left,
        q.1.support = p.1.support ∧ q.1.length = p.1.length ∧
        ∃ circuit : (G.twoColorGraph (F.erase g)
            (G.assignEdgeColor s.paint s.omitted b) b c).Walk
            s.left s.left,
          circuit.IsCycle ∧
          circuit.support = s.left :: p.1.support := by
  have hadjFirst : (G.twoColorGraph (F.erase s.omitted) s.paint a b).Adj
      s.left (s.path.1.getVert 1) := by
    simpa using s.path.1.adj_getVert_succ
      (i := 0) (by have hlen := s.path_len; omega : 0 < s.path.1.length)
  obtain ⟨g, hgF, hgL, hg1, hgColor⟩ :=
    G.exists_twoColorWitnessEdge
      (F.erase s.omitted) s.paint a b hadjFirst
  have hgNeA : s.paint g ≠ a :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.left a s.left_missing hgF hgL
  have hgB : s.paint g = b := hgColor.resolve_left hgNeA
  have hproperShift : G.IsProperOn (F.erase g)
      (G.assignEdgeColor s.paint s.omitted b) :=
    G.isProperOn_shiftOmittedEdge_at
      s.omitted_mem hgF s.proper hgB s.left_ne_right
      s.left_inc s.right_inc hgL s.right_missing
  obtain ⟨q, hsupport, hlength, circuit, hcycle, hcycleSupport⟩ :=
    G.twoColorPath_closes_to_cycle_after_shift
      s.omitted_mem hgF s.left_inc s.right_inc s.left_ne_right
      hg1 p hfirstHit
      (FivePathState.no_endpoint_bc_edge_of_external_right G s hright)
  exact ⟨g, hgF, hgL, hg1, hgB, hproperShift,
    q, hsupport, hlength, circuit, hcycle, hcycleSupport⟩

theorem path_length_at_least_two_of_no_endpoint_edge
    (H : SimpleGraph G.V) {x y : G.V} (p : H.Path x y)
    (hxy : x ≠ y) (hno : ¬H.Adj x y) :
    2 ≤ p.1.length := by
  by_contra h
  have hlen : p.1.length = 0 ∨ p.1.length = 1 := by omega
  rcases hlen with hzero | hone
  · exact hxy (SimpleGraph.Walk.eq_of_length_eq_zero hzero)
  · have hfirst : H.Adj x (p.1.getVert 1) := by
      simpa using p.1.adj_getVert_succ (i := 0) (by omega)
    have hlast : p.1.getVert 1 = y := by
      simpa [hone] using p.1.getVert_length
    exact hno (hlast ▸ hfirst)

/-- A path closed by an additional edge fills its whole component in a
graph of maximum degree two. This gives precise control of which edges
are touched by switching Andersen's new circuit. -/
theorem closedPath_support_adj_closed_of_degree_le_two
    (H : SimpleGraph G.V) {x y : G.V} (p : H.Path x y)
    (hlen : 2 ≤ p.1.length) (hxy : H.Adj x y)
    (hmax : ∀ z, H.degree z ≤ 2)
    {z w : G.V} (hz : z ∈ p.1.support) (hzw : H.Adj z w) :
    w ∈ p.1.support := by
  classical
  have htwo {v n₁ n₂ : G.V}
      (hneq : n₁ ≠ n₂) (hvn₁ : H.Adj v n₁)
      (hvn₂ : H.Adj v n₂)
      (hn₁ : n₁ ∈ p.1.support) (hn₂ : n₂ ∈ p.1.support)
      (hv : v = z) : w ∈ p.1.support := by
    have hpair : ({n₁, n₂} : Finset G.V).card = 2 := by
      simp [hneq]
    have hsubset : ({n₁, n₂} : Finset G.V) ⊆ H.neighborFinset v := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact (H.mem_neighborFinset v _).mpr hvn₁
      · exact (H.mem_neighborFinset v _).mpr hvn₂
    have hcard : (H.neighborFinset v).card ≤ 2 := by
      rw [H.card_neighborFinset_eq_degree]
      exact hmax v
    have heq : ({n₁, n₂} : Finset G.V) = H.neighborFinset v :=
      Finset.eq_of_subset_of_card_le hsubset (by omega)
    have hwPair : w = n₁ ∨ w = n₂ := by
      have hmem : w ∈ H.neighborFinset v :=
        (H.mem_neighborFinset v w).mpr (hv ▸ hzw)
      rw [← heq] at hmem
      simpa using hmem
    rcases hwPair with rfl | rfl
    · exact hn₁
    · exact hn₂
  obtain ⟨i, hi, hiLe⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  by_cases hi0 : i = 0
  · subst i
    have hzX : z = x := by simpa using hi.symm
    have hfirst : H.Adj x (p.1.getVert 1) := by
      simpa using p.1.adj_getVert_succ (i := 0) (by omega)
    have hne : p.1.getVert 1 ≠ y := by
      intro h
      have hlast : p.1.getVert p.1.length = y := p.1.getVert_length
      have hidx := p.property.getVert_injOn
        (Set.mem_Iic.mpr (by omega : 1 ≤ p.1.length))
        (Set.mem_Iic.mpr (le_refl p.1.length)) (h.trans hlast.symm)
      omega
    exact htwo hne hfirst hxy
      (p.1.getVert_mem_support 1) p.1.end_mem_support hzX.symm
  by_cases hiEnd : i = p.1.length
  · have hzY : z = y := by simpa [hiEnd] using hi.symm
    have hprev : H.Adj y (p.1.getVert (p.1.length - 1)) := by
      have hidx : p.1.length - 1 + 1 = p.1.length := by omega
      simpa [hidx] using
        (p.1.adj_getVert_succ (i := p.1.length - 1) (by omega)).symm
    have hne : p.1.getVert (p.1.length - 1) ≠ x := by
      intro h
      have hstart : p.1.getVert 0 = x := by simp
      have hidx := p.property.getVert_injOn
        (Set.mem_Iic.mpr (by omega : p.1.length - 1 ≤ p.1.length))
        (Set.mem_Iic.mpr (by omega : 0 ≤ p.1.length))
        (h.trans hstart.symm)
      omega
    exact htwo hne hprev hxy.symm
      (p.1.getVert_mem_support _) p.1.start_mem_support hzY.symm
  have hipos : 0 < i := by omega
  have hiLt : i < p.1.length := by omega
  have hprev : H.Adj z (p.1.getVert (i - 1)) := by
    have hidx : i - 1 + 1 = i := by omega
    simpa [hi, hidx] using
      (p.1.adj_getVert_succ (i := i - 1) (by omega)).symm
  have hnext : H.Adj z (p.1.getVert (i + 1)) := by
    simpa [hi] using p.1.adj_getVert_succ (i := i) hiLt
  have hne : p.1.getVert (i - 1) ≠ p.1.getVert (i + 1) := by
    intro h
    have hidx := p.property.getVert_injOn
      (Set.mem_Iic.mpr (by omega : i - 1 ≤ p.1.length))
      (Set.mem_Iic.mpr (by omega : i + 1 ≤ p.1.length)) h
    omega
  exact htwo hne hprev hnext
    (p.1.getVert_mem_support _) (p.1.getVert_mem_support _) rfl

/-- A vertex reachable from a closed path in a degree-two graph already
lies on that path. -/
theorem mem_closedPath_support_of_same_component
    (H : SimpleGraph G.V) {x y w : G.V} (p : H.Path x y)
    (hlen : 2 ≤ p.1.length) (hxy : H.Adj x y)
    (hmax : ∀ z, H.degree z ≤ 2)
    (hcomp : H.connectedComponentMk w = H.connectedComponentMk x) :
    w ∈ p.1.support := by
  have hreach : H.Reachable x w :=
    SimpleGraph.ConnectedComponent.exact hcomp.symm
  obtain ⟨r⟩ := hreach
  have hwalk : ∀ {u v : G.V}, (t : H.Walk u v) →
      v ∈ p.1.support → u ∈ p.1.support := by
    intro u v t
    induction t with
    | nil => intro h; exact h
    | cons hadj tail ih =>
      intro hv
      exact G.closedPath_support_adj_closed_of_degree_le_two
        H p hlen hxy hmax (ih hv) hadj.symm
  exact hwalk r.reverse p.1.start_mem_support

/-- After the `V = X` shift, the new `(b,c)` circuit is the whole
component of `X`; no other vertex can be reached from it. -/
theorem FivePathState.first_hit_left_shifted_component_support
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    (hfirstHit : s.path.1.getVert 1 ∉ p.1.support) :
    ∃ g : G.E, g ∈ F.erase s.omitted ∧
      G.IsProperOn (F.erase g)
        (G.assignEdgeColor s.paint s.omitted b) ∧
      ∀ v,
        (G.twoColorGraph (F.erase g)
            (G.assignEdgeColor s.paint s.omitted b) b c).connectedComponentMk
            v =
          (G.twoColorGraph (F.erase g)
            (G.assignEdgeColor s.paint s.omitted b) b c).connectedComponentMk
            s.left →
        v ∈ p.1.support := by
  obtain ⟨g, hgF, _, _, _, hproper, q, hsupport,
      hlength, _, _, _⟩ :=
    FivePathState.first_hit_left_component_closes_after_shift
      G s hright p hfirstHit
  let H := G.twoColorGraph (F.erase g)
    (G.assignEdgeColor s.paint s.omitted b) b c
  have hpLen : 2 ≤ p.1.length := by
    apply G.path_length_at_least_two_of_no_endpoint_edge
      (G.twoColorGraph (F.erase s.omitted) s.paint b c) p
      s.left_ne_right.symm
    intro hadj
    exact (FivePathState.no_endpoint_bc_edge_of_external_right G s hright)
      hadj.symm
  have hqLen : 2 ≤ q.1.length := by omega
  have heFg : s.omitted ∈ F.erase g :=
    Finset.mem_erase.mpr
      ⟨Ne.symm (Finset.mem_erase.mp hgF).1, s.omitted_mem⟩
  have hnewE : G.assignEdgeColor s.paint s.omitted b s.omitted = b := by
    simp [assignEdgeColor]
  have hXY : H.Adj s.right s.left :=
    G.twoColorGraph_adj_of_witness_inc s.left_ne_right.symm
      heFg s.right_inc s.left_inc (Or.inl hnewE)
  have hmax : ∀ v, H.degree v ≤ 2 := by
    intro v
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase g) (G.assignEdgeColor s.paint s.omitted b)
      hproper b c v
  refine ⟨g, hgF, hproper, ?_⟩
  intro v hcomp
  have hrightLeft : H.connectedComponentMk s.right =
      H.connectedComponentMk s.left :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hXY
  have hcompRight : H.connectedComponentMk v =
      H.connectedComponentMk s.right := hcomp.trans hrightLeft.symm
  have hv := G.mem_closedPath_support_of_same_component
    H q hqLen hXY hmax hcompRight
  simpa only [hsupport] using hv

end WeightedEdgeColoring.WeightedMultigraph
