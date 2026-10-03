import WeightedEdgeColoring.SubtwoOrdinaryFivePresentABComponent

/-!
# Transport of the exterior `Y→Z₁` prefix through the critical-chain switch
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Since `Y`'s unique `(b,c)` edge is the external `c` edge, it has
no `(b,c)` adjacency to another old five-path vertex. -/
theorem FivePathState.no_right_bc_adj_old_vertex
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    {v : G.V} (hvS : v ∈ s.path.1.support.toFinset) :
    ¬(G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj s.right v := by
  obtain ⟨g, hgF, hgR, hgC, hgExt⟩ := hright
  have hRmem : s.right ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.end_mem_support
  obtain ⟨w, hgw, hwOut, hwNeR⟩ :=
    FivePathState.outside_neighbor_of_external_edge G s hRmem hgF hgExt
  intro hadj
  obtain ⟨r, hrF, hrR, hrV, hrColor⟩ :=
    G.exists_twoColorWitnessEdge (F.erase s.omitted) s.paint b c hadj
  have hrNeB : s.paint r ≠ b :=
    G.color_ne_of_mem_missingColorsAt
      (F.erase s.omitted) s.paint s.right b s.right_missing hrF hrR
  have hrC : s.paint r = c := hrColor.resolve_left hrNeB
  have hrg : r = g := by
    apply s.proper s.right
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hrR⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgR⟩)
    · exact hrC.trans hgC.symm
  have hrOther := G.kempeOtherEndpoint_eq_of_incident
    hrR hrV hadj.ne
  have hgOther := G.kempeOtherEndpoint_eq_of_incident
    hgR hgw hwNeR.symm
  rw [hrg] at hrOther
  have hvw : v = w := hrOther.symm.trans hgOther
  exact hwOut (hvw ▸ hvS)

/-- The prefix ending at the first return `Z₁` contains no other old
five-path vertex except its starting vertex `Y`. -/
theorem FivePathState.first_return_z1_prefix_support
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ1 : p.1.getVert i = s.path.1.getVert 1) :
    ∃ q : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right (s.path.1.getVert 1),
      q.1.length = i ∧
        (∀ v ∈ q.1.support,
          v ∈ s.path.1.support.toFinset →
            v = s.right ∨ v = s.path.1.getVert 1) := by
  classical
  have hZ1mem : s.path.1.getVert 1 ∈ p.1.support :=
    hiZ1 ▸ p.1.getVert_mem_support i
  let qWalk := p.1.takeUntil (s.path.1.getVert 1) hZ1mem
  let q : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right (s.path.1.getVert 1) :=
    ⟨qWalk, p.property.takeUntil hZ1mem⟩
  have hqLenLe : q.1.length ≤ p.1.length :=
    p.1.length_takeUntil_le hZ1mem
  have hqEnd : p.1.getVert q.1.length = s.path.1.getVert 1 :=
    p.1.getVert_length_takeUntil hZ1mem
  have hqLen : q.1.length = i := by
    apply p.property.getVert_injOn
      (Set.mem_Iic.mpr hqLenLe)
      (Set.mem_Iic.mpr hiLe)
    exact hqEnd.trans hiZ1.symm
  refine ⟨q, hqLen, ?_⟩
  intro v hv hvS
  obtain ⟨j, hj, hjLe⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
  have hpj : p.1.getVert j = v := by
    exact (p.1.getVert_takeUntil hZ1mem hjLe).symm.trans hj
  have hjI : j ≤ i := by omega
  by_cases hj0 : j = 0
  · left
    have hstart : p.1.getVert 0 = s.right := p.1.getVert_zero
    exact hpj.symm.trans (by simpa [hj0] using hstart)
  by_cases hjIeq : j = i
  · right
    exact hpj.symm.trans (by simpa [hjIeq] using hiZ1)
  have hjOut := hfirst j (by omega) (by omega)
  exact False.elim (hjOut (hpj ▸ hvS))

/-- The actual exterior `Y→Z₁` prefix remains a `(b,c)` path after
switching the critical `(a,b)` chain. Its vertex order and support do
not change. -/
theorem FivePathState.transfer_z1_prefix_after_ab_switch
    {F : Finset G.E} {k : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    {switched : G.E → Fin k}
    (hother : ∀ r, s.paint r ≠ a → s.paint r ≠ b →
      switched r = s.paint r)
    (hstable : ∀ v, v ∉ s.path.1.support →
      ∀ r ∈ F.erase s.omitted, G.Inc v r →
        switched r = s.paint r)
    (q : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right (s.path.1.getVert 1))
    (hsupport : ∀ v ∈ q.1.support,
      v ∈ s.path.1.support.toFinset →
        v = s.right ∨ v = s.path.1.getVert 1) :
    ∃ q' : (G.twoColorGraph (F.erase s.omitted) switched b c).Path
      s.right (s.path.1.getVert 1),
      q'.1.support = q.1.support ∧ q'.1.length = q.1.length := by
  let H' := G.twoColorGraph (F.erase s.omitted) switched b c
  have hcne := FivePathState.external_endpoint_color_ne_missing
    G s hleft hright
  have hZ1mem : s.path.1.getVert 1 ∈ s.path.1.support.toFinset := by
    simpa only [List.mem_toFinset] using s.path.1.getVert_mem_support 1
  have hno : ¬(G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj
      s.right (s.path.1.getVert 1) :=
    FivePathState.no_right_bc_adj_old_vertex G s hright hZ1mem
  have hedges : ∀ e ∈ q.1.edges, e ∈ H'.edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Adj u v :=
        q.1.edges_subset_edgeSet he
      obtain ⟨r, hrF, hrU, hrV, hrColor⟩ :=
        G.exists_twoColorWitnessEdge (F.erase s.omitted) s.paint b c huv
      have hnotBoth : ¬(u ∈ s.path.1.support.toFinset ∧
          v ∈ s.path.1.support.toFinset) := by
        intro ⟨huS, hvS⟩
        have hu : u = s.right ∨ u = s.path.1.getVert 1 :=
          hsupport u (q.1.fst_mem_support_of_mem_edges he) huS
        have hv : v = s.right ∨ v = s.path.1.getVert 1 :=
          hsupport v (q.1.snd_mem_support_of_mem_edges he) hvS
        rcases hu with hu | hu <;> rcases hv with hv | hv
        · exact huv.ne (hu.trans hv.symm)
        · exact hno (by simpa [hu, hv] using huv)
        · exact hno (by simpa [hu, hv] using huv.symm)
        · exact huv.ne (hu.trans hv.symm)
      have hrNew : switched r = b ∨ switched r = c := by
        rcases hrColor with hrB | hrC
        · by_cases huS : u ∈ s.path.1.support.toFinset
          · have hvOut : v ∉ s.path.1.support.toFinset := by
              intro hvS; exact hnotBoth ⟨huS, hvS⟩
            have hsw := hstable v (by simpa only [List.mem_toFinset] using hvOut)
              r hrF hrV
            exact Or.inl (hsw.trans hrB)
          · have hsw := hstable u (by simpa only [List.mem_toFinset] using huS)
              r hrF hrU
            exact Or.inl (hsw.trans hrB)
        · have hra : s.paint r ≠ a := by
            rw [hrC]
            exact hcne.1
          have hrb : s.paint r ≠ b := by
            rw [hrC]
            exact hcne.2
          exact Or.inr ((hother r hra hrb).trans hrC)
      exact G.twoColorGraph_adj_of_witness_inc huv.ne
        hrF hrU hrV hrNew
  let qWalk := q.1.transfer H' hedges
  let q' : H'.Path s.right (s.path.1.getVert 1) :=
    ⟨qWalk, q.property.transfer hedges⟩
  refine ⟨q', ?_, ?_⟩
  · change (q.1.transfer H' hedges).support = q.1.support
    exact q.1.support_transfer hedges
  · change (q.1.transfer H' hedges).length = q.1.length
    exact q.1.length_transfer hedges

/-- The ordered exterior prefix survives the actual critical-chain
switch, with the three old internal path-edge colors flipped. -/
theorem FivePathState.exists_switched_z1_prefix
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
    (hiZ1 : p.1.getVert i = s.path.1.getVert 1) :
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
      ∃ q : (G.twoColorGraph (F.erase s.omitted) switched b c).Path
        s.right (s.path.1.getVert 1),
        q.1.length = i ∧
          (∀ v ∈ q.1.support,
            v ∈ s.path.1.support.toFinset →
              v = s.right ∨ v = s.path.1.getVert 1) := by
  obtain ⟨q₀, hqLen, hqSupport⟩ :=
    FivePathState.first_return_z1_prefix_support
      G s p hi hiLe hfirst hiZ1
  obtain ⟨switched, hproper, hswapA, hswapB, hother, hstable⟩ :=
    FivePathState.exists_ab_path_switch_stable_outside G s hcritical
  obtain ⟨q, hsupport, hlength⟩ :=
    FivePathState.transfer_z1_prefix_after_ab_switch
      G s hleft hright hother hstable q₀ hqSupport
  refine ⟨switched, hproper, hswapA, hswapB, hother, q, ?_, ?_⟩
  · omega
  · intro v hv hvS
    exact hqSupport v (by simpa [hsupport] using hv) hvS

end WeightedEdgeColoring.WeightedMultigraph
