import WeightedEdgeColoring.SubtwoOrdinaryChainUnion
import WeightedEdgeColoring.BPOrdinaryCriticalTriangleMiddle

/-!
# The outside-vertex step for a five-vertex critical chain

This file records local path geometry used in Andersen's proof that a
sixth vertex cannot lie on a critical chain.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable local instance fiveOutsideDecidableAdj
    (H : SimpleGraph G.V) : DecidableRel H.Adj :=
  Classical.decRel _

noncomputable local instance fiveOutsideFiniteNeighborSet
    (H : SimpleGraph G.V) (v : G.V) : Fintype (H.neighborSet v) :=
  @Subtype.fintype G.V (fun w ↦ w ∈ H.neighborSet v)
    (Classical.decPred _) G.instFintypeV

theorem twoColorGraph_adj_of_witness_inc
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {a b : Fin k} {v w : G.V} (hvw : v ≠ w)
    {g : G.E} (hgF : g ∈ F) (hgv : G.Inc v g)
    (hgw : G.Inc w g) (hgcolor : color g = a ∨ color g = b) :
    (G.twoColorGraph F color a b).Adj v w := by
  have hadj := G.twoColorGraph_adj_fst_snd F color a b hgF hgcolor
  rcases hgv with hfV | hsV <;> rcases hgw with hfW | hsW
  · exact False.elim (hvw (hfV.symm.trans hfW))
  · simpa [hfV, hsW] using hadj
  · simpa [hsV, hfW] using hadj.symm
  · exact False.elim (hvw (hsV.symm.trans hsW))

noncomputable def pathEndpointsCast
    {H : SimpleGraph G.V} {x x' y y' : G.V}
    (hx : x' = x) (hy : y' = y) (p : H.Path x y) : H.Path x' y' := by
  cases hx
  cases hy
  exact p

theorem pathEndpointsCast_length
    {H : SimpleGraph G.V} {x x' y y' : G.V}
    (hx : x' = x) (hy : y' = y) (p : H.Path x y) :
    (G.pathEndpointsCast hx hy p).1.length = p.1.length := by
  cases hx
  cases hy
  rfl

theorem pathEndpointsCast_support
    {H : SimpleGraph G.V} {x x' y y' : G.V}
    (hx : x' = x) (hy : y' = y) (p : H.Path x y) :
    (G.pathEndpointsCast hx hy p).1.support = p.1.support := by
  cases hx
  cases hy
  rfl

theorem exists_first_criticalPath_edge_secondColor
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hlen : 1 ≤ p.1.length) :
    ∃ g, g ∈ F.erase e ∧
      G.Inc (G.fst e) g ∧ G.Inc (p.1.getVert 1) g ∧
      color g = b := by
  have hadj : (G.twoColorGraph (F.erase e) color a b).Adj
      (G.fst e) (p.1.getVert 1) := by
    simpa using p.1.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g, hgF, hgX, hgZ, hgcol⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) color a b hadj
  have hne := G.color_ne_of_mem_missingColorsAt
    (F.erase e) color (G.fst e) a ha hgF hgX
  exact ⟨g, hgF, hgX, hgZ, hgcol.resolve_left hne⟩

/-- The second edge of a critical endpoint chain has the color missing
at its first endpoint. -/
theorem exists_second_criticalPath_edge_firstColor
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hlen : 2 ≤ p.1.length) :
    ∃ g, g ∈ F.erase e ∧
      G.Inc (p.1.getVert 1) g ∧
      G.Inc (p.1.getVert 2) g ∧ color g = a := by
  have hadj0 : (G.twoColorGraph (F.erase e) color a b).Adj
      (p.1.getVert 0) (p.1.getVert 1) :=
    p.1.adj_getVert_succ (i := 0) (by omega)
  have hadj1 : (G.twoColorGraph (F.erase e) color a b).Adj
      (p.1.getVert 1) (p.1.getVert 2) := by
    simpa using p.1.adj_getVert_succ (i := 1) (by omega)
  obtain ⟨g0, hg0F, hg00, hg01, hg0color⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) color a b hadj0
  obtain ⟨g1, hg1F, hg11, hg12, hg1color⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) color a b hadj1
  have hg0neA : color g0 ≠ a :=
    G.color_ne_of_mem_missingColorsAt (F.erase e) color
      (G.fst e) a ha hg0F (by simpa using hg00)
  have hg0B : color g0 = b := hg0color.resolve_left hg0neA
  have hne := G.path_witness_colors_ne hproper p 0 (by omega)
    hg0F hg1F hg00 hg01 hg11 hg12
  have hg1neB : color g1 ≠ b := by
    intro h; exact hne (hg0B.trans h.symm)
  exact ⟨g1, hg1F, hg11, hg12, hg1color.resolve_right hg1neB⟩

/-- If another critical chain starts through a vertex outside a fixed
five-chain and ends through its penultimate vertex, its middle vertex
must also lie outside the fixed five-chain. -/
theorem middle_outside_fivePath_of_first_and_last_neighbors
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (q : (G.twoColorGraph (F.erase e) color a c).Path
      (G.fst e) (G.snd e)) (hqLen : q.1.length = 4)
    (hfirst : q.1.getVert 1 ∉ p.1.support)
    (hlast : q.1.getVert 3 = p.1.getVert 3) :
    q.1.getVert 2 ∉ p.1.support := by
  intro hmiddle
  have hp0 : p.1.getVert 0 = G.fst e := by simp
  have hp4 : p.1.getVert 4 = G.snd e := by
    simpa [hpLen] using p.1.getVert_length
  have hq0 : q.1.getVert 0 = G.fst e := by simp
  have hq4 : q.1.getVert 4 = G.snd e := by
    simpa [hqLen] using q.1.getVert_length
  have hqInj (i j : ℕ) (hi : i ≤ 4) (hj : j ≤ 4)
      (hij : i ≠ j) : q.1.getVert i ≠ q.1.getVert j := by
    intro heq
    exact hij (q.property.getVert_injOn
      (Set.mem_Iic.mpr (by omega))
      (Set.mem_Iic.mpr (by omega)) heq)
  have hp12 : p.1.getVert 1 ≠ p.1.getVert 2 :=
    (p.1.adj_getVert_succ (i := 1) (by omega)).ne
  obtain ⟨gp, hgpF, hgp1, hgp2, hgpa⟩ :=
    G.exists_second_criticalPath_edge_firstColor hproper ha p (by omega)
  obtain ⟨gq, hgqF, hgq1, hgq2, hgqa⟩ :=
    G.exists_second_criticalPath_edge_firstColor hproper ha q (by omega)
  have hnot12 (z : G.V)
      (hz : z = p.1.getVert 1 ∨ z = p.1.getVert 2)
      (hTz : q.1.getVert 2 = z) : False := by
    have hzP : G.Inc z gp := by
      rcases hz with rfl | rfl
      · exact hgp1
      · exact hgp2
    have hzQ : G.Inc z gq := hTz ▸ hgq2
    have hgeq : gp = gq := by
      apply hproper z
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgpF, hzP⟩)
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgqF, hzQ⟩)
      · exact hgpa.trans hgqa.symm
    have hWgp : G.Inc (q.1.getVert 1) gp := hgeq ▸ hgq1
    have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc hp12 hgp1 hgp2
    have hWone : q.1.getVert 1 = p.1.getVert 1 ∨
        q.1.getVert 1 = p.1.getVert 2 := by
      rcases hends with ⟨hf, hs⟩ | ⟨hf, hs⟩
      · rcases hWgp with h | h
        · exact Or.inl (hf.symm.trans h).symm
        · exact Or.inr (hs.symm.trans h).symm
      · rcases hWgp with h | h
        · exact Or.inr (hf.symm.trans h).symm
        · exact Or.inl (hs.symm.trans h).symm
    rcases hWone with h | h
    · exact hfirst (h ▸ p.1.getVert_mem_support 1)
    · exact hfirst (h ▸ p.1.getVert_mem_support 2)
  obtain ⟨i, hi, hiLe⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hmiddle
  have hiLe' : i ≤ 4 := by omega
  interval_cases i
  · exact (hqInj 2 0 (by omega) (by omega) (by decide))
      (by simpa [hp0, hq0] using hi.symm)
  · exact hnot12 (p.1.getVert 1) (Or.inl rfl) hi.symm
  · exact hnot12 (p.1.getVert 2) (Or.inr rfl) hi.symm
  · exact (hqInj 2 3 (by omega) (by omega) (by decide))
      (hi.symm.trans hlast.symm)
  · exact (hqInj 2 4 (by omega) (by omega) (by decide))
      (by simpa [hp4, hq4] using hi.symm)

/-- The last edge of an endpoint critical chain has the color missing at
its first endpoint. -/
theorem exists_last_criticalPath_edge_firstColor
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    {a b : Fin k}
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hlen : 1 ≤ p.1.length) :
    ∃ g, g ∈ F.erase e ∧
      G.Inc (p.1.getVert (p.1.length - 1)) g ∧
      G.Inc (G.snd e) g ∧ color g = a := by
  have hend : p.1.length - 1 + 1 = p.1.length := by omega
  have hadj : (G.twoColorGraph (F.erase e) color a b).Adj
      (p.1.getVert (p.1.length - 1)) (G.snd e) := by
    simpa [hend] using
      p.1.adj_getVert_succ (i := p.1.length - 1) (by omega)
  obtain ⟨g, hgF, hgz, hgy, hgcolor⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) color a b hadj
  have hne : color g ≠ b :=
    G.color_ne_of_mem_missingColorsAt (F.erase e) color
      (G.snd e) b hb hgF hgy
  exact ⟨g, hgF, hgz, hgy, hgcolor.resolve_right hne⟩

/-- A specified edge of the unique available color at the first
endpoint determines the first neighbor of a critical chain. -/
theorem first_criticalPath_neighbor_eq_of_colored_edge
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (q : (G.twoColorGraph (F.erase e) color a c).Path
      (G.fst e) (G.snd e)) (hlen : 1 ≤ q.1.length)
    {g : G.E} (hgF : g ∈ F.erase e)
    {w : G.V} (hxw : G.fst e ≠ w)
    (hgX : G.Inc (G.fst e) g) (hgW : G.Inc w g)
    (hgc : color g = c) : q.1.getVert 1 = w := by
  have hadj : (G.twoColorGraph (F.erase e) color a c).Adj
      (G.fst e) (q.1.getVert 1) := by
    simpa using q.1.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨r, hrF, hrX, hrZ, hrcol⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) color a c hadj
  have hrneA : color r ≠ a :=
    G.color_ne_of_mem_missingColorsAt (F.erase e) color
      (G.fst e) a ha hrF hrX
  have hrc : color r = c := hrcol.resolve_left hrneA
  have hrg : r = g := by
    apply hproper (G.fst e)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hrX⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgX⟩)
    · exact hrc.trans hgc.symm
  have hqX : G.fst e ≠ q.1.getVert 1 := hadj.ne
  have hotherQ := G.kempeOtherEndpoint_eq_of_incident
    hrX hrZ hqX
  have hotherW := G.kempeOtherEndpoint_eq_of_incident hgX hgW hxw
  rw [hrg] at hotherQ
  exact hotherQ.symm.trans hotherW

/-- If two critical chains have the same first color and both end with
that color at the second endpoint, they share their last neighbor. -/
theorem last_criticalPath_neighbors_eq
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k}
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (q : (G.twoColorGraph (F.erase e) color a c).Path
      (G.fst e) (G.snd e))
    (hpLen : 1 ≤ p.1.length) (hqLen : 1 ≤ q.1.length) :
    q.1.getVert (q.1.length - 1) =
      p.1.getVert (p.1.length - 1) := by
  obtain ⟨gp, hgpF, hgpZ, hgpY, hgpa⟩ :=
    G.exists_last_criticalPath_edge_firstColor hb p hpLen
  obtain ⟨gq, hgqF, hgqZ, hgqY, hgqa⟩ :=
    G.exists_last_criticalPath_edge_firstColor hc q hqLen
  have hgeq : gq = gp := by
    apply hproper (G.snd e)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgqF, hgqY⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgpF, hgpY⟩)
    · exact hgqa.trans hgpa.symm
  have hqNeY : G.snd e ≠ q.1.getVert (q.1.length - 1) := by
    have hend : q.1.length - 1 + 1 = q.1.length := by omega
    have hadj := q.1.adj_getVert_succ (i := q.1.length - 1) (by omega)
    simpa [hend] using hadj.ne.symm
  have hpNeY : G.snd e ≠ p.1.getVert (p.1.length - 1) := by
    have hend : p.1.length - 1 + 1 = p.1.length := by omega
    have hadj := p.1.adj_getVert_succ (i := p.1.length - 1) (by omega)
    simpa [hend] using hadj.ne.symm
  have hotherQ := G.kempeOtherEndpoint_eq_of_incident
    hgqY hgqZ hqNeY
  have hotherP := G.kempeOtherEndpoint_eq_of_incident
    hgpY hgpZ hpNeY
  rw [hgeq] at hotherQ
  exact hotherQ.symm.trans hotherP

/-- No vertex of the fan at the first endpoint can lie outside a fixed
five-vertex critical chain. Otherwise the chain through its fan edge
contributes two distinct outside vertices to a neighborhood of size ≤6. -/
theorem first_oneStepFan_subset_fivePath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {w : G.V}
    (hwfan : G.InOneStepFan F e color (G.fst e) (G.snd e) w) :
    w ∈ p.1.support := by
  by_contra hwout
  obtain ⟨hxw, hwy | ⟨g, hgF, hgX, hgW, hgc⟩⟩ := hwfan
  · exact hwout (hwy ▸ p.1.end_mem_support)
  obtain ⟨q, _⟩ := G.exists_criticalEndpointPath
    hcritical heF hproper ha hgc
  have hqLenAtLeastTwo :=
    G.criticalPath_length_at_least_two hcritical heF hproper ha hgc q
  have hfirst := G.first_criticalPath_neighbor_eq_of_colored_edge
    hproper ha q (by omega) hgF hxw.symm hgX hgW rfl
  have hlast := G.last_criticalPath_neighbors_eq
    hproper hb hgc p q (by omega) (by omega)
  have hqCard := G.criticalPath_support_card_eq_three_or_five
    hcritical heF hproper ha hgc q (by omega) hdegree hthreshold
  have hqCardLength : q.1.support.toFinset.card = q.1.length + 1 := by
    rw [List.toFinset_card_of_nodup q.property.support_nodup,
      q.1.length_support]
  have hqLength : q.1.length = 2 ∨ q.1.length = 4 := by omega
  rcases hqLength with hqTwo | hqFour
  · have hWlast : w = p.1.getVert 3 := by
      simpa [hfirst, hqTwo, hpLen] using hlast
    exact hwout (hWlast ▸ p.1.getVert_mem_support 3)
  · have hlast3 : q.1.getVert 3 = p.1.getVert 3 := by
      simpa [hqFour, hpLen] using hlast
    have hmidOut := G.middle_outside_fivePath_of_first_and_last_neighbors
      hproper ha p hpLen q hqFour
        (by simpa [hfirst] using hwout) hlast3
    have hpFive : p.1.support.toFinset.card = 5 := by
      rw [List.toFinset_card_of_nodup p.property.support_nodup,
        p.1.length_support, hpLen]
    have hwN : w ∈ G.criticalNeighborhood (F := F) e color := by
      rw [G.mem_criticalNeighborhood_iff]
      exact Or.inr (Or.inl ⟨hxw, Or.inr ⟨g, hgF, hgX, hgW, hgc⟩⟩)
    have hmidN : q.1.getVert 2 ∈
        G.criticalNeighborhood (F := F) e color := by
      rw [G.mem_criticalNeighborhood_iff]
      exact Or.inl ⟨a, color g, ha, hgc, q, q.1.getVert_mem_support 2⟩
    have hWmid := G.eq_of_mem_criticalNeighborhood_outside_fivePath
      hcritical heF hproper ha hb p hpFive hdk hdegree hthreshold
      hwN hmidN (by simpa using hwout) (by simpa using hmidOut)
    have hqInj := q.property.getVert_injOn
      (show 1 ∈ Set.Iic q.1.length by exact Set.mem_Iic.mpr (by omega))
      (show 2 ∈ Set.Iic q.1.length by exact Set.mem_Iic.mpr (by omega))
    have h12 : (1 : ℕ) = 2 := hqInj (hfirst.trans hWmid)
    omega

/-- On a four-edge critical path the third edge has the color missing
at its second endpoint. -/
theorem exists_third_criticalPath_edge_secondColor
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hlen : p.1.length = 4) :
    ∃ g, g ∈ F.erase e ∧
      G.Inc (p.1.getVert 2) g ∧
      G.Inc (p.1.getVert 3) g ∧ color g = b := by
  have hadj2 : (G.twoColorGraph (F.erase e) color a b).Adj
      (p.1.getVert 2) (p.1.getVert 3) :=
    p.1.adj_getVert_succ (i := 2) (by omega)
  have hadj3 : (G.twoColorGraph (F.erase e) color a b).Adj
      (p.1.getVert 3) (p.1.getVert 4) := by
    simpa using p.1.adj_getVert_succ (i := 3) (by omega)
  obtain ⟨g2, hg2F, hg22, hg23, hg2color⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) color a b hadj2
  obtain ⟨g3, hg3F, hg33, hg34, hg3color⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) color a b hadj3
  have hp4 : p.1.getVert 4 = G.snd e := by
    simpa [hlen] using p.1.getVert_length
  have hg3neB : color g3 ≠ b :=
    G.color_ne_of_mem_missingColorsAt (F.erase e) color
      (G.snd e) b hb hg3F (by simpa only [hp4] using hg34)
  have hg3A : color g3 = a := hg3color.resolve_right hg3neB
  have hne := G.path_witness_colors_ne hproper p 2 (by omega)
    hg2F hg3F hg22 hg23 hg33 hg34
  have hg2neA : color g2 ≠ a := by
    intro h; exact hne (h.trans hg3A.symm)
  exact ⟨g2, hg2F, hg22, hg23, hg2color.resolve_left hg2neA⟩

/-- A critical path starting with the same second color as another
shares its first internal vertex. -/
theorem first_criticalPath_neighbors_eq
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (q : (G.twoColorGraph (F.erase e) color c b).Path
      (G.fst e) (G.snd e))
    (hpLen : 1 ≤ p.1.length) (hqLen : 1 ≤ q.1.length) :
    q.1.getVert 1 = p.1.getVert 1 := by
  have hpAdj : (G.twoColorGraph (F.erase e) color a b).Adj
      (G.fst e) (p.1.getVert 1) := by
    simpa using p.1.adj_getVert_succ (i := 0) (by omega)
  have hqAdj : (G.twoColorGraph (F.erase e) color c b).Adj
      (G.fst e) (q.1.getVert 1) := by
    simpa using q.1.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨gp, hgpF, hgpX, hgpZ, hgpcol⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) color a b hpAdj
  obtain ⟨gq, hgqF, hgqX, hgqZ, hgqcol⟩ :=
    G.exists_twoColorWitnessEdge (F.erase e) color c b hqAdj
  have hgpB : color gp = b := hgpcol.resolve_left
    (G.color_ne_of_mem_missingColorsAt (F.erase e) color
      (G.fst e) a ha hgpF hgpX)
  have hgqB : color gq = b := hgqcol.resolve_left
    (G.color_ne_of_mem_missingColorsAt (F.erase e) color
      (G.fst e) c hc hgqF hgqX)
  have hgeq : gq = gp := by
    apply hproper (G.fst e)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgqF, hgqX⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgpF, hgpX⟩)
    · exact hgqB.trans hgpB.symm
  have hotherQ := G.kempeOtherEndpoint_eq_of_incident
    hgqX hgqZ hqAdj.ne
  have hotherP := G.kempeOtherEndpoint_eq_of_incident
    hgpX hgpZ hpAdj.ne
  rw [hgeq] at hotherQ
  exact hotherQ.symm.trans hotherP

/-- A specified last edge of color `c` determines the last neighbor of
a critical `(c,b)` chain. -/
theorem last_criticalPath_neighbor_eq_of_colored_edge
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {c b : Fin k}
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (q : (G.twoColorGraph (F.erase e) color c b).Path
      (G.fst e) (G.snd e)) (hlen : 1 ≤ q.1.length)
    {g : G.E} (hgF : g ∈ F.erase e)
    {w : G.V} (hyw : G.snd e ≠ w)
    (hgY : G.Inc (G.snd e) g) (hgW : G.Inc w g)
    (hgc : color g = c) :
    q.1.getVert (q.1.length - 1) = w := by
  obtain ⟨r, hrF, hrZ, hrY, hrc⟩ :=
    G.exists_last_criticalPath_edge_firstColor hb q hlen
  have hrg : r = g := by
    apply hproper (G.snd e)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hrY⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgF, hgY⟩)
    · exact hrc.trans hgc.symm
  have hend : q.1.length - 1 + 1 = q.1.length := by omega
  have hadj := q.1.adj_getVert_succ (i := q.1.length - 1) (by omega)
  have hyz : G.snd e ≠ q.1.getVert (q.1.length - 1) := by
    simpa [hend] using hadj.ne.symm
  have hotherQ := G.kempeOtherEndpoint_eq_of_incident hrY hrZ hyz
  have hotherW := G.kempeOtherEndpoint_eq_of_incident hgY hgW hyw
  rw [hrg] at hotherQ
  exact hotherQ.symm.trans hotherW

/-- The mirrored local geometry: if a second chain shares the first
neighbor but exits through an outside vertex, its middle is outside too. -/
theorem middle_outside_fivePath_of_first_and_last_neighbors_mirror
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k}
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (q : (G.twoColorGraph (F.erase e) color c b).Path
      (G.fst e) (G.snd e)) (hqLen : q.1.length = 4)
    (hfirst : q.1.getVert 1 = p.1.getVert 1)
    (hlast : q.1.getVert 3 ∉ p.1.support) :
    q.1.getVert 2 ∉ p.1.support := by
  intro hmiddle
  have hp0 : p.1.getVert 0 = G.fst e := by simp
  have hp4 : p.1.getVert 4 = G.snd e := by
    simpa [hpLen] using p.1.getVert_length
  have hq0 : q.1.getVert 0 = G.fst e := by simp
  have hq4 : q.1.getVert 4 = G.snd e := by
    simpa [hqLen] using q.1.getVert_length
  have hqInj (i j : ℕ) (hi : i ≤ 4) (hj : j ≤ 4)
      (hij : i ≠ j) : q.1.getVert i ≠ q.1.getVert j := by
    intro heq
    exact hij (q.property.getVert_injOn
      (Set.mem_Iic.mpr (by omega))
      (Set.mem_Iic.mpr (by omega)) heq)
  have hp23 : p.1.getVert 2 ≠ p.1.getVert 3 :=
    (p.1.adj_getVert_succ (i := 2) (by omega)).ne
  obtain ⟨gp, hgpF, hgp2, hgp3, hgpb⟩ :=
    G.exists_third_criticalPath_edge_secondColor hproper hb p hpLen
  obtain ⟨gq, hgqF, hgq2, hgq3, hgqb⟩ :=
    G.exists_third_criticalPath_edge_secondColor hproper hb q hqLen
  have hnot23 (z : G.V)
      (hz : z = p.1.getVert 2 ∨ z = p.1.getVert 3)
      (hTz : q.1.getVert 2 = z) : False := by
    have hzP : G.Inc z gp := by
      rcases hz with rfl | rfl
      · exact hgp2
      · exact hgp3
    have hzQ : G.Inc z gq := hTz ▸ hgq2
    have hgeq : gp = gq := by
      apply hproper z
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgpF, hzP⟩)
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgqF, hzQ⟩)
      · exact hgpb.trans hgqb.symm
    have hWgp : G.Inc (q.1.getVert 3) gp := hgeq ▸ hgq3
    have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc hp23 hgp2 hgp3
    have hWone : q.1.getVert 3 = p.1.getVert 2 ∨
        q.1.getVert 3 = p.1.getVert 3 := by
      rcases hends with ⟨hf, hs⟩ | ⟨hf, hs⟩
      · rcases hWgp with h | h
        · exact Or.inl (hf.symm.trans h).symm
        · exact Or.inr (hs.symm.trans h).symm
      · rcases hWgp with h | h
        · exact Or.inr (hf.symm.trans h).symm
        · exact Or.inl (hs.symm.trans h).symm
    rcases hWone with h | h
    · exact hlast (h ▸ p.1.getVert_mem_support 2)
    · exact hlast (h ▸ p.1.getVert_mem_support 3)
  obtain ⟨i, hi, hiLe⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hmiddle
  have hiLe' : i ≤ 4 := by omega
  interval_cases i
  · exact (hqInj 2 0 (by omega) (by omega) (by decide))
      (by simpa [hp0, hq0] using hi.symm)
  · exact (hqInj 2 1 (by omega) (by omega) (by decide))
      (hi.symm.trans hfirst.symm)
  · exact hnot23 (p.1.getVert 2) (Or.inl rfl) hi.symm
  · exact hnot23 (p.1.getVert 3) (Or.inr rfl) hi.symm
  · exact (hqInj 2 4 (by omega) (by omega) (by decide))
      (by simpa [hp4, hq4] using hi.symm)

/-- The symmetric fan at the second endpoint also lies inside every
fixed five-vertex critical chain. -/
theorem second_oneStepFan_subset_fivePath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {w : G.V}
    (hwfan : G.InOneStepFan F e color (G.snd e) (G.fst e) w) :
    w ∈ p.1.support := by
  by_contra hwout
  obtain ⟨hyw, hwx | ⟨g, hgF, hgY, hgW, hgc⟩⟩ := hwfan
  · exact hwout (hwx ▸ p.1.start_mem_support)
  obtain ⟨q, _⟩ := G.exists_criticalEndpointPath
    hcritical heF hproper hgc hb
  have hqLenAtLeastTwo :=
    G.criticalPath_length_at_least_two hcritical heF hproper hgc hb q
  have hfirst := G.first_criticalPath_neighbors_eq
    hproper ha hgc p q (by omega) (by omega)
  have hlast := G.last_criticalPath_neighbor_eq_of_colored_edge
    hproper hb q (by omega) hgF hyw.symm hgY hgW rfl
  have hqCard := G.criticalPath_support_card_eq_three_or_five
    hcritical heF hproper hgc hb q (by omega) hdegree hthreshold
  have hqCardLength : q.1.support.toFinset.card = q.1.length + 1 := by
    rw [List.toFinset_card_of_nodup q.property.support_nodup,
      q.1.length_support]
  have hqLength : q.1.length = 2 ∨ q.1.length = 4 := by omega
  rcases hqLength with hqTwo | hqFour
  · have hWfirst : w = p.1.getVert 1 := by
      simpa [hfirst, hqTwo] using hlast.symm
    exact hwout (hWfirst ▸ p.1.getVert_mem_support 1)
  · have hlast3 : q.1.getVert 3 ∉ p.1.support := by
      have hq3w : q.1.getVert 3 = w := by simpa [hqFour] using hlast
      rw [hq3w]
      exact hwout
    have hmidOut := G.middle_outside_fivePath_of_first_and_last_neighbors_mirror
      hproper hb p hpLen q hqFour hfirst hlast3
    have hpFive : p.1.support.toFinset.card = 5 := by
      rw [List.toFinset_card_of_nodup p.property.support_nodup,
        p.1.length_support, hpLen]
    have hwN : w ∈ G.criticalNeighborhood (F := F) e color := by
      rw [G.mem_criticalNeighborhood_iff]
      exact Or.inr (Or.inr ⟨hyw, Or.inr ⟨g, hgF, hgY, hgW, hgc⟩⟩)
    have hmidN : q.1.getVert 2 ∈
        G.criticalNeighborhood (F := F) e color := by
      rw [G.mem_criticalNeighborhood_iff]
      exact Or.inl ⟨color g, b, hgc, hb, q, q.1.getVert_mem_support 2⟩
    have hWmid := G.eq_of_mem_criticalNeighborhood_outside_fivePath
      hcritical heF hproper ha hb p hpFive hdk hdegree hthreshold
      hwN hmidN (by simpa using hwout) (by simpa using hmidOut)
    have hqInj := q.property.getVert_injOn
      (show 3 ∈ Set.Iic q.1.length by exact Set.mem_Iic.mpr (by omega))
      (show 2 ∈ Set.Iic q.1.length by exact Set.mem_Iic.mpr (by omega))
    have hq3w : q.1.getVert 3 = w := by simpa [hqFour] using hlast
    have h32 : (3 : ℕ) = 2 := hqInj (hq3w.trans hWmid)
    omega

theorem both_oneStepFans_subset_fivePath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {w : G.V}
    (hwfan : G.InOneStepFan F e color (G.fst e) (G.snd e) w ∨
      G.InOneStepFan F e color (G.snd e) (G.fst e) w) :
    w ∈ p.1.support := by
  rcases hwfan with hwfan | hwfan
  · exact G.first_oneStepFan_subset_fivePath
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold hwfan
  · exact G.second_oneStepFan_subset_fivePath
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold hwfan

/-- Any vertex of a different critical chain lying outside a fixed
five-chain must be the middle vertex of another five-chain. Its two
neighbors on that chain lie inside the fixed one. -/
theorem outside_criticalPath_vertex_is_middle_of_fivePath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c f : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hf : f ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (q : (G.twoColorGraph (F.erase e) color c f).Path
      (G.fst e) (G.snd e))
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {w : G.V} (hwq : w ∈ q.1.support) (hwout : w ∉ p.1.support) :
    q.1.length = 4 ∧ w = q.1.getVert 2 ∧
      q.1.getVert 1 ∈ p.1.support ∧
      q.1.getVert 3 ∈ p.1.support := by
  have hqLen := G.criticalPath_length_at_least_two
    hcritical heF hproper hc hf q
  have hqCard := G.criticalPath_support_card_eq_three_or_five
    hcritical heF hproper hc hf q (by omega) hdegree hthreshold
  have hqCardLength : q.1.support.toFinset.card = q.1.length + 1 := by
    rw [List.toFinset_card_of_nodup q.property.support_nodup,
      q.1.length_support]
  have hqCases : q.1.length = 2 ∨ q.1.length = 4 := by omega
  have hqFirstFan := G.criticalPath_first_inOneStepFan hc hf q (by omega)
  have hqFirstInP := G.first_oneStepFan_subset_fivePath
    hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold hqFirstFan
  have hqLastFan := G.criticalPath_last_inOneStepFan hc hf q (by omega)
  have hqLastInP := G.second_oneStepFan_subset_fivePath
    hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold hqLastFan
  have hqFour : q.1.length = 4 := by
    rcases hqCases with htwo | hfour
    · have hlast : q.1.getVert 1 ∈ p.1.support := by
        simpa [htwo] using hqLastInP
      obtain ⟨i, hi, hiLe⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hwq
      have hiLe' : i ≤ 2 := by omega
      interval_cases i
      · have hwX : w = G.fst e := by simpa using hi.symm
        exact False.elim (hwout (hwX ▸ p.1.start_mem_support))
      · exact False.elim (hwout (hi.symm ▸ hlast))
      · have hq2 : q.1.getVert 2 = G.snd e := by
          simpa [htwo] using q.1.getVert_length
        have hwY : w = G.snd e := hi.symm.trans hq2
        exact False.elim (hwout (hwY ▸ p.1.end_mem_support))
    · exact hfour
  have hqLastInP3 : q.1.getVert 3 ∈ p.1.support := by
    simpa [hqFour] using hqLastInP
  have hwMiddle : w = q.1.getVert 2 := by
    obtain ⟨i, hi, hiLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hwq
    have hiLe' : i ≤ 4 := by omega
    interval_cases i
    · have hwX : w = G.fst e := by simpa using hi.symm
      exact False.elim (hwout (hwX ▸ p.1.start_mem_support))
    · exact False.elim (hwout (hi.symm ▸ hqFirstInP))
    · exact hi.symm
    · exact False.elim (hwout (hi.symm ▸ hqLastInP3))
    · have hq4 : q.1.getVert 4 = G.snd e := by
        simpa [hqFour] using q.1.getVert_length
      have hwY : w = G.snd e := hi.symm.trans hq4
      exact False.elim (hwout (hwY ▸ p.1.end_mem_support))
  exact ⟨hqFour, hwMiddle, hqFirstInP, hqLastInP3⟩

/-- The outside vertex is joined into the five-chain on both sides: one
edge has a color missing at the first endpoint and the other has a color
missing at the second endpoint. -/
theorem outside_criticalPath_vertex_has_two_internal_neighbors
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c f : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hf : f ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (q : (G.twoColorGraph (F.erase e) color c f).Path
      (G.fst e) (G.snd e))
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {w : G.V} (hwq : w ∈ q.1.support) (hwout : w ∉ p.1.support) :
    ∃ z₁ z₃ : G.V, z₁ ∈ p.1.support ∧ z₃ ∈ p.1.support ∧ z₁ ≠ z₃ ∧
      ∃ g₁ g₃ : G.E,
        g₁ ∈ F.erase e ∧ g₃ ∈ F.erase e ∧
        G.Inc z₁ g₁ ∧ G.Inc w g₁ ∧ color g₁ = c ∧
        G.Inc w g₃ ∧ G.Inc z₃ g₃ ∧ color g₃ = f := by
  obtain ⟨hqFour, hwMiddle, hz₁, hz₃⟩ :=
    G.outside_criticalPath_vertex_is_middle_of_fivePath
      hcritical heF hproper ha hb hc hf p hpLen q hdk hdegree hthreshold
      hwq hwout
  obtain ⟨g₁, hg₁F, hg₁1, hg₁2, hg₁c⟩ :=
    G.exists_second_criticalPath_edge_firstColor hproper hc q (by omega)
  obtain ⟨g₃, hg₃F, hg₃2, hg₃3, hg₃f⟩ :=
    G.exists_third_criticalPath_edge_secondColor hproper hf q hqFour
  have h13 : q.1.getVert 1 ≠ q.1.getVert 3 := by
    intro h
    have hidx := q.property.getVert_injOn
      (show 1 ∈ Set.Iic q.1.length by exact Set.mem_Iic.mpr (by omega))
      (show 3 ∈ Set.Iic q.1.length by exact Set.mem_Iic.mpr (by omega)) h
    omega
  exact ⟨q.1.getVert 1, q.1.getVert 3, hz₁, hz₃, h13,
    g₁, g₃, hg₁F, hg₃F, hg₁1, hwMiddle ▸ hg₁2, hg₁c,
    hwMiddle ▸ hg₃2, hg₃3, hg₃f⟩

/-- The outside vertex cannot be reached directly from either endpoint
using a color missing at the opposite endpoint. -/
theorem outside_fivePath_no_endpoint_fanEdge
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {w : G.V} (hwout : w ∉ p.1.support) :
    (¬∃ g ∈ F.erase e, G.Inc (G.fst e) g ∧ G.Inc w g ∧
      color g ∈ G.missingColorsAt (F.erase e) color (G.snd e)) ∧
    (¬∃ g ∈ F.erase e, G.Inc (G.snd e) g ∧ G.Inc w g ∧
      color g ∈ G.missingColorsAt (F.erase e) color (G.fst e)) := by
  have hwX : w ≠ G.fst e := by
    intro h; exact hwout (h ▸ p.1.start_mem_support)
  have hwY : w ≠ G.snd e := by
    intro h; exact hwout (h ▸ p.1.end_mem_support)
  constructor
  · rintro ⟨g, hgF, hgX, hgW, hgc⟩
    exact hwout (G.first_oneStepFan_subset_fivePath
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
      ⟨hwX, Or.inr ⟨g, hgF, hgX, hgW, hgc⟩⟩)
  · rintro ⟨g, hgF, hgY, hgW, hgc⟩
    exact hwout (G.second_oneStepFan_subset_fivePath
      hcritical heF hproper ha hb p hpLen hdk hdegree hthreshold
      ⟨hwY, Or.inr ⟨g, hgF, hgY, hgW, hgc⟩⟩)

/-- Shift the omitted edge from `X–Y` to the last `a`-colored edge of a
critical path. The new coloring of the edge set with that last edge
deleted remains proper. -/
theorem exists_proper_shift_to_last_criticalPath_edge
    {F : Finset G.E} {k : ℕ} {e : G.E} (heF : e ∈ F)
    {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    (hlen : 1 ≤ p.1.length) :
    ∃ g, g ∈ F.erase e ∧
      G.Inc (p.1.getVert (p.1.length - 1)) g ∧
      G.Inc (G.snd e) g ∧ color g = a ∧
      G.IsProperOn (F.erase g) (G.assignEdgeColor color e a) := by
  obtain ⟨g, hgF, hgZ, hgY, hga⟩ :=
    G.exists_last_criticalPath_edge_firstColor hb p hlen
  have hshift := G.isProperOn_shiftOmittedEdge_at
    heF hgF hproper hga
    (G.noLoop e).symm (Or.inr rfl) (Or.inl rfl) hgY ha
  exact ⟨g, hgF, hgZ, hgY, hga, hshift⟩

/-- The shifted omitted edge has the expected missing colors at its two
ends, in the orientation `Z₃,Y`. -/
theorem exists_proper_shift_to_last_edge_with_endpoint_palettes
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4) :
    ∃ g, g ∈ F.erase e ∧
      G.Inc (p.1.getVert 3) g ∧ G.Inc (G.snd e) g ∧
      color g = a ∧
      G.IsProperOn (F.erase g) (G.assignEdgeColor color e a) ∧
      a ∈ G.missingColorsAt (F.erase g)
        (G.assignEdgeColor color e a) (p.1.getVert 3) ∧
      b ∈ G.missingColorsAt (F.erase g)
        (G.assignEdgeColor color e a) (G.snd e) := by
  obtain ⟨g, hgF, hgZ, hgY, hga, hproper'⟩ :=
    G.exists_proper_shift_to_last_criticalPath_edge
      heF hproper ha hb p (by omega)
  have hgZ3 : G.Inc (p.1.getVert 3) g := by simpa [hpLen] using hgZ
  have hzinternal := G.criticalPath_last_internal p (by omega)
  have hzX : p.1.getVert 3 ≠ G.fst e := by
    simpa [hpLen] using hzinternal.2.1
  have hzY : p.1.getVert 3 ≠ G.snd e := by
    simpa [hpLen] using hzinternal.2.2
  have hzNotInc : ¬G.Inc (p.1.getVert 3) e := by
    rintro (h | h)
    · exact hzX h.symm
    · exact hzY h.symm
  have hge : g ≠ e := (Finset.mem_erase.mp hgF).1
  have heFg : e ∈ F.erase g := Finset.mem_erase.mpr ⟨hge.symm, heF⟩
  have haErase : a ∈ G.missingColorsAt ((F.erase g).erase e) color
      (p.1.getVert 3) := by
    have h := G.mem_missingColorsAt_erase_of_edgeColor
      hproper hgF hgZ
    have herase : (F.erase g).erase e = (F.erase e).erase g := by
      ext r; simp [and_left_comm]
    rw [herase]
    simpa [hga, hpLen] using h
  have haNew := G.mem_missingColorsAt_assignEdgeColor_of_not_inc
    heFg hzNotInc haErase
  have hab := G.critical_endpoint_missingColors_ne
    hcritical heF hproper ha hb
  have hbNew := G.mem_missingColorsAt_shiftOmitted_of_ne
    hab.symm hb (g := g)
  exact ⟨g, hgF, hgZ3, hgY, hga, hproper', haNew, hbNew⟩

/-- If an outside vertex meets the penultimate path vertex in a color
missing at `Y`, shifting the last path edge makes it a one-step fan vertex
for the new omitted edge. -/
theorem exists_shift_making_outside_vertex_fan
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    {w : G.V} (hwout : w ∉ p.1.support)
    {r : G.E} (hrF : r ∈ F.erase e)
    (hrZ : G.Inc (p.1.getVert 3) r) (hrW : G.Inc w r)
    (hrc : color r = c) :
    ∃ g, g ∈ F.erase e ∧
      G.Inc (p.1.getVert 3) g ∧ G.Inc (G.snd e) g ∧
      color g = a ∧
      G.IsProperOn (F.erase g) (G.assignEdgeColor color e a) ∧
      a ∈ G.missingColorsAt (F.erase g)
        (G.assignEdgeColor color e a) (p.1.getVert 3) ∧
      b ∈ G.missingColorsAt (F.erase g)
        (G.assignEdgeColor color e a) (G.snd e) ∧
      G.InOneStepFan F g (G.assignEdgeColor color e a)
        (p.1.getVert 3) (G.snd e) w := by
  obtain ⟨g, hgF, hgZ, hgY, hga, hproper', haNew, hbNew⟩ :=
    G.exists_proper_shift_to_last_edge_with_endpoint_palettes
      hcritical heF hproper ha hb p hpLen
  have hac : a ≠ c := by
    intro h
    have hgne := G.color_ne_of_mem_missingColorsAt
      (F.erase e) color (G.snd e) c hc hgF hgY
    exact hgne (hga.trans h)
  have hrg : r ≠ g := by
    intro h
    subst r
    exact hac (hga.symm.trans hrc)
  have hre : r ≠ e := (Finset.mem_erase.mp hrF).1
  have hrFg : r ∈ F.erase g :=
    Finset.mem_erase.mpr ⟨hrg, (Finset.mem_erase.mp hrF).2⟩
  have hrc' : G.assignEdgeColor color e a r = c := by
    simpa [G.assignEdgeColor_of_ne color hre a] using hrc
  have hcNew := G.mem_missingColorsAt_shiftOmitted_of_ne
    hac.symm hc (g := g)
  have hwZ : w ≠ p.1.getVert 3 := by
    intro h; exact hwout (h ▸ p.1.getVert_mem_support 3)
  exact ⟨g, hgF, hgZ, hgY, hga, hproper', haNew, hbNew,
    ⟨hwZ, Or.inr ⟨r, hrFg, hrZ, hrW, hrc' ▸ hcNew⟩⟩⟩

/-- The second edge of a simple four-edge path cannot be its last edge. -/
theorem criticalPath_second_edge_ne_last_edge
    {F : Finset G.E} {k : ℕ} {e : G.E} {color : G.E → Fin k}
    {a b : Fin k}
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    {r g : G.E}
    (hr1 : G.Inc (p.1.getVert 1) r)
    (hr2 : G.Inc (p.1.getVert 2) r)
    (hg3 : G.Inc (p.1.getVert 3) g) : r ≠ g := by
  intro hrg
  subst r
  have h12 : p.1.getVert 1 ≠ p.1.getVert 2 :=
    (p.1.adj_getVert_succ (i := 1) (by omega)).ne
  have h13 : p.1.getVert 1 ≠ p.1.getVert 3 := by
    intro h
    have hidx := p.property.getVert_injOn
      (show 1 ∈ Set.Iic p.1.length by exact Set.mem_Iic.mpr (by omega))
      (show 3 ∈ Set.Iic p.1.length by exact Set.mem_Iic.mpr (by omega)) h
    omega
  have h23 : p.1.getVert 2 ≠ p.1.getVert 3 :=
    (p.1.adj_getVert_succ (i := 2) (by omega)).ne
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc h12 hr1 hr2
  rcases hends with ⟨hf, hs⟩ | ⟨hf, hs⟩
  · rcases hg3 with h | h
    · exact h13 (hf.symm.trans h)
    · exact h23 (hs.symm.trans h)
  · rcases hg3 with h | h
    · exact h23 (hf.symm.trans h)
    · exact h13 (hs.symm.trans h)

/-- The last-edge shift produces the four adjacencies of the reversed
five-vertex critical chain `Z₃–Z₂–Z₁–X–Y`. -/
theorem shifted_last_edge_fivePath_adjacencies
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    {g : G.E} (hgF : g ∈ F.erase e)
    (hgZ : G.Inc (p.1.getVert 3) g)
    (hga : color g = a) :
    let H := G.twoColorGraph (F.erase g) (G.assignEdgeColor color e a) a b
    H.Adj (p.1.getVert 3) (p.1.getVert 2) ∧
      H.Adj (p.1.getVert 2) (p.1.getVert 1) ∧
      H.Adj (p.1.getVert 1) (G.fst e) ∧
      H.Adj (G.fst e) (G.snd e) := by
  dsimp only
  have hab := G.critical_endpoint_missingColors_ne
    hcritical heF hproper ha hb
  obtain ⟨g₀, hg₀F, hg₀X, hg₀1, hg₀b⟩ :=
    G.exists_first_criticalPath_edge_secondColor ha p (by omega)
  obtain ⟨g₁, hg₁F, hg₁1, hg₁2, hg₁a⟩ :=
    G.exists_second_criticalPath_edge_firstColor hproper ha p (by omega)
  obtain ⟨g₂, hg₂F, hg₂2, hg₂3, hg₂b⟩ :=
    G.exists_third_criticalPath_edge_secondColor hproper hb p hpLen
  have hg₀g : g₀ ≠ g := by
    intro h; subst g₀; exact hab (hga.symm.trans hg₀b)
  have hg₁g : g₁ ≠ g :=
    G.criticalPath_second_edge_ne_last_edge p hpLen hg₁1 hg₁2 hgZ
  have hg₂g : g₂ ≠ g := by
    intro h; subst g₂; exact hab (hga.symm.trans hg₂b)
  have hnewmem (r : G.E) (hrF : r ∈ F.erase e) (hrg : r ≠ g) :
      r ∈ F.erase g :=
    Finset.mem_erase.mpr ⟨hrg, (Finset.mem_erase.mp hrF).2⟩
  have hnewcolor (r : G.E) (hrF : r ∈ F.erase e) :
      G.assignEdgeColor color e a r = color r :=
    G.assignEdgeColor_of_ne color (Finset.mem_erase.mp hrF).1 a
  have h32 : p.1.getVert 3 ≠ p.1.getVert 2 :=
    (p.1.adj_getVert_succ (i := 2) (by omega)).ne.symm
  have h21 : p.1.getVert 2 ≠ p.1.getVert 1 :=
    (p.1.adj_getVert_succ (i := 1) (by omega)).ne.symm
  have h10 : p.1.getVert 1 ≠ G.fst e := by
    have h := p.1.adj_getVert_succ (i := 0) (by omega)
    simpa using h.ne.symm
  have heFg : e ∈ F.erase g :=
    Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hgF).1.symm, heF⟩
  constructor
  · apply G.twoColorGraph_adj_of_witness_inc h32
      (hnewmem g₂ hg₂F hg₂g) hg₂3 hg₂2
    rw [hnewcolor g₂ hg₂F, hg₂b]
    exact Or.inr rfl
  constructor
  · apply G.twoColorGraph_adj_of_witness_inc h21
      (hnewmem g₁ hg₁F hg₁g) hg₁2 hg₁1
    rw [hnewcolor g₁ hg₁F, hg₁a]
    exact Or.inl rfl
  constructor
  · apply G.twoColorGraph_adj_of_witness_inc h10
      (hnewmem g₀ hg₀F hg₀g) hg₀1 hg₀X
    rw [hnewcolor g₀ hg₀F, hg₀b]
    exact Or.inr rfl
  · apply G.twoColorGraph_adj_of_witness_inc (G.noLoop e)
      heFg (Or.inl rfl) (Or.inr rfl)
    simp [assignEdgeColor]

/-- The shifted two-color graph contains the explicit five-vertex path
`Z₃–Z₂–Z₁–X–Y` and no new vertex is needed for that path. -/
theorem exists_shifted_last_edge_fivePath
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    {g : G.E} (hgF : g ∈ F.erase e)
    (hgZ : G.Inc (p.1.getVert 3) g)
    (hga : color g = a) :
    ∃ q : (G.twoColorGraph (F.erase g)
      (G.assignEdgeColor color e a) a b).Path
        (p.1.getVert 3) (G.snd e),
      q.1.length = 4 ∧ q.1.support.toFinset = p.1.support.toFinset := by
  let H := G.twoColorGraph (F.erase g) (G.assignEdgeColor color e a) a b
  obtain ⟨h32, h21, h10, h0Y⟩ :=
    G.shifted_last_edge_fivePath_adjacencies
      hcritical heF hproper ha hb p hpLen hgF hgZ hga
  let qWalk : H.Walk (p.1.getVert 3) (G.snd e) :=
    .cons h32 (.cons h21 (.cons h10 (.cons h0Y .nil)))
  have hpNe (i j : ℕ) (hi : i ≤ 4) (hj : j ≤ 4) (hij : i ≠ j) :
      p.1.getVert i ≠ p.1.getVert j := by
    intro h
    exact hij (p.property.getVert_injOn
      (Set.mem_Iic.mpr (by omega))
      (Set.mem_Iic.mpr (by omega)) h)
  have hp0 : p.1.getVert 0 = G.fst e := by simp
  have hp4 : p.1.getVert 4 = G.snd e := by
    simpa [hpLen] using p.1.getVert_length
  have hqPath : qWalk.IsPath := by
    simp only [qWalk, SimpleGraph.Walk.cons_isPath_iff,
      SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      SimpleGraph.Walk.IsPath.nil]
    have h1X : p.1.getVert 1 ≠ G.fst e := by
      simpa [hp0] using hpNe 1 0 (by omega) (by omega) (by decide)
    have h1Y : p.1.getVert 1 ≠ G.snd e := by
      simpa [hp4] using hpNe 1 4 (by omega) (by omega) (by decide)
    have h2X : p.1.getVert 2 ≠ G.fst e := by
      simpa [hp0] using hpNe 2 0 (by omega) (by omega) (by decide)
    have h2Y : p.1.getVert 2 ≠ G.snd e := by
      simpa [hp4] using hpNe 2 4 (by omega) (by omega) (by decide)
    have h3X : p.1.getVert 3 ≠ G.fst e := by
      simpa [hp0] using hpNe 3 0 (by omega) (by omega) (by decide)
    have h3Y : p.1.getVert 3 ≠ G.snd e := by
      simpa [hp4] using hpNe 3 4 (by omega) (by omega) (by decide)
    simp [G.noLoop e, h1X, h1Y, h2X, h2Y, h3X, h3Y,
      hpNe 3 2 (by omega) (by omega) (by decide),
      hpNe 3 1 (by omega) (by omega) (by decide),
      hpNe 2 1 (by omega) (by omega) (by decide)]
  let q : H.Path (p.1.getVert 3) (G.snd e) := ⟨qWalk, hqPath⟩
  have hqLen : q.1.length = 4 := by simp [q, qWalk]
  have hqSupport : q.1.support.toFinset =
      ({p.1.getVert 3, p.1.getVert 2,
        p.1.getVert 1, G.fst e, G.snd e} : Finset G.V) := by
    simp [q, qWalk]
  have hpSubset : p.1.support.toFinset ⊆ q.1.support.toFinset := by
    intro v hv
    obtain ⟨i, hi, hiLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
        (by simpa using hv : v ∈ p.1.support)
    have hiLe' : i ≤ 4 := by omega
    rw [hqSupport]
    interval_cases i <;> simp [hp0, hp4] at hi ⊢
    all_goals (subst v; simp)
  have hpCard : p.1.support.toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup p.property.support_nodup,
      p.1.length_support, hpLen]
  have hqCard : q.1.support.toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup q.property.support_nodup,
      q.1.length_support, hqLen]
  have hsupport := Finset.eq_of_subset_of_card_le hpSubset (by omega)
  exact ⟨q, hqLen, hsupport.symm⟩

/-- Andersen's first remaining recoloring branch: an outside vertex
cannot meet `Z₃` in a color missing at `Y`. After shifting the last edge,
that vertex would lie in a one-step fan outside the shifted five-chain. -/
theorem no_outside_last_neighbor_of_missing_second_color
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {w : G.V} (hwout : w ∉ p.1.support)
    {r : G.E} (hrF : r ∈ F.erase e)
    (hrZ : G.Inc (p.1.getVert 3) r) (hrW : G.Inc w r)
    (hrc : color r = c) : False := by
  obtain ⟨g, hgF, hgZ, hgY, hga, hproper', haNew, hbNew, hfan⟩ :=
    G.exists_shift_making_outside_vertex_fan
      hcritical heF hproper ha hb hc p hpLen hwout hrF hrZ hrW hrc
  obtain ⟨q, hqLen, hqSupport⟩ :=
    G.exists_shifted_last_edge_fivePath
      hcritical heF hproper ha hb p hpLen hgF hgZ hga
  have hZY : p.1.getVert 3 ≠ G.snd e := by
    have h := G.criticalPath_last_internal p (by omega)
    simpa [hpLen] using h.2.2
  have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc hZY hgZ hgY
  rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · let q' := G.pathEndpointsCast hfst hsnd q
    have hfan' : G.InOneStepFan F g (G.assignEdgeColor color e a)
        (G.fst g) (G.snd g) w := by
      simpa [hfst, hsnd] using hfan
    have hqLen' : q'.1.length = 4 := by
      rw [G.pathEndpointsCast_length]
      exact hqLen
    have hwq := G.first_oneStepFan_subset_fivePath
      hcritical (Finset.mem_erase.mp hgF).2 hproper'
      (by simpa [hfst] using haNew)
      (by simpa [hsnd] using hbNew)
      q' hqLen' hdk hdegree hthreshold hfan'
    have hwP : w ∈ p.1.support.toFinset := by
      rw [← hqSupport]
      rw [← G.pathEndpointsCast_support hfst hsnd q]
      simpa using hwq
    exact hwout (by simpa using hwP)

  · let shifted := G.assignEdgeColor color e a
    have hswap := G.twoColorGraph_swap shifted b a (F := F.erase g)
    let qr := G.pathCast hswap q.reverse
    let qrev := G.pathEndpointsCast hfst hsnd qr
    have hqrevLen : qrev.1.length = 4 := by
      rw [G.pathEndpointsCast_length, G.pathCast_length]
      simpa using hqLen
    have hqrevSupport : qrev.1.support.toFinset = p.1.support.toFinset := by
      rw [G.pathEndpointsCast_support, G.pathCast_support]
      simpa using hqSupport
    have hfan' : G.InOneStepFan F g shifted
        (G.snd g) (G.fst g) w := by
      simpa [shifted, hfst, hsnd] using hfan
    have hwq := G.second_oneStepFan_subset_fivePath
      hcritical (Finset.mem_erase.mp hgF).2 hproper'
      (by simpa [shifted, hfst] using hbNew)
      (by simpa [shifted, hsnd] using haNew)
      qrev hqrevLen hdk hdegree hthreshold hfan'
    have hwP : w ∈ p.1.support.toFinset := by
      rw [← hqrevSupport]
      simpa using hwq
    exact hwout (by simpa using hwP)


/-- Andersen's other local branch begins by excluding the outside vertex
from the critical `(c,b)` path when `c` is missing at `X`. -/
theorem outside_last_neighbor_not_on_cross_criticalPath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {w : G.V} (hwout : w ∉ p.1.support)
    {r : G.E} (hrF : r ∈ F.erase e)
    (hrZ : G.Inc (p.1.getVert 3) r) (hrW : G.Inc w r)
    (hrc : color r = c)
    (q : (G.twoColorGraph (F.erase e) color c b).Path
      (G.fst e) (G.snd e)) :
    w ∉ q.1.support := by
  intro hwq
  obtain ⟨hqFour, hwMiddle, _, _⟩ :=
    G.outside_criticalPath_vertex_is_middle_of_fivePath
      hcritical heF hproper ha hb hc hb p hpLen q hdk hdegree hthreshold
      hwq hwout
  have hfirst := G.first_criticalPath_neighbors_eq
    hproper ha hc p q (by omega) (by omega)
  obtain ⟨gq, hgqF, hgq1, hgq2, hgqc⟩ :=
    G.exists_second_criticalPath_edge_firstColor hproper hc q (by omega)
  have hgqW : G.Inc w gq := hwMiddle ▸ hgq2
  have hrg : r = gq := by
    apply hproper w
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hrW⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgqF, hgqW⟩)
    · exact hrc.trans hgqc.symm
  have hwq1 : w ≠ q.1.getVert 1 := by
    intro h
    have hidx := q.property.getVert_injOn
      (show 2 ∈ Set.Iic q.1.length by exact Set.mem_Iic.mpr (by omega))
      (show 1 ∈ Set.Iic q.1.length by exact Set.mem_Iic.mpr (by omega))
      (hwMiddle.symm.trans h)
    omega
  have hwZ3 : w ≠ p.1.getVert 3 := by
    intro h; exact hwout (h ▸ p.1.getVert_mem_support 3)
  have hotherQ := G.kempeOtherEndpoint_eq_of_incident
    hgqW hgq1 hwq1
  have hotherZ := G.kempeOtherEndpoint_eq_of_incident
    hrW hrZ hwZ3
  rw [← hrg] at hotherQ
  have hq1Z3 : q.1.getVert 1 = p.1.getVert 3 :=
    hotherQ.symm.trans hotherZ
  have hp13 : p.1.getVert 1 ≠ p.1.getVert 3 := by
    intro h
    have hidx := p.property.getVert_injOn
      (show 1 ∈ Set.Iic p.1.length by exact Set.mem_Iic.mpr (by omega))
      (show 3 ∈ Set.Iic p.1.length by exact Set.mem_Iic.mpr (by omega)) h
    omega
  exact hp13 (hfirst.symm.trans hq1Z3)

/-- A path between the two degree-one vertices of a graph of maximum
degree two is closed under graph adjacency. -/
theorem path_support_adj_closed_of_degree_le_two
    (H : SimpleGraph G.V) {x y : G.V} (p : H.Path x y)
    (hlen : 0 < p.1.length)
    (hmax : ∀ z, H.degree z ≤ 2)
    (hx : H.degree x ≤ 1) (hy : H.degree y ≤ 1)
    {z w : G.V} (hz : z ∈ p.1.support) (hzw : H.Adj z w) :
    w ∈ p.1.support := by
  classical
  obtain ⟨i, hi, hiLe⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  have hwN : w ∈ H.neighborFinset z :=
    (H.mem_neighborFinset z w).mpr hzw
  by_cases hi0 : i = 0
  · subst i
    have hzX : z = x := by simpa using hi.symm
    have hfirstAdj : H.Adj x (p.1.getVert 1) := by
      simpa using p.1.adj_getVert_succ (i := 0) hlen
    have hfirstN : p.1.getVert 1 ∈ H.neighborFinset x :=
      (H.mem_neighborFinset x _).mpr hfirstAdj
    have hcard : (H.neighborFinset x).card ≤ 1 := by
      rw [H.card_neighborFinset_eq_degree]
      exact hx
    have hwEq : w = p.1.getVert 1 :=
      (Finset.card_le_one.mp hcard) w (by simpa [hzX] using hwN)
        _ hfirstN
    exact hwEq ▸ p.1.getVert_mem_support 1
  by_cases hiEnd : i = p.1.length
  · have hzY : z = y := by
      simpa [hiEnd] using hi.symm
    have hprevAdj : H.Adj y (p.1.getVert (p.1.length - 1)) := by
      have hend : p.1.length - 1 + 1 = p.1.length := by omega
      simpa [hend] using
        (p.1.adj_getVert_succ (i := p.1.length - 1) (by omega)).symm
    have hprevN : p.1.getVert (p.1.length - 1) ∈ H.neighborFinset y :=
      (H.mem_neighborFinset y _).mpr hprevAdj
    have hcard : (H.neighborFinset y).card ≤ 1 := by
      rw [H.card_neighborFinset_eq_degree]
      exact hy
    have hwEq : w = p.1.getVert (p.1.length - 1) :=
      (Finset.card_le_one.mp hcard) w (by simpa [hzY] using hwN)
        _ hprevN
    exact hwEq ▸ p.1.getVert_mem_support _
  have hipos : 0 < i := by omega
  have hiLt : i < p.1.length := by omega
  have hprevAdj : H.Adj z (p.1.getVert (i - 1)) := by
    have hidx : i - 1 + 1 = i := by omega
    simpa [hi, hidx] using
      (p.1.adj_getVert_succ (i := i - 1) (by omega)).symm
  have hnextAdj : H.Adj z (p.1.getVert (i + 1)) := by
    simpa [hi] using p.1.adj_getVert_succ (i := i) hiLt
  have hprevNext : p.1.getVert (i - 1) ≠ p.1.getVert (i + 1) := by
    intro h
    have hidx := p.property.getVert_injOn
      (show i - 1 ∈ Set.Iic p.1.length by
        exact Set.mem_Iic.mpr (by omega))
      (show i + 1 ∈ Set.Iic p.1.length by
        exact Set.mem_Iic.mpr (by omega)) h
    omega
  have hpairCard : ({p.1.getVert (i - 1), p.1.getVert (i + 1)} :
      Finset G.V).card = 2 := by simp [hprevNext]
  have hsubset : ({p.1.getVert (i - 1), p.1.getVert (i + 1)} :
      Finset G.V) ⊆ H.neighborFinset z := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact (H.mem_neighborFinset z _).mpr hprevAdj
    · exact (H.mem_neighborFinset z _).mpr hnextAdj
  have hNcard : (H.neighborFinset z).card ≤ 2 := by
    rw [H.card_neighborFinset_eq_degree]
    exact hmax z
  have hEq : ({p.1.getVert (i - 1), p.1.getVert (i + 1)} :
      Finset G.V) = H.neighborFinset z :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)
  have hwPair : w = p.1.getVert (i - 1) ∨
      w = p.1.getVert (i + 1) := by
    rw [← hEq] at hwN
    simpa using hwN
  rcases hwPair with hw | hw
  · exact hw ▸ p.1.getVert_mem_support _
  · exact hw ▸ p.1.getVert_mem_support _

theorem path_support_of_reachable_of_degree_le_two
    (H : SimpleGraph G.V) {x y w : G.V} (p : H.Path x y)
    (hlen : 0 < p.1.length)
    (hmax : ∀ z, H.degree z ≤ 2)
    (hx : H.degree x ≤ 1) (hy : H.degree y ≤ 1)
    (hreach : H.Reachable x w) : w ∈ p.1.support := by
  obtain ⟨r⟩ := hreach
  let P : G.V → Prop := fun v ↦ v ∈ p.1.support
  have hwalk : ∀ {u v : G.V}, (s : H.Walk u v) → P v → P u := by
    intro u v s
    induction s with
    | nil => intro h; exact h
    | cons hadj tail ih =>
      intro hv
      exact G.path_support_adj_closed_of_degree_le_two
        H p hlen hmax hx hy (ih hv) hadj.symm
  exact hwalk r.reverse p.1.start_mem_support

/-- Every vertex in the endpoint two-color component lies on its
critical path. In particular a vertex outside that path has a different
Kempe component from both endpoints. -/
theorem mem_criticalPath_support_of_same_twoColorComponent
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e))
    {w : G.V}
    (hcomp : (G.twoColorGraph (F.erase e) color a b).connectedComponentMk w =
      (G.twoColorGraph (F.erase e) color a b).connectedComponentMk
        (G.fst e)) : w ∈ p.1.support := by
  let H := G.twoColorGraph (F.erase e) color a b
  have hlen : 0 < p.1.length := by
    by_contra h
    have hz : p.1.length = 0 := by omega
    exact G.noLoop e (SimpleGraph.Walk.eq_of_length_eq_zero hz)
  have hmax : ∀ z, H.degree z ≤ 2 := by
    intro z
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase e) color hproper a b z
  have hactive := G.critical_endpoints_twoColorActive
    hcritical heF hproper ha hb
  have hx : H.degree (G.fst e) ≤ 1 := by
    rw [G.twoColorGraph_degree_eq_one_of_active
      (F.erase e) color hproper a b (G.fst e) hactive.1]
  have hy : H.degree (G.snd e) ≤ 1 := by
    rw [G.twoColorGraph_degree_eq_one_of_active
      (F.erase e) color hproper a b (G.snd e) hactive.2]
  have hreach : H.Reachable (G.fst e) w :=
    SimpleGraph.ConnectedComponent.exact hcomp.symm
  exact G.path_support_of_reachable_of_degree_le_two
    H p hlen hmax hx hy hreach

/-- Switch the `(c,b)` component of the outside vertex. The two
endpoint missing palettes are unchanged, and the edge joining `W` to
`Z₃` changes from `c` to `b`. -/
theorem exists_crossKempeSwitch_preserving_endpoint_palettes
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {w : G.V} (hwout : w ∉ p.1.support)
    {r : G.E} (hrF : r ∈ F.erase e)
    (hrZ : G.Inc (p.1.getVert 3) r) (hrW : G.Inc w r)
    (hrc : color r = c) :
    ∃ switched : G.E → Fin k,
      G.IsProperOn (F.erase e) switched ∧
      a ∈ G.missingColorsAt (F.erase e) switched (G.fst e) ∧
      b ∈ G.missingColorsAt (F.erase e) switched (G.snd e) ∧
      switched r = b ∧
      (∀ g ∈ F.erase e, G.Inc (G.fst e) g → switched g = color g) ∧
      (∀ g, color g ≠ c → color g ≠ b → switched g = color g) := by
  classical
  obtain ⟨q, _⟩ := G.exists_criticalEndpointPath
    hcritical heF hproper hc hb
  have hwNot := G.outside_last_neighbor_not_on_cross_criticalPath
    hcritical heF hproper ha hb hc p hpLen hdk hdegree hthreshold
    hwout hrF hrZ hrW hrc q
  let H := G.twoColorGraph (F.erase e) color c b
  let flip : G.TwoColorComponent (F.erase e) color c b → Prop :=
    fun C ↦ C = H.connectedComponentMk w
  letI : DecidablePred flip := Classical.decPred _
  let switched := G.kempeComponentSwitch (F.erase e) color c b flip
  have hproper' : G.IsProperOn (F.erase e) switched :=
    G.isProperOn_kempeComponentSwitch (F.erase e) color hproper c b flip
  have hWnotX : H.connectedComponentMk w ≠ H.connectedComponentMk (G.fst e) := by
    intro h
    exact hwNot (G.mem_criticalPath_support_of_same_twoColorComponent
      hcritical heF hproper hc hb q h)
  have hXnotFlip : ¬flip (H.connectedComponentMk (G.fst e)) := by
    intro h
    exact hWnotX h.symm
  have hXYcomp := G.critical_endpoints_same_twoColorComponent
    hcritical heF hproper hc hb
  have hYnotFlip : ¬flip (H.connectedComponentMk (G.snd e)) := by
    intro h
    exact hWnotX (h.symm.trans hXYcomp.symm)
  have haNew : a ∈ G.missingColorsAt (F.erase e) switched (G.fst e) :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_not_flip_iff
      (F.erase e) color c b flip (G.fst e) hXnotFlip a).mpr ha
  have hbNew : b ∈ G.missingColorsAt (F.erase e) switched (G.snd e) :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_not_flip_iff
      (F.erase e) color c b flip (G.snd e) hYnotFlip b).mpr hb
  have hrNew : switched r = b := by
    change G.kempeComponentSwitch (F.erase e) color c b flip r = b
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase e) color c b flip hrF hrW]
    simp [kempeLocalPerm, flip, H, hrc]
  have hXedge : ∀ g ∈ F.erase e, G.Inc (G.fst e) g →
      switched g = color g := by
    intro g hgF hgX
    change G.kempeComponentSwitch (F.erase e) color c b flip g = color g
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase e) color c b flip hgF hgX]
    have hn : ¬flip ((G.twoColorGraph (F.erase e) color c b).connectedComponentMk
        (G.fst e)) := by simpa [H] using hXnotFlip
    simp [kempeLocalPerm, hn]
  have hother : ∀ g, color g ≠ c → color g ≠ b →
      switched g = color g := by
    intro g hgc hgb
    exact G.kempeComponentSwitch_eq_of_color_ne color c b flip g hgc hgb
  exact ⟨switched, hproper', haNew, hbNew, hrNew, hXedge, hother⟩

/-- The remaining colour branch at the last internal vertex is also
impossible: switching the outside vertex's cross-colour component would
put six vertices on a critical two-colour chain. -/
theorem no_outside_last_neighbor_of_missing_first_color
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (hc : c ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {w : G.V} (hwout : w ∉ p.1.support)
    {r : G.E} (hrF : r ∈ F.erase e)
    (hrZ : G.Inc (p.1.getVert 3) r) (hrW : G.Inc w r)
    (hrc : color r = c) : False := by
  classical
  let R := F.erase e
  obtain ⟨g₀, hg₀F, hg₀X, hg₀Z, hg₀b⟩ :=
    G.exists_first_criticalPath_edge_secondColor ha p (by omega)
  obtain ⟨g₁, hg₁F, hg₁Z, hg₁T, hg₁a⟩ :=
    G.exists_second_criticalPath_edge_firstColor hproper ha p (by omega)
  obtain ⟨g₃, hg₃F, hg₃Z, hg₃Y, hg₃a⟩ :=
    G.exists_last_criticalPath_edge_firstColor hb p (by omega)
  have hZ3Y : p.1.getVert 3 ≠ G.snd e := by
    have h := G.criticalPath_last_internal p (by omega)
    simpa [hpLen] using h.2.2
  have hWZ3 : w ≠ p.1.getVert 3 := by
    intro h; exact hwout (h ▸ p.1.getVert_mem_support 3)
  have hWY : w ≠ G.snd e := by
    intro h; exact hwout (h ▸ p.1.end_mem_support)
  have hrNeG₃ : r ≠ g₃ := by
    intro heq
    have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc
      hZ3Y (by simpa [hpLen] using hg₃Z) hg₃Y
    rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
    · rcases hrW with hfw | hsw
      · exact hWZ3 (by simpa [heq, hfst] using hfw.symm)
      · exact hWY (by simpa [heq, hsnd] using hsw.symm)
    · rcases hrW with hfw | hsw
      · exact hWY (by simpa [heq, hfst] using hfw.symm)
      · exact hWZ3 (by simpa [heq, hsnd] using hsw.symm)
  have hab : a ≠ b := G.critical_endpoint_missingColors_ne
    hcritical heF hproper ha hb
  have hac : a ≠ c := by
    intro heq
    have heqEdges : r = g₃ := by
      apply hproper (p.1.getVert 3)
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hrZ⟩)
      · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hg₃F, by simpa [hpLen] using hg₃Z⟩)
      · exact hrc.trans (heq.symm.trans hg₃a.symm)
    exact hrNeG₃ heqEdges
  obtain ⟨switched, hproperNew, haNew, hbNew, hrNew, hXedge, hother⟩ :=
    G.exists_crossKempeSwitch_preserving_endpoint_palettes
      hcritical heF hproper ha hb hc p hpLen hdk hdegree hthreshold
      hwout hrF hrZ hrW hrc
  have hg₀New : switched g₀ = b := (hXedge g₀ hg₀F hg₀X).trans hg₀b
  have hg₁New : switched g₁ = a := by
    rw [hother g₁ (hg₁a ▸ hac) (hg₁a ▸ hab), hg₁a]
  have hg₃New : switched g₃ = a := by
    rw [hother g₃ (hg₃a ▸ hac) (hg₃a ▸ hab), hg₃a]
  let H := G.twoColorGraph R switched a b
  have h01 : G.fst e ≠ p.1.getVert 1 := by
    intro h
    have hi := p.property.getVert_injOn
      (show 0 ∈ Set.Iic p.1.length by simp)
      (show 1 ∈ Set.Iic p.1.length by simp [hpLen])
      (by simpa using h)
    omega
  have h12 : p.1.getVert 1 ≠ p.1.getVert 2 := by
    intro h
    have hi := p.property.getVert_injOn
      (show 1 ∈ Set.Iic p.1.length by simp [hpLen])
      (show 2 ∈ Set.Iic p.1.length by simp [hpLen]) h
    omega
  have h3Y : p.1.getVert 3 ≠ G.snd e := hZ3Y
  have h01Adj : H.Adj (G.fst e) (p.1.getVert 1) := by
    exact G.twoColorGraph_adj_of_witness_inc h01 hg₀F hg₀X hg₀Z
      (Or.inr hg₀New)
  have h12Adj : H.Adj (p.1.getVert 1) (p.1.getVert 2) := by
    exact G.twoColorGraph_adj_of_witness_inc h12 hg₁F hg₁Z hg₁T
      (Or.inl hg₁New)
  have h3YAdj : H.Adj (p.1.getVert 3) (G.snd e) := by
    exact G.twoColorGraph_adj_of_witness_inc h3Y hg₃F
      (by simpa [hpLen] using hg₃Z) hg₃Y (Or.inl hg₃New)
  have hW3Adj : H.Adj w (p.1.getVert 3) := by
    exact G.twoColorGraph_adj_of_witness_inc hWZ3 hrF hrW hrZ
      (Or.inr hrNew)
  have hcomp01 : H.connectedComponentMk (G.fst e) =
      H.connectedComponentMk (p.1.getVert 1) :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h01Adj
  have hcomp12 : H.connectedComponentMk (p.1.getVert 1) =
      H.connectedComponentMk (p.1.getVert 2) :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h12Adj
  have hcomp3Y : H.connectedComponentMk (p.1.getVert 3) =
      H.connectedComponentMk (G.snd e) :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h3YAdj
  have hcompW3 : H.connectedComponentMk w =
      H.connectedComponentMk (p.1.getVert 3) :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hW3Adj
  have hcompXY : H.connectedComponentMk (G.fst e) =
      H.connectedComponentMk (G.snd e) :=
    G.critical_endpoints_same_twoColorComponent
      hcritical heF hproperNew haNew hbNew
  obtain ⟨q, _⟩ := G.exists_criticalEndpointPath
    hcritical heF hproperNew haNew hbNew
  have hcompMem : ∀ v, H.connectedComponentMk v =
      H.connectedComponentMk (G.fst e) → v ∈ q.1.support := by
    intro v hv
    exact G.mem_criticalPath_support_of_same_twoColorComponent
      hcritical heF hproperNew haNew hbNew q hv
  have hpSubset : p.1.support.toFinset ⊆ q.1.support.toFinset := by
    intro v hv
    obtain ⟨i, hi, hiLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (by simpa using hv : v ∈ p.1.support)
    have hiLe' : i ≤ 4 := by omega
    interval_cases i
    · subst v; exact (by simpa using hcompMem _ rfl)
    · subst v; exact (by simpa using hcompMem _ hcomp01.symm)
    · subst v; exact (by simpa using hcompMem _ (hcomp12.symm.trans hcomp01.symm))
    · subst v; exact (by simpa using hcompMem _ (hcomp3Y.trans hcompXY.symm))
    · subst v
      have h4 : p.1.getVert 4 = G.snd e := by
        simpa [hpLen] using p.1.getVert_length
      rw [h4]
      simpa using hcompMem _ hcompXY.symm
  have hwComp : H.connectedComponentMk w = H.connectedComponentMk (G.fst e) :=
    (hcompW3.trans hcomp3Y).trans hcompXY.symm
  have htotalSubset : insert w p.1.support.toFinset ⊆ q.1.support.toFinset := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hp
    · exact (by simpa using hcompMem v hwComp)
    · exact hpSubset hp
  have hpCard : p.1.support.toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup p.property.support_nodup,
      p.1.length_support, hpLen]
  have htotalCard : (insert w p.1.support.toFinset).card = 6 := by
    simp [hwout, hpCard]
  have hqCard := G.criticalPath_support_card_eq_three_or_five
    hcritical heF hproperNew haNew hbNew q (by omega) hdegree hthreshold
  have hle : 6 ≤ q.1.support.toFinset.card := by
    rw [← htotalCard]
    exact Finset.card_le_card htotalSubset
  omega

end WeightedEdgeColoring.WeightedMultigraph
