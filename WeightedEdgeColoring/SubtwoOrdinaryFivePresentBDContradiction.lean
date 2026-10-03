import WeightedEdgeColoring.SubtwoOrdinaryFivePresentCriticalPathContainment

/-!
# The final (b,d) circuit switch contradicts five-path containment
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable local instance bdContradictionFiniteNeighborSet
    (H : SimpleGraph G.V) (v : G.V) : Fintype (H.neighborSet v) :=
  @Subtype.fintype G.V (fun w ↦ w ∈ H.neighborSet v)
    (Classical.decPred _) G.instFintypeV

/-- A `(b,d)` circuit through `Y` excluding `X` allows a switch at `X`.
The critical `(c,a)` five-path survives, whereas the resulting
critical `(b,a)` path must contain its exterior neighbor `Z₃`,
contradicting five-path containment. -/
theorem FivePathState.false_of_bd_circuit_outside_ca_path
    {F : Finset G.E} {k D : ℕ} {a b c d : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : D + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ D)
    (hthreshold : 7 * D < 6 * k + 2)
    (hab : a ≠ b) (had : a ≠ d)
    (hcb : c ≠ b) (hcd : c ≠ d)
    {paint₂ : G.E → Fin k}
    (hproper₂ : G.IsProperOn (F.erase s.omitted) paint₂)
    (hcX : c ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.left)
    (haY : a ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.right)
    (hdX : d ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.left)
    (qCA : (G.twoColorGraph (F.erase s.omitted) paint₂ c a).Path
      s.left s.right)
    (hqLen : qCA.1.length = 4)
    (hZ3out : s.path.1.getVert 3 ∉ qCA.1.support.toFinset)
    (qBD : (G.twoColorGraph (F.erase s.omitted) paint₂ b d).Path
      s.right (s.path.1.getVert 3))
    (hqBDLen : 2 ≤ qBD.1.length)
    (hclose : (G.twoColorGraph (F.erase s.omitted) paint₂ b d).Adj
      (s.path.1.getVert 3) s.right)
    (hXout : s.left ∉ qBD.1.support)
    {g3 : G.E} (hg3F : g3 ∈ F.erase s.omitted)
    (hg3Z3 : G.Inc (s.path.1.getVert 3) g3)
    (hg3Y : G.Inc s.right g3)
    (hg3B : paint₂ g3 = b) : False := by
  classical
  let H := G.twoColorGraph (F.erase s.omitted) paint₂ b d
  have hmax : ∀ v, H.degree v ≤ 2 := by
    intro v
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase s.omitted) paint₂ hproper₂ b d v
  have hsep : H.connectedComponentMk s.left ≠
      H.connectedComponentMk s.right := by
    intro h
    have hmem := G.mem_closedPath_support_of_same_component
      H qBD hqBDLen hclose.symm hmax h
    exact hXout hmem
  let flip : H.ConnectedComponent → Prop :=
    fun C ↦ C = H.connectedComponentMk s.left
  letI : DecidablePred flip := Classical.decPred _
  let paint₃ := G.kempeComponentSwitch
    (F.erase s.omitted) paint₂ b d flip
  have hproper₃ : G.IsProperOn (F.erase s.omitted) paint₃ :=
    G.isProperOn_kempeComponentSwitch
      (F.erase s.omitted) paint₂ hproper₂ b d flip
  have hbX : b ∈ G.missingColorsAt (F.erase s.omitted) paint₃ s.left :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_flip
      (F.erase s.omitted) paint₂ b d flip s.left rfl).2.mpr hdX
  have haY₃ : a ∈ G.missingColorsAt (F.erase s.omitted) paint₃ s.right :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_fixedColor_iff
      (F := F.erase s.omitted) paint₂ b d flip s.right a hab had).mpr haY
  have hcX₃ : c ∈ G.missingColorsAt (F.erase s.omitted) paint₃ s.left :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_fixedColor_iff
      (F := F.erase s.omitted) paint₂ b d flip s.left c hcb hcd).mpr hcX
  have hYnot : ¬flip (H.connectedComponentMk s.right) := by
    intro h
    exact hsep h.symm
  have hg3B₃ : paint₃ g3 = b := by
    change G.kempeComponentSwitch (F.erase s.omitted)
      paint₂ b d flip g3 = b
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase s.omitted) paint₂ b d flip hg3F hg3Y]
    simp [kempeLocalPerm, flip, H, hYnot, hg3B]
  let K := G.twoColorGraph (F.erase s.omitted) paint₃ c a
  have hother : ∀ r, paint₂ r ≠ b → paint₂ r ≠ d →
      paint₃ r = paint₂ r := by
    intro r hrb hrd
    exact G.kempeComponentSwitch_eq_of_color_ne
      paint₂ b d flip r hrb hrd
  have hedges : ∀ e ∈ qCA.1.edges, e ∈ K.edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : (G.twoColorGraph (F.erase s.omitted) paint₂ c a).Adj u v :=
        qCA.1.edges_subset_edgeSet he
      obtain ⟨r, hrF, hrU, hrV, hrColor⟩ :=
        G.exists_twoColorWitnessEdge
          (F.erase s.omitted) paint₂ c a huv
      have hrNew : paint₃ r = c ∨ paint₃ r = a := by
        rcases hrColor with hrC | hrA
        · exact Or.inl ((hother r (by simpa [hrC] using hcb)
            (by simpa [hrC] using hcd)).trans hrC)
        · exact Or.inr ((hother r (by simpa [hrA] using hab)
            (by simpa [hrA] using had)).trans hrA)
      exact G.twoColorGraph_adj_of_witness_inc huv.ne
        hrF hrU hrV hrNew
  let qCA₃ : K.Path s.left s.right :=
    ⟨qCA.1.transfer K hedges, qCA.property.transfer hedges⟩
  have hqCA₃Len : qCA₃.1.length = 4 := by
    change (qCA.1.transfer K hedges).length = 4
    rw [qCA.1.length_transfer hedges]
    exact hqLen
  have hqCA₃Support : qCA₃.1.support.toFinset =
      qCA.1.support.toFinset := by
    change (qCA.1.transfer K hedges).support.toFinset =
      qCA.1.support.toFinset
    rw [qCA.1.support_transfer hedges]
  let s₃ : G.FivePathState F k c a := {
    omitted := s.omitted
    paint := paint₃
    left := s.left
    right := s.right
    omitted_mem := s.omitted_mem
    left_ne_right := s.left_ne_right
    left_inc := s.left_inc
    right_inc := s.right_inc
    proper := hproper₃
    left_missing := hcX₃
    right_missing := haY₃
    path := qCA₃
    path_len := hqCA₃Len
  }
  have hcompBA := G.critical_endpoints_same_twoColorComponent_at
    hcritical s.omitted_mem hproper₃ s.left_ne_right
    s.left_inc s.right_inc hbX haY₃
  have hreachBA : (G.twoColorGraph (F.erase s.omitted) paint₃ b a).Reachable
      s.left s.right := SimpleGraph.ConnectedComponent.exact hcompBA
  obtain ⟨walk⟩ := hreachBA
  let qBA := walk.toPath
  have hZ3Y : s.path.1.getVert 3 ≠ s.right :=
    (FivePathState.internal_vertex_ne_endpoints G s
      (by omega : 0 < 3) (by omega : 3 < 4)).2
  have hY3 : (G.twoColorGraph (F.erase s.omitted) paint₃ b a).Adj
      s.right (s.path.1.getVert 3) :=
    G.twoColorGraph_adj_of_witness_inc hZ3Y.symm
      hg3F hg3Y hg3Z3 (Or.inl hg3B₃)
  have hCompY3 := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hY3
  have hZ3Comp :
      (G.twoColorGraph (F.erase s.omitted) paint₃ b a).connectedComponentMk
          (s.path.1.getVert 3) =
      (G.twoColorGraph (F.erase s.omitted) paint₃ b a).connectedComponentMk
          s.left := hCompY3.symm.trans hcompBA.symm
  have hZ3Mem : s.path.1.getVert 3 ∈ qBA.1.support :=
    G.mem_criticalPath_support_of_same_twoColorComponent_at
      hcritical s.omitted_mem hproper₃ s.left_ne_right
      s.left_inc s.right_inc hbX haY₃ qBA hZ3Comp
  have hsub := FivePathState.other_critical_path_support_subset
    G s₃ hcritical hdk hdegree hthreshold hbX haY₃ qBA
  have hmemCA : s.path.1.getVert 3 ∈ qCA₃.1.support.toFinset :=
    hsub (by simpa only [List.mem_toFinset] using hZ3Mem)
  exact hZ3out (hqCA₃Support ▸ hmemCA)

end WeightedEdgeColoring.WeightedMultigraph
