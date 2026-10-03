import WeightedEdgeColoring.SubtwoOrdinaryFivePresentVZ1InternalC

/-!
# Switching the component outside the new `Y` circuit
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable local instance vz1SecondFiniteNeighborSet
    (H : SimpleGraph G.V) (v : G.V) : Fintype (H.neighborSet v) :=
  @Subtype.fintype G.V (fun w ↦ w ∈ H.neighborSet v)
    (Classical.decPred _) G.instFintypeV

/-- The circuit through `Y` exhausts its `(b,c)` component. Switching
the distinct component through `X` therefore preserves every edge
incident with the circuit while making `c` absent at `X`. -/
theorem FivePathState.exists_second_switch_outside_right_circuit
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {paint₁ : G.E → Fin k}
    (hproper₁ : G.IsProperOn (F.erase s.omitted) paint₁)
    (hbX : b ∈ G.missingColorsAt (F.erase s.omitted) paint₁ s.left)
    (haY : a ∈ G.missingColorsAt (F.erase s.omitted) paint₁ s.right)
    (q₂ : (G.twoColorGraph (F.erase s.omitted) paint₁ b c).Path
      s.right (s.path.1.getVert 3))
    (hqLen : 2 ≤ q₂.1.length)
    (hclose : (G.twoColorGraph (F.erase s.omitted) paint₁ b c).Adj
      (s.path.1.getVert 3) s.right)
    (hXout : s.left ∉ q₂.1.support) :
    ∃ paint₂ : G.E → Fin k,
      G.IsProperOn (F.erase s.omitted) paint₂ ∧
      c ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.left ∧
      a ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.right ∧
      (∀ r, paint₁ r ≠ b → paint₁ r ≠ c → paint₂ r = paint₁ r) ∧
      (∀ v ∈ q₂.1.support,
        ∀ r ∈ F.erase s.omitted, G.Inc v r → paint₂ r = paint₁ r) ∧
      ∃ q : (G.twoColorGraph (F.erase s.omitted) paint₂ c a).Path
        s.left s.right,
        q.1.support.toFinset.card ≤ 5 := by
  classical
  let H := G.twoColorGraph (F.erase s.omitted) paint₁ b c
  have hmax : ∀ v, H.degree v ≤ 2 := by
    intro v
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      (F.erase s.omitted) paint₁ hproper₁ b c v
  have hsep : H.connectedComponentMk s.left ≠
      H.connectedComponentMk s.right := by
    intro h
    have hmem := G.mem_closedPath_support_of_same_component
      H q₂ hqLen hclose.symm hmax h
    exact hXout hmem
  let flip : H.ConnectedComponent → Prop :=
    fun C ↦ C = H.connectedComponentMk s.left
  letI : DecidablePred flip := Classical.decPred _
  let paint₂ := G.kempeComponentSwitch
    (F.erase s.omitted) paint₁ b c flip
  have hproper₂ : G.IsProperOn (F.erase s.omitted) paint₂ :=
    G.isProperOn_kempeComponentSwitch
      (F.erase s.omitted) paint₁ hproper₁ b c flip
  have hcX : c ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.left :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_flip
      (F.erase s.omitted) paint₁ b c flip s.left rfl).1.mpr hbX
  have hYnot : ¬flip (H.connectedComponentMk s.right) := by
    intro h
    exact hsep h.symm
  have haY₂ : a ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.right :=
    (G.mem_missingColorsAt_kempeComponentSwitch_of_not_flip_iff
      (F.erase s.omitted) paint₁ b c flip s.right hYnot a).mpr haY
  have hother : ∀ r, paint₁ r ≠ b → paint₁ r ≠ c →
      paint₂ r = paint₁ r := by
    intro r hrb hrc
    exact G.kempeComponentSwitch_eq_of_color_ne
      paint₁ b c flip r hrb hrc
  have hstable : ∀ v ∈ q₂.1.support,
      ∀ r ∈ F.erase s.omitted, G.Inc v r → paint₂ r = paint₁ r := by
    intro v hv r hrF hrV
    have hreach : H.Reachable s.right v :=
      ⟨q₂.1.takeUntil v hv⟩
    have hcomp : H.connectedComponentMk v =
        H.connectedComponentMk s.right :=
      (SimpleGraph.ConnectedComponent.sound hreach).symm
    have hnot : ¬flip (H.connectedComponentMk v) := by
      intro h
      exact hsep (h.symm.trans hcomp)
    change G.kempeComponentSwitch (F.erase s.omitted)
      paint₁ b c flip r = paint₁ r
    rw [G.kempeComponentSwitch_eq_localPerm
      (F.erase s.omitted) paint₁ b c flip hrF hrV]
    simp [kempeLocalPerm, flip, H, hnot]
  have hcompCA := G.critical_endpoints_same_twoColorComponent_at
    hcritical s.omitted_mem hproper₂ s.left_ne_right
    s.left_inc s.right_inc hcX haY₂
  have hreachCA : (G.twoColorGraph (F.erase s.omitted) paint₂ c a).Reachable
      s.left s.right := SimpleGraph.ConnectedComponent.exact hcompCA
  obtain ⟨walk⟩ := hreachCA
  let q := walk.toPath
  have hcard := G.criticalPath_support_card_le_five_at
    hcritical s.omitted_mem hproper₂ s.left_ne_right
    s.left_inc s.right_inc hcX haY₂ q
    hdk hdegree hthreshold
  exact ⟨paint₂, hproper₂, hcX, haY₂, hother, hstable, q, hcard⟩

/-- In the `V = Z₁` middle-`c` subcase, Andersen's two successive
switches produce a new critical `(c,a)` endpoint path of at most five
vertices while the `Y` circuit is stable under the second switch. -/
theorem FivePathState.exists_vz1_internal_c_critical_ca_path
    {F : Finset G.E} {k d : ℕ} {a b c : Fin k}
    (s : G.FivePathState F k a b)
    (hcritical : G.IsColorCriticalOn F k)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    (hleft : FivePathState.HasExternalColorAt G s c s.left)
    (hright : FivePathState.HasExternalColorAt G s c s.right)
    (p : (G.twoColorGraph (F.erase s.omitted) s.paint b c).Path
      s.right s.left)
    {i : ℕ} (hi : 1 < i) (hiLe : i ≤ p.1.length)
    (hfirst : ∀ j, 0 < j → j < i →
      p.1.getVert j ∉ s.path.1.support.toFinset)
    (hiZ1 : p.1.getVert i = s.path.1.getVert 1)
    {t : G.E} (htF : t ∈ F.erase s.omitted)
    (ht2 : G.Inc (s.path.1.getVert 2) t)
    (ht3 : G.Inc (s.path.1.getVert 3) t)
    (htC : s.paint t = c) :
    ∃ paint₁ paint₂ : G.E → Fin k,
      G.IsProperOn (F.erase s.omitted) paint₁ ∧
      G.IsProperOn (F.erase s.omitted) paint₂ ∧
      c ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.left ∧
      a ∈ G.missingColorsAt (F.erase s.omitted) paint₂ s.right ∧
      ∃ q₂ : (G.twoColorGraph (F.erase s.omitted) paint₁ b c).Path
        s.right (s.path.1.getVert 3),
        (∀ v ∈ q₂.1.support,
          ∀ r ∈ F.erase s.omitted, G.Inc v r → paint₂ r = paint₁ r) ∧
        ∃ q : (G.twoColorGraph (F.erase s.omitted) paint₂ c a).Path
          s.left s.right,
          q.1.support.toFinset.card ≤ 5 := by
  obtain ⟨paint₁, hproper₁, hbX, haY, q₂, hqLen, hclose,
    hXout, _, _, _⟩ :=
    FivePathState.exists_vz1_internal_c_circuit
      G s hcritical hleft hright p hi hiLe hfirst hiZ1
      htF ht2 ht3 htC
  obtain ⟨paint₂, hproper₂, hcX, haY₂, _, hstable, q, hcard⟩ :=
    FivePathState.exists_second_switch_outside_right_circuit
      G s hcritical hdk hdegree hthreshold
      hproper₁ hbX haY q₂ hqLen hclose hXout
  exact ⟨paint₁, paint₂, hproper₁, hproper₂, hcX, haY₂,
    q₂, hstable, q, hcard⟩

end WeightedEdgeColoring.WeightedMultigraph
