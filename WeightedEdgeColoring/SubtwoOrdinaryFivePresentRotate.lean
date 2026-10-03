import WeightedEdgeColoring.SubtwoOrdinaryFivePresentFirstShift

/-!
# Vertex order under a five-cycle omitted-edge shift

The final present-color case needs repeated shifts.  This version of the
checked last-edge shift records the actual order of the resulting path.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem exists_shifted_last_edge_fivePath_with_order
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    {g : G.E} (hgF : g ∈ F.erase e)
    (hgZ : G.Inc (p.1.getVert 3) g) (hga : color g = a) :
    ∃ q : (G.twoColorGraph (F.erase g)
      (G.assignEdgeColor color e a) a b).Path
        (p.1.getVert 3) (G.snd e),
      q.1.length = 4 ∧
      q.1.support.toFinset = p.1.support.toFinset ∧
      q.1.getVert 1 = p.1.getVert 2 ∧
      q.1.getVert 2 = p.1.getVert 1 ∧
      q.1.getVert 3 = G.fst e := by
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
  refine ⟨q, hqLen, hsupport.symm, ?_, ?_, ?_⟩
  all_goals simp [q, qWalk]

/-- The first-edge shift follows the five-cycle in the opposite direction:
`Z₁,Z₂,Z₃,Y,X`. -/
theorem exists_shifted_first_edge_fivePath_with_order
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    {g : G.E} (hgF : g ∈ F.erase e)
    (hgZ : G.Inc (p.1.getVert 1) g) (hgb : color g = b) :
    ∃ q : (G.twoColorGraph (F.erase g)
      (G.assignEdgeColor color e b) a b).Path
        (p.1.getVert 1) (G.fst e),
      q.1.length = 4 ∧
      q.1.support.toFinset = p.1.support.toFinset ∧
      q.1.getVert 1 = p.1.getVert 2 ∧
      q.1.getVert 2 = p.1.getVert 3 ∧
      q.1.getVert 3 = G.snd e := by
  let R := G.reverseEndpoints
  have hgraph : R.twoColorGraph (F.erase e) color b a =
      G.twoColorGraph (F.erase e) color a b :=
    G.reverseEndpoints_twoColorGraph color a b
  let pR : (R.twoColorGraph (F.erase e) color b a).Path
      (R.fst e) (R.snd e) := G.pathCast hgraph p.reverse
  have hpRLen : pR.1.length = 4 := by
    rw [G.pathCast_length]
    simpa using hpLen
  have hpRSupport : pR.1.support.toFinset = p.1.support.toFinset := by
    rw [G.pathCast_support]
    simp
  have hpR3 : pR.1.getVert 3 = p.1.getVert 1 := by
    rw [G.pathCast_getVert]
    change p.1.reverse.getVert 3 = p.1.getVert 1
    rw [SimpleGraph.Walk.getVert_reverse, hpLen]
  have hpR2 : pR.1.getVert 2 = p.1.getVert 2 := by
    rw [G.pathCast_getVert]
    change p.1.reverse.getVert 2 = p.1.getVert 2
    rw [SimpleGraph.Walk.getVert_reverse, hpLen]
  have hpR1 : pR.1.getVert 1 = p.1.getVert 3 := by
    rw [G.pathCast_getVert]
    change p.1.reverse.getVert 1 = p.1.getVert 3
    rw [SimpleGraph.Walk.getVert_reverse, hpLen]
  have hproperR : R.IsProperOn (F.erase e) color :=
    G.reverseEndpoints_proper_iff.mpr hproper
  have hcriticalR : R.IsColorCriticalOn F k :=
    G.reverseEndpoints_critical_iff.mpr hcritical
  have hbR : b ∈ R.missingColorsAt (F.erase e) color (R.fst e) := by
    simpa [R] using hb
  have haR : a ∈ R.missingColorsAt (F.erase e) color (R.snd e) := by
    simpa [R] using ha
  have hgZR : R.Inc (pR.1.getVert 3) g := by
    simpa [R, hpR3] using hgZ
  obtain ⟨qR, hqRLen, hqRSupport, hqR1, hqR2, hqR3⟩ :=
    R.exists_shifted_last_edge_fivePath_with_order
      hcriticalR heF hproperR hbR haR pR hpRLen hgF hgZR hgb
  have hgraphNew : R.twoColorGraph (F.erase g)
      (R.assignEdgeColor color e b) b a =
      G.twoColorGraph (F.erase g)
        (G.assignEdgeColor color e b) a b := by
    simpa [R] using
      (G.reverseEndpoints_twoColorGraph
        (G.assignEdgeColor color e b) a b (F := F.erase g))
  let q0 := G.pathCast hgraphNew.symm qR
  let q : (G.twoColorGraph (F.erase g)
      (G.assignEdgeColor color e b) a b).Path
        (p.1.getVert 1) (G.fst e) :=
    G.pathEndpointsCast hpR3.symm (by rfl) q0
  have hqVert (i : ℕ) : q.1.getVert i = qR.1.getVert i := by
    rw [G.pathEndpointsCast_getVert, G.pathCast_getVert]
  have hqLen : q.1.length = 4 := by
    rw [G.pathEndpointsCast_length, G.pathCast_length]
    exact hqRLen
  have hqSupport : q.1.support.toFinset = p.1.support.toFinset := by
    rw [G.pathEndpointsCast_support, G.pathCast_support,
      hqRSupport, hpRSupport]
  exact ⟨q, hqLen, hqSupport,
    (hqVert 1).trans (hqR1.trans hpR2),
    (hqVert 2).trans (hqR2.trans hpR1),
    (hqVert 3).trans (by simpa [R] using hqR3)⟩

/-- Package a last-edge shift as a new critical-path state, including
properness, endpoint palettes, and the exact path rotation. -/
theorem exists_last_shifted_fivePath_state
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
        (G.assignEdgeColor color e a) (G.snd e) ∧
      ∃ q : (G.twoColorGraph (F.erase g)
        (G.assignEdgeColor color e a) a b).Path
          (p.1.getVert 3) (G.snd e),
        q.1.length = 4 ∧
        q.1.support.toFinset = p.1.support.toFinset ∧
        q.1.getVert 1 = p.1.getVert 2 ∧
        q.1.getVert 2 = p.1.getVert 1 ∧
        q.1.getVert 3 = G.fst e := by
  obtain ⟨g, hgF, hgZ, hgY, hga, hproperNew, haNew, hbNew⟩ :=
    G.exists_proper_shift_to_last_edge_with_endpoint_palettes
      hcritical heF hproper ha hb p hpLen
  obtain ⟨q, hqLen, hqSupport, hq1, hq2, hq3⟩ :=
    G.exists_shifted_last_edge_fivePath_with_order
      hcritical heF hproper ha hb p hpLen hgF hgZ hga
  exact ⟨g, hgF, hgZ, hgY, hga, hproperNew,
    haNew, hbNew, q, hqLen, hqSupport, hq1, hq2, hq3⟩

end WeightedEdgeColoring.WeightedMultigraph
