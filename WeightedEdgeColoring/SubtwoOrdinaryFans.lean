import WeightedEdgeColoring.BPOrdinaryCriticalShift

/-!
# Missing colors at neighbors of a critical omitted edge

These lemmas support the union-of-chains step in Andersen's seven-sixths
theorem.  A neighbor reached by shifting the omitted edge has a missing
palette disjoint from the palettes of other such neighbors.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem twoColorGraph_swap
    {F : Finset G.E} {k : ℕ} (color : G.E → Fin k) (a b : Fin k) :
    G.twoColorGraph F color a b = G.twoColorGraph F color b a := by
  ext x y
  simp only [twoColorGraph, SimpleGraph.fromRel_adj, twoColorRel, or_comm]

/-- The critical-component lemma with either orientation of the edge. -/
theorem critical_endpoints_same_twoColorComponent_at
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {x y : G.V} (hxy : x ≠ y) (hxe : G.Inc x e) (hye : G.Inc y e)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color x)
    (hb : b ∈ G.missingColorsAt (F.erase e) color y) :
    (G.twoColorGraph (F.erase e) color a b).connectedComponentMk x =
      (G.twoColorGraph (F.erase e) color a b).connectedComponentMk y := by
  rcases hxe with hfx | hsx <;> rcases hye with hfy | hsy
  · exact False.elim (hxy (hfx.symm.trans hfy))
  · subst x; subst y
    exact G.critical_endpoints_same_twoColorComponent hcritical heF hproper ha hb
  · subst x; subst y
    have h := G.critical_endpoints_same_twoColorComponent hcritical heF hproper hb ha
    rw [G.twoColorGraph_swap color b a] at h
    exact h.symm
  · exact False.elim (hxy (hsx.symm.trans hsy))

/-- A one-step fan at `x`: the other endpoint `y`, and neighbors reached
by an edge whose color is missing at `y`. -/
def InOneStepFan
    (F : Finset G.E) {k : ℕ} (e : G.E) (color : G.E → Fin k)
    (x y z : G.V) : Prop :=
  z ≠ x ∧ (z = y ∨ ∃ g ∈ F.erase e,
    G.Inc x g ∧ G.Inc z g ∧
      color g ∈ G.missingColorsAt (F.erase e) color y)

/-- Missing colors at the center and at a fan vertex join the two
vertices by a two-color component, after shifting the omitted edge. -/
theorem same_twoColorComponent_of_oneStepFan
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {x y z : G.V} (hxy : x ≠ y) (hxe : G.Inc x e) (hye : G.Inc y e)
    (hz : G.InOneStepFan F e color x y z)
    {a c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color x)
    (hc : c ∈ G.missingColorsAt (F.erase e) color z) :
    (G.twoColorGraph (F.erase e) color a c).connectedComponentMk x =
      (G.twoColorGraph (F.erase e) color a c).connectedComponentMk z := by
  rcases hz with ⟨hzx, rfl | ⟨g, hg, hgx, hgz, hgy⟩⟩
  · exact G.critical_endpoints_same_twoColorComponent_at
      hcritical heF hproper hxy hxe hye ha hc
  · have hag : a ≠ color g :=
      (G.color_ne_of_mem_missingColorsAt (F.erase e) color x a ha hg hgx).symm
    have hcg : c ≠ color g :=
      (G.color_ne_of_mem_missingColorsAt (F.erase e) color z c hc hg hgz).symm
    have hp := G.isProperOn_shiftOmittedEdge_at
      heF hg hproper rfl hxy hxe hye hgx hgy
    have ha' := G.mem_missingColorsAt_shiftOmitted_of_ne (g := g) hag ha
    have hc' := G.mem_missingColorsAt_shiftOmitted_of_ne (g := g) hcg hc
    have h := G.critical_endpoints_same_twoColorComponent_at
      hcritical (Finset.mem_erase.mp hg).2 hp hzx.symm hgx hgz ha' hc'
    rw [G.twoColorGraph_shiftOmitted_eq_of_fixedColors heF hg rfl
      hag.symm hcg.symm] at h
    exact h

/-- A common missing color at two distinct fan vertices would create
three active vertices in one two-color component. -/
theorem disjoint_missingColorsAt_of_oneStepFan
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {x y u v : G.V} (hxy : x ≠ y) (hxe : G.Inc x e) (hye : G.Inc y e)
    (hu : G.InOneStepFan F e color x y u)
    (hv : G.InOneStepFan F e color x y v) (huv : u ≠ v)
    (hxmissing : (G.missingColorsAt (F.erase e) color x).Nonempty) :
    Disjoint (G.missingColorsAt (F.erase e) color u)
      (G.missingColorsAt (F.erase e) color v) := by
  rw [Finset.disjoint_left]
  intro c huc hvc
  obtain ⟨a, hxa⟩ := hxmissing
  have hxu := G.same_twoColorComponent_of_oneStepFan
    hcritical heF hproper hxy hxe hye hu hxa huc
  have hxv := G.same_twoColorComponent_of_oneStepFan
    hcritical heF hproper hxy hxe hye hv hxa hvc
  have hxc : c ∉ G.missingColorsAt (F.erase e) color x := by
    intro hxc
    exact hu.1 (G.eq_of_same_twoColorComponent_of_both_missing hxu hxa hxc).symm
  have hua : a ∉ G.missingColorsAt (F.erase e) color u := by
    intro hua
    exact hu.1 (G.eq_of_same_twoColorComponent_of_both_missing hxu.symm hua huc)
  have hva : a ∉ G.missingColorsAt (F.erase e) color v := by
    intro hva
    exact hv.1 (G.eq_of_same_twoColorComponent_of_both_missing hxv.symm hva hvc)
  exact G.not_three_active_in_one_twoColorComponent hproper
    hu.1.symm hv.1.symm huv (Or.inl ⟨hxa, hxc⟩)
    (Or.inr ⟨huc, hua⟩) (Or.inr ⟨hvc, hva⟩) hxu.symm hxv.symm

/-- The center and any one-step fan vertex have disjoint missing palettes. -/
theorem disjoint_missingColorsAt_center_oneStepFan
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {x y z : G.V} (hxy : x ≠ y) (hxe : G.Inc x e) (hye : G.Inc y e)
    (hz : G.InOneStepFan F e color x y z) :
    Disjoint (G.missingColorsAt (F.erase e) color x)
      (G.missingColorsAt (F.erase e) color z) := by
  rw [Finset.disjoint_left]
  intro c hxc hzc
  have h := G.same_twoColorComponent_of_oneStepFan
    hcritical heF hproper hxy hxe hye hz hxc hzc
  exact hz.1 (G.eq_of_same_twoColorComponent_of_both_missing h hxc hxc).symm

/-- Missing palettes are disjoint even when the two vertices are in fans
at opposite endpoints. The extra missing color at the first endpoint
lets us switch a component without changing the edge defining the second fan. -/
theorem disjoint_missingColorsAt_of_opposite_oneStepFans
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {x y u v : G.V} (hxy : x ≠ y) (hxe : G.Inc x e) (hye : G.Inc y e)
    (hu : G.InOneStepFan F e color x y u)
    (hv : G.InOneStepFan F e color y x v) (huv : u ≠ v)
    (hxcard : 1 < (G.missingColorsAt (F.erase e) color x).card)
    (hydegree : G.degreeOn (F.erase e) y < k) :
    Disjoint (G.missingColorsAt (F.erase e) color u)
      (G.missingColorsAt (F.erase e) color v) := by
  classical
  by_cases huy : u = y
  · subst u
    exact G.disjoint_missingColorsAt_center_oneStepFan
      hcritical heF hproper hxy.symm hye hxe hv
  by_cases hvx : v = x
  · subst v
    exact (G.disjoint_missingColorsAt_center_oneStepFan
      hcritical heF hproper hxy hxe hye hu).symm
  rw [Finset.disjoint_left]
  intro c huc hvc
  obtain ⟨g, hg, hgy, hgv, hgx⟩ := hv.2.resolve_left hvx
  obtain ⟨a, hxa, hag⟩ := Finset.exists_mem_ne hxcard (color g)
  have hgc : color g ≠ c :=
    G.color_ne_of_mem_missingColorsAt (F.erase e) color v c hvc hg hgv
  have hxu := G.same_twoColorComponent_of_oneStepFan
    hcritical heF hproper hxy hxe hye hu hxa huc
  have hxv :
      (G.twoColorGraph (F.erase e) color a c).connectedComponentMk x =
        (G.twoColorGraph (F.erase e) color a c).connectedComponentMk v := by
    by_contra hnot
    let H := G.twoColorGraph (F.erase e) color a c
    let flip : H.ConnectedComponent → Prop :=
      fun C ↦ C = H.connectedComponentMk x
    let switched := G.kempeComponentSwitch (F.erase e) color a c flip
    have hp : G.IsProperOn (F.erase e) switched :=
      G.isProperOn_kempeComponentSwitch (F.erase e) color hproper a c flip
    have hxFlip : flip (H.connectedComponentMk x) := rfl
    have hvNotFlip : ¬flip (H.connectedComponentMk v) := by
      intro h
      exact hnot h.symm
    have hxc' : c ∈ G.missingColorsAt (F.erase e) switched x :=
      (G.mem_missingColorsAt_kempeComponentSwitch_of_flip
        (F.erase e) color a c flip x hxFlip).1.mpr hxa
    have hvc' : c ∈ G.missingColorsAt (F.erase e) switched v :=
      (G.mem_missingColorsAt_kempeComponentSwitch_of_not_flip_iff
        (F.erase e) color a c flip v hvNotFlip c).mpr hvc
    have hgfixed : switched g = color g :=
      G.kempeComponentSwitch_eq_of_color_ne color a c flip g hag.symm hgc
    have hgx' : color g ∈ G.missingColorsAt (F.erase e) switched x :=
      (G.mem_missingColorsAt_kempeComponentSwitch_of_fixedColor_iff
        color a c flip x (color g) hag.symm hgc).mpr hgx
    have hv' : G.InOneStepFan F e switched y x v := by
      refine ⟨hv.1, Or.inr ⟨g, hg, hgy, hgv, ?_⟩⟩
      simpa [hgfixed] using hgx'
    have hx' : G.InOneStepFan F e switched y x x :=
      ⟨hxy, Or.inl rfl⟩
    have hymissing : (G.missingColorsAt (F.erase e) switched y).Nonempty :=
      G.exists_mem_missingColorsAt_of_degreeOn_lt hp hydegree
    have hdisjoint := G.disjoint_missingColorsAt_of_oneStepFan
      hcritical heF hp hxy.symm hye hxe hx' hv' (Ne.symm hvx) hymissing
    exact Finset.disjoint_left.mp hdisjoint hxc' hvc'
  have hxc : c ∉ G.missingColorsAt (F.erase e) color x := by
    intro hxc
    exact hu.1 (G.eq_of_same_twoColorComponent_of_both_missing hxu hxa hxc).symm
  have hua : a ∉ G.missingColorsAt (F.erase e) color u := by
    intro hua
    exact hu.1 (G.eq_of_same_twoColorComponent_of_both_missing hxu.symm hua huc)
  have hva : a ∉ G.missingColorsAt (F.erase e) color v := by
    intro hva
    exact hvx (G.eq_of_same_twoColorComponent_of_both_missing hxv.symm hva hvc)
  exact G.not_three_active_in_one_twoColorComponent hproper
    hu.1.symm (Ne.symm hvx) huv (Or.inl ⟨hxa, hxc⟩)
    (Or.inr ⟨huc, hua⟩) (Or.inr ⟨hvc, hva⟩) hxu.symm hxv.symm

end WeightedEdgeColoring.WeightedMultigraph
