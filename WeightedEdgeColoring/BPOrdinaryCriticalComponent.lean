import WeightedEdgeColoring.BPOrdinaryCriticalChain

/-!
# Internal vertices of a critical two-colour component

The endpoints of a critical chain are its two active vertices.  This file
records the elementary consequence needed in Andersen's Lemma 3: every
other vertex in that component uses both chain colours.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/- The file uses finite connected-component subtypes in theorem bodies. -/
noncomputable local instance criticalDecidableSimpleGraphAdj (H : SimpleGraph G.V) :
    DecidableRel H.Adj :=
  Classical.decRel _

noncomputable local instance criticalDecidableSetMembership (s : Set G.V) :
    DecidablePred (fun v : G.V ↦ v ∈ s) :=
  Classical.decPred _

noncomputable local instance criticalFiniteConnectedComponentSupport
    (H : SimpleGraph G.V) (C : H.ConnectedComponent) : Fintype C :=
  @Subtype.fintype G.V (fun v ↦ v ∈ C.supp)
    (criticalDecidableSetMembership G C.supp) G.instFintypeV

/-- A proper colouring with fewer incident selected edges than colours has
at least one missing colour at that vertex. -/
theorem exists_mem_missingColorsAt_of_degreeOn_lt
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    (hproper : G.IsProperOn F color) {v : G.V}
    (hdegree : G.degreeOn F v < k) :
    ∃ c, c ∈ G.missingColorsAt F color v := by
  have hcard := G.card_missingColorsAt F color hproper v
  have hpos : 0 < (G.missingColorsAt F color v).card := by
    rw [hcard]
    omega
  exact Finset.card_pos.mp hpos

/-- A vertex at which both selected colours are missing is an isolated
vertex of the two-colour graph.  Hence no different vertex belongs to its
connected component. -/
theorem eq_of_same_twoColorComponent_of_both_missing
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k} {a b : Fin k}
    {v w : G.V}
    (hcomponent :
      (G.twoColorGraph F color a b).connectedComponentMk v =
        (G.twoColorGraph F color a b).connectedComponentMk w)
    (ha : a ∈ G.missingColorsAt F color v)
    (hb : b ∈ G.missingColorsAt F color v) :
    v = w := by
  classical
  let H := G.twoColorGraph F color a b
  let C : H.ConnectedComponent := H.connectedComponentMk v
  have hvC : v ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hwC : w ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    simpa [C, H] using hcomponent.symm
  let V : C := ⟨v, hvC⟩
  let W : C := ⟨w, hwC⟩
  by_contra hvw
  have hVW : V ≠ W := by
    intro h
    apply hvw
    exact congrArg Subtype.val h
  rcases C.connected_toSimpleGraph.preconnected V W with ⟨p⟩
  obtain ⟨Z, hVZ, p', hp⟩ := p.exists_eq_cons_of_ne hVW
  have hadj : H.Adj v Z.1 := by
    simpa [V, H] using hVZ
  rcases G.exists_twoColorWitnessEdge F color a b hadj with
    ⟨g, hgF, hgv, _hgZ, hga | hgb⟩
  · exact (G.color_ne_of_mem_missingColorsAt F color v a ha hgF hgv) hga
  · exact (G.color_ne_of_mem_missingColorsAt F color v b hb hgF hgv) hgb

/-- Once the two active endpoints of a critical chain are fixed, a third
vertex in their component cannot be active. -/
theorem not_twoColorActive_of_critical_chain_internal
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    {z : G.V}
    (hzcomponent :
      (G.twoColorGraph (F.erase e) color a b).connectedComponentMk z =
        (G.twoColorGraph (F.erase e) color a b).connectedComponentMk
          (G.fst e))
    (hzfst : z ≠ G.fst e) (hzsnd : z ≠ G.snd e) :
    ¬G.IsTwoColorActive (F.erase e) color a b z := by
  classical
  let H := G.twoColorGraph (F.erase e) color a b
  let C : H.ConnectedComponent := H.connectedComponentMk (G.fst e)
  have hends := G.critical_endpoints_twoColorActive
    hcritical heF hproper ha hb
  have hxycomponent := G.critical_endpoints_same_twoColorComponent
    hcritical heF hproper ha hb
  have hxC : G.fst e ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hyC : G.snd e ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    simpa [C, H] using hxycomponent.symm
  have hzC : z ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    simpa [C, H] using hzcomponent
  let X : C := ⟨G.fst e, hxC⟩
  let Y : C := ⟨G.snd e, hyC⟩
  let Z : C := ⟨z, hzC⟩
  have hXY : X ≠ Y := by
    intro h
    exact G.noLoop e (congrArg Subtype.val h)
  have hXZ : X ≠ Z := by
    intro h
    exact hzfst (congrArg Subtype.val h).symm
  have hYZ : Y ≠ Z := by
    intro h
    exact hzsnd (congrArg Subtype.val h).symm
  intro hzactive
  let active : Finset C :=
    (Finset.univ : Finset C).filter fun v ↦
      G.IsTwoColorActive (F.erase e) color a b v.1
  have hthree : ({X, Y, Z} : Finset C) ⊆ active := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hends.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hends.2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzactive⟩
  have hcardThree : ({X, Y, Z} : Finset C).card = 3 := by
    simp [hXY, hXZ, hYZ]
  have hge : 3 ≤ active.card := by
    rw [← hcardThree]
    exact Finset.card_le_card hthree
  have hle : active.card ≤ 2 := by
    simpa [active, C, H] using
      G.card_activeVertices_twoColorComponent_le_two
        (F.erase e) color hproper a b C
  omega

/-- Every non-endpoint vertex in a critical chain uses both chain colours. -/
theorem critical_chain_internal_uses_both
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    {z : G.V}
    (hzcomponent :
      (G.twoColorGraph (F.erase e) color a b).connectedComponentMk z =
        (G.twoColorGraph (F.erase e) color a b).connectedComponentMk
          (G.fst e))
    (hzfst : z ≠ G.fst e) (hzsnd : z ≠ G.snd e) :
    a ∉ G.missingColorsAt (F.erase e) color z ∧
      b ∉ G.missingColorsAt (F.erase e) color z := by
  have hnotactive := G.not_twoColorActive_of_critical_chain_internal
    hcritical heF hproper ha hb hzcomponent hzfst hzsnd
  constructor
  · intro hza
    have hzb : b ∈ G.missingColorsAt (F.erase e) color z := by
      by_contra hzb
      exact hnotactive (Or.inl ⟨hza, hzb⟩)
    have hzEq := G.eq_of_same_twoColorComponent_of_both_missing
      hzcomponent hza hzb
    exact hzfst hzEq
  · intro hzb
    have hza : a ∈ G.missingColorsAt (F.erase e) color z := by
      by_contra hza
      exact hnotactive (Or.inr ⟨hzb, hza⟩)
    have hzEq := G.eq_of_same_twoColorComponent_of_both_missing
      hzcomponent hza hzb
    exact hzfst hzEq

/-- In the critical component, only the first endpoint can miss `a`. -/
theorem eq_fst_of_mem_missing_chain_leftColor
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    {z : G.V}
    (hzcomponent :
      (G.twoColorGraph (F.erase e) color a b).connectedComponentMk z =
        (G.twoColorGraph (F.erase e) color a b).connectedComponentMk
          (G.fst e))
    (hza : a ∈ G.missingColorsAt (F.erase e) color z) :
    z = G.fst e := by
  by_contra hzfst
  by_cases hzsnd : z = G.snd e
  · subst z
    exact G.not_both_mem_missingColorsAt_endpoints_of_colorCritical
      hcritical heF hproper a ⟨ha, hza⟩
  · exact (G.critical_chain_internal_uses_both
      hcritical heF hproper ha hb hzcomponent hzfst hzsnd).1 hza

/-- In the critical component, only the second endpoint can miss `b`. -/
theorem eq_snd_of_mem_missing_chain_rightColor
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    {z : G.V}
    (hzcomponent :
      (G.twoColorGraph (F.erase e) color a b).connectedComponentMk z =
        (G.twoColorGraph (F.erase e) color a b).connectedComponentMk
          (G.fst e))
    (hzb : b ∈ G.missingColorsAt (F.erase e) color z) :
    z = G.snd e := by
  by_contra hzsnd
  by_cases hzfst : z = G.fst e
  · subst z
    exact G.not_both_mem_missingColorsAt_endpoints_of_colorCritical
      hcritical heF hproper b ⟨hzb, hb⟩
  · exact (G.critical_chain_internal_uses_both
      hcritical heF hproper ha hb hzcomponent hzfst hzsnd).2 hzb

end WeightedMultigraph
end WeightedEdgeColoring
