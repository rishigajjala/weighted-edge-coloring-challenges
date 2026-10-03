import WeightedEdgeColoring.BPOrdinaryCriticalComponent

/-!
# The local switch in Andersen's disjoint-palette lemma

If two vertices of one two-colour component both miss a third colour `c`,
and an intermediate vertex uses `c`, switch the `(c,f)` component of that
intermediate vertex, where `f` is missing there.  The intermediate vertex
then misses `c`, while at least one of the original two vertices continues
to miss `c`.  The reason is simply that a two-colour component has at most
two active vertices.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

noncomputable local instance switchDecidableSimpleGraphAdj
    (H : SimpleGraph G.V) : DecidableRel H.Adj :=
  Classical.decRel _

noncomputable local instance switchDecidableSetMembership (s : Set G.V) :
    DecidablePred (fun v : G.V ↦ v ∈ s) :=
  Classical.decPred _

noncomputable local instance switchFiniteConnectedComponentSupport
    (H : SimpleGraph G.V) (C : H.ConnectedComponent) : Fintype C :=
  @Subtype.fintype G.V (fun v ↦ v ∈ C.supp)
    (switchDecidableSetMembership G C.supp) G.instFintypeV

/-- Three pairwise distinct active vertices cannot lie in one two-colour
component. -/
theorem not_three_active_in_one_twoColorComponent
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    (hproper : G.IsProperOn F color) {a b : Fin k}
    {x y z : G.V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : G.IsTwoColorActive F color a b x)
    (hy : G.IsTwoColorActive F color a b y)
    (hz : G.IsTwoColorActive F color a b z)
    (hycomponent :
      (G.twoColorGraph F color a b).connectedComponentMk y =
        (G.twoColorGraph F color a b).connectedComponentMk x)
    (hzcomponent :
      (G.twoColorGraph F color a b).connectedComponentMk z =
        (G.twoColorGraph F color a b).connectedComponentMk x) :
    False := by
  classical
  let H := G.twoColorGraph F color a b
  let C : H.ConnectedComponent := H.connectedComponentMk x
  have hxC : x ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hyC : y ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    simpa [C, H] using hycomponent
  have hzC : z ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    simpa [C, H] using hzcomponent
  let X : C := ⟨x, hxC⟩
  let Y : C := ⟨y, hyC⟩
  let Z : C := ⟨z, hzC⟩
  have hXY : X ≠ Y := by
    intro h
    exact hxy (congrArg Subtype.val h)
  have hXZ : X ≠ Z := by
    intro h
    exact hxz (congrArg Subtype.val h)
  have hYZ : Y ≠ Z := by
    intro h
    exact hyz (congrArg Subtype.val h)
  let active : Finset C :=
    (Finset.univ : Finset C).filter fun v ↦
      G.IsTwoColorActive F color a b v.1
  have hthree : ({X, Y, Z} : Finset C) ⊆ active := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
  have hcardThree : ({X, Y, Z} : Finset C).card = 3 := by
    simp [hXY, hXZ, hYZ]
  have hge : 3 ≤ active.card := by
    rw [← hcardThree]
    exact Finset.card_le_card hthree
  have hle : active.card ≤ 2 := by
    simpa [active, C, H] using
      G.card_activeVertices_twoColorComponent_le_two
        F color hproper a b C
  omega

/-- A component switch in colours `c,f` preserves the missing indicator of
every third colour. -/
theorem mem_missingColorsAt_kempeComponentSwitch_of_fixedColor_iff
    {F : Finset G.E} {k : ℕ} (color : G.E → Fin k)
    (c f : Fin k)
    (flip : G.TwoColorComponent F color c f → Prop)
    [DecidablePred flip] (v : G.V) (d : Fin k)
    (hdc : d ≠ c) (hdf : d ≠ f) :
    d ∈ G.missingColorsAt F
        (G.kempeComponentSwitch F color c f flip) v ↔
      d ∈ G.missingColorsAt F color v := by
  have h := G.mem_missingColorsAt_kempeComponentSwitch_localPerm_iff
    F color c f flip v d
  have hfixed : G.kempeLocalPerm F color c f flip v d = d := by
    simp only [kempeLocalPerm]
    split
    · exact Equiv.swap_apply_of_ne_of_ne hdc hdf
    · rfl
  simpa [hfixed] using h

/-- On every edge whose old colour is neither switched colour, a Kempe
component switch leaves the colour unchanged. -/
theorem kempeComponentSwitch_eq_of_color_ne
    {F : Finset G.E} {k : ℕ} (color : G.E → Fin k)
    (c f : Fin k)
    (flip : G.TwoColorComponent F color c f → Prop)
    [DecidablePred flip] (g : G.E)
    (hgc : color g ≠ c) (hgf : color g ≠ f) :
    G.kempeComponentSwitch F color c f flip g = color g := by
  simp [kempeComponentSwitch, hgc, hgf]

/-- A switch in `c,f` produces a fixed third colour `d` exactly on the
edges that already had colour `d`. -/
theorem kempeComponentSwitch_eq_fixedColor_iff
    {F : Finset G.E} {k : ℕ} (color : G.E → Fin k)
    (c f : Fin k)
    (flip : G.TwoColorComponent F color c f → Prop)
    [DecidablePred flip] (d : Fin k)
    (hdc : d ≠ c) (hdf : d ≠ f) (g : G.E) :
    G.kempeComponentSwitch F color c f flip g = d ↔ color g = d := by
  classical
  by_cases hgF : g ∈ F
  · let pi := G.kempeLocalPerm F color c f flip (G.fst g)
    have hlocal : G.kempeComponentSwitch F color c f flip g =
        pi (color g) := by
      exact G.kempeComponentSwitch_eq_localPerm
        F color c f flip hgF (Or.inl rfl)
    have hfixed : pi d = d := by
      dsimp [pi]
      simp only [kempeLocalPerm]
      split
      · exact Equiv.swap_apply_of_ne_of_ne hdc hdf
      · rfl
    rw [hlocal]
    constructor
    · intro h
      apply pi.injective
      simpa [hfixed] using h
    · intro h
      rw [h, hfixed]
  · simp [kempeComponentSwitch, hgF]

/-- Switching two colours leaves every two-colour graph formed by two
other colours unchanged. -/
theorem twoColorGraph_kempeComponentSwitch_eq_of_fixedColors
    {F : Finset G.E} {k : ℕ} (color : G.E → Fin k)
    (c f : Fin k)
    (flip : G.TwoColorComponent F color c f → Prop)
    [DecidablePred flip] (a b : Fin k)
    (hac : a ≠ c) (haf : a ≠ f)
    (hbc : b ≠ c) (hbf : b ≠ f) :
    G.twoColorGraph F (G.kempeComponentSwitch F color c f flip) a b =
      G.twoColorGraph F color a b := by
  ext x y
  constructor
  · rintro ⟨hxy, hrel | hrel⟩
    · refine ⟨hxy, Or.inl ?_⟩
      rcases hrel with ⟨g, hgF, hgx, hgy, hga | hgb⟩
      · exact ⟨g, hgF, hgx, hgy, Or.inl
          ((G.kempeComponentSwitch_eq_fixedColor_iff
            color c f flip a hac haf g).mp hga)⟩
      · exact ⟨g, hgF, hgx, hgy, Or.inr
          ((G.kempeComponentSwitch_eq_fixedColor_iff
            color c f flip b hbc hbf g).mp hgb)⟩
    · refine ⟨hxy, Or.inr ?_⟩
      rcases hrel with ⟨g, hgF, hgy, hgx, hga | hgb⟩
      · exact ⟨g, hgF, hgy, hgx, Or.inl
          ((G.kempeComponentSwitch_eq_fixedColor_iff
            color c f flip a hac haf g).mp hga)⟩
      · exact ⟨g, hgF, hgy, hgx, Or.inr
          ((G.kempeComponentSwitch_eq_fixedColor_iff
            color c f flip b hbc hbf g).mp hgb)⟩
  · rintro ⟨hxy, hrel | hrel⟩
    · refine ⟨hxy, Or.inl ?_⟩
      rcases hrel with ⟨g, hgF, hgx, hgy, hga | hgb⟩
      · exact ⟨g, hgF, hgx, hgy, Or.inl
          ((G.kempeComponentSwitch_eq_fixedColor_iff
            color c f flip a hac haf g).mpr hga)⟩
      · exact ⟨g, hgF, hgx, hgy, Or.inr
          ((G.kempeComponentSwitch_eq_fixedColor_iff
            color c f flip b hbc hbf g).mpr hgb)⟩
    · refine ⟨hxy, Or.inr ?_⟩
      rcases hrel with ⟨g, hgF, hgy, hgx, hga | hgb⟩
      · exact ⟨g, hgF, hgy, hgx, Or.inl
          ((G.kempeComponentSwitch_eq_fixedColor_iff
            color c f flip a hac haf g).mpr hga)⟩
      · exact ⟨g, hgF, hgy, hgx, Or.inr
          ((G.kempeComponentSwitch_eq_fixedColor_iff
            color c f flip b hbc hbf g).mpr hgb)⟩

/-- The local propagation switch used in Andersen's Lemma 3. -/
theorem exists_kempeSwitch_propagating_common_missingColor
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    (hproper : G.IsProperOn F color)
    {c f : Fin k} {u v z : G.V}
    (huv : u ≠ v) (huz : u ≠ z) (hvz : v ≠ z)
    (huc : c ∈ G.missingColorsAt F color u)
    (hvc : c ∈ G.missingColorsAt F color v)
    (hzf : f ∈ G.missingColorsAt F color z)
    (hzc : c ∉ G.missingColorsAt F color z) :
    ∃ switched : G.E → Fin k,
      G.IsProperOn F switched ∧
      c ∈ G.missingColorsAt F switched z ∧
      (c ∈ G.missingColorsAt F switched u ∨
        c ∈ G.missingColorsAt F switched v) ∧
      (∀ d w, d ≠ c → d ≠ f →
        (d ∈ G.missingColorsAt F switched w ↔
          d ∈ G.missingColorsAt F color w)) ∧
      (∀ a b, a ≠ c → a ≠ f → b ≠ c → b ≠ f →
        G.twoColorGraph F switched a b =
          G.twoColorGraph F color a b) := by
  classical
  let H := G.twoColorGraph F color c f
  let Cz : H.ConnectedComponent := H.connectedComponentMk z
  let flip : H.ConnectedComponent → Prop := fun C ↦ C = Cz
  let switched : G.E → Fin k :=
    G.kempeComponentSwitch F color c f flip
  have hproperSwitched : G.IsProperOn F switched := by
    exact G.isProperOn_kempeComponentSwitch F color hproper c f flip
  have hzFlip : flip (H.connectedComponentMk z) := by rfl
  have hzcNew : c ∈ G.missingColorsAt F switched z := by
    have hiff :=
      (G.mem_missingColorsAt_kempeComponentSwitch_of_flip
        F color c f flip z hzFlip).2
    exact hiff.mpr hzf
  have hfixedMissing : ∀ d w, d ≠ c → d ≠ f →
      (d ∈ G.missingColorsAt F switched w ↔
        d ∈ G.missingColorsAt F color w) := by
    intro d w hdc hdf
    exact G.mem_missingColorsAt_kempeComponentSwitch_of_fixedColor_iff
      color c f flip w d hdc hdf
  have hfixedGraph : ∀ a b, a ≠ c → a ≠ f → b ≠ c → b ≠ f →
      G.twoColorGraph F switched a b =
        G.twoColorGraph F color a b := by
    intro a b hac haf hbc hbf
    exact G.twoColorGraph_kempeComponentSwitch_eq_of_fixedColors
      color c f flip a b hac haf hbc hbf
  by_cases huFlip : flip (H.connectedComponentMk u)
  · have hucomponent : H.connectedComponentMk u = H.connectedComponentMk z := by
      simpa [flip, Cz] using huFlip
    have huf : f ∉ G.missingColorsAt F color u := by
      intro huf
      have := G.eq_of_same_twoColorComponent_of_both_missing
        hucomponent huc huf
      exact huz this
    have huActive : G.IsTwoColorActive F color c f u :=
      Or.inl ⟨huc, huf⟩
    have hzActive : G.IsTwoColorActive F color c f z :=
      Or.inr ⟨hzf, hzc⟩
    have hvNotFlip : ¬flip (H.connectedComponentMk v) := by
      intro hvFlip
      have hvcomponent :
          H.connectedComponentMk v = H.connectedComponentMk z := by
        simpa [flip, Cz] using hvFlip
      have hvf : f ∉ G.missingColorsAt F color v := by
        intro hvf
        have := G.eq_of_same_twoColorComponent_of_both_missing
          hvcomponent hvc hvf
        exact hvz this
      have hvActive : G.IsTwoColorActive F color c f v :=
        Or.inl ⟨hvc, hvf⟩
      exact G.not_three_active_in_one_twoColorComponent
        hproper huv huz hvz huActive hvActive hzActive
        (hvcomponent.trans hucomponent.symm) hucomponent.symm
    have hvcNew : c ∈ G.missingColorsAt F switched v := by
      exact (G.mem_missingColorsAt_kempeComponentSwitch_of_not_flip_iff
        F color c f flip v hvNotFlip c).mpr hvc
    exact ⟨switched, hproperSwitched, hzcNew, Or.inr hvcNew,
      hfixedMissing, hfixedGraph⟩
  · have hucNew : c ∈ G.missingColorsAt F switched u := by
      exact (G.mem_missingColorsAt_kempeComponentSwitch_of_not_flip_iff
        F color c f flip u huFlip c).mpr huc
    exact ⟨switched, hproperSwitched, hzcNew, Or.inl hucNew,
      hfixedMissing, hfixedGraph⟩

/-- Critical-chain form of the propagation switch.  At a non-endpoint
chain vertex `z`, a missing colour `f` can be chosen away from the two chain
colours.  The `(c,f)` switch therefore preserves the entire `(a,b)` chain,
including the endpoint missing colours. -/
theorem exists_criticalChainSwitch_propagating_common_missingColor
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    {u v z : G.V}
    (huv : u ≠ v) (huz : u ≠ z) (hvz : v ≠ z)
    (hucomponent :
      (G.twoColorGraph (F.erase e) color a b).connectedComponentMk u =
        (G.twoColorGraph (F.erase e) color a b).connectedComponentMk
          (G.fst e))
    (hvcomponent :
      (G.twoColorGraph (F.erase e) color a b).connectedComponentMk v =
        (G.twoColorGraph (F.erase e) color a b).connectedComponentMk
          (G.fst e))
    (hzcomponent :
      (G.twoColorGraph (F.erase e) color a b).connectedComponentMk z =
        (G.twoColorGraph (F.erase e) color a b).connectedComponentMk
          (G.fst e))
    (hzfst : z ≠ G.fst e) (hzsnd : z ≠ G.snd e)
    {c : Fin k}
    (huc : c ∈ G.missingColorsAt (F.erase e) color u)
    (hvc : c ∈ G.missingColorsAt (F.erase e) color v)
    (hzc : c ∉ G.missingColorsAt (F.erase e) color z)
    (hdegree : G.degreeOn (F.erase e) z < k) :
    ∃ switched : G.E → Fin k,
      G.IsProperOn (F.erase e) switched ∧
      a ∈ G.missingColorsAt (F.erase e) switched (G.fst e) ∧
      b ∈ G.missingColorsAt (F.erase e) switched (G.snd e) ∧
      G.twoColorGraph (F.erase e) switched a b =
        G.twoColorGraph (F.erase e) color a b ∧
      c ∈ G.missingColorsAt (F.erase e) switched z ∧
      (c ∈ G.missingColorsAt (F.erase e) switched u ∨
        c ∈ G.missingColorsAt (F.erase e) switched v) := by
  have hca : c ≠ a := by
    intro h
    subst c
    have huEq := G.eq_fst_of_mem_missing_chain_leftColor
      hcritical heF hproper ha hb hucomponent huc
    have hvEq := G.eq_fst_of_mem_missing_chain_leftColor
      hcritical heF hproper ha hb hvcomponent hvc
    exact huv (huEq.trans hvEq.symm)
  have hcb : c ≠ b := by
    intro h
    subst c
    have huEq := G.eq_snd_of_mem_missing_chain_rightColor
      hcritical heF hproper ha hb hucomponent huc
    have hvEq := G.eq_snd_of_mem_missing_chain_rightColor
      hcritical heF hproper ha hb hvcomponent hvc
    exact huv (huEq.trans hvEq.symm)
  obtain ⟨f, hzf⟩ :=
    G.exists_mem_missingColorsAt_of_degreeOn_lt hproper hdegree
  have huses := G.critical_chain_internal_uses_both
    hcritical heF hproper ha hb hzcomponent hzfst hzsnd
  have hfa : f ≠ a := by
    intro h
    subst f
    exact huses.1 hzf
  have hfb : f ≠ b := by
    intro h
    subst f
    exact huses.2 hzf
  obtain ⟨switched, hproperSwitched, hzcNew, hcommon,
      hfixedMissing, hfixedGraph⟩ :=
    G.exists_kempeSwitch_propagating_common_missingColor
      hproper huv huz hvz huc hvc hzf hzc
  have haNew :
      a ∈ G.missingColorsAt (F.erase e) switched (G.fst e) :=
    (hfixedMissing a (G.fst e) hca.symm hfa.symm).mpr ha
  have hbNew :
      b ∈ G.missingColorsAt (F.erase e) switched (G.snd e) :=
    (hfixedMissing b (G.snd e) hcb.symm hfb.symm).mpr hb
  have hgraph := hfixedGraph a b hca.symm hfa.symm hcb.symm hfb.symm
  exact ⟨switched, hproperSwitched, haNew, hbNew, hgraph,
    hzcNew, hcommon⟩

end WeightedMultigraph
end WeightedEdgeColoring
