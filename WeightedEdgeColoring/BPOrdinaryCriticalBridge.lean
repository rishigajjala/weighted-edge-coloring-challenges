import WeightedEdgeColoring.BPOrdinaryCriticalTree
import WeightedEdgeColoring.BPOrdinaryCriticalSwitch

/-!
# The bridge edge of a critical chain has one witness

An adjacency in the simple two-colour graph might a priori come from two
parallel original edges, one of each colour.  This cannot happen inside a
critical component.  Two such edges would use both colours at the vertex
and leave it only one simple neighbour, while every non-endpoint critical
chain vertex has degree two.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Removing selected edges can only enlarge the missing-colour set. -/
theorem mem_missingColorsAt_of_subset
    {F R : Finset G.E} (hRF : R ⊆ F)
    {k : ℕ} {color : G.E → Fin k} {v : G.V} {c : Fin k}
    (hc : c ∈ G.missingColorsAt F color v) :
    c ∈ G.missingColorsAt R color v := by
  classical
  simp only [missingColorsAt, Finset.mem_sdiff, Finset.mem_univ,
    true_and, Finset.mem_image] at hc ⊢
  intro hused
  rcases hused with ⟨g, hg, hgc⟩
  apply hc
  exact ⟨g, Finset.mem_filter.mpr
    ⟨hRF (Finset.mem_filter.mp hg).1, (Finset.mem_filter.mp hg).2⟩, hgc⟩

/-- Recolour an already selected edge with a colour missing at both of its
endpoints. -/
theorem isProperOn_replaceEdgeColor_of_missing_endpoints
    {R : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    (hproper : G.IsProperOn R color)
    {g : G.E} (hgR : g ∈ R) {c : Fin k}
    (hfst : c ∈ G.missingColorsAt R color (G.fst g))
    (hsnd : c ∈ G.missingColorsAt R color (G.snd g)) :
    G.IsProperOn R (G.assignEdgeColor color g c) := by
  have hproperErase : G.IsProperOn (R.erase g) color :=
    IsProperOn.mono G hproper (Finset.erase_subset g R)
  have hfstErase :
      c ∈ G.missingColorsAt (R.erase g) color (G.fst g) :=
    G.mem_missingColorsAt_of_subset (Finset.erase_subset g R) hfst
  have hsndErase :
      c ∈ G.missingColorsAt (R.erase g) color (G.snd g) :=
    G.mem_missingColorsAt_of_subset (Finset.erase_subset g R) hsnd
  exact G.isProperOn_assignEdgeColor_of_missing_endpoints
    hgR hproperErase hfstErase hsndErase

/-- Recolouring one edge with `c` preserves every missing third colour. -/
theorem mem_missingColorsAt_assignEdgeColor_of_ne
    {R : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {g : G.E} {c d : Fin k} (hdc : d ≠ c)
    {v : G.V} (hd : d ∈ G.missingColorsAt R color v) :
    d ∈ G.missingColorsAt R (G.assignEdgeColor color g c) v := by
  classical
  simp only [missingColorsAt, Finset.mem_sdiff, Finset.mem_univ,
    true_and, Finset.mem_image] at hd ⊢
  intro hused
  rcases hused with ⟨r, hr, hrd⟩
  have hrData := Finset.mem_filter.mp hr
  by_cases hrg : r = g
  · subst r
    have : c = d := by simpa using hrd
    exact hdc this.symm
  · apply hd
    refine ⟨r, hr, ?_⟩
    simpa [G.assignEdgeColor_of_ne color hrg c] using hrd

/-- If `g` is the unique old `a,b` witness between `u,v`, recolouring it
with a third colour deletes that simple adjacency and creates no new
`a,b` adjacency. -/
theorem twoColorGraph_assignEdgeColor_le_deleteEdges
    {R : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {a b c : Fin k} {u v : G.V} {g : G.E}
    (hca : c ≠ a) (hcb : c ≠ b)
    (hunique : ∀ r, r ∈ R → G.Inc u r → G.Inc v r →
      (color r = a ∨ color r = b) → r = g) :
    G.twoColorGraph R (G.assignEdgeColor color g c) a b ≤
      (G.twoColorGraph R color a b).deleteEdges {s(u, v)} := by
  classical
  intro x y hxy
  rcases G.exists_twoColorWitnessEdge R
      (G.assignEdgeColor color g c) a b hxy with
    ⟨r, hrR, hrx, hry, hrNewColor⟩
  have hrne : r ≠ g := by
    intro hrg
    subst r
    rcases hrNewColor with h | h
    · exact hca (by simpa using h)
    · exact hcb (by simpa using h)
  have hrOldColor : color r = a ∨ color r = b := by
    simpa [G.assignEdgeColor_of_ne color hrne c] using hrNewColor
  have hOldAdj : (G.twoColorGraph R color a b).Adj x y := by
    have hfg := G.twoColorGraph_adj_fst_snd R color a b hrR hrOldColor
    rcases hrx with hfx | hsx <;> rcases hry with hfy | hsy
    · exact False.elim (hxy.ne (hfx.symm.trans hfy))
    · simpa [hfx, hsy] using hfg
    · simpa [hsx, hfy] using hfg.symm
    · exact False.elim (hxy.ne (hsx.symm.trans hsy))
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨hOldAdj, ?_⟩
  intro hpairs
  rcases (Sym2.eq_iff.mp hpairs) with hdirect | hswap
  · have hru : G.Inc u r := by simpa [hdirect.1] using hrx
    have hrv : G.Inc v r := by simpa [hdirect.2] using hry
    exact hrne (hunique r hrR hru hrv hrOldColor)
  · have hru : G.Inc u r := by simpa [hswap.2] using hry
    have hrv : G.Inc v r := by simpa [hswap.1] using hrx
    exact hrne (hunique r hrR hru hrv hrOldColor)

/-- In a critical two-colour component, two selected edges with the same
two distinct endpoints and a chain colour must be the same indexed edge. -/
theorem critical_chain_adj_has_unique_witness
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    {u v : G.V} (huv : u ≠ v)
    (hucomponent :
      (G.twoColorGraph (F.erase e) color a b).connectedComponentMk u =
        (G.twoColorGraph (F.erase e) color a b).connectedComponentMk
          (G.fst e))
    {g h : G.E}
    (hgF : g ∈ F.erase e) (hhF : h ∈ F.erase e)
    (hgu : G.Inc u g) (hgv : G.Inc v g)
    (hhu : G.Inc u h) (hhv : G.Inc v h)
    (hgcolor : color g = a ∨ color g = b)
    (hhcolor : color h = a ∨ color h = b) :
    g = h := by
  classical
  have edge_eq_of_same_color {r s : G.E}
      (hrF : r ∈ F.erase e) (hsF : s ∈ F.erase e)
      (hru : G.Inc u r) (hsu : G.Inc u s)
      (hcolor : color r = color s) : r = s := by
    apply hproper u
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrF, hru⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hsF, hsu⟩)
    · exact hcolor
  by_cases hsame : color g = color h
  · exact edge_eq_of_same_color hgF hhF hgu hhu hsame
  have hab : a ≠ b :=
    G.critical_endpoint_missingColors_ne hcritical heF hproper ha hb
  have hedgeA :
      ∃ r, r ∈ F.erase e ∧ G.Inc u r ∧ G.Inc v r ∧ color r = a := by
    rcases hgcolor with hga | hgb <;> rcases hhcolor with hha | hhb
    · exact False.elim (hsame (hga.trans hha.symm))
    · exact ⟨g, hgF, hgu, hgv, hga⟩
    · exact ⟨h, hhF, hhu, hhv, hha⟩
    · exact False.elim (hsame (hgb.trans hhb.symm))
  have hedgeB :
      ∃ r, r ∈ F.erase e ∧ G.Inc u r ∧ G.Inc v r ∧ color r = b := by
    rcases hgcolor with hga | hgb <;> rcases hhcolor with hha | hhb
    · exact False.elim (hsame (hga.trans hha.symm))
    · exact ⟨h, hhF, hhu, hhv, hhb⟩
    · exact ⟨g, hgF, hgu, hgv, hgb⟩
    · exact False.elim (hsame (hgb.trans hhb.symm))
  obtain ⟨ga, hgaF, hgaU, hgaV, hgaColor⟩ := hedgeA
  obtain ⟨gb, hgbF, hgbU, hgbV, hgbColor⟩ := hedgeB
  have haUsed : a ∉ G.missingColorsAt (F.erase e) color u := by
    simpa [hgaColor] using
      (G.not_mem_missingColorsAt_of_used
        (base := color) hgaF hgaU)
  have hbUsed : b ∉ G.missingColorsAt (F.erase e) color u := by
    simpa [hgbColor] using
      (G.not_mem_missingColorsAt_of_used
        (base := color) hgbF hgbU)
  have huFst : u ≠ G.fst e := by
    intro h
    subst u
    exact haUsed ha
  have huSnd : u ≠ G.snd e := by
    intro h
    subst u
    exact hbUsed hb
  let H := G.twoColorGraph (F.erase e) color a b
  have huDegreeTwo : H.degree u = 2 := by
    exact G.critical_chain_internal_degree_eq_two
      hcritical heF hproper ha hb hucomponent huFst huSnd
  have huDegreeLeOne : H.degree u ≤ 1 := by
    rw [← H.card_neighborSet_eq_degree, Fintype.card_le_one_iff]
    intro w₁ w₂
    apply Subtype.ext
    have neighbor_eq_v (w : H.neighborSet u) : w.1 = v := by
      have hw := G.twoColorNeighborEdge_spec
        (F.erase e) color a b u w
      let r := G.twoColorNeighborEdge (F.erase e) color a b u w
      have hrEq : r = ga ∨ r = gb := by
        rcases hw.2.2.2 with hra | hrb
        · exact Or.inl (edge_eq_of_same_color hw.1 hgaF hw.2.1 hgaU
            (hra.trans hgaColor.symm))
        · exact Or.inr (edge_eq_of_same_color hw.1 hgbF hw.2.1 hgbU
            (hrb.trans hgbColor.symm))
      have hwAdj : H.Adj u w.1 := (H.mem_neighborSet u w.1).mp w.property
      have hrOther : G.kempeOtherEndpoint u r = w.1 :=
        G.kempeOtherEndpoint_eq_of_incident hw.2.1 hw.2.2.1 hwAdj.ne
      rcases hrEq with hr | hr
      · calc
          w.1 = G.kempeOtherEndpoint u r := hrOther.symm
          _ = G.kempeOtherEndpoint u ga := by rw [hr]
          _ = v := G.kempeOtherEndpoint_eq_of_incident hgaU hgaV huv
      · calc
          w.1 = G.kempeOtherEndpoint u r := hrOther.symm
          _ = G.kempeOtherEndpoint u gb := by rw [hr]
          _ = v := G.kempeOtherEndpoint_eq_of_incident hgbU hgbV huv
    exact (neighbor_eq_v w₁).trans (neighbor_eq_v w₂).symm
  omega

end WeightedMultigraph
end WeightedEdgeColoring
