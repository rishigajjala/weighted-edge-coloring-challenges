import WeightedEdgeColoring.BPOrdinaryCriticalTriangleMiddle
import WeightedEdgeColoring.BPOrdinaryKempeActiveTree
import WeightedEdgeColoring.SimpleGraphRedundantEdgeReachable

/-!
# The two-colour graph after shifting the omitted triangle edge

This file isolates the graph comparison used in the last part of
Andersen's three-vertex argument.  The old `b,c` component is cut at the
unique `b`-edge `xz`; shifting the omitted edge colours `xy` with `b`.
Thus the new two-colour graph is contained in the cut graph with the one
new simple edge `xy` added.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Graph comparison for a shift `xy -> xz`.  The hypothesis on colour
`c` is needed only to say that deleting the simple adjacency `xz` really
removes every old `b,c` witness between those two vertices. -/
theorem twoColorGraph_shiftOmitted_le_cut_sup_edge
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {e g : G.E} (heF : e ∈ F) (hgFe : g ∈ F.erase e)
    (hproper : G.IsProperOn (F.erase e) color)
    {b c : Fin k} (hgb : color g = b)
    {z : G.V} (hgx : G.Inc (G.fst e) g) (hgz : G.Inc z g)
    (hxz : G.fst e ≠ z)
    (hnoC : ∀ r, r ∈ F.erase e → G.Inc (G.fst e) r →
      G.Inc z r → color r ≠ c) :
    G.twoColorGraph (F.erase g) (G.assignEdgeColor color e b) b c ≤
      (G.twoColorGraph (F.erase e) color b c).deleteEdges
          {s(G.fst e, z)} ⊔
        SimpleGraph.edge (G.fst e) (G.snd e) := by
  classical
  intro u v huv
  rcases G.exists_twoColorWitnessEdge (F.erase g)
      (G.assignEdgeColor color e b) b c huv with
    ⟨r, hrFg, hru, hrv, hrNew⟩
  by_cases hre : r = e
  · subst r
    have hEdge :
        (SimpleGraph.edge (G.fst e) (G.snd e)).Adj u v := by
      rcases hru with hfu | hsu <;> rcases hrv with hfv | hsv
      · exact False.elim (huv.ne (hfu.symm.trans hfv))
      · rw [SimpleGraph.edge_adj]
        exact ⟨Or.inl ⟨hfu.symm, hsv.symm⟩, huv.ne⟩
      · rw [SimpleGraph.edge_adj]
        exact ⟨Or.inr ⟨hsu.symm, hfv.symm⟩, huv.ne⟩
      · exact False.elim (huv.ne (hsu.symm.trans hsv))
    rw [SimpleGraph.sup_adj]
    exact Or.inr hEdge
  · rw [SimpleGraph.sup_adj]
    apply Or.inl
    have hrF : r ∈ F := (Finset.mem_erase.mp hrFg).2
    have hrg : r ≠ g := (Finset.mem_erase.mp hrFg).1
    have hrFe : r ∈ F.erase e := Finset.mem_erase.mpr ⟨hre, hrF⟩
    have hrOld : color r = b ∨ color r = c := by
      simpa [G.assignEdgeColor_of_ne color hre b] using hrNew
    have hOldAdj :
        (G.twoColorGraph (F.erase e) color b c).Adj u v := by
      have hfg := G.twoColorGraph_adj_fst_snd
        (F.erase e) color b c hrFe hrOld
      rcases hru with hfu | hsu <;> rcases hrv with hfv | hsv
      · exact False.elim (huv.ne (hfu.symm.trans hfv))
      · simpa [hfu, hsv] using hfg
      · simpa [hsu, hfv] using hfg.symm
      · exact False.elim (huv.ne (hsu.symm.trans hsv))
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hOldAdj, ?_⟩
    intro hpairs
    rcases Sym2.eq_iff.mp hpairs with hdirect | hswap
    · have hrx : G.Inc (G.fst e) r := by
        simpa [hdirect.1] using hru
      have hrz : G.Inc z r := by simpa [hdirect.2] using hrv
      rcases hrOld with hrb | hrc
      · have hrEq : r = g := by
          have hrmem : r ∈ ((F.erase e).filter (G.Inc (G.fst e)) : Set G.E) :=
            Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrFe, hrx⟩)
          have hgmem : g ∈ ((F.erase e).filter (G.Inc (G.fst e)) : Set G.E) :=
            Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgFe, hgx⟩)
          exact hproper (G.fst e) hrmem hgmem (hrb.trans hgb.symm)
        exact hrg hrEq
      · exact (hnoC r hrFe hrx hrz) hrc
    · have hrx : G.Inc (G.fst e) r := by
        simpa [hswap.2] using hrv
      have hrz : G.Inc z r := by simpa [hswap.1] using hru
      rcases hrOld with hrb | hrc
      · have hrEq : r = g := by
          have hrmem : r ∈ ((F.erase e).filter (G.Inc (G.fst e)) : Set G.E) :=
            Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrFe, hrx⟩)
          have hgmem : g ∈ ((F.erase e).filter (G.Inc (G.fst e)) : Set G.E) :=
            Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgFe, hgx⟩)
          exact hproper (G.fst e) hrmem hgmem (hrb.trans hgb.symm)
        exact hrg hrEq
      · exact (hnoC r hrFe hrx hrz) hrc

/-- Endpoint-free version of the shifted-graph comparison. -/
theorem twoColorGraph_shiftOmitted_le_cut_sup_edge_at
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {e g : G.E} (heF : e ∈ F) (hgFe : g ∈ F.erase e)
    (hproper : G.IsProperOn (F.erase e) color)
    {b c : Fin k} (hgb : color g = b)
    {x y z : G.V} (hxy : x ≠ y) (hxz : x ≠ z)
    (hxe : G.Inc x e) (hye : G.Inc y e)
    (hgx : G.Inc x g) (hgz : G.Inc z g)
    (hnoC : ∀ r, r ∈ F.erase e → G.Inc x r →
      G.Inc z r → color r ≠ c) :
    G.twoColorGraph (F.erase g) (G.assignEdgeColor color e b) b c ≤
      (G.twoColorGraph (F.erase e) color b c).deleteEdges
          {s(x, z)} ⊔ SimpleGraph.edge x y := by
  classical
  intro u v huv
  rcases G.exists_twoColorWitnessEdge (F.erase g)
      (G.assignEdgeColor color e b) b c huv with
    ⟨r, hrFg, hru, hrv, hrNew⟩
  by_cases hre : r = e
  · subst r
    have hEdge : (SimpleGraph.edge x y).Adj u v := by
      rcases hru with hfu | hsu <;> rcases hrv with hfv | hsv
      · exact False.elim (huv.ne (hfu.symm.trans hfv))
      · rcases hxe with hfx | hsx <;> rcases hye with hfy | hsy
        · exact False.elim (hxy (hfx.symm.trans hfy))
        · rw [SimpleGraph.edge_adj]
          exact ⟨Or.inl ⟨hfu.symm.trans hfx, hsv.symm.trans hsy⟩, huv.ne⟩
        · rw [SimpleGraph.edge_adj]
          exact ⟨Or.inr ⟨hfu.symm.trans hfy, hsv.symm.trans hsx⟩, huv.ne⟩
        · exact False.elim (hxy (hsx.symm.trans hsy))
      · rcases hxe with hfx | hsx <;> rcases hye with hfy | hsy
        · exact False.elim (hxy (hfx.symm.trans hfy))
        · rw [SimpleGraph.edge_adj]
          exact ⟨Or.inr ⟨hsu.symm.trans hsy, hfv.symm.trans hfx⟩, huv.ne⟩
        · rw [SimpleGraph.edge_adj]
          exact ⟨Or.inl ⟨hsu.symm.trans hsx, hfv.symm.trans hfy⟩, huv.ne⟩
        · exact False.elim (hxy (hsx.symm.trans hsy))
      · exact False.elim (huv.ne (hsu.symm.trans hsv))
    rw [SimpleGraph.sup_adj]
    exact Or.inr hEdge
  · have hrF : r ∈ F := (Finset.mem_erase.mp hrFg).2
    have hrg : r ≠ g := (Finset.mem_erase.mp hrFg).1
    have hrFe : r ∈ F.erase e := Finset.mem_erase.mpr ⟨hre, hrF⟩
    have hrOld : color r = b ∨ color r = c := by
      simpa [G.assignEdgeColor_of_ne color hre b] using hrNew
    have hOldAdj :
        (G.twoColorGraph (F.erase e) color b c).Adj u v := by
      have hfg := G.twoColorGraph_adj_fst_snd
        (F.erase e) color b c hrFe hrOld
      rcases hru with hfu | hsu <;> rcases hrv with hfv | hsv
      · exact False.elim (huv.ne (hfu.symm.trans hfv))
      · simpa [hfu, hsv] using hfg
      · simpa [hsu, hfv] using hfg.symm
      · exact False.elim (huv.ne (hsu.symm.trans hsv))
    rw [SimpleGraph.sup_adj]
    apply Or.inl
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hOldAdj, ?_⟩
    intro hpairs
    rcases Sym2.eq_iff.mp hpairs with hdirect | hswap
    · have hrx : G.Inc x r := by simpa [hdirect.1] using hru
      have hrz : G.Inc z r := by simpa [hdirect.2] using hrv
      rcases hrOld with hrb | hrc
      · have hrEq : r = g := by
          have hrmem : r ∈ ((F.erase e).filter (G.Inc x) : Set G.E) :=
            Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrFe, hrx⟩)
          have hgmem : g ∈ ((F.erase e).filter (G.Inc x) : Set G.E) :=
            Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgFe, hgx⟩)
          exact hproper x hrmem hgmem (hrb.trans hgb.symm)
        exact hrg hrEq
      · exact (hnoC r hrFe hrx hrz) hrc
    · have hrx : G.Inc x r := by simpa [hswap.2] using hrv
      have hrz : G.Inc z r := by simpa [hswap.1] using hru
      rcases hrOld with hrb | hrc
      · have hrEq : r = g := by
          have hrmem : r ∈ ((F.erase e).filter (G.Inc x) : Set G.E) :=
            Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hrFe, hrx⟩)
          have hgmem : g ∈ ((F.erase e).filter (G.Inc x) : Set G.E) :=
            Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hgFe, hgx⟩)
          exact hproper x hrmem hgmem (hrb.trans hgb.symm)
        exact hrg hrEq
      · exact (hnoC r hrFe hrx hrz) hrc

end WeightedMultigraph
end WeightedEdgeColoring
