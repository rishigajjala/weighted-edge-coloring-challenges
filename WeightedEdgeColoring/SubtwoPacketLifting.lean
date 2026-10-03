import WeightedEdgeColoring.SubtwoContraction
import WeightedEdgeColoring.GeneralPacketization

/-!
# Lifting quotient packet colors to physical weighted edges

A proper coloring of selected crossing packets gives a feasible weighted
coloring of their physical edges. At each contracted block, each such
color meets exactly one original endpoint whenever it is used.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

def subtwoCrossingSelectedEdges (block : G.V → Q) (F : Finset G.E) :
    Finset G.E :=
  F.filter fun e ↦ block (G.fst e) ≠ block (G.snd e)

def subtwoQuotientSelectedEdges (block : G.V → Q) (F : Finset G.E) :
    Finset (G.subtwoQuotient block).E :=
  Finset.univ.filter fun e ↦ e.1 ∈ F

def subtwoLiftQuotientColor {k : ℕ} (hk : 0 < k)
    (block : G.V → Q) (color : (G.subtwoQuotient block).E → Fin k) :
    G.E → Fin k :=
  fun e ↦ if h : block (G.fst e) ≠ block (G.snd e)
    then color ⟨e, h⟩ else ⟨0, hk⟩

theorem subtwo_same_quotient_color_edges_eq
    {k : ℕ} (hk : 0 < k) (block : G.V → Q) (F : Finset G.E)
    (color : (G.subtwoQuotient block).E → Fin k)
    (hproper : (G.subtwoQuotient block).IsProperOn
      (G.subtwoQuotientSelectedEdges block F) color)
    {e f : G.E}
    (he : e ∈ G.subtwoCrossingSelectedEdges block F)
    (hf : f ∈ G.subtwoCrossingSelectedEdges block F)
    {q : Q}
    (heq : block (G.fst e) = q ∨ block (G.snd e) = q)
    (hfq : block (G.fst f) = q ∨ block (G.snd f) = q)
    (hcolor : G.subtwoLiftQuotientColor hk block color e =
      G.subtwoLiftQuotientColor hk block color f) : e = f := by
  have hedata := Finset.mem_filter.mp he
  have hfdata := Finset.mem_filter.mp hf
  let e' : (G.subtwoQuotient block).E := ⟨e, hedata.2⟩
  let f' : (G.subtwoQuotient block).E := ⟨f, hfdata.2⟩
  have he' : e' ∈ G.subtwoQuotientSelectedEdges block F := by
    simp [subtwoQuotientSelectedEdges, e', hedata.1]
  have hf' : f' ∈ G.subtwoQuotientSelectedEdges block F := by
    simp [subtwoQuotientSelectedEdges, f', hfdata.1]
  have heq' : (G.subtwoQuotient block).Inc q e' := heq
  have hfq' : (G.subtwoQuotient block).Inc q f' := hfq
  have hc : color e' = color f' := by
    simpa [subtwoLiftQuotientColor, hedata.2, hfdata.2, e', f'] using hcolor
  have h := hproper q
    (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨he', heq'⟩))
    (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hf', hfq'⟩)) hc
  exact congrArg Subtype.val h

theorem subtwo_isProperOn_liftQuotientColor
    {k : ℕ} (hk : 0 < k) (block : G.V → Q) (F : Finset G.E)
    (color : (G.subtwoQuotient block).E → Fin k)
    (hproper : (G.subtwoQuotient block).IsProperOn
      (G.subtwoQuotientSelectedEdges block F) color) :
    G.IsProperOn (G.subtwoCrossingSelectedEdges block F)
      (G.subtwoLiftQuotientColor hk block color) := by
  intro v e he f hf hc
  have hedata := Finset.mem_filter.mp (Finset.mem_coe.mp he)
  have hfdata := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
  apply G.subtwo_same_quotient_color_edges_eq hk block F color hproper
    hedata.1 hfdata.1 (q := block v) _ _ hc
  · rcases hedata.2 with he | he
    · exact Or.inl (congrArg block he)
    · exact Or.inr (congrArg block he)
  · rcases hfdata.2 with hf | hf
    · exact Or.inl (congrArg block hf)
    · exact Or.inr (congrArg block hf)

namespace Packetization

variable {G} (P : G.Packetization)

/-- Expand a proper quotient packet coloring to a feasible coloring of the
physical edges of all selected crossing packets. -/
theorem subtwo_isFeasibleOn_expand_quotient
    {k : ℕ} (hk : 0 < k) (block : G.V → Q) (S : Finset P.Packet)
    (color : (P.groupedGraph.subtwoQuotient block).E → Fin k)
    (hproper : (P.groupedGraph.subtwoQuotient block).IsProperOn
      (P.groupedGraph.subtwoQuotientSelectedEdges block S) color) :
    G.IsFeasibleOn
      (P.originalEdgesOfPackets (P.groupedGraph.subtwoCrossingSelectedEdges block S))
      (P.expandColor (P.groupedGraph.subtwoLiftQuotientColor hk block color)) := by
  apply P.isFeasibleOn_originalEdgesOfPackets
  apply P.groupedGraph.isFeasibleOn_of_isProperOn
  exact P.groupedGraph.subtwo_isProperOn_liftQuotientColor
    hk block S color hproper

/-- At a block, a quotient packet color has a unique original endpoint.
Several physical edges may use it, but all of them use that same endpoint
inside the block. -/
theorem subtwo_expanded_quotient_color_endpoint_unique
    {k : ℕ} (hk : 0 < k) (block : G.V → Q) (S : Finset P.Packet)
    (color : (P.groupedGraph.subtwoQuotient block).E → Fin k)
    (hproper : (P.groupedGraph.subtwoQuotient block).IsProperOn
      (P.groupedGraph.subtwoQuotientSelectedEdges block S) color)
    {e f : G.E}
    (he : e ∈ P.originalEdgesOfPackets
      (P.groupedGraph.subtwoCrossingSelectedEdges block S))
    (hf : f ∈ P.originalEdgesOfPackets
      (P.groupedGraph.subtwoCrossingSelectedEdges block S))
    {v w : G.V} (hev : G.Inc v e) (hfw : G.Inc w f)
    (hblock : block v = block w)
    (hcolor : P.expandColor (P.groupedGraph.subtwoLiftQuotientColor hk block color) e =
      P.expandColor (P.groupedGraph.subtwoLiftQuotientColor hk block color) f) :
    v = w := by
  have heS := (Finset.mem_filter.mp he).2
  have hfS := (Finset.mem_filter.mp hf).2
  have heinc := (P.incidence v e).mpr hev
  have hfinc := (P.incidence w f).mpr hfw
  have heq : block (P.tail (P.packetOf e)) = block v ∨
      block (P.head (P.packetOf e)) = block v := by
    rcases heinc with h | h
    · exact Or.inl (congrArg block h)
    · exact Or.inr (congrArg block h)
  have hfq : block (P.tail (P.packetOf f)) = block v ∨
      block (P.head (P.packetOf f)) = block v := by
    rcases hfinc with h | h
    · exact Or.inl ((congrArg block h).trans hblock.symm)
    · exact Or.inr ((congrArg block h).trans hblock.symm)
  have hp : P.packetOf e = P.packetOf f :=
    P.groupedGraph.subtwo_same_quotient_color_edges_eq
      hk block S color hproper heS hfS heq hfq hcolor
  have hcross : block (P.tail (P.packetOf e)) ≠
      block (P.head (P.packetOf e)) := (Finset.mem_filter.mp heS).2
  rw [← hp] at hfinc
  rcases heinc with htv | hhv <;> rcases hfinc with htw | hhw
  · exact htv.symm.trans htw
  · exact False.elim (hcross (by rw [htv, hhw]; exact hblock))
  · exact False.elim (hcross (by rw [htw, hhv]; exact hblock.symm))
  · exact hhv.symm.trans hhw

end Packetization
end WeightedEdgeColoring.WeightedMultigraph
