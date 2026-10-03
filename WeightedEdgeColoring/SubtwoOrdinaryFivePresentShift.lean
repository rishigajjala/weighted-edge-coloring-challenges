import WeightedEdgeColoring.SubtwoOrdinaryFivePresent

/-!
# Transporting boundary edges through an omitted-edge shift

The five-cycle symmetry in Andersen's final saturation argument repeatedly
colors the old omitted edge and omits a different internal edge.  An edge
leaving the fixed five-vertex set is untouched by such a shift.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem external_colored_edge_transport_erase_swap
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {S : Finset G.V} {e g r : G.E} {a c : Fin k}
    (hr : r ∈ F.erase e) (hrExternal : r ∉ G.internalEdges (F.erase e) S)
    (hrColor : color r = c)
    (hgInternal : g ∈ G.internalEdges (F.erase e) S) :
    r ∈ F.erase g ∧
      G.assignEdgeColor color e a r = c ∧
      r ∉ G.internalEdges (F.erase g) S := by
  have hrNeG : r ≠ g := by
    intro h
    subst r
    exact hrExternal hgInternal
  have hrF : r ∈ F := (Finset.mem_erase.mp hr).2
  have hrNew : r ∈ F.erase g := Finset.mem_erase.mpr ⟨hrNeG, hrF⟩
  refine ⟨hrNew, ?_, ?_⟩
  · simpa [G.assignEdgeColor_of_ne color (Finset.mem_erase.mp hr).1 a]
      using hrColor
  · intro hrInternal
    apply hrExternal
    simp only [internalEdges, Finset.mem_filter] at hrInternal ⊢
    exact ⟨hr, hrInternal.2⟩

/-- A boundary-color pair at `Z₃,Y` becomes a pair at the endpoints after
shifting the omitted edge from `X,Y` to the last path edge. -/
theorem external_endpoint_pair_of_shifted_last_edge_fivePath
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b c : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    {g r s : G.E} (hgF : g ∈ F.erase e)
    (hgZ : G.Inc (p.1.getVert 3) g)
    (hgY : G.Inc (G.snd e) g) (hga : color g = a)
    (hrF : r ∈ F.erase e) (hrZ : G.Inc (p.1.getVert 3) r)
    (hrColor : color r = c)
    (hrExternal : r ∉ G.internalEdges (F.erase e) p.1.support.toFinset)
    (hsF : s ∈ F.erase e) (hsY : G.Inc (G.snd e) s)
    (hsColor : color s = c)
    (hsExternal : s ∉ G.internalEdges (F.erase e) p.1.support.toFinset) :
    ∃ q : (G.twoColorGraph (F.erase g)
      (G.assignEdgeColor color e a) a b).Path
        (p.1.getVert 3) (G.snd e),
      q.1.length = 4 ∧
      q.1.support.toFinset = p.1.support.toFinset ∧
      r ∈ F.erase g ∧ G.Inc (q.1.getVert 0) r ∧
      G.assignEdgeColor color e a r = c ∧
      r ∉ G.internalEdges (F.erase g) q.1.support.toFinset ∧
      s ∈ F.erase g ∧ G.Inc (q.1.getVert 4) s ∧
      G.assignEdgeColor color e a s = c ∧
      s ∉ G.internalEdges (F.erase g) q.1.support.toFinset := by
  have hgInternal : g ∈ G.internalEdges (F.erase e) p.1.support.toFinset := by
    have hZY : p.1.getVert 3 ≠ G.snd e := by
      intro h
      have h4 : p.1.getVert 4 = G.snd e := by
        simpa [hpLen] using p.1.getVert_length
      exact (by decide : (3 : ℕ) ≠ 4)
        (p.property.getVert_injOn
          (Set.mem_Iic.mpr (by omega))
          (Set.mem_Iic.mpr (by omega)) (h.trans h4.symm))
    have hends := G.endpoint_eq_or_endpoint_eq_swap_of_inc hZY hgZ hgY
    have hZmem : p.1.getVert 3 ∈ p.1.support.toFinset := by
      simpa only [List.mem_toFinset] using p.1.getVert_mem_support 3
    have hYmem : G.snd e ∈ p.1.support.toFinset := by
      simpa only [List.mem_toFinset] using p.1.end_mem_support
    simp only [internalEdges, Finset.mem_filter]
    rcases hends with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
    · exact ⟨hgF, hfst.symm ▸ hZmem, hsnd.symm ▸ hYmem⟩
    · exact ⟨hgF, hfst.symm ▸ hYmem, hsnd.symm ▸ hZmem⟩
  obtain ⟨q, hqLen, hqSupport⟩ :=
    G.exists_shifted_last_edge_fivePath
      hcritical heF hproper ha hb p hpLen hgF hgZ hga
  obtain ⟨hrNew, hrNewColor, hrNewExternal⟩ :=
    G.external_colored_edge_transport_erase_swap
      hrF hrExternal hrColor hgInternal
  obtain ⟨hsNew, hsNewColor, hsNewExternal⟩ :=
    G.external_colored_edge_transport_erase_swap
      hsF hsExternal hsColor hgInternal
  refine ⟨q, hqLen, hqSupport, hrNew, ?_, hrNewColor, ?_,
    hsNew, ?_, hsNewColor, ?_⟩
  · simpa using hrZ
  · simpa [hqSupport] using hrNewExternal
  · have hq4 : q.1.getVert 4 = G.snd e := by
      simpa [hqLen] using q.1.getVert_length
    simpa [hq4] using hsY
  · simpa [hqSupport] using hsNewExternal

end WeightedEdgeColoring.WeightedMultigraph
