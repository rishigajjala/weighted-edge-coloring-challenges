import WeightedEdgeColoring.BPOrdinaryCriticalCore

/-!
# Recolouring one omitted critical edge

This file proves the first elementary step of the Andersen argument: the
missing palettes at the endpoints of an omitted critical edge are disjoint.
The proof explicitly inserts a common missing colour and uses no external
edge-colouring theorem.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Assign one chosen colour to one edge, leaving all other edge colours
unchanged. -/
def assignEdgeColor {k : ℕ} (color : G.E → Fin k) (e : G.E) (c : Fin k) :
    G.E → Fin k :=
  Function.update color e c

@[simp] theorem assignEdgeColor_self {k : ℕ} (color : G.E → Fin k)
    (e : G.E) (c : Fin k) : G.assignEdgeColor color e c e = c := by
  simp [assignEdgeColor]

theorem assignEdgeColor_of_ne {k : ℕ} (color : G.E → Fin k)
    {e f : G.E} (hef : f ≠ e) (c : Fin k) :
    G.assignEdgeColor color e c f = color f := by
  simp [assignEdgeColor, hef]

/-- If `e` is omitted from a proper colouring and `c` is missing wherever
`e` is incident, assigning `c` to `e` gives a proper colouring of `F`. -/
theorem isProperOn_assignEdgeColor
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {e : G.E} (heF : e ∈ F) (hproper : G.IsProperOn (F.erase e) color)
    {c : Fin k}
    (hmissing : ∀ v, G.Inc v e →
      c ∈ G.missingColorsAt (F.erase e) color v) :
    G.IsProperOn F (G.assignEdgeColor color e c) := by
  classical
  intro v f hf g hg hsame
  have hfData := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
  have hgData := Finset.mem_filter.mp (Finset.mem_coe.mp hg)
  by_cases hfe : f = e
  · subst f
    by_cases hge : g = e
    · exact hge.symm
    · have hgErase : g ∈ F.erase e := Finset.mem_erase.mpr ⟨hge, hgData.1⟩
      have hne : color g ≠ c :=
        G.color_ne_of_mem_missingColorsAt (F.erase e) color v c
          (hmissing v hfData.2) hgErase hgData.2
      have hcg : c = color g := by
        simpa [assignEdgeColor, hge] using hsame
      exact False.elim (hne hcg.symm)
  · by_cases hge : g = e
    · subst g
      have hfErase : f ∈ F.erase e := Finset.mem_erase.mpr ⟨hfe, hfData.1⟩
      have hne : color f ≠ c :=
        G.color_ne_of_mem_missingColorsAt (F.erase e) color v c
          (hmissing v hgData.2) hfErase hfData.2
      have hfc : color f = c := by
        simpa [assignEdgeColor, hfe] using hsame
      exact False.elim (hne hfc)
    · apply hproper v
      · exact Finset.mem_coe.mpr
          (Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨hfe, hfData.1⟩, hfData.2⟩)
      · exact Finset.mem_coe.mpr
          (Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨hge, hgData.1⟩, hgData.2⟩)
      simpa [assignEdgeColor, hfe, hge] using hsame

/-- Endpoint form of `isProperOn_assignEdgeColor`. -/
theorem isProperOn_assignEdgeColor_of_missing_endpoints
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k}
    {e : G.E} (heF : e ∈ F) (hproper : G.IsProperOn (F.erase e) color)
    {c : Fin k}
    (hfst : c ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hsnd : c ∈ G.missingColorsAt (F.erase e) color (G.snd e)) :
    G.IsProperOn F (G.assignEdgeColor color e c) := by
  apply G.isProperOn_assignEdgeColor heF hproper
  intro v hv
  rcases hv with h | h
  · simpa [h] using hfst
  · simpa [h] using hsnd

/-- The two endpoint missing palettes of a critical edge are disjoint. -/
theorem missingColorsAt_endpoints_disjoint_of_colorCritical
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color) :
    Disjoint
      (G.missingColorsAt (F.erase e) color (G.fst e))
      (G.missingColorsAt (F.erase e) color (G.snd e)) := by
  rw [Finset.disjoint_left]
  intro c hfst hsnd
  apply hcritical.1
  exact ⟨G.assignEdgeColor color e c,
    G.isProperOn_assignEdgeColor_of_missing_endpoints
      heF hproper hfst hsnd⟩

/-- In particular, no colour can be missing at both endpoints. -/
theorem not_both_mem_missingColorsAt_endpoints_of_colorCritical
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color) (c : Fin k) :
    ¬(c ∈ G.missingColorsAt (F.erase e) color (G.fst e) ∧
      c ∈ G.missingColorsAt (F.erase e) color (G.snd e)) := by
  intro hc
  have hd := G.missingColorsAt_endpoints_disjoint_of_colorCritical
    hcritical heF hproper
  exact (Finset.disjoint_left.mp hd) hc.1 hc.2

end WeightedMultigraph
end WeightedEdgeColoring
