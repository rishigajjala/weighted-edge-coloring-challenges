import WeightedEdgeColoring.BPOrdinaryCriticalRecolor

/-!
# The Kempe component of a critical edge

For a critical omitted edge `xy`, choose a colour missing at `x` and a
colour missing at `y`.  The two endpoints must lie in the same two-colour
component; otherwise switching the component of `x` creates a colour
missing at both endpoints and the omitted edge can be inserted.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- The endpoints of a critical omitted edge lie in one Kempe component
for every pair of endpoint-missing colours. -/
theorem critical_endpoints_same_twoColorComponent
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e)) :
    (G.twoColorGraph (F.erase e) color a b).connectedComponentMk (G.fst e) =
      (G.twoColorGraph (F.erase e) color a b).connectedComponentMk
        (G.snd e) := by
  classical
  by_contra hcomponents
  let H := G.twoColorGraph (F.erase e) color a b
  let Cx : H.ConnectedComponent := H.connectedComponentMk (G.fst e)
  let flip : H.ConnectedComponent → Prop := fun C ↦ C = Cx
  let switched : G.E → Fin k :=
    G.kempeComponentSwitch (F.erase e) color a b flip
  have hproperSwitched : G.IsProperOn (F.erase e) switched := by
    exact G.isProperOn_kempeComponentSwitch
      (F.erase e) color hproper a b flip
  have hxFlip : flip (H.connectedComponentMk (G.fst e)) := by
    rfl
  have hyNotFlip : ¬flip (H.connectedComponentMk (G.snd e)) := by
    intro hy
    apply hcomponents
    simpa [flip, Cx, H] using hy.symm
  have hbx : b ∈ G.missingColorsAt (F.erase e) switched (G.fst e) := by
    have hiff :=
      (G.mem_missingColorsAt_kempeComponentSwitch_of_flip
        (F.erase e) color a b flip (G.fst e) hxFlip).1
    exact hiff.mpr ha
  have hby : b ∈ G.missingColorsAt (F.erase e) switched (G.snd e) := by
    have hiff :=
      G.mem_missingColorsAt_kempeComponentSwitch_of_not_flip_iff
        (F.erase e) color a b flip (G.snd e) hyNotFlip b
    exact hiff.mpr hb
  apply hcritical.1
  exact ⟨G.assignEdgeColor switched e b,
    G.isProperOn_assignEdgeColor_of_missing_endpoints
      heF hproperSwitched hbx hby⟩

/-- The two endpoint colours in a critical chain are distinct. -/
theorem critical_endpoint_missingColors_ne
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e)) :
    a ≠ b := by
  intro hab
  subst b
  exact G.not_both_mem_missingColorsAt_endpoints_of_colorCritical
    hcritical heF hproper a ⟨ha, hb⟩

/-- Both endpoints are active vertices of their common critical
two-colour component, with opposite missing colours. -/
theorem critical_endpoints_twoColorActive
    {F : Finset G.E} {k : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e)) :
    G.IsTwoColorActive (F.erase e) color a b (G.fst e) ∧
      G.IsTwoColorActive (F.erase e) color a b (G.snd e) := by
  have hnotBx : b ∉ G.missingColorsAt (F.erase e) color (G.fst e) := by
    intro hbx
    exact G.not_both_mem_missingColorsAt_endpoints_of_colorCritical
      hcritical heF hproper b ⟨hbx, hb⟩
  have hnotAy : a ∉ G.missingColorsAt (F.erase e) color (G.snd e) := by
    intro hay
    exact G.not_both_mem_missingColorsAt_endpoints_of_colorCritical
      hcritical heF hproper a ⟨ha, hay⟩
  exact ⟨Or.inl ⟨ha, hnotBx⟩, Or.inr ⟨hb, hnotAy⟩⟩

end WeightedMultigraph
end WeightedEdgeColoring
