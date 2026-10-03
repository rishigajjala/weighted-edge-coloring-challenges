import WeightedEdgeColoring.SubtwoPacketLifting

/-!
# Original endpoint-label counts survive packet recoloring

A proper packet coloring uses distinct color names on the selected packets
at one contracted vertex. Therefore the number of colors carrying an
original endpoint label equals the number of packets with that label. Any
sequence of proper recolorings preserves these counts exactly.
-/

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u

variable (G : WeightedMultigraph.{u})
variable {L : Type*} [DecidableEq L]

noncomputable def subtwoUsedPacketLabelColors
    {q : ℕ} (F : Finset G.E) (color : G.E → Fin q)
    (label : G.V → G.E → L) (v : G.V) (l : L) : Finset (Fin q) :=
  (F.filter fun e => G.Inc v e ∧ label v e = l).image color

theorem card_subtwoUsedPacketLabelColors
    {q : ℕ} (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color)
    (label : G.V → G.E → L) (v : G.V) (l : L) :
    (G.subtwoUsedPacketLabelColors F color label v l).card =
      (F.filter fun e => G.Inc v e ∧ label v e = l).card := by
  classical
  apply Finset.card_image_iff.mpr
  intro e he f hf hc
  obtain ⟨heF, hev, _⟩ := Finset.mem_filter.mp he
  obtain ⟨hfF, hfv, _⟩ := Finset.mem_filter.mp hf
  exact hproper v (Finset.mem_filter.mpr ⟨heF, hev⟩)
    (Finset.mem_filter.mpr ⟨hfF, hfv⟩) hc

/-- Recoloring preserves every original endpoint-label count, even if
several labels occur at the same contracted vertex. -/
theorem subtwoPacketLabelCounts_invariant
    {q r : ℕ} (F : Finset G.E)
    (color : G.E → Fin q) (color' : G.E → Fin r)
    (hproper : G.IsProperOn F color) (hproper' : G.IsProperOn F color')
    (label : G.V → G.E → L) (v : G.V) (l : L) :
    (G.subtwoUsedPacketLabelColors F color label v l).card =
      (G.subtwoUsedPacketLabelColors F color' label v l).card := by
  rw [G.card_subtwoUsedPacketLabelColors F color hproper,
    G.card_subtwoUsedPacketLabelColors F color' hproper']

end
end WeightedEdgeColoring.WeightedMultigraph
