import WeightedEdgeColoring.BPOrdinaryFiniteSearch
import WeightedEdgeColoring.KempeComponentEndpoints

/-!
# Minimal uncolourable ordinary edge sets

The Andersen argument starts by replacing an uncolourable finite edge set
with an inclusion-minimal one.  This file supplies that reduction in the
indexed-multigraph model and records the inherited degree and odd-set
bounds.  It contains no unproved graph-colouring input.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Every selected edge is critical for `k`-edge-colourability. -/
def IsColorCriticalOn (F : Finset G.E) (k : ℕ) : Prop :=
  (¬ G.HasProperColoringOn F k) ∧
    ∀ e ∈ F, G.HasProperColoringOn (F.erase e) k

/-- Properness restricts to a smaller selected edge set. -/
theorem IsProperOn.mono {F F' : Finset G.E} {k : ℕ}
    {color : G.E → Fin k} (hproper : G.IsProperOn F color)
    (hsub : F' ⊆ F) : G.IsProperOn F' color := by
  intro v
  apply (hproper v).mono
  intro e he
  have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
  exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hsub he'.1, he'.2⟩)

/-- Colourability is monotone under deleting selected edges. -/
theorem HasProperColoringOn.mono {F F' : Finset G.E} {k : ℕ}
    (hcolor : G.HasProperColoringOn F k) (hsub : F' ⊆ F) :
    G.HasProperColoringOn F' k := by
  obtain ⟨color, hproper⟩ := hcolor
  exact ⟨color, IsProperOn.mono G hproper hsub⟩

/-- Every finite uncolourable edge set contains an inclusion-minimal
uncolourable set. -/
theorem exists_colorCritical_subset {F : Finset G.E} {k : ℕ}
    (hbad : ¬ G.HasProperColoringOn F k) :
    ∃ C : Finset G.E, C ⊆ F ∧ G.IsColorCriticalOn C k := by
  classical
  let bad : Finset (Finset G.E) :=
    F.powerset.filter fun C ↦ ¬ G.HasProperColoringOn C k
  have hbadNonempty : bad.Nonempty := by
    refine ⟨F, ?_⟩
    simp [bad, hbad]
  obtain ⟨C, hCbad, hminimal⟩ :=
    Finset.exists_min_image bad Finset.card hbadNonempty
  have hCdata := Finset.mem_filter.mp hCbad
  refine ⟨C, Finset.mem_powerset.mp hCdata.1, hCdata.2, ?_⟩
  intro e heC
  by_contra heraseBad
  have heraseMem : C.erase e ∈ bad := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, heraseBad⟩
    exact (Finset.erase_subset e C).trans (Finset.mem_powerset.mp hCdata.1)
  have hcardMin := hminimal (C.erase e) heraseMem
  rw [Finset.card_erase_of_mem heC] at hcardMin
  have hpos : 0 < C.card := Finset.card_pos.mpr ⟨e, heC⟩
  omega

/-- Degree can only decrease when selected edges are deleted. -/
theorem degreeOn_mono_critical {F F' : Finset G.E} (hsub : F' ⊆ F) (v : G.V) :
    G.degreeOn F' v ≤ G.degreeOn F v := by
  unfold degreeOn
  apply Finset.card_le_card
  intro e he
  have he' := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨hsub he'.1, he'.2⟩

/-- Odd-set density bounds pass to a smaller selected edge set. -/
theorem OddSetDensityAtMost.mono_edges {F F' : Finset G.E} {L : ℝ}
    (hodd : G.OddSetDensityAtMost F L) (hsub : F' ⊆ F) :
    G.OddSetDensityAtMost F' L := by
  intro S hSodd hS3
  have hi : G.internalEdges F' S ⊆ G.internalEdges F S := by
    intro e he
    have he' := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨hsub he'.1, he'.2⟩
  have hcard : ((G.internalEdges F' S).card : ℝ) ≤
      (G.internalEdges F S).card := by
    exact_mod_cast Finset.card_le_card hi
  calc
    (2 : ℝ) * (G.internalEdges F' S).card ≤
        2 * (G.internalEdges F S).card := by gcongr
    _ ≤ L * ((S.card : ℝ) - 1) := hodd S hSodd hS3

/-- A color-critical set is nonempty. -/
theorem IsColorCriticalOn.nonempty {F : Finset G.E} {k : ℕ}
    (hk : 0 < k) (hcritical : G.IsColorCriticalOn F k) : F.Nonempty := by
  by_contra hF
  have hempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
  let color : G.E → Fin k := fun _ ↦ ⟨0, hk⟩
  apply hcritical.1
  refine ⟨color, ?_⟩
  simp [hempty, IsProperOn]

end WeightedMultigraph
end WeightedEdgeColoring
