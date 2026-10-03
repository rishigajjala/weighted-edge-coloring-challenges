import WeightedEdgeColoring.SubtwoOrdinaryFiveSaturation

/-!
# Orientation symmetry for critical five-chains

The indexed multigraph stores an arbitrary orientation on each edge. We
reverse every orientation to transport the last-internal-vertex theorem to
the first internal vertex of a critical chain.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

/-- Reverse the stored orientation of every indexed edge. -/
def reverseEndpoints : WeightedMultigraph.{u} where
  V := G.V
  E := G.E
  instFintypeV := G.instFintypeV
  instFintypeE := G.instFintypeE
  instDecidableEqV := G.instDecidableEqV
  instDecidableEqE := G.instDecidableEqE
  fst := G.snd
  snd := G.fst
  noLoop := fun e ↦ (G.noLoop e).symm
  weight := G.weight
  weight_pos := G.weight_pos
  weight_le_one := G.weight_le_one

@[simp] theorem reverseEndpoints_inc (v : G.V) (e : G.E) :
    G.reverseEndpoints.Inc v e ↔ G.Inc v e := by
  simp only [Inc, reverseEndpoints, or_comm]

@[simp] theorem reverseEndpoints_inc_filter (F : Finset G.E) (v : G.V) :
    F.filter (G.reverseEndpoints.Inc v) = F.filter (G.Inc v) := by
  ext e
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ ↦ G.reverseEndpoints_inc v e

theorem reverseEndpoints_proper_iff
    {F : Finset G.E} {k : ℕ} {color : G.E → Fin k} :
    G.reverseEndpoints.IsProperOn F color ↔ G.IsProperOn F color := by
  constructor
  · intro h v
    simpa only [IsProperOn, G.reverseEndpoints_inc_filter] using h v
  · intro h v
    simpa only [IsProperOn, G.reverseEndpoints_inc_filter] using h v

@[simp] theorem reverseEndpoints_degree (F : Finset G.E) (v : G.V) :
    G.reverseEndpoints.degreeOn F v = G.degreeOn F v := by
  simp only [degreeOn, G.reverseEndpoints_inc_filter]

@[simp] theorem reverseEndpoints_missingColorsAt
    {k : ℕ} (F : Finset G.E) (color : G.E → Fin k) (v : G.V) :
    G.reverseEndpoints.missingColorsAt F color v =
      G.missingColorsAt F color v := by
  simp only [missingColorsAt, G.reverseEndpoints_inc_filter]

theorem reverseEndpoints_critical_iff
    {F : Finset G.E} {k : ℕ} :
    G.reverseEndpoints.IsColorCriticalOn F k ↔ G.IsColorCriticalOn F k := by
  constructor
  · rintro ⟨hbad, hcrit⟩
    refine ⟨?_, ?_⟩
    · rintro ⟨color, hproper⟩
      exact hbad ⟨color, G.reverseEndpoints_proper_iff.mpr hproper⟩
    · intro e heF
      obtain ⟨color, hproper⟩ := hcrit e heF
      exact ⟨color, G.reverseEndpoints_proper_iff.mp hproper⟩
  · rintro ⟨hbad, hcrit⟩
    refine ⟨?_, ?_⟩
    · rintro ⟨color, hproper⟩
      exact hbad ⟨color, G.reverseEndpoints_proper_iff.mp hproper⟩
    · intro e heF
      obtain ⟨color, hproper⟩ := hcrit e heF
      exact ⟨color, G.reverseEndpoints_proper_iff.mpr hproper⟩

theorem reverseEndpoints_twoColorGraph
    {F : Finset G.E} {k : ℕ} (color : G.E → Fin k) (a b : Fin k) :
    G.reverseEndpoints.twoColorGraph F color b a =
      G.twoColorGraph F color a b := by
  ext u v
  simp only [twoColorGraph, SimpleGraph.fromRel_adj]
  unfold twoColorRel reverseEndpoints
  constructor
  · rintro ⟨hne, hrel⟩
    refine ⟨hne, ?_⟩
    rcases hrel with ⟨g, hgF, hgu, hgv, hcolor⟩ |
      ⟨g, hgF, hgv, hgu, hcolor⟩
    · right
      exact ⟨g, hgF, hgv, hgu, hcolor.elim Or.inr Or.inl⟩
    · left
      exact ⟨g, hgF, hgu, hgv, hcolor.elim Or.inr Or.inl⟩
  · rintro ⟨hne, hrel⟩
    refine ⟨hne, ?_⟩
    rcases hrel with ⟨g, hgF, hgu, hgv, hcolor⟩ |
      ⟨g, hgF, hgv, hgu, hcolor⟩
    · right
      exact ⟨g, hgF, hgv, hgu, hcolor.elim Or.inr Or.inl⟩
    · left
      exact ⟨g, hgF, hgu, hgv, hcolor.elim Or.inr Or.inl⟩

@[simp] theorem reverseEndpoints_internalEdges (F : Finset G.E)
    (S : Finset G.V) :
    G.reverseEndpoints.internalEdges F S = G.internalEdges F S := by
  ext g
  simp only [internalEdges, Finset.mem_filter]
  exact and_congr_right fun _ ↦ and_comm

/-- The endpoint-missing-color exclusion also holds at the first internal
vertex, by reversing the arbitrary stored orientation of every edge. -/
theorem first_internal_missingColor_edge_internal_fivePath
    {F : Finset G.E} {k d : ℕ} (hcritical : G.IsColorCriticalOn F k)
    {e : G.E} (heF : e ∈ F) {color : G.E → Fin k}
    (hproper : G.IsProperOn (F.erase e) color)
    {a b : Fin k}
    (ha : a ∈ G.missingColorsAt (F.erase e) color (G.fst e))
    (hb : b ∈ G.missingColorsAt (F.erase e) color (G.snd e))
    (p : (G.twoColorGraph (F.erase e) color a b).Path
      (G.fst e) (G.snd e)) (hpLen : p.1.length = 4)
    (hdk : d + 1 < k) (hdegree : ∀ z, G.degreeOn F z ≤ d)
    (hthreshold : 7 * d < 6 * k + 2)
    {g : G.E} (hgF : g ∈ F.erase e)
    (hgZ : G.Inc (p.1.getVert 1) g)
    (hgMissing : color g ∈
      G.missingColorsAt (F.erase e) color (G.fst e) ∪
      G.missingColorsAt (F.erase e) color (G.snd e)) :
    g ∈ G.internalEdges (F.erase e) p.1.support.toFinset := by
  let R := G.reverseEndpoints
  have hgraph : R.twoColorGraph (F.erase e) color b a =
      G.twoColorGraph (F.erase e) color a b :=
    G.reverseEndpoints_twoColorGraph color a b
  let q : (R.twoColorGraph (F.erase e) color b a).Path
      (R.fst e) (R.snd e) :=
    G.pathCast hgraph p.reverse
  have hqLen : q.1.length = 4 := by
    rw [G.pathCast_length]
    simpa using hpLen
  have hqSupport : q.1.support.toFinset = p.1.support.toFinset := by
    rw [G.pathCast_support]
    simp
  have hq3 : q.1.getVert 3 = p.1.getVert 1 := by
    rw [G.pathCast_getVert]
    change p.1.reverse.getVert 3 = p.1.getVert 1
    rw [SimpleGraph.Walk.getVert_reverse, hpLen]
  have hproperR : R.IsProperOn (F.erase e) color :=
    G.reverseEndpoints_proper_iff.mpr hproper
  have hcriticalR : R.IsColorCriticalOn F k :=
    G.reverseEndpoints_critical_iff.mpr hcritical
  have hdegreeR : ∀ z, R.degreeOn F z ≤ d := by
    intro z
    simpa [R] using hdegree z
  have hbR : b ∈ R.missingColorsAt (F.erase e) color (R.fst e) := by
    simpa [R] using hb
  have haR : a ∈ R.missingColorsAt (F.erase e) color (R.snd e) := by
    simpa [R] using ha
  have hgZR : R.Inc (q.1.getVert 3) g := by
    simpa [R, hq3] using hgZ
  have hgMissingR : color g ∈
      R.missingColorsAt (F.erase e) color (R.fst e) ∪
      R.missingColorsAt (F.erase e) color (R.snd e) := by
    rcases Finset.mem_union.mp hgMissing with hx | hy
    · exact Finset.mem_union.mpr (Or.inr (by simpa [R] using hx))
    · exact Finset.mem_union.mpr (Or.inl (by simpa [R] using hy))
  have hresult := R.last_internal_missingColor_edge_internal_fivePath
    hcriticalR heF hproperR hbR haR q hqLen hdk hdegreeR hthreshold
    hgF hgZR hgMissingR
  simpa [R, hqSupport] using hresult

end WeightedEdgeColoring.WeightedMultigraph
