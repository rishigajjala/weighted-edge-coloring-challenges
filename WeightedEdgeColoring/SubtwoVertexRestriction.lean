import WeightedEdgeColoring.SubtwoLocalPackingFractionalBins

/-! Restrict a weighted multigraph to a finite vertex set, retaining all
indexed edges with both endpoints in that set. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable def vertexRestriction (S : Finset G.V) : WeightedMultigraph.{u} := by
  classical
  exact {
    V := {v : G.V // v ∈ S}
    E := {e : G.E // G.fst e ∈ S ∧ G.snd e ∈ S}
    instFintypeV := inferInstance
    instFintypeE := inferInstance
    instDecidableEqV := inferInstance
    instDecidableEqE := inferInstance
    fst := fun e => ⟨G.fst e.1, e.2.1⟩
    snd := fun e => ⟨G.snd e.1, e.2.2⟩
    noLoop := fun e h => G.noLoop e.1 (congrArg Subtype.val h)
    weight := fun e => G.weight e.1
    weight_pos := fun e => G.weight_pos e.1
    weight_le_one := fun e => G.weight_le_one e.1 }

theorem vertexRestriction_card (S : Finset G.V) :
    Fintype.card (G.vertexRestriction S).V = S.card := by
  classical
  simpa only [vertexRestriction] using (Fintype.card_coe S)

theorem vertexRestriction_inc (S : Finset G.V)
    (v : (G.vertexRestriction S).V) (e : (G.vertexRestriction S).E) :
    (G.vertexRestriction S).Inc v e ↔ G.Inc v.1 e.1 := by
  simp [WeightedMultigraph.Inc, vertexRestriction, Subtype.ext_iff]

theorem vertexRestriction_locallyPacksInto (S : Finset G.V) {n : ℕ}
    (hlocal : G.LocallyPacksInto n) :
    (G.vertexRestriction S).LocallyPacksInto n := by
  classical
  intro v
  let oldBin := Classical.choose (hlocal v.1)
  let intoOld : (G.vertexRestriction S).StarEdge v → G.StarEdge v.1 :=
    fun e => ⟨e.1.1, (G.vertexRestriction_inc S v e.1).mp e.2⟩
  let newBin : (G.vertexRestriction S).StarEdge v → Fin n :=
    fun e => oldBin (intoOld e)
  refine ⟨newBin, ?_⟩
  intro j
  let f : G.E → ℝ := fun e =>
    if h : G.Inc v.1 e then
      if oldBin ⟨e, h⟩ = j then G.weight e else 0 else 0
  have hsub : (Finset.univ : Finset ((G.vertexRestriction S).StarEdge v)).image
      (fun e => (intoOld e)) ⊆ (Finset.univ : Finset (G.StarEdge v.1)) := by
    intro e he
    exact Finset.mem_univ _
  have hload : (G.vertexRestriction S).starBinLoad newBin j ≤
      G.starBinLoad oldBin j := by
    have hinj : Function.Injective intoOld := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : G.StarEdge v.1 => x.1) hab
    have heq : (G.vertexRestriction S).starBinLoad newBin j =
        ∑ e ∈ (Finset.univ : Finset ((G.vertexRestriction S).StarEdge v)).image intoOld,
          if oldBin e = j then G.weight e.1 else 0 := by
      rw [Finset.sum_image]
      · rfl
      · intro a _ b _ h
        exact hinj h
    rw [heq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (by intro e _ _; by_cases h : oldBin e = j <;> simp [h, G.weight_nonneg])
  exact hload.trans (Classical.choose_spec (hlocal v.1) j)

end WeightedEdgeColoring.WeightedMultigraph
