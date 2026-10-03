import WeightedEdgeColoring.TwoConstraintChoice
import WeightedEdgeColoring.GreedySkeleton

/-!
# Balanced selection of indexed edges

From a finite set of edges, we can select any prescribed fraction up to an
additive error of two at every vertex.  Parallel edges cause no problem,
because jobs are indexed by edges.  The proof is the two-constraint rounding
lemma applied to the two choices `selected` and `unselected` for each edge.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- A finite loopless weighted multigraph has an edge subset whose degree at
every vertex is within two of any prescribed fraction of the original
degree.  The statement applies to an arbitrary supplied edge set `J` and does
not require bipartiteness. -/
theorem exists_balanced_edge_selection
    (J : Finset G.E) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ F : Finset G.E, F ⊆ J ∧ ∀ v : G.V,
      t * (G.degreeOn J v : ℝ) - 2 ≤ (G.degreeOn F v : ℝ) ∧
      (G.degreeOn F v : ℝ) ≤ t * (G.degreeOn J v : ℝ) + 2 := by
  let job : ({e : G.E // e ∈ J} × Bool) → {e : G.E // e ∈ J} := Prod.fst
  let use : ({e : G.E // e ∈ J} × Bool) → (G.V × Bool) → ℝ := fun o r =>
    if r.2 = o.2 ∧ G.Inc r.1 o.1.1 then 1 else 0
  let x : ({e : G.E // e ∈ J} × Bool) → ℝ := fun o =>
    if o.2 then t else 1 - t
  have hx : ∀ o, 0 ≤ x o ∧ x o ≤ 1 := by
    intro o
    cases h : o.2 <;> simp [x, h, ht0, ht1, sub_nonneg.mpr ht1]
  have hjob : ∀ j, optionJobMass job x j = 1 := by
    intro j
    simp only [optionJobMass, job, x]
    rw [Fintype.sum_prod_type]
    simp
  have huse0 : ∀ o r, 0 ≤ use o r := by
    intro o r
    by_cases h : r.2 = o.2 ∧ G.Inc r.1 o.1.1 <;> simp [use, h]
  have huse1 : ∀ o r, use o r ≤ 1 := by
    intro o r
    by_cases h : r.2 = o.2 ∧ G.Inc r.1 o.1.1 <;> simp [use, h]
  have hsparse : ∀ o,
      (Finset.univ.filter fun r => use o r ≠ 0).card ≤ 2 := by
    intro o
    let endpoints : Finset (G.V × Bool) :=
      {(G.fst o.1.1, o.2), (G.snd o.1.1, o.2)}
    apply (Finset.card_le_card ?_).trans
      (show endpoints.card ≤ 2 by
        calc
          endpoints.card ≤ ({(G.snd o.1.1, o.2)} : Finset (G.V × Bool)).card + 1 := by
            exact Finset.card_insert_le _ _
          _ = 2 := by simp)
    intro r hr
    have hnonzero : use o r ≠ 0 := by simpa using hr
    have hcond : r.2 = o.2 ∧ G.Inc r.1 o.1.1 := by
      by_contra h
      simp [use, h] at hnonzero
    rcases hcond.2 with hfst | hsnd
    · have hr_eq : r = (G.fst o.1.1, o.2) := by
        apply Prod.ext
        · exact hfst.symm
        · exact hcond.1
      simp [endpoints, hr_eq]
    · have hr_eq : r = (G.snd o.1.1, o.2) := by
        apply Prod.ext
        · exact hsnd.symm
        · exact hcond.1
      simp [endpoints, hr_eq]
  obtain ⟨selected, howner, hload⟩ :=
    choose_one_option_per_job job use 1 x zero_lt_one hx hjob huse0 huse1 hsparse
  let take : {e : G.E // e ∈ J} → Bool := fun e => (selected e).2
  let chosenJobs : Finset {e : G.E // e ∈ J} :=
    Finset.univ.filter fun e => take e = true
  let edgeEmbedding : {e : G.E // e ∈ J} ↪ G.E :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let F : Finset G.E := chosenJobs.map edgeEmbedding
  have hFJ : F ⊆ J := by
    intro e he
    rcases Finset.mem_map.mp he with ⟨j, _hj, rfl⟩
    exact j.2
  refine ⟨F, hFJ, ?_⟩
  intro v
  have howner' : ∀ j : {e : G.E // e ∈ J}, (selected j).1 = j := by
    intro j
    exact howner j
  have hchosenDegree :
      (G.degreeOn F v : ℝ) =
        ∑ j : {e : G.E // e ∈ J}, use (selected j) (v, true) := by
    calc
      (G.degreeOn F v : ℝ) =
          ((chosenJobs.filter fun j => G.Inc v j.1).card : ℝ) := by
        have hsets : F.filter (G.Inc v) =
            (chosenJobs.filter fun j => G.Inc v j.1).map edgeEmbedding := by
          ext e
          simp [F, edgeEmbedding]
        rw [degreeOn, hsets, Finset.card_map]
      _ = ∑ j : {e : G.E // e ∈ J},
          if take j = true ∧ G.Inc v j.1 then 1 else 0 := by
        have hsets : chosenJobs.filter (fun j => G.Inc v j.1) =
            Finset.univ.filter fun j => take j = true ∧ G.Inc v j.1 := by
          ext j
          simp [chosenJobs]
        rw [hsets]
        simp
      _ = ∑ j : {e : G.E // e ∈ J}, use (selected j) (v, true) := by
        apply Finset.sum_congr rfl
        intro j _hj
        simp only [use]
        rw [howner' j]
        simp [take]
  have htotalDegree :
      (G.degreeOn J v : ℝ) =
        ∑ j : {e : G.E // e ∈ J}, if G.Inc v j.1 then 1 else 0 := by
    calc
      (G.degreeOn J v : ℝ) =
          ∑ e ∈ J, if G.Inc v e then (1 : ℝ) else 0 := by
        simp [degreeOn]
      _ = ∑ j : {e : G.E // e ∈ J},
          if G.Inc v j.1 then (1 : ℝ) else 0 := by
        exact Finset.sum_subtype J (by intro e; simp)
          (fun e => if G.Inc v e then (1 : ℝ) else 0)
  have hselectedFractional :
      optionLoad use x (v, true) = t * (G.degreeOn J v : ℝ) := by
    calc
      optionLoad use x (v, true) =
          ∑ j : {e : G.E // e ∈ J},
            t * (if G.Inc v j.1 then 1 else 0) := by
        simp only [optionLoad, Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro j _hj
        simp [use, x]
      _ = t * ∑ j : {e : G.E // e ∈ J},
          (if G.Inc v j.1 then 1 else 0) := by
        rw [Finset.mul_sum]
      _ = t * (G.degreeOn J v : ℝ) := by rw [htotalDegree]
  have hunselectedFractional :
      optionLoad use x (v, false) = (1 - t) * (G.degreeOn J v : ℝ) := by
    calc
      optionLoad use x (v, false) =
          ∑ j : {e : G.E // e ∈ J},
            (1 - t) * (if G.Inc v j.1 then 1 else 0) := by
        simp only [optionLoad, Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro j _hj
        simp [use, x]
      _ = (1 - t) * ∑ j : {e : G.E // e ∈ J},
          (if G.Inc v j.1 then 1 else 0) := by
        rw [Finset.mul_sum]
      _ = (1 - t) * (G.degreeOn J v : ℝ) := by rw [htotalDegree]
  have hselectedUpper := hload (v, true)
  rw [← hchosenDegree, hselectedFractional] at hselectedUpper
  have hselectedPlusUnselected :
      (∑ j : {e : G.E // e ∈ J}, use (selected j) (v, true)) +
          (∑ j : {e : G.E // e ∈ J}, use (selected j) (v, false)) =
        (G.degreeOn J v : ℝ) := by
    rw [htotalDegree]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    change (if true = (selected j).2 ∧ G.Inc v (selected j).1.1 then 1 else 0) +
        (if false = (selected j).2 ∧ G.Inc v (selected j).1.1 then 1 else 0) = _
    rw [howner' j]
    cases (selected j).2 <;> simp
  have hunselectedUpper := hload (v, false)
  rw [hunselectedFractional] at hunselectedUpper
  constructor
  · rw [hchosenDegree]
    linarith
  · norm_num at hselectedUpper ⊢
    exact hselectedUpper

end WeightedMultigraph

end

end WeightedEdgeColoring
