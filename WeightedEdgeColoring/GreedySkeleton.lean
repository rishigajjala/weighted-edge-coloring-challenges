import WeightedEdgeColoring.WeightedInsertion

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- The degree of `v` in a selected set of indexed edges. -/
def degreeOn (F : Finset G.E) (v : G.V) : ℕ :=
  (F.filter (G.Inc v)).card

/-- Process a list from right to left.  If the input list is ordered from
light to heavy, this is exactly the usual heavy-first greedy construction. -/
def greedySkeletonList (n : ℕ) : List G.E → Finset G.E
  | [] => ∅
  | e :: es =>
      let F := greedySkeletonList n es
      if G.degreeOn F (G.fst e) < 2 * n ∧
          G.degreeOn F (G.snd e) < 2 * n then
        insert e F
      else
        F

theorem greedySkeletonList_subset_toFinset (n : ℕ) (es : List G.E) :
    G.greedySkeletonList n es ⊆ es.toFinset := by
  induction es with
  | nil => simp [greedySkeletonList]
  | cons e es ih =>
      simp only [greedySkeletonList]
      split_ifs
      · exact Finset.insert_subset_iff.mpr
          ⟨by simp, ih.trans (by simp)⟩
      · exact ih.trans (by simp)

theorem degreeOn_greedySkeletonList_le (n : ℕ) (es : List G.E) (v : G.V) :
    G.degreeOn (G.greedySkeletonList n es) v ≤ 2 * n := by
  induction es with
  | nil => simp [greedySkeletonList, degreeOn]
  | cons e es ih =>
      simp only [greedySkeletonList]
      split_ifs with hadd
      · rcases hadd with ⟨hfst, hsnd⟩
        simp only [degreeOn] at hfst hsnd
        by_cases hinc : G.Inc v e
        · have hcard := Finset.card_insert_le e
              ((G.greedySkeletonList n es).filter (G.Inc v))
          have hv : v = G.fst e ∨ v = G.snd e := by
            rcases hinc with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          rcases hv with rfl | rfl
          · rw [degreeOn, Finset.filter_insert, if_pos hinc]
            omega
          · rw [degreeOn, Finset.filter_insert, if_pos hinc]
            omega
        · rw [degreeOn, Finset.filter_insert, if_neg hinc]
          exact ih
      · exact ih

theorem heavyWitnessEdges_mono {F H : Finset G.E} (hFH : F ⊆ H)
    (v : G.V) (e : G.E) :
    G.heavyWitnessEdges F v e ⊆ G.heavyWitnessEdges H v e := by
  intro f hf
  simp only [heavyWitnessEdges, Finset.mem_filter] at hf ⊢
  exact ⟨hFH hf.1, hf.2⟩

/-- On a light-to-heavy list, every rejected edge has `2n` incident
skeleton edges that are no lighter. -/
theorem greedySkeletonList_hasHeavyWitnesses
    (n : ℕ) (es : List G.E)
    (hsorted : es.Pairwise fun e f => G.weight e ≤ G.weight f) :
    ∀ e ∈ es, e ∉ G.greedySkeletonList n es →
      2 * n ≤ (G.heavyWitnessEdges (G.greedySkeletonList n es)
        (G.fst e) e).card ∨
      2 * n ≤ (G.heavyWitnessEdges (G.greedySkeletonList n es)
        (G.snd e) e).card := by
  induction es with
  | nil => simp
  | cons a es ih =>
      have hsort := List.pairwise_cons.mp hsorted
      let F := G.greedySkeletonList n es
      have hFsub : F ⊆ es.toFinset := G.greedySkeletonList_subset_toFinset n es
      have ih' := ih hsort.2
      intro e heList heOut
      simp only [greedySkeletonList] at heOut ⊢
      by_cases hadd : G.degreeOn F (G.fst a) < 2 * n ∧
          G.degreeOn F (G.snd a) < 2 * n
      · rw [if_pos hadd] at heOut ⊢
        have hea : e ≠ a := by
          intro h
          subst e
          exact heOut (Finset.mem_insert_self _ _)
        have heTail : e ∈ es := (List.mem_cons.mp heList).resolve_left hea
        have heF : e ∉ F := fun he => heOut (Finset.mem_insert_of_mem he)
        rcases ih' e heTail heF with h | h
        · exact Or.inl (h.trans (Finset.card_le_card
            (G.heavyWitnessEdges_mono (Finset.subset_insert a F) (G.fst e) e)))
        · exact Or.inr (h.trans (Finset.card_le_card
            (G.heavyWitnessEdges_mono (Finset.subset_insert a F) (G.snd e) e)))
      · rw [if_neg hadd] at heOut ⊢
        rcases List.mem_cons.mp heList with heq | heTail
        · subst e
          have hnot : 2 * n ≤ G.degreeOn F (G.fst a) ∨
              2 * n ≤ G.degreeOn F (G.snd a) := by omega
          rcases hnot with hfst | hsnd
          · apply Or.inl
            apply hfst.trans
            apply Finset.card_le_card
            intro f hf
            have hfF : f ∈ F := (Finset.mem_filter.mp hf).1
            have hfTail : f ∈ es := by
              exact List.mem_toFinset.mp (hFsub hfF)
            simp only [heavyWitnessEdges, Finset.mem_filter]
            exact ⟨hfF, (Finset.mem_filter.mp hf).2, hsort.1 f hfTail⟩
          · apply Or.inr
            apply hsnd.trans
            apply Finset.card_le_card
            intro f hf
            have hfF : f ∈ F := (Finset.mem_filter.mp hf).1
            have hfTail : f ∈ es := by
              exact List.mem_toFinset.mp (hFsub hfF)
            simp only [heavyWitnessEdges, Finset.mem_filter]
            exact ⟨hfF, (Finset.mem_filter.mp hf).2, hsort.1 f hfTail⟩
        · exact ih' e heTail heOut

/-- All edges, sorted from light to heavy. -/
noncomputable def edgesByIncreasingWeight : List G.E :=
  Finset.univ.toList.mergeSort
    (fun e f => decide (G.weight e ≤ G.weight f))

theorem edgesByIncreasingWeight_pairwise :
    (G.edgesByIncreasingWeight).Pairwise
      (fun e f => G.weight e ≤ G.weight f) := by
  classical
  have hsorted := List.pairwise_mergeSort
    (le := fun e f : G.E => decide (G.weight e ≤ G.weight f))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact hab.trans hbc)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total (G.weight a) (G.weight b))
    Finset.univ.toList
  simpa [edgesByIncreasingWeight] using hsorted

theorem mem_edgesByIncreasingWeight (e : G.E) :
    e ∈ G.edgesByIncreasingWeight := by
  classical
  rw [edgesByIncreasingWeight, List.mem_mergeSort, Finset.mem_toList]
  simp

/-- The canonical heavy-first greedy skeleton. -/
noncomputable def greedySkeleton (n : ℕ) : Finset G.E :=
  G.greedySkeletonList n G.edgesByIncreasingWeight

theorem degreeOn_greedySkeleton_le (n : ℕ) (v : G.V) :
    G.degreeOn (G.greedySkeleton n) v ≤ 2 * n := by
  exact G.degreeOn_greedySkeletonList_le n G.edgesByIncreasingWeight v

theorem greedySkeleton_hasHeavyWitnesses (n : ℕ) :
    G.HasHeavySkeletonWitnesses (G.greedySkeleton n) n := by
  intro e he
  exact G.greedySkeletonList_hasHeavyWitnesses n G.edgesByIncreasingWeight
    G.edgesByIncreasingWeight_pairwise e (G.mem_edgesByIncreasingWeight e) he

/-- The degree and heavy-witness properties packaged as an existence result. -/
theorem exists_heavySkeleton (n : ℕ) :
    ∃ F : Finset G.E,
      (∀ v, G.degreeOn F v ≤ 2 * n) ∧
      G.HasHeavySkeletonWitnesses F n := by
  exact ⟨G.greedySkeleton n, G.degreeOn_greedySkeleton_le n,
    G.greedySkeleton_hasHeavyWitnesses n⟩

theorem outside_greedySkeleton_weight_lt_half
    (n : ℕ) (hdelta : G.deltaW ≤ n) :
    ∀ e ∉ G.greedySkeleton n, G.weight e < 1 / 2 :=
  G.outside_weight_lt_half_of_heavySkeleton n (G.greedySkeleton n) hdelta
    (G.greedySkeleton_hasHeavyWitnesses n)

/-- The complete certificate needed by the weighted insertion theorem. -/
theorem exists_heavySkeleton_with_light_outside
    (n : ℕ) (hdelta : G.deltaW ≤ n) :
    ∃ F : Finset G.E,
      (∀ v, G.degreeOn F v ≤ 2 * n) ∧
      G.HasHeavySkeletonWitnesses F n ∧
      (∀ e ∉ F, G.weight e < 1 / 2) := by
  exact ⟨G.greedySkeleton n, G.degreeOn_greedySkeleton_le n,
    G.greedySkeleton_hasHeavyWitnesses n,
    G.outside_greedySkeleton_weight_lt_half n hdelta⟩

end WeightedMultigraph
end WeightedEdgeColoring
