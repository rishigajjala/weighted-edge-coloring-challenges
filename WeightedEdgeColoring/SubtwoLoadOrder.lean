import WeightedEdgeColoring.SubtwoProfileRankTable

/-! Choose the largest and second-largest projection loads by two swaps. -/

namespace WeightedEdgeColoring.SubtwoHarmonicRanks

theorem exists_four_load_order (w : Fin 4 → ℝ) :
    ∃ p : Equiv.Perm (Fin 4), (∀ i, w i ≤ w (p 0)) ∧
      w (p 2) ≤ w (p 1) ∧ w (p 3) ≤ w (p 1) := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 4)) w
    ⟨0, Finset.mem_univ _⟩
  let first : Equiv.Perm (Fin 4) := Equiv.swap 0 i
  let rest : Finset (Fin 4) := Finset.univ.erase 0
  have hrest : rest.Nonempty := ⟨1, by simp [rest]⟩
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image rest (fun k => w (first k)) hrest
  have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
  let second : Equiv.Perm (Fin 4) := Equiv.swap 1 j
  have hfix : second 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hj0)
  refine ⟨second.trans first, ?_, ?_, ?_⟩
  · intro k
    simpa [Equiv.trans_apply, hfix, first] using hmax k (Finset.mem_univ k)
  · have hm : second 2 ∈ rest := by
      apply Finset.mem_erase.mpr
      constructor
      · intro h
        have he : (2 : Fin 4) = 0 := second.injective (h.trans hfix.symm)
        exact (by decide : (2 : Fin 4) ≠ 0) he
      · exact Finset.mem_univ _
    simpa [Equiv.trans_apply, second] using hjmax (second 2) hm
  · have hm : second 3 ∈ rest := by
      apply Finset.mem_erase.mpr
      constructor
      · intro h
        have he : (3 : Fin 4) = 0 := second.injective (h.trans hfix.symm)
        exact (by decide : (3 : Fin 4) ≠ 0) he
      · exact Finset.mem_univ _
    simpa [Equiv.trans_apply, second] using hjmax (second 3) hm

noncomputable def fourLoadOrder (w : Fin 4 → ℝ) : Equiv.Perm (Fin 4) :=
  Classical.choose (exists_four_load_order w)

theorem fourLoadOrder_first (w : Fin 4 → ℝ) (i : Fin 4) :
    w i ≤ w (fourLoadOrder w 0) :=
  (Classical.choose_spec (exists_four_load_order w)).1 i

theorem fourLoadOrder_second (w : Fin 4 → ℝ) :
    w (fourLoadOrder w 2) ≤ w (fourLoadOrder w 1) ∧
      w (fourLoadOrder w 3) ≤ w (fourLoadOrder w 1) :=
  (Classical.choose_spec (exists_four_load_order w)).2

theorem fourLoadOrder_heavy (w : Fin 4 → ℝ) (h : ∃ i, 1 / 2 < w i) :
    1 / 2 < w (fourLoadOrder w 0) := by
  obtain ⟨i, hi⟩ := h
  exact hi.trans_le (fourLoadOrder_first w i)

end WeightedEdgeColoring.SubtwoHarmonicRanks
