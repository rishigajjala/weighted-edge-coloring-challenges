import WeightedEdgeColoring.MainTheorems

open scoped BigOperators

namespace WeightedEdgeColoring

/-- The numerical heart of the Shannon-style weighted insertion argument.
There are `3n` colors.  At the first endpoint, `2n` distinct witness colors
already carry load at least `a`.  If both total loads are at most `n` and
`a < 1/2`, then some color has room for an item of size `a` at both ends. -/
theorem exists_common_room_of_two_thirds_witness
    (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha0 : 0 < a) (hahalf : a < 1 / 2)
    (loadU loadV : Fin (3 * n) → ℝ)
    (hU0 : ∀ i, 0 ≤ loadU i) (hV0 : ∀ i, 0 ≤ loadV i)
    (hUsum : ∑ i, loadU i ≤ n) (hVsum : ∑ i, loadV i ≤ n)
    (W : Finset (Fin (3 * n))) (hWcard : 2 * n ≤ W.card)
    (hWload : ∀ i ∈ W, a ≤ loadU i) :
    ∃ i, loadU i + a ≤ 1 ∧ loadV i + a ≤ 1 := by
  classical
  by_contra hroom
  have hblocked (i : Fin (3 * n)) :
      1 - a < loadU i ∨ 1 - a < loadV i := by
    by_contra h
    push_neg at h
    apply hroom
    exact ⟨i, by constructor <;> linarith⟩
  let S : Finset (Fin (3 * n)) := Finset.univ.filter fun i => 1 - a < loadV i
  let T : Finset (Fin (3 * n)) := S ∩ W
  let U : Finset (Fin (3 * n)) := Finset.univ \ S

  have hS_lower : (S.card : ℝ) * (1 - a) ≤ ∑ i ∈ S, loadV i := by
    calc
      (S.card : ℝ) * (1 - a) = ∑ _i ∈ S, (1 - a) := by
        simp
        ring
      _ ≤ ∑ i ∈ S, loadV i :=
        Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2.le
  have hS_upper : ∑ i ∈ S, loadV i ≤ n := by
    calc
      (∑ i ∈ S, loadV i) ≤ ∑ i, loadV i := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) fun i _hi _ => hV0 i
      _ ≤ n := hVsum
  have hScard_load : (S.card : ℝ) * (1 - a) ≤ n := hS_lower.trans hS_upper

  have hWcompl_card : (Finset.univ \ W).card ≤ n := by
    have htotal : (Finset.univ : Finset (Fin (3 * n))).card = 3 * n := by simp
    rw [Finset.card_sdiff, Finset.inter_univ, htotal]
    omega
  have hTcard : S.card ≤ T.card + n := by
    have hsplit : S.card = T.card + (S \ W).card := by
      simpa [T] using (Finset.card_inter_add_card_sdiff S W).symm
    have hsub : (S \ W).card ≤ n := by
      exact (Finset.card_le_card (by intro i hi; simp_all)).trans hWcompl_card
    omega

  have hUcard : U.card + S.card = 3 * n := by
    have hSle : S.card ≤ 3 * n := by
      simpa using Finset.card_le_card (Finset.subset_univ S)
    simp [U, Finset.card_sdiff]
    omega
  have hU_nonempty : U.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hUempty
    have hcardzero : U.card = 0 := by simp [hUempty]
    have hSfull : S.card = 3 * n := by omega
    have hna : (n : ℝ) < (S.card : ℝ) * (1 - a) := by
      rw [hSfull]
      norm_num at hahalf ⊢
      nlinarith [show (0 : ℝ) < n by exact_mod_cast Nat.zero_lt_of_lt hn]
    linarith

  have hUload (i : Fin (3 * n)) (hi : i ∈ U) : 1 - a < loadU i := by
    have hiS : i ∉ S := by simpa [U] using hi
    have hv : ¬1 - a < loadV i := by simpa [S] using hiS
    exact (hblocked i).resolve_right hv
  have hU_lower : (U.card : ℝ) * (1 - a) < ∑ i ∈ U, loadU i := by
    calc
      (U.card : ℝ) * (1 - a) = ∑ _i ∈ U, (1 - a) := by
        simp
        ring
      _ < ∑ i ∈ U, loadU i :=
        Finset.sum_lt_sum_of_nonempty hU_nonempty hUload
  have hT_lower : (T.card : ℝ) * a ≤ ∑ i ∈ T, loadU i := by
    calc
      (T.card : ℝ) * a = ∑ _i ∈ T, a := by simp
      _ ≤ ∑ i ∈ T, loadU i :=
        Finset.sum_le_sum fun i hi => hWload i (Finset.mem_inter.mp hi).2
  have hdisj : Disjoint U T := by
    rw [Finset.disjoint_left]
    intro i hiU hiT
    have hiS : i ∉ S := by simpa [U] using hiU
    exact hiS (Finset.mem_inter.mp hiT).1
  have hunion_upper : (∑ i ∈ U, loadU i) + ∑ i ∈ T, loadU i ≤ n := by
    rw [← Finset.sum_union hdisj]
    calc
      (∑ i ∈ U ∪ T, loadU i) ≤ ∑ i, loadU i := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) fun i _hi _ => hU0 i
      _ ≤ n := hUsum
  have hmaster :
      (U.card : ℝ) * (1 - a) + (T.card : ℝ) * a < n := by
    calc
      (U.card : ℝ) * (1 - a) + (T.card : ℝ) * a
          < (∑ i ∈ U, loadU i) + (T.card : ℝ) * a := by linarith
      _ ≤ (∑ i ∈ U, loadU i) + ∑ i ∈ T, loadU i := by gcongr
      _ ≤ n := hunion_upper

  by_cases hk : S.card ≤ n
  · have hUlarge : 2 * n ≤ U.card := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
    have hUlargeR : (2 * n : ℕ) ≤ U.card := hUlarge
    have hcast : (2 * (n : ℝ)) ≤ (U.card : ℝ) := by exact_mod_cast hUlargeR
    have hposa : 0 < 1 - a := by linarith
    nlinarith
  · have hk' : n < S.card := Nat.lt_of_not_ge hk
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
    have hposa : 0 < 1 - a := by linarith
    have hScard_bound : (S.card : ℝ) ≤ (n : ℝ) / (1 - a) := by
      apply (le_div_iff₀ hposa).2
      simpa [mul_comm] using hScard_load
    have hTcast0 : (S.card : ℝ) ≤ (T.card : ℝ) + n := by
      exact_mod_cast hTcard
    have hTcast : (S.card : ℝ) - n ≤ (T.card : ℝ) := by linarith
    have hUeq : (U.card : ℝ) + S.card = 3 * n := by
      exact_mod_cast hUcard
    nlinarith [sq_pos_of_pos (sub_pos.mpr (show 2 * a < 1 by linarith))]

end WeightedEdgeColoring
