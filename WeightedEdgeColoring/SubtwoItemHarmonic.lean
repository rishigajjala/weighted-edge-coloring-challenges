import WeightedEdgeColoring.SubtwoHarmonicRanks

/-! The item-level harmonic estimates used by the shared-heavy-item proof.
The number of items is unrestricted; these are not bounds on four bundle
projections. Repeated copies can be represented by separate finite indices. -/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo.ItemHarmonic

open SubtwoHarmonicRanks

theorem sum_charge_linear {I : Type*} [DecidableEq I]
    (S : Finset I) (w : I → ℝ) (r : ℕ) (hr : 0 < r)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hsmall : ∀ i ∈ S, w i ≤ 1 / (r : ℝ)) :
    (∑ i ∈ S, harmonicCharge (w i)) ≤
      (((r + 1 : ℕ) : ℝ) / r) * (∑ i ∈ S, w i) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi ↦ charge_le_linear hr (hw i hi) (hsmall i hi)

theorem sum_charge_linear_of_load {I : Type*} [DecidableEq I]
    (S : Finset I) (w : I → ℝ) (r : ℕ) (hr : 0 < r)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hload : ∑ i ∈ S, w i ≤ 1 / (r : ℝ)) :
    (∑ i ∈ S, harmonicCharge (w i)) ≤
      (((r + 1 : ℕ) : ℝ) / r) * (∑ i ∈ S, w i) := by
  apply sum_charge_linear S w r hr hw
  intro i hi
  exact (Finset.single_le_sum hw hi).trans hload

/-- An arbitrary finite light remainder of load at most one half. -/
theorem residual_charge {I : Type*} [DecidableEq I]
    (S : Finset I) (w : I → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hload : ∑ i ∈ S, w i ≤ 1 / 2) :
    ∑ i ∈ S, harmonicCharge (w i) ≤ (25 / 36 : ℝ) := by
  by_cases hlarge : ∃ i ∈ S, 1 / 3 < w i
  · obtain ⟨i, hi, hwi⟩ := hlarge
    have hhalf : w i ≤ 1 / 2 := (Finset.single_le_sum hw hi).trans hload
    have hc := charge_le_inv (r := 2) (by decide) (hw i hi) hhalf
    have hs := Finset.sum_erase_add S w hi
    have hcs := Finset.sum_erase_add S (fun j ↦ harmonicCharge (w j)) hi
    have hrest : ∑ j ∈ S.erase i, w j ≤ 1 / 6 := by linarith
    have hlin := sum_charge_linear_of_load (S.erase i) w 6 (by decide)
      (fun j hj ↦ hw j (Finset.mem_of_mem_erase hj)) hrest
    norm_num at hlin hc
    linarith
  · have hsmall : ∀ i ∈ S, w i ≤ 1 / 3 := by
      intro i hi
      exact le_of_not_gt fun h ↦ hlarge ⟨i, hi, h⟩
    have hlin := sum_charge_linear S w 3 (by decide) hw hsmall
    norm_num at hlin
    linarith

/-- An arbitrary finite unit bin containing no item heavier than one half. -/
theorem light_unit_charge {I : Type*} [DecidableEq I]
    (S : Finset I) (w : I → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hhalf : ∀ i ∈ S, w i ≤ 1 / 2) (hload : ∑ i ∈ S, w i ≤ 1) :
    ∑ i ∈ S, harmonicCharge (w i) ≤ (205 / 144 : ℝ) := by
  by_cases hfirst : ∃ i ∈ S, 1 / 3 < w i
  · obtain ⟨i, hi, hwi⟩ := hfirst
    have hci := charge_le_inv (r := 2) (by decide) (hw i hi) (hhalf i hi)
    have hwiSum := Finset.sum_erase_add S w hi
    have hciSum := Finset.sum_erase_add S (fun k ↦ harmonicCharge (w k)) hi
    have hw₁ : ∀ j ∈ S.erase i, 0 ≤ w j :=
      fun j hj ↦ hw j (Finset.mem_of_mem_erase hj)
    by_cases hsecond : ∃ j ∈ S.erase i, 1 / 3 < w j
    · obtain ⟨j, hj, hwj⟩ := hsecond
      have hjS := Finset.mem_of_mem_erase hj
      have hcj := charge_le_inv (r := 2) (by decide) (hw j hjS) (hhalf j hjS)
      have hwjSum := Finset.sum_erase_add (S.erase i) w hj
      have hcjSum := Finset.sum_erase_add (S.erase i) (fun k ↦ harmonicCharge (w k)) hj
      have hw₂ : ∀ k ∈ (S.erase i).erase j, 0 ≤ w k :=
        fun k hk ↦ hw₁ k (Finset.mem_of_mem_erase hk)
      have hrest : ∑ k ∈ (S.erase i).erase j, w k ≤ 1 / 3 := by linarith
      by_cases hthird : ∃ k ∈ (S.erase i).erase j, 1 / 4 < w k
      · obtain ⟨k, hk, hwk⟩ := hthird
        have hwk_third : w k ≤ 1 / 3 := (Finset.single_le_sum hw₂ hk).trans hrest
        have hck := charge_le_inv (r := 3) (by decide) (hw₂ k hk) hwk_third
        have hwkSum := Finset.sum_erase_add ((S.erase i).erase j) w hk
        have hckSum := Finset.sum_erase_add ((S.erase i).erase j)
          (fun l ↦ harmonicCharge (w l)) hk
        have htail : ∑ l ∈ ((S.erase i).erase j).erase k, w l ≤ 1 / 12 := by
          linarith
        have hlin := sum_charge_linear_of_load (((S.erase i).erase j).erase k) w 12
          (by decide) (fun l hl ↦ hw₂ l (Finset.mem_of_mem_erase hl)) htail
        norm_num at hlin hci hcj hck
        linarith
      · have hsmall : ∀ k ∈ (S.erase i).erase j, w k ≤ 1 / 4 := by
          intro k hk
          exact le_of_not_gt fun h ↦ hthird ⟨k, hk, h⟩
        have hlin := sum_charge_linear ((S.erase i).erase j) w 4 (by decide) hw₂ hsmall
        norm_num at hlin hci hcj
        linarith
    · have hsmall : ∀ j ∈ S.erase i, w j ≤ 1 / 3 := by
        intro j hj
        exact le_of_not_gt fun h ↦ hsecond ⟨j, hj, h⟩
      have hlin := sum_charge_linear (S.erase i) w 3 (by decide) hw₁ hsmall
      norm_num at hlin hci
      linarith
  · have hsmall : ∀ i ∈ S, w i ≤ 1 / 3 := by
      intro i hi
      exact le_of_not_gt fun h ↦ hfirst ⟨i, hi, h⟩
    have hlin := sum_charge_linear S w 3 (by decide) hw hsmall
    norm_num at hlin
    linarith

/-- The same estimate with arbitrary natural multiplicities of each type. -/
theorem residual_charge_counts {E : Type*} [Fintype E]
    (w : E → ℝ) (n : E → ℕ) (hw : ∀ e, 0 ≤ w e)
    (hload : (∑ e, (n e : ℝ) * w e) ≤ 1 / 2) :
    (∑ e, (n e : ℝ) * harmonicCharge (w e)) ≤ (25 / 36 : ℝ) := by
  classical
  have h := residual_charge (Finset.univ : Finset (Σ e, Fin (n e)))
    (fun i ↦ w i.1) (fun i _ ↦ hw i.1) ?_
  · simpa [Fintype.sum_sigma] using h
  · simpa [Fintype.sum_sigma] using hload

/-- The light-bin estimate also permits arbitrary type multiplicities. -/
theorem light_unit_charge_counts {E : Type*} [Fintype E]
    (w : E → ℝ) (n : E → ℕ) (hw : ∀ e, 0 ≤ w e)
    (hhalf : ∀ e, n e ≠ 0 → w e ≤ 1 / 2)
    (hload : (∑ e, (n e : ℝ) * w e) ≤ 1) :
    (∑ e, (n e : ℝ) * harmonicCharge (w e)) ≤ (205 / 144 : ℝ) := by
  classical
  have h := light_unit_charge (Finset.univ : Finset (Σ e, Fin (n e)))
    (fun i ↦ w i.1) (fun i _ ↦ hw i.1) ?_ ?_
  · simpa [Fintype.sum_sigma] using h
  · intro i _
    exact hhalf i.1 (by have := i.2.isLt; omega)
  · simpa [Fintype.sum_sigma] using hload

end WeightedEdgeColoring.Subtwo.ItemHarmonic
