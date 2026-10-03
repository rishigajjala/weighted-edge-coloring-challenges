import Mathlib

/-! A compact linear optimization problem has a maximizer that admits no
nonzero symmetric feasible perturbation. The secondary objective is the
sum of squared coordinates. -/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo.LinearQuadraticMax

variable {E : Type*} [Fintype E]

def linear (p x : E → ℝ) : ℝ := ∑ e, p e * x e
def square (x : E → ℝ) : ℝ := ∑ e, x e ^ 2

theorem continuous_linear (p : E → ℝ) : Continuous (linear p) := by
  exact continuous_finset_sum _ fun e _ ↦ continuous_const.mul (continuous_apply e)

theorem continuous_square : Continuous (square (E := E)) := by
  exact continuous_finset_sum _ fun e _ ↦ (continuous_apply e).pow 2

theorem exists_max (K : Set (E → ℝ)) (hK : IsCompact K) (hne : K.Nonempty)
    (p : E → ℝ) :
    ∃ y ∈ K, (∀ z ∈ K, linear p z ≤ linear p y) ∧
      ∀ z ∈ K, linear p z = linear p y → square z ≤ square y := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne (continuous_linear p).continuousOn
  let L : Set (E → ℝ) := K ∩ {z | linear p z = linear p x}
  have hL : IsCompact L := hK.inter_right
    (isClosed_eq (continuous_linear p) continuous_const)
  have hnL : L.Nonempty := ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hsq⟩ := hL.exists_isMaxOn hnL continuous_square.continuousOn
  refine ⟨y, hy.1, ?_, ?_⟩
  · intro z hz
    rw [hy.2]
    exact hmax hz
  · intro z hz hp
    exact hsq ⟨hz, hp.trans hy.2⟩

theorem linear_add (p y d : E → ℝ) :
    linear p (fun e ↦ y e + d e) = linear p y + linear p d := by
  simp [linear, mul_add, Finset.sum_add_distrib]

theorem linear_sub (p y d : E → ℝ) :
    linear p (fun e ↦ y e - d e) = linear p y - linear p d := by
  simp [linear, mul_sub, Finset.sum_sub_distrib]

theorem square_symmetric (y d : E → ℝ) :
    square (fun e ↦ y e + d e) + square (fun e ↦ y e - d e) =
      2 * square y + 2 * square d := by
  simp only [square, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem no_symmetric_perturbation (K : Set (E → ℝ)) (p y : E → ℝ)
    (hmax : ∀ z ∈ K, linear p z ≤ linear p y)
    (hsq : ∀ z ∈ K, linear p z = linear p y → square z ≤ square y)
    (d : E → ℝ) (hne : ∃ e, d e ≠ 0)
    (hplus : (fun e ↦ y e + d e) ∈ K)
    (hminus : (fun e ↦ y e - d e) ∈ K) : False := by
  have hp := hmax _ hplus
  have hm := hmax _ hminus
  rw [linear_add] at hp
  rw [linear_sub] at hm
  have hd : linear p d = 0 := by linarith
  have hpeq : linear p (fun e ↦ y e + d e) = linear p y := by
    rw [linear_add, hd, add_zero]
  have hmeq : linear p (fun e ↦ y e - d e) = linear p y := by
    rw [linear_sub, hd, sub_zero]
  have hsp := hsq _ hplus hpeq
  have hsm := hsq _ hminus hmeq
  have hid := square_symmetric y d
  have hpos : 0 < square d := by
    obtain ⟨e, he⟩ := hne
    exact (Finset.sum_pos_iff_of_nonneg (fun z _ ↦ sq_nonneg (d z))).mpr
      ⟨e, Finset.mem_univ e, sq_pos_of_ne_zero he⟩
  linarith

end WeightedEdgeColoring.Subtwo.LinearQuadraticMax
