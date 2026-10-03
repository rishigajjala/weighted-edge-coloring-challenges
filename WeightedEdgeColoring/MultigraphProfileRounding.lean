import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.FieldSimp
import WeightedEdgeColoring.MultigraphFiniteProfiles

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

/-!
# Reservoir rounding for finite profiles

This file formalizes the numerical reservoir rounding used in the finite
profile lemma.  A nonnegative reservoir `R` is rounded down to the largest
multiple of `r` below it.  The loss is less than `r`, every positive rounded
reservoir is at least `r`, and averaging loses at most `r` in total capacity.
-/

/-- Round `R` down to an integral multiple of the positive scale `r`. -/
noncomputable def roundReservoir (r R : ℝ) : ℝ :=
  r * (⌊R / r⌋ : ℝ)

theorem roundReservoir_nonneg {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) :
    0 ≤ roundReservoir r R := by
  unfold roundReservoir
  have hfloor : (0 : ℤ) ≤ ⌊R / r⌋ :=
    Int.floor_nonneg.mpr (div_nonneg hR hr)
  exact mul_nonneg hr (by exact_mod_cast hfloor)

theorem roundReservoir_le {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    roundReservoir r R ≤ R := by
  have hdiv : 0 ≤ R / r := div_nonneg hR hr.le
  have hfloor : ((⌊R / r⌋ : ℤ) : ℝ) ≤ R / r := Int.floor_le (R / r)
  unfold roundReservoir
  calc
    r * ((⌊R / r⌋ : ℤ) : ℝ) ≤ r * (R / r) :=
      mul_le_mul_of_nonneg_left hfloor hr.le
    _ = R := by field_simp

theorem lt_roundReservoir_add {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    R < roundReservoir r R + r := by
  have hdiv : 0 ≤ R / r := div_nonneg hR hr.le
  have hfloor : R / r < ((⌊R / r⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one (R / r)
  unfold roundReservoir
  have hmul := mul_lt_mul_of_pos_left hfloor hr
  calc
    R = r * (R / r) := by field_simp
    _ < r * (((⌊R / r⌋ : ℤ) : ℝ) + 1) := hmul
    _ = r * ((⌊R / r⌋ : ℤ) : ℝ) + r := by ring

theorem sub_lt_roundReservoir {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    R - r < roundReservoir r R := by
  linarith [lt_roundReservoir_add hr hR]

theorem sub_le_roundReservoir {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    R - r ≤ roundReservoir r R :=
  (sub_lt_roundReservoir hr hR).le

theorem roundReservoir_eq_zero_or_ge {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    roundReservoir r R = 0 ∨ r ≤ roundReservoir r R := by
  let k : ℤ := ⌊R / r⌋
  have hk0 : (0 : ℤ) ≤ k := by
    dsimp [k]
    exact Int.floor_nonneg.mpr (div_nonneg hR hr.le)
  by_cases hk : k = 0
  · left
    simp [roundReservoir, k, hk]
  · right
    have hk1 : (1 : ℤ) ≤ k := by omega
    unfold roundReservoir
    have hcast : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    simpa [k] using mul_le_mul_of_nonneg_left hcast hr.le

theorem roundReservoir_pos_iff {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    0 < roundReservoir r R ↔ r ≤ roundReservoir r R := by
  constructor
  · intro hpos
    rcases roundReservoir_eq_zero_or_ge hr hR with hzero | hge
    · exact (hpos.ne' hzero).elim
    · exact hge
  · exact fun h ↦ hr.trans_le h

variable (G : WeightedMultigraph)

/-- Rounding the reservoir of a raw feasible profile preserves safety. -/
theorem rawProfile_safe_after_roundReservoir
    {v : G.V} {r β : ℝ} (hr : 0 < r)
    {S : Finset (G.StarEdge v)} (hS : G.StarFeasible v S) :
    (∑ e ∈ (G.rawProfile β S).ordinary, G.weight e.1) +
        roundReservoir r (G.rawProfile β S).reservoir ≤ 1 := by
  have hR0 := G.rawProfile_reservoir_nonneg (β := β) hS
  have hround := roundReservoir_le hr hR0
  rw [rawProfile_reservoir] at hround
  rw [rawProfile_ordinary, rawProfile_reservoir]
  linarith

/-- Rounding every reservoir in a probability law loses at most one scale
`r` of expected reservoir capacity. -/
theorem sum_roundReservoir_ge_sub
    {m : ℕ} {r : ℝ} (hr : 0 < r)
    (p R : Fin m → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hR : ∀ k, 0 ≤ R k) (hpsum : ∑ k, p k = 1) :
    (∑ k, p k * roundReservoir r (R k)) ≥
      (∑ k, p k * R k) - r := by
  have hterm : ∀ k, p k * (R k - r) ≤
      p k * roundReservoir r (R k) := by
    intro k
    exact mul_le_mul_of_nonneg_left
      (sub_le_roundReservoir hr (hR k)) (hp k)
  calc
    (∑ k, p k * R k) - r = ∑ k, p k * (R k - r) := by
      calc
        (∑ k, p k * R k) - r =
            (∑ k, p k * R k) - (∑ k, p k) * r := by rw [hpsum, one_mul]
        _ = (∑ k, (p k * R k - p k * r)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_mul]
        _ = ∑ k, p k * (R k - r) := by
          apply Finset.sum_congr rfl
          intro k _hk
          ring
    _ ≤ ∑ k, p k * roundReservoir r (R k) :=
      Finset.sum_le_sum fun k _hk ↦ hterm k

end WeightedMultigraph
end WeightedEdgeColoring
