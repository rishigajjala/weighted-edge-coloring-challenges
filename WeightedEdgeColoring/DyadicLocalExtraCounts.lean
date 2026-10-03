import Mathlib.Data.Nat.Log
import WeightedEdgeColoring.ExtraSlotBudget

/-!
# Power-of-two padding for local extra-slot counts

Rounding every positive local count up to a power of two makes any two
endpoint counts comparable by divisibility.  This is the arithmetic input
for the sparse unequal-marginal cyclic coupling.
-/

namespace WeightedEdgeColoring

/-- Least power of two which is at least `m`. -/
def dyadicCeil (m : ℕ) : ℕ := 2 ^ Nat.clog 2 m

theorem dyadicCeil_pos (m : ℕ) : 0 < dyadicCeil m := by
  unfold dyadicCeil
  positivity

theorem le_dyadicCeil (m : ℕ) : m ≤ dyadicCeil m := by
  exact Nat.le_pow_clog (by norm_num) m

theorem dyadicCeil_le_two_mul {m : ℕ} (hm : 0 < m) :
    dyadicCeil m ≤ 2 * m := by
  by_cases hm1 : m = 1
  · subst m
    simp [dyadicCeil]
  · have hm2 : 1 < m := lt_of_le_of_ne (Nat.succ_le_iff.mpr hm) (Ne.symm hm1)
    have hpred := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hm2
    have hclog : 0 < Nat.clog 2 m := Nat.clog_pos (by norm_num) hm2
    have heq : 2 ^ Nat.clog 2 m =
        2 ^ (Nat.clog 2 m - 1) * 2 := by
      have hc : Nat.clog 2 m = (Nat.clog 2 m - 1) + 1 := by omega
      calc
        2 ^ Nat.clog 2 m = 2 ^ ((Nat.clog 2 m - 1) + 1) :=
          congrArg (fun x : ℕ ↦ 2 ^ x) hc
        _ = 2 ^ (Nat.clog 2 m - 1) * 2 := by rw [Nat.pow_succ]
    have hpred' : 2 ^ (Nat.clog 2 m - 1) < m := by
      simpa [Nat.pred_eq_sub_one] using hpred
    unfold dyadicCeil
    rw [heq]
    omega

theorem pow_two_dvd_of_le {a b : ℕ} (hab : a ≤ b) :
    2 ^ a ∣ 2 ^ b := by
  refine ⟨2 ^ (b - a), ?_⟩
  rw [← Nat.pow_add, Nat.add_sub_of_le hab]

/-- Any two padded counts divide one another. -/
theorem dyadicCeil_dvd_or_dvd (a b : ℕ) :
    dyadicCeil a ∣ dyadicCeil b ∨ dyadicCeil b ∣ dyadicCeil a := by
  rcases le_total (Nat.clog 2 a) (Nat.clog 2 b) with h | h
  · exact Or.inl (pow_two_dvd_of_le h)
  · exact Or.inr (pow_two_dvd_of_le h)

theorem dyadicCeil_dvd_max (a b : ℕ) :
    dyadicCeil a ∣ max (dyadicCeil a) (dyadicCeil b) := by
  rcases dyadicCeil_dvd_or_dvd a b with hab | hba
  · rw [Nat.max_eq_right (Nat.le_of_dvd (dyadicCeil_pos b) hab)]
    exact hab
  · rw [Nat.max_eq_left (Nat.le_of_dvd (dyadicCeil_pos a) hba)]

/-- Power-of-two padded graph count with a local load term and an additive
reserve. -/
noncomputable def dyadicExtraSlotCount (R gamma : ℝ) (reserve : ℕ) : ℕ :=
  dyadicCeil (extraSlotCount R gamma reserve)

theorem dyadicExtraSlotCount_pos (R gamma : ℝ) (reserve : ℕ) :
    0 < dyadicExtraSlotCount R gamma reserve :=
  dyadicCeil_pos _

theorem extraSlotCount_le_dyadicExtraSlotCount
    (R gamma : ℝ) (reserve : ℕ) :
    extraSlotCount R gamma reserve ≤
      dyadicExtraSlotCount R gamma reserve :=
  le_dyadicCeil _

theorem reserve_le_dyadicExtraSlotCount
    (R gamma : ℝ) (reserve : ℕ) :
    reserve ≤ dyadicExtraSlotCount R gamma reserve :=
  (extraSlotCount_ge_reserve R gamma reserve).trans
    (extraSlotCount_le_dyadicExtraSlotCount R gamma reserve)

theorem dyadicExtraSlotCount_le_twice
    (R gamma : ℝ) {reserve : ℕ} (hreserve : 0 < reserve) :
    dyadicExtraSlotCount R gamma reserve ≤
      2 * extraSlotCount R gamma reserve := by
  apply dyadicCeil_le_two_mul
  exact extraSlotCount_pos R gamma hreserve

end WeightedEdgeColoring
