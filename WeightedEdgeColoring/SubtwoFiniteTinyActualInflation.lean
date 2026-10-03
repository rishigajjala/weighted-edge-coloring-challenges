import WeightedEdgeColoring.GeneralFiniteTinyChargeAccounting
import WeightedEdgeColoring.SubtwoHarmonicMargin

/-! The tiny-tail artificial charge exceeds physical harmonic charge by at
most a uniform multiple of the actual local packing load. -/

namespace WeightedEdgeColoring

open scoped BigOperators
noncomputable section

theorem weight_le_harmonicCharge_of_unit {w : ℝ}
    (hw : 0 < w) (hw1 : w ≤ 1) : w ≤ harmonicCharge w := by
  let k : ℕ := ⌊(1 : ℝ) / w⌋₊
  have hkpos : 0 < k := by
    have hdiv : (1 : ℝ) ≤ 1 / w := by
      exact (one_le_div hw).2 hw1
    exact (Nat.le_floor_iff (div_nonneg zero_le_one hw.le)).2
      (by simpa using hdiv)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hfloor : (k : ℝ) ≤ 1 / w := Nat.floor_le (div_nonneg zero_le_one hw.le)
  have hmul : w * k ≤ 1 := by
    nlinarith [(le_div_iff₀ hw).1 hfloor]
  unfold harmonicCharge
  change w ≤ (1 : ℝ) / k
  exact (le_div_iff₀ hkR).2 (by nlinarith)

theorem tinyInflatedWeight_le_harmonic_add {tau w : ℝ}
    (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (hw : 0 < w) (hw1 : w ≤ 1) :
    w / (1 - tau) ≤ harmonicCharge w + tau / (1 - tau) * w := by
  have hh := weight_le_harmonicCharge_of_unit hw hw1
  have hden : 1 - tau ≠ 0 := by linarith
  have heq : w / (1 - tau) = w + tau / (1 - tau) * w := by
    field_simp
    ring
  rw [heq]
  linarith

theorem inflatedReserve_fifth_of_quarter
    {tau n Jphysical Jinflated Missing : ℝ}
    (hn : 0 ≤ n) (htau0 : 0 ≤ tau)
    (htau : tau ≤ (1 : ℝ) / 40)
    (hinflate : Jinflated ≤ Jphysical + 2 * tau * n)
    (hquarter : Jphysical + (1 / 4 : ℝ) * n ≤ Missing) :
    Jinflated + (1 / 5 : ℝ) * n ≤ Missing := by
  have hmul := mul_le_mul_of_nonneg_right htau hn
  nlinarith

namespace WeightedMultigraph

universe u
variable {G : WeightedMultigraph.{u}} {tau : ℝ}

namespace GeneralTinyThresholdPacketization

variable (P : G.GeneralTinyThresholdPacketization tau)

def smallObjectStarHarmonicCharge (v : G.V) : ℝ :=
  ∑ o ∈ P.smallObjects,
    if P.mixedObjectGraph.Inc v o then
      harmonicCharge (P.mixedObjectGraph.weight o) else 0

theorem smallObjectStarWeight_inflation_le
    (htau0 : 0 ≤ tau) (htau1 : tau < 1) (v : G.V) :
    P.smallObjectStarWeight v / (1 - tau) ≤
      P.smallObjectStarHarmonicCharge v +
        tau / (1 - tau) * P.smallObjectStarWeight v := by
  unfold smallObjectStarWeight smallObjectStarHarmonicCharge
  rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro o _
  by_cases hi : P.mixedObjectGraph.Inc v o
  · simp only [if_pos hi]
    exact tinyInflatedWeight_le_harmonic_add htau0 htau1
      (P.mixedObjectGraph.weight_pos o)
      (P.mixedObjectGraph.weight_le_one o)
  · simp [hi]

theorem smallObjectStarWeight_inflation_le_local
    (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    {n : ℕ} (hlocal : G.LocallyPacksInto n) (v : G.V) :
    P.smallObjectStarWeight v / (1 - tau) ≤
      P.smallObjectStarHarmonicCharge v + tau / (1 - tau) * n := by
  have hstar := P.smallObjectStarWeight_le_original v
  have hlocalStar := G.starWeight_le_of_packsStarInto (hlocal v)
  have hcoef : 0 ≤ tau / (1 - tau) := div_nonneg htau0 (by linarith)
  have hmul := mul_le_mul_of_nonneg_left (hstar.trans hlocalStar) hcoef
  exact (P.smallObjectStarWeight_inflation_le htau0 htau1 v).trans
    (add_le_add_right hmul _)

theorem smallObjectStarWeight_inflation_le_twoTau
    (htau0 : 0 ≤ tau) (htauHalf : tau ≤ (1 : ℝ) / 2)
    {n : ℕ} (hlocal : G.LocallyPacksInto n) (v : G.V) :
    P.smallObjectStarWeight v / (1 - tau) ≤
      P.smallObjectStarHarmonicCharge v + 2 * tau * n := by
  have htau1 : tau < 1 := by linarith
  have hcoef : tau / (1 - tau) ≤ 2 * tau := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - tau)).2
    nlinarith [mul_nonneg htau0 (sub_nonneg.mpr htauHalf)]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmul := mul_le_mul_of_nonneg_right hcoef hn
  have htail :
      P.smallObjectStarHarmonicCharge v + tau / (1 - tau) * n ≤
        P.smallObjectStarHarmonicCharge v + 2 * tau * n := by
    simpa only [mul_assoc] using
      (add_le_add_right hmul (P.smallObjectStarHarmonicCharge v))
  exact (P.smallObjectStarWeight_inflation_le_local htau0 htau1 hlocal v).trans
    htail

end GeneralTinyThresholdPacketization
end WeightedMultigraph
end
end WeightedEdgeColoring
