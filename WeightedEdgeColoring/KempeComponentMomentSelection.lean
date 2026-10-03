import WeightedEdgeColoring.KempeComponentInfluence
import WeightedEdgeColoring.WeightedMomentTwoSidedSelection

/-!
# Simultaneous statistic control for one Kempe color pair

This theorem is the direct bridge from the two-endpoint combinatorics to the
mass-sensitive partial-resampling selector.  The sources are the two-color
components and their states are fair Boolean switch coins.  A per-active-
vertex cap budget gives, with the exact factor two, the required component
column budget.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open scoped BigOperators
open WeightedEdgeColoring.FiniteCategoricalSelection
open WeightedEdgeColoring.FinitePartialResamplingNumerics

noncomputable section

universe u w

variable (G : WeightedMultigraph.{u})
variable {Row : Type w} [Fintype Row] [DecidableEq Row]

theorem exists_componentCoins_abs_rowLoad_sub_mean_lt_scaledDeviation
    {q : ℕ} (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q)
    (use : G.TwoColorComponent F color a b → Bool → Row → ℝ)
    (vertexCap : G.V → Row → ℝ)
    (M D B : ℝ) (hM : 0 < M) (hD : 0 ≤ D) (hB : 0 < B)
    (hDB1 : 1 ≤ D / B)
    (K : ℕ) (hK : 0 < K) (hMK : M / B ≤ K)
    (huse0 : ∀ component bit row, 0 ≤ use component bit row)
    (huseCap : ∀ component bit row,
      use component bit row ≤
        G.componentInfluenceCap F color a b vertexCap component row)
    (hvertexCap0 : ∀ v row, 0 ≤ vertexCap v row)
    (hvertexCapRow : ∀ v row, vertexCap v row ≤ B / 2)
    (hvertexCapTotal : ∀ v, ∑ row : Row, vertexCap v row ≤ D / 2)
    (hmeanUpper : ∀ row,
      rowMean (fun _component _bit ↦ (1 : ℝ) / 2) use row ≤ M)
    (hmeanLower : ∀ row,
      (∑ component : G.TwoColorComponent F color a b,
        G.componentInfluenceCap F color a b vertexCap component row) -
          rowMean (fun _component _bit ↦ (1 : ℝ) / 2) use row ≤ M) :
    ∃ coin : G.TwoColorComponent F color a b → Bool,
      ∀ row,
        |rowLoad use row coin -
            rowMean (fun _component _bit ↦ (1 : ℝ) / 2) use row| <
          B * packingDeviation (M / B) (D / B) := by
  let cap : G.TwoColorComponent F color a b → Row → ℝ :=
    fun component row ↦
      G.componentInfluenceCap F color a b vertexCap component row
  have hcapB : ∀ component row, cap component row ≤ B := by
    intro component row
    let active := G.activeVerticesInComponent F color a b component
    have hcard : active.card ≤ 2 :=
      G.card_activeVerticesInComponent_le_two
        F color hproper a b component
    calc
      cap component row = ∑ v ∈ active, vertexCap v.1 row := rfl
      _ ≤ ∑ _v ∈ active, B / 2 := by
        exact Finset.sum_le_sum fun v _hv ↦ hvertexCapRow v.1 row
      _ = (active.card : ℝ) * (B / 2) := by simp
      _ ≤ 2 * (B / 2) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
          (div_nonneg hB.le (by norm_num))
      _ = B := by ring
  have hcolumn : ∀ component, ∑ row : Row, cap component row ≤ D := by
    intro component
    have htwo := G.sum_componentInfluenceCap_le_two_mul
      F color hproper a b vertexCap hvertexCap0 (D / 2)
      (div_nonneg hD (by norm_num)) hvertexCapTotal component
    change (∑ row : Row,
      G.componentInfluenceCap F color a b vertexCap component row) ≤ D
    calc
      _ ≤ 2 * (D / 2) := htwo
      _ = D := by ring
  have hprob0 : ∀ (_component : G.TwoColorComponent F color a b)
      (_bit : Bool), 0 ≤ (1 : ℝ) / 2 := by
    intro _component _bit
    exact div_nonneg zero_le_one (by norm_num)
  have hprobSum : ∀ (_component : G.TwoColorComponent F color a b),
      ∑ _bit : Bool, (1 : ℝ) / 2 = 1 := by intro; simp
  have hdummy0 : ∀ _bit : Bool, 0 ≤ (1 : ℝ) / 2 := by
    intro _bit
    exact div_nonneg zero_le_one (by norm_num)
  have hdummySum : ∑ _bit : Bool, (1 : ℝ) / 2 = 1 := by simp
  obtain ⟨coin, _hsupport, hcoin⟩ :=
    WeightedEdgeColoring.WeightedMomentTwoSidedSelection.exists_supported_choice_abs_rowLoad_sub_mean_lt_scaledDeviation
        M D B hM hD hB hDB1 K hK hMK
        (fun _component _bit ↦ (1 : ℝ) / 2)
        (fun _bit ↦ (1 : ℝ) / 2) use cap
        hprob0 hprobSum hdummy0 hdummySum huse0
        (by simpa [cap] using huseCap) hcapB hmeanUpper
        (by simpa [cap] using hmeanLower) hcolumn
  exact ⟨coin, hcoin⟩

end

end WeightedMultigraph
end WeightedEdgeColoring
