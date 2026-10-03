import WeightedEdgeColoring.SubtwoK6SupportReal
import WeightedEdgeColoring.SubtwoK6UnitEdge
import WeightedEdgeColoring.SubtwoK6AllTightTriangles

namespace WeightedEdgeColoring.Subtwo.K6MatchingDeficits
open K6SupportReal

theorem weighted_sum_le_one_of_regular (x p : Edge → ℝ)
    (hx : RegularFeasible x)
    (hp : ∀ M : Finset Edge, IsMatching M → (∑ e ∈ M, p e) ≤ 1) :
    (∑ e : Edge, p e * x e) ≤ 1 := by
  obtain ⟨y, hy, hxy, hno⟩ := exists_regular_max p x hx
  apply hxy.trans
  by_cases ht : ∃ S : Finset Vertex, S.card = 3 ∧ triangleMass y S = 1
  · obtain ⟨S, hS, hmass⟩ := ht
    exact weighted_sum_le_one_of_any_tight_triangle y p hy.1 hy.2.1 S hS hmass hp
  · have hstrict : ∀ S : Finset Vertex, S.card = 3 → triangleMass y S < 1 := by
      intro S hS
      have hle := hy.2.2 S hS
      have hne : triangleMass y S ≠ 1 := by
        intro heq
        exact ht ⟨S, hS, heq⟩
      exact lt_of_le_of_ne hle hne
    have hlow := strict_no_symmetric_implies_low_support y hy hstrict hno
    obtain ⟨e, he⟩ := low_support_has_unit_edge y hy hlow
    exact weighted_sum_le_one_of_unit_edge y p hy.1 hy.2.1 e he hp

theorem weighted_sum_le_one_of_fractional_matching (x p : Edge → ℝ)
    (hp0 : ∀ e, 0 ≤ p e)
    (hx0 : ∀ e, 0 ≤ x e)
    (hd : ∀ v, degree x v ≤ 1)
    (ht : ∀ S : Finset Vertex, S.card = 3 → triangleMass x S ≤ 1)
    (hf : ∀ v, omitFive x v ≤ 2)
    (hp : ∀ M : Finset Edge, IsMatching M → (∑ e ∈ M, p e) ≤ 1) :
    (∑ e : Edge, p e * x e) ≤ 1 := by
  obtain ⟨y, hxy, hy0, hyd, hyt⟩ := exists_regular_completion x hx0 hd ht hf
  have hprofit : (∑ e : Edge, p e * x e) ≤ (∑ e : Edge, p e * y e) := by
    apply Finset.sum_le_sum
    intro e _
    exact mul_le_mul_of_nonneg_left (hxy e) (hp0 e)
  exact hprofit.trans (weighted_sum_le_one_of_regular y p ⟨hy0, hyd, hyt⟩ hp)

theorem degree_div (x : Edge → ℝ) (a : ℝ) (v : Vertex) :
    degree (fun e => x e / a) v = degree x v / a := by
  fin_cases v <;> simp [degree, div_eq_mul_inv] <;> ring

theorem triangleMass_div (x : Edge → ℝ) (a : ℝ) (S : Finset Vertex) :
    triangleMass (fun e => x e / a) S = triangleMass x S / a := by
  simp [triangleMass, div_eq_mul_inv, Finset.sum_mul]

theorem omitFive_div (x : Edge → ℝ) (a : ℝ) (v : Vertex) :
    omitFive (fun e => x e / a) v = omitFive x v / a := by
  simp only [omitFive, total]
  rw [degree_div, ← Finset.sum_div]
  ring

theorem weighted_sum_le_scale_of_fractional_matching (x p : Edge → ℝ) (a : ℝ)
    (ha : 0 < a)
    (hp0 : ∀ e, 0 ≤ p e)
    (hx0 : ∀ e, 0 ≤ x e)
    (hd : ∀ v, degree x v ≤ a)
    (ht : ∀ S : Finset Vertex, S.card = 3 → triangleMass x S ≤ a)
    (hf : ∀ v, omitFive x v ≤ 2 * a)
    (hp : ∀ M : Finset Edge, IsMatching M → (∑ e ∈ M, p e) ≤ 1) :
    (∑ e : Edge, p e * x e) ≤ a := by
  let z : Edge → ℝ := fun e => x e / a
  have hz0 : ∀ e, 0 ≤ z e := by
    intro e
    exact div_nonneg (hx0 e) ha.le
  have hzd : ∀ v, degree z v ≤ 1 := by
    intro v
    rw [degree_div]
    exact (div_le_one ha).mpr (hd v)
  have hzt : ∀ S : Finset Vertex, S.card = 3 → triangleMass z S ≤ 1 := by
    intro S hS
    rw [triangleMass_div]
    exact (div_le_one ha).mpr (ht S hS)
  have hzf : ∀ v, omitFive z v ≤ 2 := by
    intro v
    rw [omitFive_div]
    exact (div_le_iff₀ ha).mpr (by nlinarith [hf v])
  have hbound := weighted_sum_le_one_of_fractional_matching z p hp0 hz0 hzd hzt hzf hp
  have hsum : (∑ e : Edge, p e * z e) = (∑ e : Edge, p e * x e) / a := by
    calc
      (∑ e : Edge, p e * z e) = ∑ e : Edge, (p e * x e) / a := by
        apply Finset.sum_congr rfl
        intro e _
        simp [z]
        ring
      _ = (∑ e : Edge, p e * x e) / a := by rw [Finset.sum_div]
  rw [hsum] at hbound
  exact (div_le_one ha).mp hbound

theorem weighted_sum_le_scale_mul_price_cap (x p : Edge → ℝ) (a C : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C)
    (hp0 : ∀ e, 0 ≤ p e)
    (hx0 : ∀ e, 0 ≤ x e)
    (hd : ∀ v, degree x v ≤ a)
    (ht : ∀ S : Finset Vertex, S.card = 3 → triangleMass x S ≤ a)
    (hf : ∀ v, omitFive x v ≤ 2 * a)
    (hp : ∀ M : Finset Edge, IsMatching M → (∑ e ∈ M, p e) ≤ C) :
    (∑ e : Edge, p e * x e) ≤ a * C := by
  by_cases hCp : 0 < C
  · let q : Edge → ℝ := fun e => p e / C
    have hq0 : ∀ e, 0 ≤ q e := fun e => div_nonneg (hp0 e) hCp.le
    have hqcap : ∀ M : Finset Edge, IsMatching M → (∑ e ∈ M, q e) ≤ 1 := by
      intro M hM
      have hcap := hp M hM
      have hsum : (∑ e ∈ M, q e) = (∑ e ∈ M, p e) / C := by
        simp [q, Finset.sum_div]
      rw [hsum]
      exact (div_le_one hCp).mpr hcap
    have hb := weighted_sum_le_scale_of_fractional_matching x q a ha hq0 hx0 hd ht hf hqcap
    have hsum : (∑ e : Edge, q e * x e) = (∑ e : Edge, p e * x e) / C := by
      calc
        (∑ e : Edge, q e * x e) = ∑ e : Edge, (p e * x e) / C := by
          apply Finset.sum_congr rfl
          intro e _
          simp [q]
          ring
        _ = (∑ e : Edge, p e * x e) / C := by rw [Finset.sum_div]
    rw [hsum] at hb
    exact (div_le_iff₀ hCp).mp hb
  · have hC0 : C = 0 := le_antisymm (le_of_not_gt hCp) hC
    have hpz : ∀ e : Edge, p e = 0 := by
      intro e
      have hM : IsMatching ({e} : Finset Edge) := by
        simp [IsMatching]
      have hpe : p e ≤ C := by simpa using hp {e} hM
      exact le_antisymm (by simpa [hC0] using hpe) (hp0 e)
    simp [hC0, hpz]

end WeightedEdgeColoring.Subtwo.K6MatchingDeficits
