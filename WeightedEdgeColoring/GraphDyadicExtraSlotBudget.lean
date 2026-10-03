import WeightedEdgeColoring.DyadicLocalExtraCounts
import WeightedEdgeColoring.DivisibleLocalExtraSlotOptions
import WeightedEdgeColoring.GraphExtraSlotBudget

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u w

namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]

def graphDyadicExtraSlotCount
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) (reserve : ℕ) (v : G.V) (h : Class) : ℕ :=
  dyadicExtraSlotCount (G.classResidual bucket residual v h) gamma reserve

theorem graphDyadicExtraSlotCount_pos
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) (reserve : ℕ) (v : G.V) (h : Class) :
    0 < G.graphDyadicExtraSlotCount bucket residual gamma reserve v h :=
  dyadicExtraSlotCount_pos _ _ _

theorem graphDyadicExtraSlotCount_ge_reserve
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) (reserve : ℕ) (v : G.V) (h : Class) :
    reserve ≤ G.graphDyadicExtraSlotCount bucket residual gamma reserve v h :=
  reserve_le_dyadicExtraSlotCount _ _ _

theorem graphDyadic_left_dvd_support
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) (reserve : ℕ) (e : G.E) :
    G.graphDyadicExtraSlotCount bucket residual gamma reserve
        (G.fst e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
        (G.graphDyadicExtraSlotCount bucket residual gamma reserve) e := by
  exact dyadicCeil_dvd_max
    (extraSlotCount
      (G.classResidual bucket residual (G.fst e) (bucket e)) gamma reserve)
    (extraSlotCount
      (G.classResidual bucket residual (G.snd e) (bucket e)) gamma reserve)

theorem graphDyadic_right_dvd_support
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) (reserve : ℕ) (e : G.E) :
    G.graphDyadicExtraSlotCount bucket residual gamma reserve
        (G.snd e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
        (G.graphDyadicExtraSlotCount bucket residual gamma reserve) e := by
  exact (dyadicCeil_both_dvd_max
    (extraSlotCount
      (G.classResidual bucket residual (G.fst e) (bucket e)) gamma reserve)
    (extraSlotCount
      (G.classResidual bucket residual (G.snd e) (bucket e)) gamma reserve)).2

theorem classResidual_div_graphDyadicExtraSlotCount_le
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (hr0 : ∀ e, 0 ≤ residual e)
    (gamma : ℝ) {reserve : ℕ} (hreserve : 0 < reserve)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1)
    (v : G.V) (h : Class) :
    G.classResidual bucket residual v h /
        G.graphDyadicExtraSlotCount bucket residual gamma reserve v h ≤
      1 - gamma := by
  let R := G.classResidual bucket residual v h
  let C := extraSlotCount R gamma reserve
  let D := G.graphDyadicExtraSlotCount bucket residual gamma reserve v h
  have hR : 0 ≤ R := G.classResidual_nonneg bucket residual hr0 v h
  have hC : 0 < C := extraSlotCount_pos R gamma hreserve
  have hCD : C ≤ D := extraSlotCount_le_dyadicExtraSlotCount R gamma reserve
  have hD : (0 : ℝ) < D := by
    exact_mod_cast lt_of_lt_of_le hC hCD
  have hmono : R / D ≤ R / C := by
    exact div_le_div_of_nonneg_left hR (by exact_mod_cast hC)
      (by exact_mod_cast hCD)
  exact hmono.trans
    (residual_div_extraSlotCount_le R gamma reserve hR hgamma0 hgamma1 hreserve)

theorem sum_graphDyadic_endpointShares_eq_classResidual_div
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) (reserve : ℕ) (v : G.V) (h : Class) :
    (∑ e,
      (if (v, h) = (G.fst e, bucket e) then residual e /
          G.graphDyadicExtraSlotCount bucket residual gamma reserve
            (G.fst e) (bucket e)
        else if (v, h) = (G.snd e, bucket e) then residual e /
          G.graphDyadicExtraSlotCount bucket residual gamma reserve
            (G.snd e) (bucket e) else 0)) =
      G.classResidual bucket residual v h /
        G.graphDyadicExtraSlotCount bucket residual gamma reserve v h := by
  unfold classResidual
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hl : (v, h) = (G.fst e, bucket e)
  · have hl' := hl.symm
    have hr : (v, h) ≠ (G.snd e, bucket e) := by
      intro heq
      exact G.noLoop e (congrArg Prod.fst (hl.symm.trans heq))
    have hr' : (G.snd e, bucket e) ≠ (v, h) := fun heq ↦ hr heq.symm
    have hv : v = G.fst e := congrArg Prod.fst hl
    have hh : h = bucket e := congrArg Prod.snd hl
    subst v
    subst h
    rw [if_pos rfl, if_pos rfl, if_neg hr']
    simp
  · have hl' : (G.fst e, bucket e) ≠ (v, h) := fun heq ↦ hl heq.symm
    by_cases hr : (v, h) = (G.snd e, bucket e)
    · have hr' := hr.symm
      have hv : v = G.snd e := congrArg Prod.fst hr
      have hh : h = bucket e := congrArg Prod.snd hr
      subst v
      subst h
      rw [if_neg hl, if_pos rfl, if_neg hl', if_pos rfl]
      simp
    · have hr' : (G.snd e, bucket e) ≠ (v, h) := fun heq ↦ hr heq.symm
      rw [if_neg hl, if_neg hr, if_neg hl', if_neg hr']
      simp

theorem quantized_graphDyadicExtraSlotDegree_le
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (hr0 : ∀ e, 0 ≤ residual e)
    (gamma : ℝ) {reserve : ℕ} (hreserve : 0 < reserve)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (N : ℕ)
    (s : ExtraSlot G.V Class
      (G.graphDyadicExtraSlotCount bucket residual gamma reserve)) :
    ((((DivisibleLocalExtraChoice.system G.fst G.snd bucket
      (G.graphDyadicExtraSlotCount bucket residual gamma reserve)
      (G.graphDyadic_left_dvd_support bucket residual gamma reserve)
      (G.graphDyadic_right_dvd_support bucket residual gamma reserve)).quantized N
      (DivisibleLocalExtraChoice.mass G.fst G.snd bucket
        (G.graphDyadicExtraSlotCount bucket residual gamma reserve) residual)).slotDegree
        s : ℕ) : ℝ) ≤ (1 - gamma) * N := by
  let B := G.graphDyadicExtraSlotCount bucket residual gamma reserve
  have hBleft : ∀ e, 0 < B (G.fst e) (bucket e) := fun e ↦
    G.graphDyadicExtraSlotCount_pos bucket residual gamma reserve _ _
  have hBright : ∀ e, 0 < B (G.snd e) (bucket e) := fun e ↦
    G.graphDyadicExtraSlotCount_pos bucket residual gamma reserve _ _
  have hbase := DivisibleLocalExtraChoice.quantized_slotDegree_le_endpointShares
    G.fst G.snd bucket B
    (G.graphDyadic_left_dvd_support bucket residual gamma reserve)
    (G.graphDyadic_right_dvd_support bucket residual gamma reserve)
    residual hr0 hBleft hBright G.noLoop N s
  rcases s with ⟨⟨v, h⟩, i⟩
  change _ ≤ (1 - gamma) * N
  have hshares := G.sum_graphDyadic_endpointShares_eq_classResidual_div
    bucket residual gamma reserve v h
  change (∑ e,
      (if (v, h) = (G.fst e, bucket e) then residual e / B (G.fst e) (bucket e)
      else if (v, h) = (G.snd e, bucket e) then
        residual e / B (G.snd e) (bucket e) else 0)) = _ at hshares
  rw [hshares] at hbase
  have hratio := G.classResidual_div_graphDyadicExtraSlotCount_le
    bucket residual hr0 gamma hreserve hgamma0 hgamma1 v h
  calc
    _ ≤ (N : ℝ) *
        (G.classResidual bucket residual v h /
          G.graphDyadicExtraSlotCount bucket residual gamma reserve v h) := hbase
    _ ≤ (N : ℝ) * (1 - gamma) :=
      mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg N)
    _ = (1 - gamma) * N := by ring

theorem graphDyadicExtraSlotCount_cast_le
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (hr0 : ∀ e, 0 ≤ residual e)
    (gamma : ℝ) {reserve : ℕ} (hreserve : 0 < reserve)
    (hgamma1 : gamma < 1) (v : G.V) (h : Class) :
    (G.graphDyadicExtraSlotCount bucket residual gamma reserve v h : ℕ) ≤
      2 * (G.classResidual bucket residual v h / (1 - gamma) +
        1 + reserve) := by
  have htwice := dyadicExtraSlotCount_le_twice
    (G.classResidual bucket residual v h) gamma hreserve
  have hcount := extraSlotCount_cast_le
    (G.classResidual bucket residual v h) gamma reserve
    (G.classResidual_nonneg bucket residual hr0 v h) hgamma1
  exact_mod_cast (show
    (G.graphDyadicExtraSlotCount bucket residual gamma reserve v h : ℝ) ≤
      2 * (G.classResidual bucket residual v h / (1 - gamma) +
        1 + reserve) by
    exact (by exact_mod_cast htwice :
      (G.graphDyadicExtraSlotCount bucket residual gamma reserve v h : ℝ) ≤
        2 * (extraSlotCount
          (G.classResidual bucket residual v h) gamma reserve : ℕ)).trans
      (mul_le_mul_of_nonneg_left hcount (by norm_num)))

end WeightedSimpleGraph

end

end WeightedEdgeColoring
