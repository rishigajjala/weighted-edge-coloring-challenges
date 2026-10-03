import WeightedEdgeColoring.DyadicLargeEdgeOptions
import WeightedEdgeColoring.OrdinaryMatchingExtraction
import WeightedEdgeColoring.QuantizedMatchingProjection
import WeightedEdgeColoring.SumMatchingRestriction

/-!
# Extracting the ordinary part of a locally dyadic large-edge matching

The right summand is used only to leave a job uncolored.  This file forgets
that summand and turns the selected ordinary base options into a feasible
weighted edge coloring, exactly as in the uniform cyclic special case.
-/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

universe u w

variable (G : WeightedSimpleGraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]

def selectedDyadicOrdinaryBaseOptions
    (q K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Fin q → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))) :
    Finset (OrdinarySlotChoice G.E (Fin q) K) :=
  RankThreeOptionSystem.leftOptionSet
    (RankThreeOptionSystem.baseOptionSet N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M)

theorem selectedDyadicOrdinaryBaseOptions_isPartialMatching
    (q K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Fin q → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (hM : ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).IsPartialMatching M) :
    (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching
      (G.selectedDyadicOrdinaryBaseOptions q K N bucket gamma reserve
        residual x M) := by
  let Hord : RankThreeOptionSystem G.E (OrdinarySlot G.V (Fin q) K)
      (OrdinarySlotChoice G.E (Fin q) K) :=
    OrdinarySlotChoice.system G.fst G.snd K
  let Hextra : RankThreeOptionSystem G.E
      (ExtraSlot G.V Class
        (G.graphDyadicExtraSlotCount bucket residual gamma reserve))
      (DivisibleLocalExtraChoice G.E G.V Class G.fst G.snd bucket
        (G.graphDyadicExtraSlotCount bucket residual gamma reserve)) :=
    DivisibleLocalExtraChoice.system G.fst G.snd bucket
      (G.graphDyadicExtraSlotCount bucket residual gamma reserve)
      (G.graphDyadic_left_dvd_support bucket residual gamma reserve)
      (G.graphDyadic_right_dvd_support bucket residual gamma reserve)
  let mass := G.dyadicLargeEdgeMass K bucket gamma reserve residual x
  let base := RankThreeOptionSystem.baseOptionSet N mass M
  have hbase : (Hord.separatedSum Hextra).IsPartialMatching base :=
    (Hord.separatedSum Hextra).baseOptionSet_isPartialMatching N mass M hM
  exact Hord.separatedSum_leftOptionSet_isPartialMatching Hextra base hbase

theorem selectedDyadicOrdinaryBaseOptions_mass_pos
    (q K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Fin q → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    {o : OrdinarySlotChoice G.E (Fin q) K}
    (ho : o ∈ G.selectedDyadicOrdinaryBaseOptions q K N bucket gamma reserve
      residual x M) :
    0 < x o.job o.color o.leftPlace o.rightPlace := by
  have hinl : Sum.inl o ∈ RankThreeOptionSystem.baseOptionSet N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M :=
    (RankThreeOptionSystem.mem_leftOptionSet_iff _ o).mp ho
  exact RankThreeOptionSystem.baseOptionSet_mass_pos N
    (G.dyadicLargeEdgeMass K bucket gamma reserve residual x) M hinl

theorem dyadicLargeEdgeQuantizedMatching_isFeasibleOn
    {q K N : ℕ} (hq : 0 < q) (bucket : G.E → Class)
    (gamma : ℝ) (reserve : ℕ) (residual : G.E → ℝ)
    (x : G.E → Fin q → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (hM : ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).IsPartialMatching M)
    (slotSize : G.V → Fin q → Fin K → ℝ)
    (hslot0 : ∀ v c i, 0 ≤ slotSize v c i)
    (hsafe : ∀ v c, (∑ i, slotSize v c i) ≤ 1)
    (hleft : ∀ e c i j, 0 < x e c i j →
      G.weight e ≤ slotSize (G.fst e) c i)
    (hright : ∀ e c i j, 0 < x e c i j →
      G.weight e ≤ slotSize (G.snd e) c j) :
    let O := G.selectedDyadicOrdinaryBaseOptions q K N bucket gamma reserve
      residual x M
    G.asMultigraph.IsFeasibleOn (G.ordinarySelectedEdges O)
      (G.extendSelectedOrdinaryColor hq O
        (G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
          q K N bucket gamma reserve residual x M hM)) := by
  let O := G.selectedDyadicOrdinaryBaseOptions q K N bucket gamma reserve
    residual x M
  have hO := G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
    q K N bucket gamma reserve residual x M hM
  apply G.ordinaryMatching_isFeasibleOn hq hO slotSize hslot0 hsafe
  · intro o ho
    exact hleft o.job o.color o.leftPlace o.rightPlace
      (G.selectedDyadicOrdinaryBaseOptions_mass_pos
        q K N bucket gamma reserve residual x M ho)
  · intro o ho
    exact hright o.job o.color o.leftPlace o.rightPlace
      (G.selectedDyadicOrdinaryBaseOptions_mass_pos
        q K N bucket gamma reserve residual x M ho)

end WeightedSimpleGraph

end

end WeightedEdgeColoring
