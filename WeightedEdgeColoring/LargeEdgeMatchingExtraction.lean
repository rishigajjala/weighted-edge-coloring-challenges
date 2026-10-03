import WeightedEdgeColoring.LargeEdgeOptions
import WeightedEdgeColoring.OrdinaryMatchingExtraction
import WeightedEdgeColoring.QuantizedMatchingProjection
import WeightedEdgeColoring.SumMatchingRestriction

/-!
# Extracting the colored part of a combined large-edge matching

The combined option system contains ordinary colored options and separated
leave-uncolored options.  This module forgets copy labels, discards the
leave-uncolored summand, and applies the concrete-place packing theorem to
the remaining ordinary matching.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u w

variable (G : WeightedSimpleGraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]

/-- Ordinary base options represented by the selected copies in a combined
large-edge matching. -/
def selectedOrdinaryBaseOptions
    (q K N : ℕ) (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (x : G.E → Fin q → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K bucket B x residual))) :
    Finset (OrdinarySlotChoice G.E (Fin q) K) :=
  RankThreeOptionSystem.leftOptionSet
    (RankThreeOptionSystem.baseOptionSet N
      (G.largeEdgeMass K bucket B x residual) M)

/-- A combined quantized partial matching projects to an ordinary partial
matching after copy labels and leave-uncolored options are removed. -/
theorem selectedOrdinaryBaseOptions_isPartialMatching
    (q K N : ℕ) (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (x : G.E → Fin q → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K bucket B x residual)))
    (hM : ((G.largeEdgeOptionSystem K bucket B).quantized N
      (G.largeEdgeMass K bucket B x residual)).IsPartialMatching M) :
    (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching
      (G.selectedOrdinaryBaseOptions q K N bucket B x residual M) := by
  let Hord : RankThreeOptionSystem G.E (OrdinarySlot G.V (Fin q) K)
      (OrdinarySlotChoice G.E (Fin q) K) :=
    OrdinarySlotChoice.system G.fst G.snd K
  let Hextra : RankThreeOptionSystem G.E (ExtraSlot G.V Class B)
      (ExtraSlotChoice G.E G.V Class G.fst G.snd bucket B) :=
    ExtraSlotChoice.system G.fst G.snd bucket B
  let mass : G.LargeEdgeOption (Color := Fin q) K bucket B → ℝ :=
    G.largeEdgeMass K bucket B x residual
  let base : Finset (G.LargeEdgeOption (Color := Fin q) K bucket B) :=
    RankThreeOptionSystem.baseOptionSet N mass M
  have hbase : (Hord.separatedSum Hextra).IsPartialMatching base :=
    (Hord.separatedSum Hextra).baseOptionSet_isPartialMatching N mass M hM
  exact Hord.separatedSum_leftOptionSet_isPartialMatching Hextra base hbase

/-- Every selected ordinary base option has positive ordinary mass. -/
theorem selectedOrdinaryBaseOptions_mass_pos
    (q K N : ℕ) (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (x : G.E → Fin q → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K bucket B x residual)))
    {o : OrdinarySlotChoice G.E (Fin q) K}
    (ho : o ∈ G.selectedOrdinaryBaseOptions q K N bucket B x residual M) :
    0 < x o.job o.color o.leftPlace o.rightPlace := by
  have hinl : Sum.inl o ∈ RankThreeOptionSystem.baseOptionSet N
      (G.largeEdgeMass K bucket B x residual) M := by
    exact (RankThreeOptionSystem.mem_leftOptionSet_iff _ o).mp ho
  have hmass := RankThreeOptionSystem.baseOptionSet_mass_pos N
    (G.largeEdgeMass K bucket B x residual) M hinl
  exact hmass

/-- The colored part of a combined quantized matching is a feasible weighted
partial coloring whenever its concrete ordinary places form safe bins. -/
theorem largeEdgeQuantizedMatching_isFeasibleOn
    {q K N : ℕ} (hq : 0 < q)
    (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (x : G.E → Fin q → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K bucket B x residual)))
    (hM : ((G.largeEdgeOptionSystem K bucket B).quantized N
      (G.largeEdgeMass K bucket B x residual)).IsPartialMatching M)
    (slotSize : G.V → Fin q → Fin K → ℝ)
    (hslot0 : ∀ v c i, 0 ≤ slotSize v c i)
    (hsafe : ∀ v c, (∑ i, slotSize v c i) ≤ 1)
    (hleft : ∀ e c i j, 0 < x e c i j →
      G.weight e ≤ slotSize (G.fst e) c i)
    (hright : ∀ e c i j, 0 < x e c i j →
      G.weight e ≤ slotSize (G.snd e) c j) :
    let O := G.selectedOrdinaryBaseOptions q K N bucket B x residual M
    G.asMultigraph.IsFeasibleOn (G.ordinarySelectedEdges O)
      (G.extendSelectedOrdinaryColor hq O
        (G.selectedOrdinaryBaseOptions_isPartialMatching
          q K N bucket B x residual M hM)) := by
  let O := G.selectedOrdinaryBaseOptions q K N bucket B x residual M
  have hO : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching O :=
    G.selectedOrdinaryBaseOptions_isPartialMatching
      q K N bucket B x residual M hM
  apply G.ordinaryMatching_isFeasibleOn hq hO slotSize hslot0 hsafe
  · intro o ho
    exact hleft o.job o.color o.leftPlace o.rightPlace
      (G.selectedOrdinaryBaseOptions_mass_pos
        q K N bucket B x residual M ho)
  · intro o ho
    exact hright o.job o.color o.leftPlace o.rightPlace
      (G.selectedOrdinaryBaseOptions_mass_pos
        q K N bucket B x residual M ho)

end WeightedSimpleGraph

end

end WeightedEdgeColoring
