import WeightedEdgeColoring.SubtwoActualQuotientProposal

/-! Canonical finite-class local laws and conditional endpoint realizations for
an actual physical quotient proposal. -/

namespace WeightedEdgeColoring.WeightedMultigraph

open scoped BigOperators
noncomputable section
universe u
namespace GeneralColoredPacketBase
variable {G : WeightedMultigraph.{u}} {K : ℕ}
variable (C : G.GeneralColoredPacketBase K)

/-- The quotient proposal's per-color split row is exactly the hypothesis
needed by the canonical finite/tiny single-label law. -/
theorem exists_quotientThresholdSingleLabelLawAndRealizations
    (T n : ℕ) (hT : 160 ≤ T) (hn : 0 < n)
    (edgeLabel : ∀ v : G.V, C.residualGraph.StarEdge v → Fin 6)
    (x : C.residualGraph.E → Fin K → ℝ)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hxM : ∀ e c, x e c ≤ 100 / n)
    (hrow : ∀ v c,
      (∑ e : C.residualGraph.StarEdge v,
        C.quotientSplitCharge (C.quotientFiniteEdges T) ((1 : ℝ) / T)
          e.1 * x e.1 c) +
          6 * (T + 1 : ℝ) * (100 / n) ≤ 1)
    {s β qstep r : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hqstep : 0 < qstep) (hr : 0 < r) :
    let finite := C.quotientFiniteEdges T
    let classOf := C.quotientThresholdClass T (by omega : 0 < T)
    ∃ (qLaw : ∀ v : G.V, Fin K →
        Finset (C.residualGraph.StarEdge v) → ℝ)
      (R : ∀ (v : G.V) (c : Fin K) (label : Fin 6),
        C.residualGraph.BoundedProfileRealization
          (C.residualGraph.conditionalEndpointProposal
            (edgeLabel v)
            (fun f : C.residualGraph.StarEdge v => x f.1 c)
            (qLaw v c) label) s β qstep r hβ hr),
      (∀ v c S, 0 ≤ qLaw v c S) ∧
      (∀ v c, ∑ S, qLaw v c S = 1) ∧
      (∀ v c S, qLaw v c S ≠ 0 →
        C.residualGraph.StarFeasible v S) ∧
      (∀ v c (f : C.residualGraph.StarEdge v),
        (∑ S, if f ∈ S then qLaw v c S else 0) = x f.1 c) ∧
      (∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
        ∃ l : Fin 6, ∀ f ∈ S, edgeLabel v f = l) ∧
      (∀ v c l, subsetLabelMass (edgeLabel v) (qLaw v c) l ≤
        (∑ e : {e : C.residualGraph.StarEdge v // e.1 ∈ finite},
          if edgeLabel v e.1 = l then
            x e.1.1 c / (finiteClassSize (classOf e.1.1) : ℝ) else 0) +
        (∑ e : {e : C.residualGraph.StarEdge v // e.1 ∉ finite},
          if edgeLabel v e.1 = l then
            C.residualGraph.weight e.1.1 * x e.1.1 c else 0) /
              (1 - (1 : ℝ) / T) +
          (T + 1 : ℝ) * (100 / n)) ∧
      (∀ v c label (f : C.residualGraph.StarEdge v) j,
        0 < (R v c label).largeAssign f j → edgeLabel v f = label) ∧
      (∀ v c label (f : C.residualGraph.StarEdge v) P,
        0 < (R v c label).tinyAssign f P → edgeLabel v f = label) ∧
      (∀ v c (f : C.residualGraph.StarEdge v),
        (∑ label : Fin 6,
          subsetLabelMass (edgeLabel v) (qLaw v c) label *
            (∑ j : C.residualGraph.ExplicitLargeSlot
              (R v c label).law hβ hr,
              (R v c label).largeAssign f j)) +
        (∑ label : Fin 6,
          subsetLabelMass (edgeLabel v) (qLaw v c) label *
            (∑ P : C.residualGraph.RoundedProfileIndex
              (R v c label).law hβ hr,
              (R v c label).tinyAssign f P)) = s * x f.1 c) := by
  dsimp only
  have hTpos : 0 < T := by omega
  have hM : (0 : ℝ) < 100 / n := by
    exact div_pos (by norm_num) (by exact_mod_cast hn)
  have htau0 : 0 ≤ (1 : ℝ) / T := by positivity
  have htau1 : (1 : ℝ) / T < 1 := by
    have hTreal : (160 : ℝ) ≤ T := by exact_mod_cast hT
    have hpos : (0 : ℝ) < T := by positivity
    apply (div_lt_iff₀ hpos).2
    linarith
  have hcharge : ∀ e ∈ C.quotientFiniteEdges T,
      harmonicCharge (C.residualGraph.weight e) =
      (1 : ℝ) / finiteClassSize (C.quotientThresholdClass T hTpos e) := by
    intro e he
    exact C.quotientThresholdClass_charge T hTpos e he
  have hweight : ∀ e ∈ C.quotientFiniteEdges T,
      C.residualGraph.weight e ≤
      (1 : ℝ) / finiteClassSize (C.quotientThresholdClass T hTpos e) := by
    intro e he
    exact C.quotientThresholdClass_weight_le T hTpos e he
  have htiny : ∀ e ∉ C.quotientFiniteEdges T,
      C.residualGraph.weight e ≤ (1 : ℝ) / T := by
    intro e he
    exact C.quotientTinyWeight_le T e he
  have hbudget : ∀ v c,
      (∑ e : C.residualGraph.StarEdge v,
        C.quotientSplitCharge (C.quotientFiniteEdges T) ((1 : ℝ) / T)
          e.1 * x e.1 c) +
          (Fintype.card (Fin 6) : ℝ) * (T + 1 : ℝ) * (100 / n) ≤ 1 := by
    simpa using hrow
  exact C.exists_quotientSplitSingleLabelLawAndRealizations hTpos
    (C.quotientFiniteEdges T) (C.quotientThresholdClass T hTpos)
    ((1 : ℝ) / T) (100 / n) edgeLabel x hM htau0 htau1
    hweight htiny hcharge hx0 hxM hbudget hs hs1 hβ hqstep hr

end GeneralColoredPacketBase
end
end WeightedEdgeColoring.WeightedMultigraph
