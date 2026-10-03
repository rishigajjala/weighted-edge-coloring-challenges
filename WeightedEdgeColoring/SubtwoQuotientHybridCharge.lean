import WeightedEdgeColoring.SubtwoQuotientHybrid
import WeightedEdgeColoring.SubtwoQuotientFiniteTinyLabelFactory
import WeightedEdgeColoring.GeneralFiniteTinyHybridProposal

/-! Generic artificial split charge on a physical quotient packet hybrid. -/
namespace WeightedEdgeColoring.WeightedMultigraph
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
universe u
namespace GeneralColoredPacketBase
variable {G : WeightedMultigraph.{u}} {K : ℕ}
variable (C : G.GeneralColoredPacketBase K)
variable (finite : Finset C.residualGraph.E) (tau : ℝ)

def quotientSplitStarCharge (v : G.V) : ℝ :=
  ∑ e : C.residualGraph.StarEdge v, C.quotientSplitCharge finite tau e.1

def quotientHybridResidualCharge : C.quotientHybridGraph.E → ℝ
  | Sum.inl _ => 0
  | Sum.inr e => C.quotientSplitCharge finite tau e

theorem quotientSplit_weight_le_charge
    (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (e : C.residualGraph.E) :
    C.residualGraph.weight e ≤ C.quotientSplitCharge finite tau e := by
  by_cases he : e ∈ finite
  · simp only [quotientSplitCharge, he, if_true]
    exact TinyThresholdPacketization.weight_le_harmonicCharge e
  · simp only [quotientSplitCharge, he, if_false]
    rw [le_div_iff₀ (sub_pos.mpr htau1)]
    have hw := C.residualGraph.weight_nonneg e
    nlinarith

theorem quotientSplitCharge_nonneg
    (htau1 : tau < 1) (e : C.residualGraph.E) :
    0 ≤ C.quotientSplitCharge finite tau e := by
  by_cases he : e ∈ finite
  · simp [quotientSplitCharge, he, harmonicCharge_nonneg]
  · simp only [quotientSplitCharge, he, if_false]
    exact div_nonneg (C.residualGraph.weight_nonneg e)
      (sub_pos.mpr htau1).le

theorem quotientSplitCharge_le_one
    (htau0 : 0 ≤ tau) (htauHalf : tau ≤ (1 : ℝ) / 2)
    (htiny : ∀ e ∉ finite, C.residualGraph.weight e ≤ tau)
    (e : C.residualGraph.E) :
    C.quotientSplitCharge finite tau e ≤ 1 := by
  have htau1 : tau < 1 := by linarith
  by_cases he : e ∈ finite
  · simp only [quotientSplitCharge, he, if_true]
    exact harmonicCharge_le_one (C.residualGraph.weight_pos e)
      (C.residualGraph.weight_le_one e)
  · simp only [quotientSplitCharge, he, if_false]
    apply (div_le_one (sub_pos.mpr htau1)).2
    have hsmall := htiny e he
    have hw : C.residualGraph.weight e ≤ tau := hsmall
    linarith

/-- Uncovered artificial charge controls the physical proposal deficit on
the joint residual. -/
theorem quotientSplit_proposalDeficit_le_uncoveredCharge
    {q : ℕ} (x : C.residualGraph.E → Fin q → ℝ)
    (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (hmass : ∀ e, ∑ c, x e c ≤ 1) (v : G.V) :
    C.residualGraph.proposalDeficit x v ≤
      ∑ e : C.residualGraph.E,
        if C.residualGraph.Inc v e then
          C.quotientSplitCharge finite tau e * (1 - ∑ c, x e c) else 0 := by
  unfold proposalDeficit
  apply Finset.sum_le_sum
  intro e _he
  by_cases hinc : C.residualGraph.Inc v e
  · simp only [hinc, if_true]
    exact mul_le_mul_of_nonneg_right
      (C.quotientSplit_weight_le_charge finite tau htau0 htau1 e)
      (sub_nonneg.mpr (hmass e))
  · simp [hinc]

theorem sum_quotientHybridResidualEdges
    (f : C.quotientHybridGraph.E → ℝ) :
    (∑ e ∈ C.quotientHybridResidualEdges, f e) =
      ∑ e : C.residualGraph.E, f (Sum.inr e) := by
  classical
  symm
  apply Finset.sum_bij (fun e _ => Sum.inr e)
  · intro e _he
    exact C.mem_quotientHybridResidualEdges_inr e
  · intro e₁ _ e₂ _ h
    exact Sum.inr_injective h
  · intro e he
    rcases e with p | e
    · exact (C.not_mem_quotientHybridResidualEdges_inl p he).elim
    · exact ⟨e, Finset.mem_univ _, rfl⟩
  · intro e _he
    rfl

/-- Restricted hybrid charge is exactly joint-residual artificial star
charge. -/
theorem quotientHybrid_restrictedCharge_eq_jointStarCharge (v : G.V) :
    C.quotientHybridGraph.restrictedCharge
        C.quotientHybridResidualEdges
        (C.quotientHybridResidualCharge finite tau) v =
      C.quotientSplitStarCharge finite tau v := by
  classical
  unfold restrictedCharge quotientSplitStarCharge
  rw [show
      (∑ e : C.residualGraph.StarEdge v,
        C.quotientSplitCharge finite tau e.1) =
      ∑ e : C.residualGraph.E,
        if C.residualGraph.Inc v e then
          C.quotientSplitCharge finite tau e else 0 by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype
      (p := fun e : C.residualGraph.E =>
        C.residualGraph.Inc v e)
      ((Finset.univ : Finset C.residualGraph.E).filter
        (C.residualGraph.Inc v)) (by
          intro e
          rw [Finset.mem_filter]
          simp only [Finset.mem_univ, true_and])
      (fun e => C.quotientSplitCharge finite tau e)).symm]
  rw [C.sum_quotientHybridResidualEdges]
  rfl

/-- Hybrid proposal charge load is the joint-residual star sum. -/
theorem quotientHybrid_proposalChargeLoad_eq_joint
    {q : ℕ} (x : C.quotientHybridGraph.E → Fin q → ℝ)
    (v : G.V) (c : Fin q) :
    C.quotientHybridGraph.proposalChargeLoad
        C.quotientHybridResidualEdges (C.quotientHybridResidualCharge finite tau)
        x v c =
      ∑ e : C.residualGraph.StarEdge v,
        C.quotientSplitCharge finite tau e.1 * x (Sum.inr e.1) c := by
  classical
  unfold proposalChargeLoad
  rw [show
      (∑ e : C.residualGraph.StarEdge v,
        C.quotientSplitCharge finite tau e.1 * x (Sum.inr e.1) c) =
      ∑ e : C.residualGraph.E,
        if C.residualGraph.Inc v e then
          C.quotientSplitCharge finite tau e * x (Sum.inr e) c else 0 by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype
      (p := fun e : C.residualGraph.E =>
        C.residualGraph.Inc v e)
      ((Finset.univ : Finset C.residualGraph.E).filter
        (C.residualGraph.Inc v)) (by
          intro e
          rw [Finset.mem_filter]
          simp only [Finset.mem_univ, true_and])
      (fun e => C.quotientSplitCharge finite tau e * x (Sum.inr e) c)).symm]
  rw [C.sum_quotientHybridResidualEdges]
  rfl

/-- Hybrid uncovered charge is the joint-residual uncovered star sum. -/
theorem quotientHybrid_uncoveredCharge_eq_joint
    {q : ℕ} (x : C.quotientHybridGraph.E → Fin q → ℝ)
    (v : G.V) :
    C.quotientHybridGraph.uncoveredProposalCharge
        C.quotientHybridResidualEdges (C.quotientHybridResidualCharge finite tau)
        x v =
      ∑ e : C.residualGraph.E,
        if C.residualGraph.Inc v e then
          C.quotientSplitCharge finite tau e *
            (1 - ∑ c, x (Sum.inr e) c) else 0 := by
  classical
  unfold uncoveredProposalCharge
  rw [C.sum_quotientHybridResidualEdges]
  rfl

/-- A joint endpoint-multiplicity bound controls the hybrid pair charge,
because every finite or tiny artificial edge charge is at most one. -/
theorem quotientHybrid_pairCharge_le_of_pairMultiplicity
    {L : ℕ} (htau0 : 0 ≤ tau) (htauHalf : tau ≤ (1 : ℝ) / 2)
    (htiny : ∀ e ∉ finite, C.residualGraph.weight e ≤ tau)
    (hmult : C.residualGraph.PairMultiplicityAtMost L)
    (u v : G.V) :
    C.quotientHybridGraph.pairCharge
        C.quotientHybridResidualEdges (C.quotientHybridResidualCharge finite tau)
          u v ≤ L := by
  have hsum := C.residualGraph.sum_le_mul_of_pairMultiplicityAtMost
    hmult u v
    (fun e => if C.residualGraph.EndpointPairMatches u v e then
      C.quotientSplitCharge finite tau e else 0) 1
    (by norm_num)
    (fun e _he => by
      simp only [if_pos _he]
      exact C.quotientSplitCharge_le_one finite tau htau0 htauHalf htiny e)
    (fun e he => by simp [he])
  calc
    C.quotientHybridGraph.pairCharge
        C.quotientHybridResidualEdges (C.quotientHybridResidualCharge finite tau)
          u v =
        ∑ e : C.residualGraph.E,
          if C.residualGraph.EndpointPairMatches u v e then
            C.quotientSplitCharge finite tau e else 0 := by
      classical
      unfold pairCharge
      rw [C.sum_quotientHybridResidualEdges]
      apply Finset.sum_congr rfl
      intro e _he
      have hcond :
          (C.quotientHybridGraph.fst (Sum.inr e) = u ∧
              C.quotientHybridGraph.snd (Sum.inr e) = v) ∨
            (C.quotientHybridGraph.fst (Sum.inr e) = v ∧
              C.quotientHybridGraph.snd (Sum.inr e) = u) ↔
          C.residualGraph.EndpointPairMatches u v e := by
        simp only [EndpointPairMatches, quotientHybridGraph]
        constructor
        · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
          · exact Or.inl ⟨h₁.symm, h₂.symm⟩
          · exact Or.inr ⟨h₂.symm, h₁.symm⟩
        · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
          · exact Or.inl ⟨h₁.symm, h₂.symm⟩
          · exact Or.inr ⟨h₂.symm, h₁.symm⟩
      rw [if_congr hcond rfl rfl]
      rfl
    _ ≤ (L : ℝ) * 1 := hsum
    _ = L := by ring

end GeneralColoredPacketBase
end
end WeightedEdgeColoring.WeightedMultigraph
