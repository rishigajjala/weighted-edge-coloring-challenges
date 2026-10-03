import WeightedEdgeColoring.SubtwoQuotientHybridCharge
import WeightedEdgeColoring.WeightedMomentPaletteMixingProof

/-! The weighted-moment hybrid proposal retains the stronger charge row
needed by the original-label local law. -/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open scoped BigOperators
noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

universe u

namespace GeneralColoredPacketBase

variable {T : ℕ}

/-- The moment proposal carries an extra fixed label/class atom budget.
It is precisely the row consumed by `exists_jointSingleLabelLawAndRealizations`.
The required graph size threshold remains the one from weighted-moment
mixing; the stronger local slack is a separate input. -/
theorem exists_quotientSplitHybridProposal_with_labelCharge
    {Label : Type*} [Fintype Label]
    (alpha Cbound eps : ℝ) (L : ℕ)
    (halpha : 0 < alpha) (hCbound : 0 < Cbound)
    (hL : 0 < L) (heps : 0 < eps) (hT : 0 < T)
    (tau : ℝ)
    (htau0 : 0 ≤ tau) (htauHalf : tau ≤ (1 : ℝ) / 2) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (K n : ℕ)
      (C : G.GeneralColoredPacketBase K)
      (finite : Finset C.residualGraph.E),
      (∀ e ∉ finite, C.residualGraph.weight e ≤ tau) →
      N ≤ n → 0 < n → Even K → 4 ≤ K →
      (∀ v, alpha * n ≤
        (G.missingColorsAt C.fullEdges
          C.baseColor v).card) →
      (K : ℝ) ≤ Cbound * n →
      (∀ v, C.quotientSplitStarCharge finite tau v ≤ n) →
      C.residualGraph.PairMultiplicityAtMost L →
      (∀ v,
        C.quotientSplitStarCharge finite tau v /
            (G.missingColorsAt C.fullEdges
              C.baseColor v).card + eps +
          (Fintype.card Label : ℝ) * (T + 1 : ℝ) *
            (Cbound / (alpha ^ 2 * n)) ≤ 1) →
      ∃ (C' : G.GeneralColoredPacketBase K)
        (x : C.residualGraph.E → Fin K → ℝ)
        (mixed : C.quotientHybridGraph.E → Fin K)
        (hmixed : C.quotientHybridGraph.IsProperOn
          C.quotientHybridPacketEdges mixed),
        C' = C.quotientRecoloredBase mixed hmixed ∧
        C'.fullEdges = C.fullEdges ∧
        C'.residualEdges = C.residualEdges ∧
        C.residualGraph.PairMultiplicityAtMost L ∧
        (∀ e c, 0 ≤ x e c ∧ x e c ≤ Cbound / (alpha ^ 2 * n)) ∧
        (∀ e, ∑ c, x e c ≤ 1) ∧
        (∀ v c,
          (∑ e : C.residualGraph.StarEdge v,
            C.quotientSplitCharge finite tau e.1 * x e.1 c) +
            (Fintype.card Label : ℝ) * (T + 1 : ℝ) *
              (Cbound / (alpha ^ 2 * n)) ≤ 1) ∧
        (∀ e c, 0 < x e c →
          c ∈ G.missingColorsAt C'.fullEdges
              C'.baseColor (G.fst e.1) ∧
            c ∈ G.missingColorsAt C'.fullEdges
              C'.baseColor (G.snd e.1)) ∧
        ∀ v, C.residualGraph.proposalDeficit x v ≤ eps * n := by
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have htau1 : tau < 1 := by linarith
  rcases weightedMomentPaletteMixing_proved alpha Cbound (L : ℝ) eps
      halpha hCbound hLreal heps with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro G K n C finite htiny hn hnpos heven hfour hmissing hpalette hchargeStar hmult
    hlocal
  have hcharge0 : ∀ e ∈ C.quotientHybridResidualEdges,
      0 ≤ (C.quotientHybridResidualCharge finite tau) e := by
    intro e he
    rcases e with p | e
    · exact (C.not_mem_quotientHybridResidualEdges_inl p he).elim
    · exact C.quotientSplitCharge_nonneg finite tau htau1 e
  have hrestricted : ∀ v,
      C.quotientHybridGraph.restrictedCharge
        C.quotientHybridResidualEdges (C.quotientHybridResidualCharge finite tau) v ≤ n := by
    intro v
    rw [C.quotientHybrid_restrictedCharge_eq_jointStarCharge finite tau]
    exact hchargeStar v
  have hpair : ∀ u v,
      C.quotientHybridGraph.pairCharge
        C.quotientHybridResidualEdges (C.quotientHybridResidualCharge finite tau)
          u v ≤ (L : ℝ) := by
    intro u v
    exact C.quotientHybrid_pairCharge_le_of_pairMultiplicity finite tau
      htau0 htauHalf htiny hmult u v
  have hmissingHybrid : ∀ v, alpha * n ≤
      (C.quotientHybridGraph.missingColorsAt
        C.quotientHybridPacketEdges C.quotientHybridBaseColor v).card := by
    intro v
    rw [C.quotientHybrid_missingColorsAt_eq_base v]
    exact hmissing v
  rcases hN C.quotientHybridGraph n K C.quotientHybridPacketEdges
      C.quotientHybridResidualEdges C.quotientHybridBaseColor
      (C.quotientHybridResidualCharge finite tau) hn hnpos heven hfour
      C.quotientHybridPacketEdges_disjoint_residualEdges
      C.quotientHybridBaseColor_isProperOn hmissingHybrid hpalette
      hcharge0 hrestricted hpair with
    ⟨mixed, xHybrid, hmixed, hsupport, hx, hmass, hrow, huncovered⟩
  let C' := C.quotientRecoloredBase mixed hmixed
  let x : C.residualGraph.E → Fin K → ℝ :=
    fun e c ↦ xHybrid (Sum.inr e) c
  refine ⟨C', x, mixed, hmixed, rfl, rfl, rfl, hmult, ?_, ?_, ?_, ?_, ?_⟩
  · intro e c
    exact hx (Sum.inr e) (C.mem_quotientHybridResidualEdges_inr e) c
  · intro e
    exact hmass (Sum.inr e) (C.mem_quotientHybridResidualEdges_inr e)
  · intro v c
    have hr := hrow v c
    rw [C.quotientHybrid_proposalChargeLoad_eq_joint finite tau] at hr
    rw [C.quotientHybrid_restrictedCharge_eq_jointStarCharge finite tau] at hr
    have hcard :
        ((C.quotientHybridGraph.missingColorsAt
          C.quotientHybridPacketEdges mixed v).card : ℝ) =
        ((G.missingColorsAt C.fullEdges
          C.baseColor v).card : ℝ) := by
      congr 1
      calc
        (C.quotientHybridGraph.missingColorsAt
            C.quotientHybridPacketEdges mixed v).card =
          (C.quotientHybridGraph.missingColorsAt
            C.quotientHybridPacketEdges C.quotientHybridBaseColor v).card :=
          C.quotientHybridGraph.card_missingColorsAt_eq_of_isProperOn
            C.quotientHybridPacketEdges mixed C.quotientHybridBaseColor
            hmixed C.quotientHybridBaseColor_isProperOn v
        _ = _ := by
          rw [C.quotientHybrid_missingColorsAt_eq_base v]
    rw [hcard] at hr
    have hl := hlocal v
    change
      (∑ e : C.residualGraph.StarEdge v,
        C.quotientSplitCharge finite tau e.1 * xHybrid (Sum.inr e.1) c) +
          (Fintype.card Label : ℝ) * (T + 1 : ℝ) *
            (Cbound / (alpha ^ 2 * n)) ≤ 1
    linarith
  · intro e c hpos
    have hs := hsupport (Sum.inr e)
      (C.mem_quotientHybridResidualEdges_inr e) c hpos
    simpa [C', x, quotientRecolored_missingColorsAt_eq_hybrid] using hs
  · intro v
    have hu := huncovered v
    rw [C.quotientHybrid_uncoveredCharge_eq_joint finite tau] at hu
    exact (C.quotientSplit_proposalDeficit_le_uncoveredCharge finite tau
      (fun e c ↦ xHybrid (Sum.inr e) c) htau0 htau1
      (fun e ↦ hmass (Sum.inr e)
        (C.mem_quotientHybridResidualEdges_inr e)) v).trans hu

end GeneralColoredPacketBase
end
end WeightedMultigraph
end WeightedEdgeColoring
