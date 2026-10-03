import WeightedEdgeColoring.ExtendedProfileSelectedDecoderBudget

/-!
# Small-loss form of the selected-profile decoder
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})
variable {B k N reserve L K steps : ℕ}
variable {s beta q r extraGamma rho omega nibbleA nibbleDelta epsilon sigma : ℝ}
variable {hbeta : 0 < beta} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s beta q r hbeta hr)

/-- Decode a completed trace when each scalar loss has already been put on
the common `epsilon * palette` scale. -/
theorem exists_partialColoring_of_selectedBlockDyadicTrace_smallLoss
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (hrs : rho * s ≤ 1)
    (hrhoKappa : rho ≤ extendedProfileSmoothingKappa omega beta q r)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k beta q r)
    (hcapacityTiny : ∀ v c,
      G.selectedBlockNormalizedTinyReservoirLoad R0 rho omega choice (v, c) ≤
        (rho / extendedProfileSmoothingKappa omega beta q r) *
            G.extendedProfileReservoirSize R0 v
              (G.decodedExtendedProfileBlockSelection R0 choice v c) +
          extendedProfileCandidateCapacityScale rho s omega beta q r /
              ((B * k : ℕ) : ℝ) *
            extendedProfileBlockCombinedDeviation rho s omega beta q r B k)
    (hjointError :
      extendedProfileCandidateCapacityScale rho s omega beta q r /
            ((B * k : ℕ) : ℝ) *
          extendedProfileBlockCombinedDeviation rho s omega beta q r B k +
          2 * beta ≤
        (1 - rho / extendedProfileSmoothingKappa omega beta q r) * r)
    (hreserve : 0 < reserve) (hextraGamma0 : 0 ≤ extraGamma)
    (hextraGammaHalf : extraGamma ≤ 1 / 2)
    (hdyadicCover : 1 ≤ dyadicScale beta L)
    (hdyadicTop : dyadicScale beta L ≤ 2)
    (final : RankThreeOptionSystem.OriginalIterationState
      (G.largeEdgeJobSystem
        (G.selectedBlockDyadicQuantizedSystem
          (N := N) (reserve := reserve) (gamma := extraGamma) R0 omega rho choice
          (dyadicBucket beta L G.weight)) beta))
    (T : RankThreeOptionSystem.OriginalIterationState.EndpointSharpTrace
      (G.largeEdgeRestriction beta) beta nibbleA nibbleDelta L K steps
      (RankThreeOptionSystem.OriginalIterationState.full
        (G.largeEdgeJobSystem
          (G.selectedBlockDyadicQuantizedSystem
            (N := N) (reserve := reserve) (gamma := extraGamma) R0 omega rho choice
            (dyadicBucket beta L G.weight)) beta)) final)
    (hactive0 : ∀ j, j ∈
      (G.largeEdgeJobSystem
        (G.selectedBlockDyadicQuantizedSystem
          (N := N) (reserve := reserve) (gamma := extraGamma) R0 omega rho choice
          (dyadicBucket beta L G.weight)) beta).activeJobs)
    (htrace : ∀ v,
      RankThreeOptionSystem.OriginalIterationState.stateActiveStarWeight
        (G.largeEdgeRestriction beta) final v ≤ epsilon * (B * k : ℕ))
    (hquad : ∀ v,
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedExtendedProfileTotalOptionMass
          R0 rho omega choice e.1 - rho * s) ^ 2) ≤ sigma)
    (hpack : G.LocallyPacksInto (B * k))
    (hepsilon : 0 ≤ epsilon)
    (hsigma0 : 0 ≤ sigma) (hsigma : sigma ≤ epsilon ^ 2 * (B * k : ℕ))
    (hrhoLoss : 1 - rho * s ≤ epsilon)
    (hone : 1 ≤ epsilon * (B * k : ℕ))
    (hreserveSmall : (reserve : ℝ) ≤ epsilon * (B * k : ℕ))
    (hbetaSmall : beta ≤ epsilon * (B * k : ℕ)) :
    ∃ (P : Finset G.E) (color : G.E → Fin (B * k)),
      G.asMultigraph.IsFeasibleOn P color ∧
      ∀ v,
        (∑ e ∈ Finset.univ \ P,
          if G.Inc v e then G.weight e else 0) ≤
            37 * epsilon * (B * k : ℕ) := by
  have hgamma1 : extraGamma < 1 := hextraGammaHalf.trans_lt (by norm_num)
  have htinyA0 : 0 ≤
      rho / extendedProfileSmoothingKappa omega beta q r := by
    exact div_nonneg hrho (extendedProfileSmoothingKappa_pos
      (β := beta) (q := q) (r := r) homega0 homega1).le
  have htinyA1 : rho / extendedProfileSmoothingKappa omega beta q r ≤ 1 := by
    apply (div_le_one (extendedProfileSmoothingKappa_pos
      (β := beta) (q := q) (r := r) homega0 homega1)).2
    exact hrhoKappa
  obtain ⟨P, color, hfeasible, hloss⟩ :=
    G.exists_partialColoring_of_selectedBlockDyadicTrace R0 hn hs hq hr0 hr1
      hleft homega0 homega1 hrho hrs choice hcapacityTiny htinyA0 htinyA1
      hjointError hreserve hgamma1 hdyadicCover hdyadicTop final T hactive0
      (fun _ ↦ epsilon * (B * k : ℕ)) (fun _ ↦ sigma) htrace
      (fun _ ↦ hsigma0) hquad
  refine ⟨P, color, hfeasible, ?_⟩
  intro v
  apply (hloss v).trans
  apply selectedProfileDecoderLoss_le hepsilon (by positivity) le_rfl
  · unfold starWeight
    exact Finset.sum_nonneg fun e _he ↦ G.weight_nonneg e.1
  · exact G.starWeight_le_of_locallyPacksInto hpack v
  · exact hsigma0
  · exact hsigma
  · exact sub_nonneg.mpr hrs
  · exact hrhoLoss
  · exact hextraGamma0
  · exact hextraGammaHalf
  · exact hone
  · exact hreserveSmall
  · exact hbetaSmall

end WeightedSimpleGraph
end
end WeightedEdgeColoring
