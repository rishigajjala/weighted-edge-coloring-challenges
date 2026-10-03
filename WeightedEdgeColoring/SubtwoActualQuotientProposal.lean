import WeightedEdgeColoring.SubtwoActualQuotientReserve
import WeightedEdgeColoring.SubtwoActualQuotientResidualMultiplicity
import WeightedEdgeColoring.SubtwoQuotientFiniteThresholdClass
import WeightedEdgeColoring.SubtwoQuotientProposalFixedScale

/-! The actual floor quotient supplies every graph-side input to the diffuse
finite/tiny proposal: a fifth-bin reserve, bounded residual pairs, and the
canonical reciprocal harmonic classes. -/

namespace WeightedEdgeColoring.WeightedMultigraph

open scoped BigOperators
noncomputable section
universe u

/-- Actual physical quotient moment proposals, uniform in the graph and the
chosen floor packet coloring. The only structural input is the proved
bounded-type/one-tiny floor premise of the preprocessed graph. -/
theorem exists_subtwoFloorPhysicalProposal_fixedScale
    (T D : ℕ) (hT : 160 ≤ T)
    (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 100) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (n k : ℕ)
      (hk : 0 < k) (hn : 0 < n)
      (hlocal : G.LocallyPacksInto n)
      (hfloor : G.FloorBundleAtMostOneTiny D T)
      (hKlower : subtwoKappa * n ≤ k)
      (hKupper : (k : ℝ) ≤ 4 * n)
      (heven : Even k) (hfour : 4 ≤ k)
      (color : (G.subtwoFloorQuotient n).E → Fin k)
      (hproper : (G.subtwoFloorQuotient n).IsProperOn
        (G.subtwoFloorQuotientEdges n) color),
      N ≤ 4 * n → 60000 * (T + 1) ≤ n →
      let C := G.subtwoFloorPhysicalColoredPacketBase hk n color hproper
      let finite := C.quotientFiniteEdges T
      ∃ (C' : (G.subtwoQuotient (G.subtwoFloorBlock n)).GeneralColoredPacketBase k)
        (x : C.residualGraph.E → Fin k → ℝ)
        (mixed : C.quotientHybridGraph.E → Fin k)
        (hmixed : C.quotientHybridGraph.IsProperOn
          C.quotientHybridPacketEdges mixed),
        C' = C.quotientRecoloredBase mixed hmixed ∧
        C'.fullEdges = C.fullEdges ∧
        C'.residualEdges = C.residualEdges ∧
        (∀ e c, 0 ≤ x e c ∧ x e c ≤ 100 / n) ∧
        (∀ e, ∑ c, x e c ≤ 1) ∧
        (∀ v c,
          (∑ e : C.residualGraph.StarEdge v,
            C.quotientSplitCharge finite ((1 : ℝ) / T) e.1 * x e.1 c) +
              6 * (T + 1 : ℝ) * (100 / n) ≤ 1) ∧
        (∀ e c, 0 < x e c →
          c ∈ (G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
            C'.fullEdges C'.baseColor
              ((G.subtwoQuotient (G.subtwoFloorBlock n)).fst e.1) ∧
          c ∈ (G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
            C'.fullEdges C'.baseColor
              ((G.subtwoQuotient (G.subtwoFloorBlock n)).snd e.1)) ∧
        ∀ v, C.residualGraph.proposalDeficit x v ≤ 4 * eps * n := by
  have hTpos : 0 < T := by omega
  have htau0 : 0 ≤ (1 : ℝ) / T := by positivity
  have htau160 : (1 : ℝ) / T ≤ 1 / 160 := by
    have ht : (160 : ℝ) ≤ T := by exact_mod_cast hT
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < T)).2
    nlinarith
  let L := 25*((D+1)*(((T+1)^(D+1)*T+T)+1))
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨N, hN⟩ :=
    GeneralColoredPacketBase.exists_quotientSplitHybridProposal_fixedScale
      (T := T) eps ((1 : ℝ) / T) L heps0 heps1 hL hTpos
      htau0 (by linarith)
  refine ⟨N, ?_⟩
  intro G n k hk hn hlocal hfloor hKlower hKupper heven hfour color hproper
    hnN hnlarge
  let C := G.subtwoFloorPhysicalColoredPacketBase hk n color hproper
  let finite := C.quotientFiniteEdges T
  have htiny : ∀ e ∉ finite, C.residualGraph.weight e ≤ (1 : ℝ) / T := by
    intro e he
    exact C.quotientTinyWeight_le T e he
  have hmult : C.residualGraph.PairMultiplicityAtMost L := by
    exact G.subtwoFloorPhysicalColoredPacketBase_residualMultiplicity_of_oneTiny
      D T hk hn hlocal hfloor color hproper
  have hgap : ∀ v, C.quotientSplitStarCharge finite ((1 : ℝ) / T) v +
      (n : ℝ) / 5 ≤
      ((G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
        C.fullEdges C.baseColor v).card := by
    intro v
    exact G.subtwoFloorPhysical_splitReserve_fifth_of_paletteBound
      hk hn hlocal hKlower hKupper color hproper finite _
      htau0 htau160 v
  exact hN (G.subtwoQuotient (G.subtwoFloorBlock n)) k n C finite
    htiny hnN hnlarge heven hfour hKupper hmult hgap

end
end WeightedEdgeColoring.WeightedMultigraph
