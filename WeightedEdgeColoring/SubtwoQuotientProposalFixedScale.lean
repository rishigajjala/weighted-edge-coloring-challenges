import WeightedEdgeColoring.SubtwoQuotientHybridMixing
import WeightedEdgeColoring.SubtwoFiniteTinyLabelParameterBounds

/-! Concrete fourfold scale and six-symbol label budget for the physical
quotient moment proposal. -/

namespace WeightedEdgeColoring.WeightedMultigraph

open scoped BigOperators
noncomputable section
universe u
namespace GeneralColoredPacketBase

variable {T : ℕ}

/-- The only numerical input left after actual packet-charge accounting is
`J+n/5≤Missing`; the diffuse label row is then automatic. -/
theorem exists_quotientSplitHybridProposal_fixedScale
    (eps tau : ℝ) (L : ℕ)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 100)
    (hL : 0 < L) (hT : 0 < T)
    (htau0 : 0 ≤ tau) (htauHalf : tau ≤ (1 : ℝ) / 2) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (K n : ℕ)
      (C : G.GeneralColoredPacketBase K)
      (finite : Finset C.residualGraph.E),
      (∀ e ∉ finite, C.residualGraph.weight e ≤ tau) →
      N ≤ 4 * n → 60000 * (T + 1) ≤ n →
      Even K → 4 ≤ K →
      (K : ℝ) ≤ 4 * n →
      C.residualGraph.PairMultiplicityAtMost L →
      (∀ v, C.quotientSplitStarCharge finite tau v + (n : ℝ) / 5 ≤
        (G.missingColorsAt C.fullEdges C.baseColor v).card) →
      ∃ (C' : G.GeneralColoredPacketBase K)
        (x : C.residualGraph.E → Fin K → ℝ)
        (mixed : C.quotientHybridGraph.E → Fin K)
        (hmixed : C.quotientHybridGraph.IsProperOn
          C.quotientHybridPacketEdges mixed),
        C' = C.quotientRecoloredBase mixed hmixed ∧
        C'.fullEdges = C.fullEdges ∧
        C'.residualEdges = C.residualEdges ∧
        (∀ e c, 0 ≤ x e c ∧ x e c ≤ 100 / n) ∧
        (∀ e, ∑ c, x e c ≤ 1) ∧
        (∀ v c,
          (∑ e : C.residualGraph.StarEdge v,
            C.quotientSplitCharge finite tau e.1 * x e.1 c) +
              6 * (T + 1 : ℝ) * (100 / n) ≤ 1) ∧
        (∀ e c, 0 < x e c →
          c ∈ G.missingColorsAt C'.fullEdges C'.baseColor (G.fst e.1) ∧
          c ∈ G.missingColorsAt C'.fullEdges C'.baseColor (G.snd e.1)) ∧
        ∀ v, C.residualGraph.proposalDeficit x v ≤ 4 * eps * n := by
  obtain ⟨N, hN⟩ :=
    exists_quotientSplitHybridProposal_with_labelCharge
      (T := T) (Label := Fin 6)
      (1 / 20) 1 eps L (by norm_num) (by norm_num) hL heps0 hT
      tau htau0 htauHalf
  refine ⟨N, ?_⟩
  intro G K n C finite htiny hn hlarge heven hfour hK hmult hgap
  have hnpos : 0 < n := by omega
  have hnMix : 0 < 4 * n := by omega
  have htau1 : tau < 1 := by linarith
  have hJ0 : ∀ v, 0 ≤ C.quotientSplitStarCharge finite tau v := by
    intro v
    unfold quotientSplitStarCharge
    exact Finset.sum_nonneg fun e _ =>
      C.quotientSplitCharge_nonneg finite tau htau1 e.1
  have hmissing : ∀ v, (1 / 20 : ℝ) * (4 * n : ℕ) ≤
      (G.missingColorsAt C.fullEdges C.baseColor v).card := by
    intro v
    have h := hgap v
    have h0 := hJ0 v
    push_cast
    nlinarith
  have hcharge : ∀ v, C.quotientSplitStarCharge finite tau v ≤
      (4 * n : ℕ) := by
    intro v
    have h := hgap v
    have hcardNat : (G.missingColorsAt C.fullEdges C.baseColor v).card ≤ K := by
      simpa using Finset.card_le_card
        (Finset.subset_univ (G.missingColorsAt C.fullEdges C.baseColor v))
    have hcard : ((G.missingColorsAt C.fullEdges C.baseColor v).card : ℝ) ≤ K := by
      exact_mod_cast hcardNat
    have hK4 : (K : ℝ) ≤ (4 * n : ℕ) := by simpa [Nat.cast_mul] using hK
    linarith
  have hlocal : ∀ v,
      C.quotientSplitStarCharge finite tau v /
          (G.missingColorsAt C.fullEdges C.baseColor v).card + eps +
        (Fintype.card (Fin 6) : ℝ) * (T + 1 : ℝ) *
          (1 / (((1 / 20 : ℝ) ^ 2) * (4 * n : ℕ))) ≤ 1 := by
    intro v
    apply subtwoFiniteTiny_sixLabelLocalBudget_smallEps
      hlarge (by decide) (hJ0 v) (by
        convert hgap v using 1 <;> ring)
      (by
        have hcardNat : (G.missingColorsAt C.fullEdges C.baseColor v).card ≤ K := by
          simpa using Finset.card_le_card
            (Finset.subset_univ (G.missingColorsAt C.fullEdges C.baseColor v))
        have hcard : ((G.missingColorsAt C.fullEdges C.baseColor v).card : ℝ) ≤ K := by
          exact_mod_cast hcardNat
        have hK4 : (K : ℝ) ≤ (4 * n : ℕ) := by
          simpa [Nat.cast_mul] using hK
        exact hcard.trans hK4) heps1
  obtain ⟨C', x, mixed, hmixed, hrec, hfull, hres, _hmult,
      hx, hmass, hrow, hsupport, hdef⟩ :=
    hN G K (4 * n) C finite htiny hn hnMix heven hfour hmissing (by simpa using hK)
      hcharge hmult hlocal
  have hfactor :
      (1 / (((1 / 20 : ℝ) ^ 2) * (4 * n : ℕ))) = 100 / n := by
    push_cast
    field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hnpos.ne']
    ring
  refine ⟨C', x, mixed, hmixed, hrec, hfull, hres, ?_, hmass,
    ?_, hsupport, ?_⟩
  · intro e c
    have hh := hx e c
    rw [hfactor] at hh
    exact hh
  · intro v c
    have hh := hrow v c
    rw [hfactor] at hh
    simpa using hh
  · intro v
    have hh := hdef v
    push_cast at hh
    nlinarith

end GeneralColoredPacketBase
end
end WeightedEdgeColoring.WeightedMultigraph
