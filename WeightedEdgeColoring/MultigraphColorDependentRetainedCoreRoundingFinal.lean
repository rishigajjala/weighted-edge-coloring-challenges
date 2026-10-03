import WeightedEdgeColoring.MultigraphColorDependentRetainedCoreLargeScales
import WeightedEdgeColoring.StarSigmaSqrtBound

/-!
# Retained proposal core rounding

The block selector, closed large-edge iteration, and deterministic decoder
are composed here.  The only threshold in the result is the ambient star
scale `n`.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

universe u

namespace WeightedMultigraph

set_option maxHeartbeats 1000000 in
/-- The colour-dependent selector and isolated endpoint iteration prove the
retained proposal core rounding statement. -/
theorem boundedMultiplicityRetainedProposalCoreRounding_proved
    (mult : ℕ) (hmultPos : 0 < mult) (C0 gamma eta : ℝ)
    (hC0 : 0 < C0) (hgamma0 : 0 < gamma) (hgamma1 : gamma < 1)
    (hgammaEta : 64 * gamma < eta) :
    ∃ N k : ℕ, 0 < k ∧
      ∀ (G : WeightedMultigraph.{u}) (n B : ℕ)
      (x : G.E → Fin (B * k) → ℝ),
      N ≤ n → G.PairMultiplicityAtMost mult → 0 < B →
      (∀ v, G.starWeight v ≤ n) →
      ((B * k : ℕ) : ℝ) ≤ 4 * n →
      (∀ e c, 0 ≤ x e c ∧ x e c ≤ C0 / n) →
      (∀ e, ∑ c, x e c ≤ 1) →
      (∀ v c, G.IsAverageOfStarFeasibleSets v
        (fun e : G.StarEdge v ↦ x e.1 c)) →
      ∃ (P : Finset G.E) (color : G.E → Fin (B * k)),
        G.IsFeasibleOn P color ∧
        (∀ e ∈ P, 0 < x e (color e)) ∧
        ∀ v,
          (∑ e ∈ (Finset.univ \ G.lowProposalMassEdges x gamma) \ P,
            if G.Inc v e then G.weight e else 0) ≤ eta * n := by
  by_cases hetaLarge : 1 ≤ eta
  · refine ⟨0, 1, by norm_num, ?_⟩
    intro G n B x _hn _hpair hB hstar _hpalette _hx _hmass _hlocal
    classical
    have hpalettePos : 0 < B * 1 := Nat.mul_pos hB (by norm_num)
    let color : G.E → Fin (B * 1) := fun _e ↦ ⟨0, hpalettePos⟩
    refine ⟨∅, color, ?_, ?_, ?_⟩
    · intro v c
      simp [WeightedMultigraph.colorLoadOn]
    · simp
    · intro v
      have hrestricted := G.restrictedStarWeight_le_starWeight
        ((Finset.univ \ G.lowProposalMassEdges x gamma) \ (∅ : Finset G.E)) v
      have hneta : (n : ℝ) ≤ eta * n := by
        nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      exact hrestricted.trans ((hstar v).trans hneta)
  · have heta1 : eta < 1 := lt_of_not_ge hetaLarge
    have hgammaEta' : gamma < eta := by nlinarith
    let tau := retainedCoreTau C0 gamma eta
    have htau0 : 0 < tau := retainedCoreTau_pos hC0 hgammaEta'
    have htau1 : tau ≤ 1 / 4 := retainedCoreTau_le_quarter C0 gamma eta
    obtain ⟨k, Nselector, hk4, hselectorScales⟩ :=
      exists_retainedCoreSelectorScales hmultPos hC0 hgammaEta'
    obtain ⟨Nlarge, hlarge⟩ :=
      exists_retainedCoreLargeMatching_eventually
        hmultPos hC0 hgamma0 hgammaEta heta1
    refine ⟨max Nselector Nlarge, k, lt_of_lt_of_le (by norm_num) hk4, ?_⟩
    intro G n B x hnLarge hpair hB hstar hpaletteR hx hmass hlocal
    have hnSelector : Nselector ≤ n :=
      (le_max_left Nselector Nlarge).trans hnLarge
    have hnLarge' : Nlarge ≤ n :=
      (le_max_right Nselector Nlarge).trans hnLarge
    have hn : 0 < n := by
      have hkn : 0 < B * k := Nat.mul_pos hB
        (lt_of_lt_of_le (by norm_num) hk4)
      have hpal0 : (0 : ℝ) < (B * k : ℕ) := by exact_mod_cast hkn
      have hfourN : (0 : ℝ) < 4 * (n : ℝ) :=
        hpal0.trans_le (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hpaletteR)
      have hnreal : (0 : ℝ) < n := by nlinarith only [hfourN]
      exact_mod_cast hnreal
    have hn1 : 1 ≤ n := hn
    have hpalette : B * k ≤ 4 * n := by exact_mod_cast hpaletteR
    have hselector := hselectorScales n B hnSelector hpalette
    let proposal := G.retainedCoreProductProposal x
    let scale := (mult : ℝ) * colorDependentCandidateCapacityScale
      (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
      (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) C0
    let D := FinitePartialResamplingNumerics.packingDeviation n
      (colorDependentBlockCombinedColumnBound n k
        (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau))
    let rawSigma := colorDependentBlockNaturalSigma mult B n k
      (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
      (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) C0
    let sigma := max 0 rawSigma
    obtain ⟨hβ, hr, R, selected, _hsupport, hcapacity, hquad, htiny⟩ :=
      G.exists_jointProfileColorDependentSelection hmultPos hpair x hB hk4 hn hpalette
        htau0 htau1 hC0 (retainedCoreTau_le_C0_div C0 gamma eta)
        hx hmass hlocal hstar
    have hrawSigma : rawSigma ≤ ((eta - gamma) / 1024) ^ 2 * n := by
      simpa [rawSigma, tau] using hselector.1
    have hsigma : sigma ≤ ((eta - gamma) / 1024) ^ 2 * n := by
      apply max_le
      · positivity
      · exact hrawSigma
    have hdev : scale / n * D ≤ tau ^ 2 / 4 := by
      simpa [scale, D, tau] using hselector.2
    rcases jointProfile_parameters htau0 htau1 with
      ⟨hspos, _hbeta, hqpos, _hrpos, homega0, _homega1, _hleft,
        _hr1, hrhopos, _hrhoKappa, _hfraction⟩
    have hsigma0 : 0 ≤ sigma := le_max_left _ _
    have hquadSigma : ∀ v,
        (∑ e : G.StarEdge v, G.weight e.1 *
          (G.selectedColorDependentTotalOptionMass proposal R
              (jointProfileRho tau) (jointProfileOmega tau)
              (G.encodedColorDependentSelectedBlock proposal R selected) e.1 -
            G.colorDependentTotalTarget proposal
              (jointProfileRho tau) (jointProfileS tau) e.1) ^ 2) ≤ sigma := by
      intro v
      exact (hquad v).trans (le_max_right _ _)
    have hproposalMass : ∀ e, G.proposalMass proposal e ≤ 1 := by
      intro e
      change (∑ c : Fin B × Fin k, x e (finProdFinEquiv c)) ≤ 1
      rw [show (∑ c : Fin B × Fin k, x e (finProdFinEquiv c)) =
          ∑ d : Fin (B * k), x e d by
        exact Equiv.sum_comp finProdFinEquiv (x e)]
      exact hmass e
    have hrhos0 : 0 ≤ jointProfileRho tau * jointProfileS tau :=
      mul_nonneg hrhopos.le hspos.le
    have hrhos1 : jointProfileRho tau * jointProfileS tau ≤ 1 := by
      unfold jointProfileRho jointProfileS
      nlinarith [sq_nonneg (1 - 2 * tau)]
    have hresidual : ∀ v,
        G.weightedResidualStar
            (G.selectedColorDependentRetainedMacroscopicResidual
              proposal R gamma (jointProfileBeta tau)
              (jointProfileRho tau) (jointProfileOmega tau)
              (G.encodedColorDependentSelectedBlock proposal R selected)) v ≤
          (gamma + 4 * tau + (eta - gamma) / 1024) * n := by
      intro v
      have hquadAll :
          (∑ e : G.StarEdge v, G.weight e.1 *
            (G.selectedColorDependentAllOptionMass proposal R
                (jointProfileRho tau) (jointProfileOmega tau)
                (G.encodedColorDependentSelectedBlock proposal R selected) e.1 -
              G.colorDependentTotalTarget proposal
                (jointProfileRho tau) (jointProfileS tau) e.1) ^ 2) ≤ sigma := by
        simpa only [G.selectedColorDependentAllOptionMass_eq_total] using
          hquadSigma v
      have hraw :=
        G.weightedResidualStar_selectedColorDependentRetained_le_sqrt
          proposal R gamma (jointProfileBeta tau)
          (jointProfileRho tau) (jointProfileOmega tau) hgamma0.le
          hrhos0 hrhos1 hproposalMass
          (G.encodedColorDependentSelectedBlock proposal R selected)
          v sigma hsigma0 hquadAll
      have hgap := jointProfile_retainedGap_le htau0 htau1
        hgamma0.le hgamma1.le
      have hstar0 : 0 ≤ G.starWeight v :=
        Finset.sum_nonneg fun e _he ↦ G.weight_nonneg e.1
      have heps0 : 0 ≤ (eta - gamma) / 1024 := by
        exact div_nonneg (by nlinarith [hgammaEta, hgamma0]) (by norm_num)
      have hsqrt : Real.sqrt (G.starWeight v * sigma) ≤
          (eta - gamma) / 1024 * n := by
        exact sqrt_star_mul_sigma_le hstar0 (hstar v) hsigma0 hsigma
          heps0 (Nat.cast_nonneg n)
      have hcoef0 : 0 ≤ gamma + 4 * tau := by positivity
      have hlinear :
          (1 - jointProfileRho tau * jointProfileS tau * (1 - gamma)) *
              G.starWeight v ≤
            (gamma + 4 * tau) * n := by
        exact (mul_le_mul_of_nonneg_right hgap hstar0).trans
          (mul_le_mul_of_nonneg_left (hstar v) hcoef0)
      exact hraw.trans (by nlinarith)
    obtain ⟨M, hM, hlargeSubset, hlargeSupport, hlargeLoad, hlargeLoss⟩ :=
      hlarge G n B k x hnLarge' hpair hB hk4 hpalette hstar hx hmass
        hβ hr R selected hcapacity hdev hresidual
    have htiny' := fun v c ↦ (htiny v c).le
    exact G.exists_retainedCore_partialColoring_of_selection_and_matching x
      hC0 hgamma0 hgamma1 hgammaEta hn1 hB
      (lt_of_lt_of_le (by norm_num) hk4)
      (fun e c ↦ (hx e c).1) hmass hstar hsigma0 hsigma hdev hβ hr
      R selected hquadSigma M hM hlargeSubset hlargeSupport hlargeLoad htiny'
      hlargeLoss le_rfl

end WeightedMultigraph

end

end WeightedEdgeColoring
