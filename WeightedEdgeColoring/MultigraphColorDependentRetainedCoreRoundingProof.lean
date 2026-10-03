import WeightedEdgeColoring.MultigraphStarHalfLoad

import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileBlockSelectorAsymptotics
import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileSelectedCapacityOptionBridge
import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileRetainedCoreDecoder
import WeightedEdgeColoring.MultigraphColorDependentRetainedCoreScalars


/-!
# Colour-dependent selection for retained-core rounding

This file carries out the first half of the retained-core proof.  It
reindexes the flat palette into fixed blocks, constructs all local profile
realizations, and applies the natural capacity-and-variance selector.  Its
output is the exact input consumed by the large-edge matching constructor
and the retained-core decoder.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

def retainedCoreProductProposal
    {B k : ℕ} (x : G.E → Fin (B * k) → ℝ) :
    G.E → (Fin B × Fin k) → ℝ :=
  fun e c ↦ x e (finProdFinEquiv c)

/-- Reindexing a flat exact-multiple palette preserves all proposal
hypotheses needed by the profile construction. -/
theorem reindexedProposal_basic
    {B k n : ℕ} {C0 : ℝ}
    (x : G.E → Fin (B * k) → ℝ)
    (hx : ∀ e c, 0 ≤ x e c ∧ x e c ≤ C0 / n)
    (hmass : ∀ e, ∑ c, x e c ≤ 1)
    (hload : ∀ v c,
      (∑ e : G.StarEdge v, G.weight e.1 * x e.1 c) ≤ 1 / 2) :
    let proposal : G.E → (Fin B × Fin k) → ℝ :=
      fun e c ↦ x e (finProdFinEquiv c)
    (∀ e c, 0 ≤ proposal e c ∧ proposal e c ≤ C0 / n) ∧
      (∀ e, ∑ c, proposal e c ≤ 1) ∧
      ∀ v c,
        (∑ e : G.StarEdge v, G.weight e.1 * proposal e.1 c) ≤ 1 / 2 := by
  dsimp
  refine ⟨fun e c ↦ hx e (finProdFinEquiv c), ?_, ?_⟩
  · intro e
    have hreindex :
        (∑ c : Fin B × Fin k, x e (finProdFinEquiv c)) =
          ∑ d : Fin (B * k), x e d := by
      exact Equiv.sum_comp finProdFinEquiv (x e)
    rw [hreindex]
    exact hmass e
  · intro v c
    exact hload v (finProdFinEquiv c)

theorem proposalMass_reindexed_eq
    {B k : ℕ} (x : G.E → Fin (B * k) → ℝ) (e : G.E) :
    G.proposalMass (fun e (c : Fin B × Fin k) ↦
        x e (finProdFinEquiv c)) e = G.proposalMass x e := by
  unfold proposalMass
  exact Equiv.sum_comp finProdFinEquiv (x e)

theorem lowProposalMassEdges_reindexed_eq
    {B k : ℕ} (x : G.E → Fin (B * k) → ℝ) (gamma : ℝ) :
    G.lowProposalMassEdges
        (fun e (c : Fin B × Fin k) ↦ x e (finProdFinEquiv c)) gamma =
      G.lowProposalMassEdges x gamma := by
  ext e
  simp only [lowProposalMassEdges, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rw [G.proposalMass_reindexed_eq x e]

/-- A nonempty retained core forces the exact-multiple palette to have
linear size.  This is the lower scale used by the large-edge iteration. -/
theorem palette_lower_of_mem_retainedCore
    {B k n : ℕ} {C0 gamma : ℝ}
    (x : G.E → Fin (B * k) → ℝ)
    (hn : 0 < n) (hC0 : 0 ≤ C0)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hx : ∀ e c, x e c ≤ C0 / n)
    {e : G.E} (he : e ∉ G.lowProposalMassEdges x gamma) :
    (1 - gamma) * n ≤ C0 * (B * k : ℕ) := by
  have hhigh : 1 - gamma ≤ G.proposalMass x e := by
    have hnot : ¬G.proposalMass x e < 1 - gamma := by
      simpa [lowProposalMassEdges] using he
    exact le_of_not_gt hnot
  have hsum : G.proposalMass x e ≤ (B * k : ℕ) * (C0 / n) := by
    unfold proposalMass
    calc
      (∑ c, x e c) ≤ ∑ _c : Fin (B * k), C0 / n := by
        apply Finset.sum_le_sum
        intro c _hc
        exact hx e c
      _ = (B * k : ℕ) * (C0 / n) := by simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (1 - gamma) * n ≤ G.proposalMass x e * n :=
      mul_le_mul_of_nonneg_right hhigh hnR.le
    _ ≤ ((B * k : ℕ) * (C0 / n)) * n :=
      mul_le_mul_of_nonneg_right hsum hnR.le
    _ = C0 * (B * k : ℕ) := by
      field_simp [hnR.ne']

/-- The empty retained-core case is already a valid output. -/
theorem exists_retainedCore_partialColoring_of_empty
    {B k : ℕ} (x : G.E → Fin (B * k) → ℝ) {gamma eta : ℝ}
    (hpalettePos : 0 < B * k) (heta0 : 0 ≤ eta) (hn : ℕ)
    (hempty : Finset.univ \ G.lowProposalMassEdges x gamma = ∅) :
    ∃ (P : Finset G.E) (color : G.E → Fin (B * k)),
      G.IsFeasibleOn P color ∧
      (∀ e ∈ P, 0 < x e (color e)) ∧
      ∀ v,
        (∑ e ∈ (Finset.univ \ G.lowProposalMassEdges x gamma) \ P,
          if G.Inc v e then G.weight e else 0) ≤ eta * hn := by
  classical
  let color : G.E → Fin (B * k) := fun _e ↦ ⟨0, hpalettePos⟩
  refine ⟨∅, color, ?_, ?_, ?_⟩
  · intro v c
    simp [WeightedMultigraph.colorLoadOn]
  · simp
  · intro v
    rw [hempty]
    simpa using mul_nonneg heta0 (Nat.cast_nonneg hn)

/-- One selector accuracy simultaneously pays the final square-root error
and the tiny-reservoir capacity error. -/
def retainedCoreSelectorError (C0 gamma eta : ℝ) : ℝ :=
  min ((eta - gamma) / 1024)
    (retainedCoreTau C0 gamma eta ^ 2 / 4)

theorem retainedCoreSelectorError_pos
    {C0 gamma eta : ℝ} (hC0 : 0 < C0) (hgammaEta : gamma < eta) :
    0 < retainedCoreSelectorError C0 gamma eta := by
  unfold retainedCoreSelectorError
  exact lt_min (div_pos (sub_pos.mpr hgammaEta) (by norm_num)) (by
    have htau := retainedCoreTau_pos hC0 hgammaEta
    positivity)

/-- Natural block widths and thresholds for the retained-core selector. -/
theorem exists_retainedCoreSelectorScales
    {mult : ℕ} {C0 gamma eta : ℝ} (hmult : 0 < mult)
    (hC0 : 0 < C0) (hgammaEta : gamma < eta) :
    ∃ k N : ℕ, 4 ≤ k ∧ ∀ n B : ℕ, N ≤ n → B * k ≤ 4 * n →
      colorDependentBlockNaturalSigma mult B n k
          (jointProfileRho (retainedCoreTau C0 gamma eta))
          (jointProfileS (retainedCoreTau C0 gamma eta))
          (jointProfileOmega (retainedCoreTau C0 gamma eta))
          (jointProfileBeta (retainedCoreTau C0 gamma eta))
          (jointProfileQ (retainedCoreTau C0 gamma eta))
          (jointProfileR (retainedCoreTau C0 gamma eta)) C0 ≤
        ((eta - gamma) / 1024) ^ 2 * n ∧
      (mult : ℝ) * colorDependentCandidateCapacityScale
          (jointProfileRho (retainedCoreTau C0 gamma eta))
          (jointProfileS (retainedCoreTau C0 gamma eta))
          (jointProfileOmega (retainedCoreTau C0 gamma eta))
          (jointProfileBeta (retainedCoreTau C0 gamma eta))
          (jointProfileQ (retainedCoreTau C0 gamma eta))
          (jointProfileR (retainedCoreTau C0 gamma eta)) C0 / n *
        FinitePartialResamplingNumerics.packingDeviation n
          (colorDependentBlockCombinedColumnBound n k
            (jointProfileBeta (retainedCoreTau C0 gamma eta))
            (jointProfileQ (retainedCoreTau C0 gamma eta))
            (jointProfileR (retainedCoreTau C0 gamma eta))) ≤
        retainedCoreTau C0 gamma eta ^ 2 / 4 := by
  let tau := retainedCoreTau C0 gamma eta
  let eps := retainedCoreSelectorError C0 gamma eta
  have htau0 : 0 < tau := retainedCoreTau_pos hC0 hgammaEta
  have htau1 : tau ≤ 1 / 4 := retainedCoreTau_le_quarter C0 gamma eta
  rcases jointProfile_parameters htau0 htau1 with
    ⟨hs, hβ, _hq, _hr, homega0, _homega1, _hleft, _hr1,
      hrho, _hrhoKappa, _hfraction⟩
  have heps : 0 < eps := retainedCoreSelectorError_pos hC0 hgammaEta
  obtain ⟨k, N, hk, hscales⟩ :=
    exists_colorDependentBlockNaturalScales_small
      (q := jointProfileQ tau) (r := jointProfileR tau)
      hmult hβ hs homega0 hrho hC0 eps heps
  refine ⟨k, N, hk, ?_⟩
  intro n B hn hpalette
  rcases hscales n B hn hpalette with ⟨hsigma, hcapacity⟩
  have hepsQuad : eps ≤ (eta - gamma) / 1024 := by
    exact min_le_left _ _
  have hepsCapacity : eps ≤ tau ^ 2 / 4 := by
    exact min_le_right _ _
  have hquad0 : 0 ≤ (eta - gamma) / 1024 := by
    exact div_nonneg (sub_nonneg.mpr hgammaEta.le) (by norm_num)
  have heps0 : 0 ≤ eps := heps.le
  have hepsSq : eps ^ 2 ≤ ((eta - gamma) / 1024) ^ 2 := by
    nlinarith
  refine ⟨hsigma.trans ?_, hcapacity.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hepsSq (Nat.cast_nonneg n)
  · simpa [tau] using hepsCapacity

/-- Fixed-scale selector/profile-realization package.  The capacity rows
remain in their exact-mean form for the large matching.  The last clause
is the reservoir-sensitive inequality used directly by the tiny decoder. -/
theorem exists_jointProfileColorDependentSelection
    {mult B k n : ℕ} {C0 tau : ℝ}
    (hmult : 0 < mult) (hpair : G.PairMultiplicityAtMost mult)
    (x : G.E → Fin (B * k) → ℝ)
    (hB : 0 < B) (hk4 : 4 ≤ k) (hn : 0 < n)
    (hpalette : B * k ≤ 4 * n)
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (hC0 : 0 < C0) (htauC0 : tau ≤ C0 / 32)
    (hx : ∀ e c, 0 ≤ x e c ∧ x e c ≤ C0 / n)
    (hmass : ∀ e, ∑ c, x e c ≤ 1)
    (hlocal : ∀ v c,
      G.IsAverageOfStarFeasibleSets v (fun e : G.StarEdge v ↦ x e.1 c))
    (hstar : ∀ v, G.starWeight v ≤ n) :
    let proposal : G.E → (Fin B × Fin k) → ℝ :=
      fun e c ↦ x e (finProdFinEquiv c)
    let scale := (mult : ℝ) * colorDependentCandidateCapacityScale
      (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
      (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) C0
    let D := FinitePartialResamplingNumerics.packingDeviation n
      (colorDependentBlockCombinedColumnBound n k
        (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau))
    let sigma := colorDependentBlockNaturalSigma mult B n k
      (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
      (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) C0
    ∃ (hβ : 0 < jointProfileBeta tau) (hr : 0 < jointProfileR tau)
      (R : ∀ v c, G.BoundedProfileRealization
        (fun e : G.StarEdge v ↦ proposal e.1 c)
        (jointProfileS tau) (jointProfileBeta tau)
        (jointProfileQ tau) (jointProfileR tau) hβ hr)
      (selected : G.ColorDependentSelectedStates proposal R),
      (∀ v b,
        0 < G.paddedColorDependentExtendedProfileBlockProbability
          proposal R (jointProfileOmega tau) (v, b)
          (G.encodeColorDependentExtendedProfileBlock
            proposal R v b (selected v b))) ∧
      (∀ row : G.ColorDependentExtendedProfileCapacityRow
          (G.ColorDependentCandidateRowAt R),
        FiniteCategoricalSelection.rowLoad
          (G.colorDependentBlockCandidateUse proposal R n scale
            (jointProfileRho tau) (jointProfileOmega tau)) row
          (G.encodedColorDependentSelectedBlock proposal R selected) <
        FiniteCategoricalSelection.rowMean
          (G.paddedColorDependentExtendedProfileBlockProbability
            proposal R (jointProfileOmega tau))
          (G.colorDependentBlockCandidateUse proposal R n scale
            (jointProfileRho tau) (jointProfileOmega tau)) row + D) ∧
      (∀ v,
        (∑ e : G.StarEdge v, G.weight e.1 *
          (G.selectedColorDependentTotalOptionMass proposal R
              (jointProfileRho tau) (jointProfileOmega tau)
              (G.encodedColorDependentSelectedBlock proposal R selected) e.1 -
            G.colorDependentTotalTarget proposal
              (jointProfileRho tau) (jointProfileS tau) e.1) ^ 2) ≤ sigma) ∧
      ∀ v c,
        G.selectedColorDependentNormalizedTinyReservoirLoad proposal R
            (jointProfileRho tau) (jointProfileOmega tau) selected v c <
          jointProfileColorDependentRate tau *
              G.colorDependentExtendedProfileReservoirSize
                R v c (selected v c.1 c.2) + scale / n * D := by
  dsimp only
  let proposal : G.E → (Fin B × Fin k) → ℝ :=
    fun e c ↦ x e (finProdFinEquiv c)
  let scale := (mult : ℝ) * colorDependentCandidateCapacityScale
    (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
    (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) C0
  let D := FinitePartialResamplingNumerics.packingDeviation n
    (colorDependentBlockCombinedColumnBound n k
      (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau))
  let sigma := colorDependentBlockNaturalSigma mult B n k
    (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
    (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) C0
  rcases jointProfile_parameters htau0 htau1 with
    ⟨hs, hβ, hq, hr, homega0, homega1, hleft, hr1,
      hrho, _hrhoKappa, _hfraction⟩
  have hproposalBounds : ∀ e c, 0 ≤ proposal e c ∧ proposal e c ≤ C0 / n := by
    intro e c
    exact hx e (finProdFinEquiv c)
  have hproposalMass : ∀ e, ∑ c, proposal e c ≤ 1 := by
    intro e
    change (∑ c : Fin B × Fin k, x e (finProdFinEquiv c)) ≤ 1
    rw [show (∑ c : Fin B × Fin k, x e (finProdFinEquiv c)) =
        ∑ d : Fin (B * k), x e d by
      exact Equiv.sum_comp finProdFinEquiv (x e)]
    exact hmass e
  have hlocal' : ∀ v c,
      G.IsAverageOfStarFeasibleSets v
        (fun e : G.StarEdge v ↦ proposal e.1 c) := by
    intro v c
    exact hlocal v (finProdFinEquiv c)
  obtain ⟨R⟩ := G.exists_boundedProfileRealization_family
    (s := jointProfileS tau) (β := jointProfileBeta tau)
    (q := jointProfileQ tau) (r := jointProfileR tau)
    (hβ := hβ) (hr := hr) proposal
    hlocal' hs.le (by unfold jointProfileS; linarith) hq
  have hk : 0 < k := lt_of_lt_of_le (by norm_num) hk4
  have hBn : B ≤ n := by
    have hmul : 4 * B ≤ B * k := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left B hk4
    omega
  have hcapacityMean := jointProfile_colorDependentCapacityMean_le
    htau0 htau1 hC0 htauC0 hn
  have hmultR : (1 : ℝ) ≤ mult := by exact_mod_cast hmult
  have hbaseScalePos := colorDependentCandidateCapacityScale_pos
    (β := jointProfileBeta tau) (q := jointProfileQ tau)
    (r := jointProfileR tau) hrho hs hC0 homega0
  have hcapacityMeanScaled :
      (n : ℝ) * (jointProfileRho tau / (1 - jointProfileOmega tau)) /
          ((mult : ℝ) * colorDependentCandidateCapacityScale
            (jointProfileRho tau) (jointProfileS tau)
            (jointProfileOmega tau) (jointProfileBeta tau)
            (jointProfileQ tau) (jointProfileR tau) C0) ≤ n := by
    calc
      _ ≤ (n : ℝ) * (jointProfileRho tau / (1 - jointProfileOmega tau)) /
          colorDependentCandidateCapacityScale
            (jointProfileRho tau) (jointProfileS tau)
            (jointProfileOmega tau) (jointProfileBeta tau)
            (jointProfileQ tau) (jointProfileR tau) C0 := by
        apply div_le_div_of_nonneg_left
        · exact mul_nonneg (Nat.cast_nonneg n)
            (div_nonneg hrho.le (sub_nonneg.mpr homega1))
        · exact hbaseScalePos
        · nlinarith
      _ ≤ n := hcapacityMean
  obtain ⟨selected, hsupport, hcapacity, hquad, _hsigned⟩ :=
    G.exists_colorDependentExtendedProfileBlock_capacity_and_variance_natural
      proposal R hmult hpair hB hk hn hBn hs hq.le hr.le hleft
      (jointProfileOmega tau) homega0 (by
        unfold jointProfileOmega
        linarith)
      (jointProfileRho tau) C0 hrho hC0
      (fun e c ↦ (hproposalBounds e c).1)
      (fun e c ↦ (hproposalBounds e c).2)
      hproposalMass hstar hcapacityMeanScaled
  have hquad' : ∀ v,
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedColorDependentTotalOptionMass proposal R
            (jointProfileRho tau) (jointProfileOmega tau)
            (G.encodedColorDependentSelectedBlock proposal R selected) e.1 -
          G.colorDependentTotalTarget proposal
            (jointProfileRho tau) (jointProfileS tau) e.1) ^ 2) ≤ sigma := by
    intro v
    exact (hquad v).trans
      (colorDependentBlockVarianceExpression_le_naturalSigma hβ hn hk hpalette)
  refine ⟨hβ, hr, R, selected, hsupport, hcapacity, hquad', ?_⟩
  intro v c
  let row := G.selectedColorDependentTinyCapacityRow proposal R selected v c
  have hrow := hcapacity row
  have hmean :
      FiniteCategoricalSelection.rowMean
          (G.paddedColorDependentExtendedProfileBlockProbability
            proposal R (jointProfileOmega tau))
          (G.colorDependentBlockCandidateUse proposal R n scale
            (jointProfileRho tau) (jointProfileOmega tau)) row ≤
        (n : ℝ) *
          (jointProfileRho tau *
            G.colorDependentExtendedProfileReservoirSize
              R v c (selected v c.1 c.2) /
            (1 - jointProfileOmega tau)) / scale := by
    rw [G.colorDependentBlockCandidate_rowMean_eq]
    exact G.scaledColorDependentTinyCandidateAtomMean_le_reservoir
      proposal R n scale hs.le hq.le hr.le hleft homega0
      (by unfold jointProfileOmega; linarith) hrho.le
      (mul_pos (by exact_mod_cast hmult)
        (colorDependentCandidateCapacityScale_pos hrho hs hC0 homega0))
      c (row := ⟨v, selected v c.1 c.2⟩)
  have hrow' :
      FiniteCategoricalSelection.rowLoad
          (G.colorDependentBlockCandidateUse proposal R n scale
            (jointProfileRho tau) (jointProfileOmega tau)) row
          (G.encodedColorDependentSelectedBlock proposal R selected) <
        (n : ℝ) *
          (jointProfileRho tau *
            G.colorDependentExtendedProfileReservoirSize
              R v c (selected v c.1 c.2) /
            (1 - jointProfileOmega tau)) / scale + D :=
    hrow.trans_le (add_le_add hmean le_rfl)
  have htiny :=
    G.selectedColorDependentNormalizedTinyReservoirLoad_lt proposal R
      hn hs.le hq.le hr.le hleft homega0 homega1 hrho.le
      scale D
      (mul_pos (by exact_mod_cast hmult)
        (colorDependentCandidateCapacityScale_pos hrho hs hC0 homega0))
      selected v c hrow'
  change _ < jointProfileColorDependentRate tau *
      G.colorDependentExtendedProfileReservoirSize
        R v c (selected v c.1 c.2) + scale / n * D
  convert htiny using 1 <;>
    unfold jointProfileColorDependentRate <;> ring

/-- Decoder-side composition for the final large-matching call point.  All
profile, selector, and matching conclusions are concrete arguments; the
only quantitative assumptions are the two explicit final budgets. -/
theorem exists_retainedCore_partialColoring_of_selection_and_matching
    {B k K n : ℕ} {C0 gamma eta sigma delta largeLoss : ℝ}
    (x : G.E → Fin (B * k) → ℝ)
    (hC0 : 0 < C0) (hgamma0 : 0 < gamma) (hgamma1 : gamma < 1)
    (hgammaEta : 64 * gamma < eta)
    (hn : 1 ≤ n) (hB : 0 < B) (hk : 0 < k)
    (hx0 : ∀ e c, 0 ≤ x e c)
    (hmass : ∀ e, ∑ c, x e c ≤ 1)
    (hstar : ∀ v, G.starWeight v ≤ n)
    (hsigma0 : 0 ≤ sigma)
    (hsigma : sigma ≤ ((eta - gamma) / 1024) ^ 2 * n)
    (hdelta : delta ≤ retainedCoreTau C0 gamma eta ^ 2 / 4)
    (hβ : 0 < jointProfileBeta (retainedCoreTau C0 gamma eta))
    (hr : 0 < jointProfileR (retainedCoreTau C0 gamma eta))
    (R : ∀ v c, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ G.retainedCoreProductProposal x e.1 c)
      (jointProfileS (retainedCoreTau C0 gamma eta))
      (jointProfileBeta (retainedCoreTau C0 gamma eta))
      (jointProfileQ (retainedCoreTau C0 gamma eta))
      (jointProfileR (retainedCoreTau C0 gamma eta)) hβ hr)
    (selected : G.ColorDependentSelectedStates
      (G.retainedCoreProductProposal x) R)
    (hquad : ∀ v,
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedColorDependentTotalOptionMass
            (G.retainedCoreProductProposal x) R
            (jointProfileRho (retainedCoreTau C0 gamma eta))
            (jointProfileOmega (retainedCoreTau C0 gamma eta))
            (G.encodedColorDependentSelectedBlock
              (G.retainedCoreProductProposal x) R selected) e.1 -
          G.colorDependentTotalTarget (G.retainedCoreProductProposal x)
            (jointProfileRho (retainedCoreTau C0 gamma eta))
            (jointProfileS (retainedCoreTau C0 gamma eta)) e.1) ^ 2) ≤ sigma)
    (M : Finset (OrdinarySlotChoice G.E (Fin (B * k)) K))
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (hlargeSubset : G.ordinarySelectedEdges M ⊆
      G.largeEdgeJobs (jointProfileBeta (retainedCoreTau C0 gamma eta)))
    (hlargeSupport : ∀ e ∈ G.ordinarySelectedEdges M,
      0 < G.retainedCoreProductProposal x e
        (finProdFinEquiv.symm
          (G.extendSelectedOrdinaryColor (Nat.mul_pos hB hk) M hM e)))
    (hlargeLoad : ∀ v c,
      G.selectedOrdinaryIntegralColorLoad M hM v (finProdFinEquiv c) ≤
        ∑ i, G.colorDependentExtendedProfileConcreteSlotSize R v c
          (selected v c.1 c.2) i)
    (htiny : ∀ v c,
      G.selectedColorDependentNormalizedTinyReservoirLoad
          (G.retainedCoreProductProposal x) R
          (jointProfileRho (retainedCoreTau C0 gamma eta))
          (jointProfileOmega (retainedCoreTau C0 gamma eta)) selected v c ≤
        jointProfileColorDependentRate (retainedCoreTau C0 gamma eta) *
          G.colorDependentExtendedProfileReservoirSize
            R v c (selected v c.1 c.2) + delta)
    (hlargeLoss : ∀ v,
      (∑ e ∈ G.retainedMacroscopicEdges (G.retainedCoreProductProposal x)
          gamma (jointProfileBeta (retainedCoreTau C0 gamma eta)) \
            G.ordinarySelectedEdges M,
        if G.Inc v e then G.weight e else 0) ≤ largeLoss)
    (hlargeBudget : largeLoss ≤ (eta - gamma) / 4 * n) :
    ∃ (P : Finset G.E) (color : G.E → Fin (B * k)),
      G.IsFeasibleOn P color ∧
      (∀ e ∈ P, 0 < x e (color e)) ∧
      ∀ v,
        (∑ e ∈ (Finset.univ \ G.lowProposalMassEdges x gamma) \ P,
          if G.Inc v e then G.weight e else 0) ≤ eta * n := by
  let tau := retainedCoreTau C0 gamma eta
  let proposal := G.retainedCoreProductProposal x
  have hgammaEta' : gamma < eta := by nlinarith
  have htau0 : 0 < tau := retainedCoreTau_pos hC0 hgammaEta'
  have htau1 : tau ≤ 1 / 4 := retainedCoreTau_le_quarter C0 gamma eta
  rcases jointProfile_parameters htau0 htau1 with
    ⟨hs, _hβ, hq, _hr, homega0, homega1, hleft, hr1,
      hrho, _hrhoKappa, _hfraction⟩
  have hproposal0 : ∀ e c, 0 ≤ proposal e c := by
    intro e c
    exact hx0 e (finProdFinEquiv c)
  have hproposalMass : ∀ e, ∑ c, proposal e c ≤ 1 := by
    intro e
    change (∑ c : Fin B × Fin k, x e (finProdFinEquiv c)) ≤ 1
    rw [show (∑ c : Fin B × Fin k, x e (finProdFinEquiv c)) =
        ∑ d : Fin (B * k), x e d by
      exact Equiv.sum_comp finProdFinEquiv (x e)]
    exact hmass e
  have ha0 : 0 ≤ jointProfileColorDependentRate tau :=
    jointProfileColorDependentRate_nonneg htau0 htau1
  have ha1 : jointProfileColorDependentRate tau ≤ 1 :=
    jointProfileColorDependentRate_le_one htau0 htau1
  have hrhos0 : 0 ≤ jointProfileRho tau * jointProfileS tau :=
    mul_nonneg hrho.le hs.le
  have hrho1 : jointProfileRho tau ≤ 1 := by
    unfold jointProfileRho
    linarith
  have hs1 : jointProfileS tau ≤ 1 := by
    unfold jointProfileS
    linarith
  have hrhos1 : jointProfileRho tau * jointProfileS tau ≤ 1 := by
    nlinarith
  have herror : delta + 2 * jointProfileBeta tau ≤
      (1 - jointProfileColorDependentRate tau) * jointProfileR tau := by
    exact retainedCoreTau_tinySlack hC0 hgammaEta' hdelta
  have hbudget : ∀ v,
      largeLoss +
          ((1 - jointProfileRho tau * jointProfileS tau * (1 - gamma)) *
              G.starWeight v + Real.sqrt (G.starWeight v * sigma)) +
        2 * jointProfileBeta tau ≤ eta * n := by
    intro v
    apply retainedCoreTau_decoderBudget_le hC0 hgamma0.le hgamma1.le
      hgammaEta'
    · exact_mod_cast hn
    · exact Finset.sum_nonneg fun e _he ↦ G.weight_nonneg e.1
    · exact hstar v
    · exact hsigma0
    · exact hsigma
    · exact hlargeBudget
  have hquadAll : ∀ v,
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedColorDependentAllOptionMass proposal R
            (jointProfileRho tau) (jointProfileOmega tau)
            (G.encodedColorDependentSelectedBlock proposal R selected) e.1 -
          G.colorDependentTotalTarget proposal
            (jointProfileRho tau) (jointProfileS tau) e.1) ^ 2) ≤ sigma := by
    intro v
    simpa only [G.selectedColorDependentAllOptionMass_eq_total] using hquad v
  obtain ⟨P, color, hfeasible, hsupport, hloss⟩ :=
    G.exists_retainedColorDependentCore_partialColoring_of_quadraticError
      proposal R hs.le hq.le (by simpa [tau] using hr.le) hr1 hleft
      homega0 homega1 hrho.le hproposal0 hB hk hproposalMass
      gamma (jointProfileColorDependentRate tau) delta largeLoss sigma
      (eta * n) hgamma0.le ha0 ha1 hrhos0 hrhos1 hsigma0 herror
      selected hquadAll M hM hlargeSubset hlargeSupport hlargeLoad htiny
      hlargeLoss hbudget
  refine ⟨P, color, hfeasible, ?_, ?_⟩
  · intro e he
    have hp := hsupport e he
    change 0 < x e
      (finProdFinEquiv (finProdFinEquiv.symm (color e))) at hp
    simpa only [finProdFinEquiv.apply_symm_apply] using hp
  · intro v
    rw [show G.lowProposalMassEdges proposal gamma =
        G.lowProposalMassEdges x gamma by
      simpa [proposal, retainedCoreProductProposal] using
        G.lowProposalMassEdges_reindexed_eq x gamma] at hloss
    exact hloss v

end WeightedMultigraph

end

end WeightedEdgeColoring
