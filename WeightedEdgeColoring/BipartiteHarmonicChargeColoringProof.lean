import WeightedEdgeColoring.BPHarmonicColoringInterface
import WeightedEdgeColoring.BPBipartiteThreeModeReduction
import WeightedEdgeColoring.BipartiteFiniteTinyCompletion
import WeightedEdgeColoring.BipartiteHarmonicConstructionBounds

/-!
# Harmonic-charge coloring from coordinated bounded-multiplicity rounding

This file performs the final uniform parameter choice.  All finite harmonic
classes and the tiny tail are rounded in one common missing palette; the only
remaining input is the coordinated whole-edge rounding theorem.
-/

namespace WeightedEdgeColoring

open WeightedMultigraph

noncomputable section

universe u

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

/-- The finite-plus-tiny construction proves the uniform harmonic-charge
interface from coordinated bounded-multiplicity whole-edge rounding. -/
theorem bipartiteHarmonicChargeColoring_of_boundedMultiplicityWholeEdgeUniformRounding
    (hround : BoundedMultiplicityWholeEdgeUniformRounding.{u}) :
    BipartiteHarmonicChargeColoring.{u} := by
  intro eta heta
  let gamma : ℝ := bipartiteProofSlack eta
  have hgamma : 0 < gamma := bipartiteProofSlack_pos heta
  have hgammaOne : gamma ≤ (1 : ℝ) / 64 :=
    bipartiteProofSlack_le_one_div eta
  have hgammaEta : 5 * gamma ≤ eta / 8 :=
    five_mul_bipartiteProofSlack_le_eta_eighth heta
  obtain ⟨t, ht2, hinv⟩ := exists_nat_two_le_one_div_lt hgamma
  have ht : 0 < t := by omega
  let T : ℕ := 2 * t
  let alpha : ℝ := gamma / 4
  let eps : ℝ := gamma / 32
  have hT : 0 < T := by dsimp [T]; omega
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have heps : 0 < eps := by dsimp [eps]; positivity
  rcases WeightedMultigraph.TinyThresholdPacketization.exists_uniform_hasWeightedColoring_of_finiteTinyHybrid
      hround T alpha 1 eps eps halpha (by norm_num) heps heps hT with
    ⟨Ncomplete, hcomplete⟩
  let N : ℕ := max Ncomplete
    (max 6 (max (bipartiteDiffuseThreshold T gamma)
      (Nat.ceil (16 / eta))))
  refine ⟨N, ?_⟩
  intro G n A hbip hn hA hstar hcharge
  rcases hbip with ⟨b⟩
  let tau : ℝ := reciprocalTinyThreshold t
  have htau : 0 < tau := reciprocalTinyThreshold_pos ht
  have htau0 : 0 ≤ tau := htau.le
  have htauHalf : tau ≤ (1 : ℝ) / 2 :=
    reciprocalTinyThreshold_le_half (by omega)
  have htau1 : tau < 1 := by linarith
  have htauGamma : tau ≤ gamma / 2 :=
    (reciprocalTinyThreshold_lt_half ht hinv).le
  obtain ⟨P⟩ := G.exists_tinyThresholdPacketization b tau htau htauHalf
  let K : ℕ := evenCeilingPalette (bipartitePaletteTarget A n tau gamma)
  have hK : 0 < K := by dsimp [K]; exact evenCeilingPalette_pos _
  have hnComplete : Ncomplete ≤ n := by
    exact (le_max_left _ _).trans hn
  have hn6 : 6 ≤ n := by
    exact (le_max_left 6
      (max (bipartiteDiffuseThreshold T gamma) (Nat.ceil (16 / eta)))).trans
        ((le_max_right Ncomplete _).trans hn)
  have hnpos : 0 < n := by omega
  have hnDiffuse : bipartiteDiffuseThreshold T gamma ≤ n := by
    exact (le_max_left (bipartiteDiffuseThreshold T gamma)
      (Nat.ceil (16 / eta))).trans
        ((le_max_right 6 _).trans ((le_max_right Ncomplete _).trans hn))
  have hnAbsNat : Nat.ceil (16 / eta) ≤ n := by
    exact (le_max_right (bipartiteDiffuseThreshold T gamma)
      (Nat.ceil (16 / eta))).trans
        ((le_max_right 6 _).trans ((le_max_right Ncomplete _).trans hn))
  have hnAbs : 16 / eta ≤ (n : ℝ) :=
    (Nat.le_ceil (16 / eta)).trans (by exact_mod_cast hnAbsNat)
  have hpaletteBound : K ≤ 4 * n := by
    dsimp [K]
    exact evenCeiling_bipartitePaletteTarget_le_four_mul hA htau0 htauHalf
      htauGamma hgammaOne hn6
  obtain ⟨C⟩ := P.exists_targetPacketColoringCertificate ht hgamma.le
    hstar hcharge
  have hmissing : ∀ v, alpha * (4 * n : ℕ) ≤
      (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
        (C.ambientBaseColor hK) v).card := by
    intro v
    have hs := C.jointResidualStarCharge_add_slack_le_missingColors
      ht hgamma.le hstar hcharge v
    have hj0 : 0 ≤ C.jointResidualStarCharge v :=
      C.jointResidualStarCharge_nonneg_of_tau_lt_one htau1 v
    dsimp [alpha]
    push_cast
    nlinarith
  have hpalette : (K : ℝ) ≤ (1 : ℝ) * (4 * n : ℕ) := by
    norm_num
    exact_mod_cast hpaletteBound
  have hchargeStar : ∀ v, C.jointResidualStarCharge v ≤ (4 * n : ℕ) := by
    intro v
    have hs := C.jointResidualStarCharge_add_slack_le_missingColors
      ht hgamma.le hstar hcharge v
    have hgap0 : 0 ≤ gamma * (n : ℝ) :=
      mul_nonneg hgamma.le (Nat.cast_nonneg n)
    have hcardNat :
        (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
          (C.ambientBaseColor hK) v).card ≤ K :=
      by
        simpa using Finset.card_le_univ
          (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
            (C.ambientBaseColor hK) v)
    have hcard :
        ((P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
          (C.ambientBaseColor hK) v).card : ℝ) ≤ K := by
      exact_mod_cast hcardNat
    have hK4 : (K : ℝ) ≤ (4 * n : ℕ) := by
      exact_mod_cast hpaletteBound
    linarith
  have hdiffuse :
      (T + 1 : ℝ) * (1 / (alpha ^ 2 * (4 * n : ℕ))) ≤
        gamma / 16 := by
    simpa [alpha] using
      finiteClassDiffuseTerm_le hgamma hnpos hnDiffuse
  have hlocal : ∀ v,
      C.jointResidualStarCharge v /
          (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
            (C.ambientBaseColor hK) v).card + eps +
        (T + 1 : ℝ) * (1 / (alpha ^ 2 * (4 * n : ℕ))) ≤ 1 := by
    intro v
    let M : ℝ :=
      (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
        (C.ambientBaseColor hK) v).card
    have hs := C.jointResidualStarCharge_add_slack_le_missingColors
      ht hgamma.le hstar hcharge v
    have hj0 : 0 ≤ C.jointResidualStarCharge v :=
      C.jointResidualStarCharge_nonneg_of_tau_lt_one htau1 v
    have hgap : C.jointResidualStarCharge v + alpha * (4 * n : ℕ) ≤ M := by
      dsimp [alpha, M]
      push_cast
      nlinarith
    have hMnat :
        (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
          (C.ambientBaseColor hK) v).card ≤ K := by
      simpa using Finset.card_le_univ
        (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
          (C.ambientBaseColor hK) v)
    have hupper : M ≤ (1 : ℝ) * (4 * n : ℕ) := by
      have hMK' :
          ((P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
            (C.ambientBaseColor hK) v).card : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast hMnat
      have hMK : M ≤ (K : ℝ) := by simpa [M] using hMK'
      exact hMK.trans hpalette
    apply WeightedMultigraph.div_add_errors_le_one_of_add_gap_le
      hj0 halpha (by norm_num) (by positivity : (0 : ℝ) < (4 * n : ℕ))
      hgap hupper
    · dsimp [eps, alpha]
      nlinarith [hgamma.le]
    · calc
        (T + 1 : ℝ) * (1 / (alpha ^ 2 * (4 * n : ℕ)))
            ≤ gamma / 16 := hdiffuse
        _ = alpha / (4 * (1 : ℝ)) := by dsimp [alpha]; ring
  have hfiniteWeight : ∀ e : P.coreObjectGraph.E,
      P.coreObjectGraph.weight e ≤
        (1 : ℝ) / finiteClassSize (P.coreHarmonicClass ht e) :=
    fun e ↦ P.coreObjectGraph.weight_le_inv_finiteClassSize_finiteHarmonicClassOf
      T hT P.coreObject_weight_ge_inv_two_mul e
  have hfiniteCharge : ∀ e : P.coreObjectGraph.E,
      harmonicCharge (P.coreObjectGraph.weight e) =
        (1 : ℝ) / finiteClassSize (P.coreHarmonicClass ht e) :=
    fun e ↦
      P.coreObjectGraph.harmonicCharge_eq_inv_finiteClassSize_finiteHarmonicClassOf
        T hT P.coreObject_weight_ge_inv_two_mul e
  have hcolored := hcomplete G b tau P K (P.coreHarmonicClass ht)
    (4 * n) C hK htau0 htau1 htauHalf
    (hnComplete.trans (by omega)) (by omega) (even_evenCeilingPalette _)
    (four_le_evenCeilingPalette _) hmissing hpalette hchargeStar hlocal
    hfiniteWeight hfiniteCharge
  have hchiNat := G.chiW_le_of_hasWeightedColoring hcolored
  have hchi : (G.chiW : ℝ) ≤
      (K + (4 * Nat.ceil ((eps + eps) * (4 * n)) + 1) : ℕ) := by
    exact_mod_cast hchiNat
  have hcost :
      ((K + (4 * Nat.ceil ((eps + eps) * (4 * n)) + 1) : ℕ) : ℝ) ≤
        A + 5 * gamma * n + 11 := by
    simpa [K, eps] using bipartitePalette_add_cleanup_le
      (A := A) (tau := tau) (gamma := gamma) (n := n)
      hA htau0 htauHalf htauGamma hgamma.le
  have habsorb : 5 * gamma * n + 11 ≤ eta * n :=
    five_slack_mul_add_eleven_le_eta_mul heta hgammaEta hnAbs
  exact hchi.trans (hcost.trans (by linarith))

/-- Deficit-aware finite-plus-tiny harmonic-charge endpoint. -/
theorem bipartiteHarmonicChargeColoring_of_deficitAwareBoundedMultiplicityWholeEdgeUniformRounding
    (hround : DeficitAwareBoundedMultiplicityWholeEdgeUniformRounding.{u}) :
    BipartiteHarmonicChargeColoring.{u} := by
  intro eta heta
  let gamma : ℝ := bipartiteProofSlack eta
  have hgamma : 0 < gamma := bipartiteProofSlack_pos heta
  have hgammaOne : gamma ≤ (1 : ℝ) / 64 :=
    bipartiteProofSlack_le_one_div eta
  have hgammaEta : 5 * gamma ≤ eta / 8 :=
    five_mul_bipartiteProofSlack_le_eta_eighth heta
  obtain ⟨t, ht2, hinv⟩ := exists_nat_two_le_one_div_lt hgamma
  have ht : 0 < t := by omega
  let T : ℕ := 2 * t
  let alpha : ℝ := gamma / 4
  let trim : ℝ := gamma / 4096
  let eps : ℝ := gamma ^ 2 / 131072
  let roundEta : ℝ := gamma / 32
  have hT : 0 < T := by dsimp [T]; omega
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have htrim0 : 0 < trim := by dsimp [trim]; positivity
  have htrim1 : trim < 1 := by dsimp [trim]; linarith
  have htrimRoundEta : 64 * trim < roundEta := by
    dsimp [trim, roundEta]
    linarith [hgamma]
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hroundEta : 0 < roundEta := by dsimp [roundEta]; positivity
  rcases WeightedMultigraph.TinyThresholdPacketization.exists_uniform_hasWeightedColoring_of_finiteTinyHybrid_deficitAware
      hround T alpha 1 trim eps roundEta halpha (by norm_num) (by norm_num)
      htrim0 htrim1 htrimRoundEta heps hroundEta hT with
    ⟨Ncomplete, hcomplete⟩
  let N : ℕ := max Ncomplete
    (max 6 (max (bipartiteDiffuseThreshold T gamma)
      (Nat.ceil (16 / eta))))
  refine ⟨N, ?_⟩
  intro G n A hbip hn hA hstar hcharge
  rcases hbip with ⟨b⟩
  let tau : ℝ := reciprocalTinyThreshold t
  have htau : 0 < tau := reciprocalTinyThreshold_pos ht
  have htau0 : 0 ≤ tau := htau.le
  have htauHalf : tau ≤ (1 : ℝ) / 2 :=
    reciprocalTinyThreshold_le_half (by omega)
  have htau1 : tau < 1 := by linarith
  have htauGamma : tau ≤ gamma / 2 :=
    (reciprocalTinyThreshold_lt_half ht hinv).le
  obtain ⟨P⟩ := G.exists_tinyThresholdPacketization b tau htau htauHalf
  let K : ℕ := evenCeilingPalette (bipartitePaletteTarget A n tau gamma)
  have hK : 0 < K := by dsimp [K]; exact evenCeilingPalette_pos _
  have hnComplete : Ncomplete ≤ n := by
    exact (le_max_left _ _).trans hn
  have hn6 : 6 ≤ n := by
    exact (le_max_left 6
      (max (bipartiteDiffuseThreshold T gamma) (Nat.ceil (16 / eta)))).trans
        ((le_max_right Ncomplete _).trans hn)
  have hnpos : 0 < n := by omega
  have hnDiffuse : bipartiteDiffuseThreshold T gamma ≤ n := by
    exact (le_max_left (bipartiteDiffuseThreshold T gamma)
      (Nat.ceil (16 / eta))).trans
        ((le_max_right 6 _).trans ((le_max_right Ncomplete _).trans hn))
  have hnAbsNat : Nat.ceil (16 / eta) ≤ n := by
    exact (le_max_right (bipartiteDiffuseThreshold T gamma)
      (Nat.ceil (16 / eta))).trans
        ((le_max_right 6 _).trans ((le_max_right Ncomplete _).trans hn))
  have hnAbs : 16 / eta ≤ (n : ℝ) :=
    (Nat.le_ceil (16 / eta)).trans (by exact_mod_cast hnAbsNat)
  have hpaletteBound : K ≤ 4 * n := by
    dsimp [K]
    exact evenCeiling_bipartitePaletteTarget_le_four_mul hA htau0 htauHalf
      htauGamma hgammaOne hn6
  obtain ⟨C⟩ := P.exists_targetPacketColoringCertificate ht hgamma.le
    hstar hcharge
  have hmissing : ∀ v, alpha * (4 * n : ℕ) ≤
      (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
        (C.ambientBaseColor hK) v).card := by
    intro v
    have hs := C.jointResidualStarCharge_add_slack_le_missingColors
      ht hgamma.le hstar hcharge v
    have hj0 : 0 ≤ C.jointResidualStarCharge v :=
      C.jointResidualStarCharge_nonneg_of_tau_lt_one htau1 v
    dsimp [alpha]
    push_cast
    nlinarith
  have hpalette : (K : ℝ) ≤ (1 : ℝ) * (4 * n : ℕ) := by
    norm_num
    exact_mod_cast hpaletteBound
  have hchargeStar : ∀ v, C.jointResidualStarCharge v ≤ (4 * n : ℕ) := by
    intro v
    have hs := C.jointResidualStarCharge_add_slack_le_missingColors
      ht hgamma.le hstar hcharge v
    have hgap0 : 0 ≤ gamma * (n : ℝ) :=
      mul_nonneg hgamma.le (Nat.cast_nonneg n)
    have hcardNat :
        (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
          (C.ambientBaseColor hK) v).card ≤ K :=
      by
        simpa using Finset.card_le_univ
          (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
            (C.ambientBaseColor hK) v)
    have hcard :
        ((P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
          (C.ambientBaseColor hK) v).card : ℝ) ≤ K := by
      exact_mod_cast hcardNat
    have hK4 : (K : ℝ) ≤ (4 * n : ℕ) := by
      exact_mod_cast hpaletteBound
    linarith
  have hdiffuse :
      (T + 1 : ℝ) * (1 / (alpha ^ 2 * (4 * n : ℕ))) ≤
        gamma / 16 := by
    simpa [alpha] using
      finiteClassDiffuseTerm_le hgamma hnpos hnDiffuse
  have hlocal : ∀ v,
      C.jointResidualStarCharge v /
          (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
            (C.ambientBaseColor hK) v).card + eps +
        (T + 1 : ℝ) * (1 / (alpha ^ 2 * (4 * n : ℕ))) ≤ 1 := by
    intro v
    let M : ℝ :=
      (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
        (C.ambientBaseColor hK) v).card
    have hs := C.jointResidualStarCharge_add_slack_le_missingColors
      ht hgamma.le hstar hcharge v
    have hj0 : 0 ≤ C.jointResidualStarCharge v :=
      C.jointResidualStarCharge_nonneg_of_tau_lt_one htau1 v
    have hgap : C.jointResidualStarCharge v + alpha * (4 * n : ℕ) ≤ M := by
      dsimp [alpha, M]
      push_cast
      nlinarith
    have hMnat :
        (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
          (C.ambientBaseColor hK) v).card ≤ K := by
      simpa using Finset.card_le_univ
        (P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
          (C.ambientBaseColor hK) v)
    have hupper : M ≤ (1 : ℝ) * (4 * n : ℕ) := by
      have hMK' :
          ((P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
            (C.ambientBaseColor hK) v).card : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast hMnat
      have hMK : M ≤ (K : ℝ) := by simpa [M] using hMK'
      exact hMK.trans hpalette
    apply WeightedMultigraph.div_add_errors_le_one_of_add_gap_le
      hj0 halpha (by norm_num) (by positivity : (0 : ℝ) < (4 * n : ℕ))
      hgap hupper
    · dsimp [eps, alpha]
      nlinarith [hgamma.le]
    · calc
        (T + 1 : ℝ) * (1 / (alpha ^ 2 * (4 * n : ℕ)))
            ≤ gamma / 16 := hdiffuse
        _ = alpha / (4 * (1 : ℝ)) := by dsimp [alpha]; ring
  have hfiniteWeight : ∀ e : P.coreObjectGraph.E,
      P.coreObjectGraph.weight e ≤
        (1 : ℝ) / finiteClassSize (P.coreHarmonicClass ht e) :=
    fun e ↦ P.coreObjectGraph.weight_le_inv_finiteClassSize_finiteHarmonicClassOf
      T hT P.coreObject_weight_ge_inv_two_mul e
  have hfiniteCharge : ∀ e : P.coreObjectGraph.E,
      harmonicCharge (P.coreObjectGraph.weight e) =
        (1 : ℝ) / finiteClassSize (P.coreHarmonicClass ht e) :=
    fun e ↦
      P.coreObjectGraph.harmonicCharge_eq_inv_finiteClassSize_finiteHarmonicClassOf
        T hT P.coreObject_weight_ge_inv_two_mul e
  have hcolored := hcomplete G b tau P K (P.coreHarmonicClass ht)
    (4 * n) C hK htau0 htau1 htauHalf
    (hnComplete.trans (by omega)) (by omega) (even_evenCeilingPalette _)
    (four_le_evenCeilingPalette _) hmissing hpalette hchargeStar hlocal
    hfiniteWeight hfiniteCharge
  have hchiNat := G.chiW_le_of_hasWeightedColoring hcolored
  have hchi : (G.chiW : ℝ) ≤
      (K + (4 * Nat.ceil ((eps / trim + roundEta) * (4 * n)) + 1) : ℕ) := by
    exact_mod_cast hchiNat
  have hcleanup : eps / trim + roundEta = gamma / 32 + gamma / 32 := by
    dsimp [eps, trim, roundEta]
    field_simp [hgamma.ne']
    ring
  have hcost :
      ((K + (4 * Nat.ceil ((eps / trim + roundEta) * (4 * n)) + 1) : ℕ) : ℝ) ≤
        A + 5 * gamma * n + 11 := by
    rw [hcleanup]
    simpa [K] using bipartitePalette_add_cleanup_le
      (A := A) (tau := tau) (gamma := gamma) (n := n)
      hA htau0 htauHalf htauGamma hgamma.le
  have habsorb : 5 * gamma * n + 11 ≤ eta * n :=
    five_slack_mul_add_eleven_le_eta_mul heta hgammaEta hnAbs
  exact hchi.trans (hcost.trans (by linarith))

/-- Conditional sharp bipartite bin-packing endpoint. -/
theorem bipartiteMultigraphBPAsymptotic_of_boundedMultiplicityWholeEdgeUniformRounding
    (hround : BoundedMultiplicityWholeEdgeUniformRounding.{u}) :
    BipartiteMultigraphBPAsymptotic.{u} :=
  bipartiteMultigraphBPAsymptotic_of_harmonicChargeColoring
    (bipartiteHarmonicChargeColoring_of_boundedMultiplicityWholeEdgeUniformRounding
      hround)

/-- Deficit-aware sharp bipartite bin-packing endpoint. -/
theorem bipartiteMultigraphBPAsymptotic_of_deficitAwareBoundedMultiplicityWholeEdgeUniformRounding
    (hround : DeficitAwareBoundedMultiplicityWholeEdgeUniformRounding.{u}) :
    BipartiteMultigraphBPAsymptotic.{u} :=
  bipartiteMultigraphBPAsymptotic_of_harmonicChargeColoring
    (bipartiteHarmonicChargeColoring_of_deficitAwareBoundedMultiplicityWholeEdgeUniformRounding
      hround)

end

end WeightedEdgeColoring
