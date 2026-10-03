import WeightedEdgeColoring.SubtwoActualQuotientResidualColor
import WeightedEdgeColoring.SubtwoDecoderSmallParameters
import WeightedEdgeColoring.SubtwoSelectedLabelOriginalBudget

/-! Uniform small-error actual quotient residual coloring. All profile,
inner-palette, bucket and physical cutoff choices precede the graph. -/

namespace WeightedEdgeColoring.WeightedMultigraph

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2500000
universe u

/-- An actual κ-floor quotient packet coloring extends to a supported
residual coloring with arbitrarily small uncolored weight. The endpoint-label
excess has a fixed rate within the padding allowance, plus the unavoidable
fixed finite-class atom count. -/
theorem exists_uniform_smallActualQuotientResidualColor
    (padding loss : ℝ) (hpadding : 0 < padding) (hloss : 0 < loss) :
    ∃ (δ : ℝ) (k S0 : ℕ), 0 < δ ∧ 0 < k ∧ Even k ∧
      ∀ S : ℕ, max 160 S0 ≤ S →
        let rate : ℝ := 2 * ((1 : ℝ) / S) + 8 * δ
        0 ≤ rate ∧ rate ≤ padding / 20 ∧
        ∀ D : ℕ, ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (n B : ℕ),
          N ≤ n → (hB : 0 < B) → (hn : 0 < n) →
          (hlocal : G.LocallyPacksInto n) →
          (hfloor : G.FloorBundleAtMostOneTiny D S) →
          (hKlower : subtwoKappa * n ≤ B * k) →
          (hKupper : B * k ≤ 4 * n) →
          (heven : Even (B * k)) → (hfour : 4 ≤ B * k) →
          (baseColor : (G.subtwoFloorQuotient n).E → Fin (B * k)) →
          (hproper : (G.subtwoFloorQuotient n).IsProperOn
            (G.subtwoFloorQuotientEdges n) baseColor) →
          let block := G.subtwoFloorBlock n
          let C := G.subtwoFloorPhysicalColoredPacketBase
            (Nat.mul_pos hB (by
              by_contra h
              have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
              simp [hk0] at hfour : 0 < k)) n baseColor hproper
          let edgeLabel := G.subtwoQuotientResidualEdgeLabel block
            (G.subtwoFloorBlock_fiber_card_le_five hn hlocal) C
          ∃ (C' : (G.subtwoQuotient block).GeneralColoredPacketBase (B*k))
            (mixed : C.quotientHybridGraph.E → Fin (B*k)),
          ∃ (hmixed : C.quotientHybridGraph.IsProperOn
              C.quotientHybridPacketEdges mixed)
            (F : Finset C.residualGraph.E)
            (color : C.residualGraph.E → Fin (B*k))
            (selectedLabel : C.residualGraph.V → Fin (B*k) → Option (Fin 6)),
            C' = C.quotientRecoloredBase mixed hmixed ∧
            C'.fullEdges = C.fullEdges ∧
            C'.residualEdges = C.residualEdges ∧
            C.residualGraph.IsFeasibleOn F color ∧
            (∀ e ∈ F,
              color e ∈ (G.subtwoQuotient block).missingColorsAt
                C'.fullEdges C'.baseColor (C.residualGraph.fst e) ∧
              color e ∈ (G.subtwoQuotient block).missingColorsAt
                C'.fullEdges C'.baseColor (C.residualGraph.snd e)) ∧
            (∀ e ∈ F, ∀ v (hinc : C.residualGraph.Inc v e),
              selectedLabel v (color e) = some (edgeLabel v ⟨e, hinc⟩)) ∧
            (∀ v : G.V,
              ((Finset.univ.filter (fun c : Fin (B*k) ↦
                selectedLabel (block v) c =
                  some (G.subtwoLocalSixLabel block
                    (G.subtwoFloorBlock_fiber_card_le_five hn hlocal)
                    (block v) v))).card : ℝ) ≤
              G.chargeOn harmonicCharge
                (G.subtwoCrossingSelectedEdges block Finset.univ \
                  G.subtwoFloorBaseEdges n) v +
                rate * n + 400 * (S+1 : ℝ)) ∧
            ∀ v : C.residualGraph.V,
              (∑ e ∈ Finset.univ \ F,
                if C.residualGraph.Inc v e then
                  C.residualGraph.weight e else 0) ≤ loss * n := by
  obtain ⟨δ, k, Lbucket, S0, Nadd, hδ0, hδsmall, hδloss,
    hk, hevenK, hcover, htop, hratePair, hScut, hNadd⟩ :=
      exists_uniform_decoder_parameter_package padding loss hpadding hloss
  refine ⟨δ, k, S0, hδ0, hk, hevenK, ?_⟩
  intro S hS
  dsimp only
  have hS0 : S0 ≤ S := (le_max_right 160 S0).trans hS
  obtain ⟨hS160, hrate⟩ := hScut S hS0
  have hSpos : 0 < S := by omega
  have hrate0 : 0 ≤ 2 * ((1 : ℝ) / S) + 8 * δ := by positivity
  refine ⟨hrate0, hrate, ?_⟩
  intro D
  let alpha : ℝ := 1 / 1000000
  let traceDelta : ℝ := 1 / 2
  have hδquart : δ ≤ 1 / 4 := by linarith
  have hδcent : δ ≤ 1 / 100 := by linarith
  have hδone : δ ≤ 1 := by linarith
  obtain ⟨Ncert, hcert⟩ := eventually_actualQuotientResidualColor
    S D k hS160 hk hδ0 hδquart hδ0 hδ0 hδ0 hδcent
    (by norm_num : 0 < alpha)
    (by norm_num : alpha ≤ 1 / 100000)
    (by norm_num : alpha ≤ traceDelta / 96)
    (by norm_num : 0 < traceDelta)
    (by norm_num : traceDelta ≤ 1)
    rfl hδ0 hδone Lbucket hcover htop
  refine ⟨max Ncert Nadd, ?_⟩
  intro G n B hn hB hnpos hlocal hfloor hKlower hKupper heven hfour
    baseColor hproper
  have hNcert : Ncert ≤ n := (le_max_left _ _).trans hn
  have hNadd4 : Nadd ≤ 4 * n := by
    have hNadd' : Nadd ≤ n := (le_max_right _ _).trans hn
    omega
  obtain ⟨C', x, mixed, hmixed, qLaw, F, color, selectedLabel,
    hrec, hfull, hres, hmass, hlabel, hfeas, _hpositive, hmissing,
    hselected, hselectedCount, hleft⟩ :=
      hcert G n B hNcert hB hnpos hlocal hfloor hKlower hKupper
        heven hfour baseColor hproper
  let block := G.subtwoFloorBlock n
  let C := G.subtwoFloorPhysicalColoredPacketBase
    (Nat.mul_pos hB hk) n baseColor hproper
  let edgeLabel := G.subtwoQuotientResidualEdgeLabel block
    (G.subtwoFloorBlock_fiber_card_le_five hnpos hlocal) C
  refine ⟨C', mixed, hmixed, F, color, selectedLabel,
    hrec, hfull, hres, hfeas, hmissing, hselected, ?_, ?_⟩
  · intro v
    have hKreal : ((B*k : ℕ) : ℝ) ≤ 4 * n := by exact_mod_cast hKupper
    have hfullBase : C.fullEdges =
        G.subtwoQuotientSelectedEdges block (G.subtwoFloorBaseEdges n) := by
      simpa [C, block] using
        (G.subtwoFloorPhysicalColoredPacketBase_fullEdges
          (Nat.mul_pos hB hk) n baseColor hproper)
    have hbudget := G.quotientThreshold_selectedLabels_originalBudget
      block (G.subtwoFloorBlock_fiber_card_le_five hnpos hlocal)
      C (G.subtwoFloorBaseEdges n) hfullBase S hS160 hnpos
      hlocal hKreal δ δ hδ0.le x hmass qLaw hlabel
      selectedLabel (by
        intro q label
        simpa only [Nat.cast_mul] using hselectedCount q label) v
    simpa only [add_assoc, show (4:ℝ)*δ + 4*δ = 8*δ by ring] using hbudget
  · intro v
    let A : ℝ := mixedCandidateOrientedScale (Label := Fin 6)
      (β := jointProfileBeta δ) (qstep := jointProfileQ δ)
      (r := jointProfileR δ)
      (jointProfileRho δ) (jointProfileS δ)
      (jointProfileOmega δ) 400
    have hβ0 : 0 ≤ jointProfileBeta δ := by
      unfold jointProfileBeta
      positivity
    have hadd := hNadd (4*n) hNadd4
    have hsmall := compact_decoder_displayed_loss_small
      loss δ A (jointProfileRho δ) (jointProfileS δ)
      (jointProfileBeta δ) k Lbucket n hloss hδ0 hδquart hδloss
      hk hβ0 hratePair.2 hratePair.1 hadd
    exact (hleft v).trans (by simpa [A] using hsmall)

end
end WeightedEdgeColoring.WeightedMultigraph
