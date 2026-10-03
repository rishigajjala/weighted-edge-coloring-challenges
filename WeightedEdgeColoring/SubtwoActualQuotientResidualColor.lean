import WeightedEdgeColoring.SubtwoActualQuotientLabelRealizations
import WeightedEdgeColoring.SubtwoActualLabelBudget
import WeightedEdgeColoring.SubtwoMixedGraphBlockCompactDecoder

/-! Apply the uniform mixed decoder to an actual floor-quotient residual. -/

namespace WeightedEdgeColoring.WeightedMultigraph

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 10000000
universe u

/-- The actual palette is flattened, while the mixed selector uses blocks. -/
def actualBlockProposal (G : WeightedMultigraph.{u}) {B k : ℕ}
    (x : G.E → Fin (B * k) → ℝ) :
    G.E → (Fin B × Fin k) → ℝ :=
  fun e c => x e (finProdFinEquiv c)

theorem actualBlockProposal_sum {G : WeightedMultigraph.{u}} {B k : ℕ}
    (x : G.E → Fin (B * k) → ℝ) (e : G.E) :
    (∑ c : Fin B × Fin k, G.actualBlockProposal x e c) =
      ∑ c : Fin (B * k), x e c := by
  exact Equiv.sum_comp finProdFinEquiv (x e)

def actualBlockLaw (G : WeightedMultigraph.{u}) {B k : ℕ}
    (qLaw : ∀ v : G.V, Fin (B * k) → Finset (G.StarEdge v) → ℝ) :
    ∀ v : G.V, (Fin B × Fin k) → Finset (G.StarEdge v) → ℝ :=
  fun v c S => qLaw v (finProdFinEquiv c) S

/-- The actual floor quotient has residual star weight at most four times the
original local packing scale. This is the scale used by the uniform decoder. -/
theorem subtwoFloorPhysical_residualStarWeight_le_four
    (G : WeightedMultigraph.{u}) (T : ℕ) (hT : 160 ≤ T)
    {n K : ℕ} (hK : 0 < K) (hn : 0 < n)
    (hlocal : G.LocallyPacksInto n)
    (hKlower : subtwoKappa * n ≤ K) (hKupper : (K : ℝ) ≤ 4 * n)
    (color : (G.subtwoFloorQuotient n).E → Fin K)
    (hproper : (G.subtwoFloorQuotient n).IsProperOn
      (G.subtwoFloorQuotientEdges n) color)
    (v : (G.subtwoFloorPhysicalColoredPacketBase hK n color hproper).residualGraph.V) :
    (G.subtwoFloorPhysicalColoredPacketBase hK n color hproper).residualGraph.starWeight v
      ≤ 4 * n := by
  classical
  let C := G.subtwoFloorPhysicalColoredPacketBase hK n color hproper
  let finite := C.quotientFiniteEdges T
  have hTpos : 0 < T := by omega
  have htau0 : (0 : ℝ) ≤ 1 / T := by positivity
  have htau160 : (1 : ℝ) / T ≤ 1 / 160 := by
    have ht : (160 : ℝ) ≤ T := by exact_mod_cast hT
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < T)).2
    nlinarith
  have hsplit := G.subtwoFloorPhysical_splitReserve_fifth_of_paletteBound
    hK hn hlocal hKlower hKupper color hproper finite
    ((1 : ℝ) / T) htau0 htau160 v
  dsimp only at hsplit
  have hweight : C.residualGraph.starWeight v ≤
      C.quotientSplitStarCharge finite ((1 : ℝ) / T) v := by
    unfold starWeight GeneralColoredPacketBase.quotientSplitStarCharge
    apply Finset.sum_le_sum
    intro e _
    exact C.quotientSplit_weight_le_charge finite ((1 : ℝ) / T)
      htau0 (by linarith) e.1
  have hmiss :
      (((G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
        C.fullEdges C.baseColor v).card : ℝ) ≤ K := by
    have hcard :
        ((G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
          C.fullEdges C.baseColor v).card ≤ K := by
      simpa using (Finset.card_le_card (Finset.subset_univ
        ((G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
          C.fullEdges C.baseColor v)))
    exact_mod_cast hcard
  linarith

/-- An actual quotient proposal and its canonical single-label laws feed the
uniform mixed decoder at scale `4*n`. The output keeps the local law and
recolored packet base for the original-vertex boundary lift. -/
theorem eventually_actualQuotientResidualColor
    (T D k : ℕ) (hT : 160 ≤ T) (hk : 0 < k)
    {tau t eta eps alpha delta traceEps : ℝ}
    (htau0 : 0 < tau) (htau1 : tau ≤ 1 / 4)
    (ht : 0 < t) (heta : 0 < eta)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1 / 100)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (halphaDelta : alpha ≤ delta / 96)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaHalf : delta = 1 / 2)
    (htrace0 : 0 < traceEps) (htrace1 : traceEps ≤ 1)
    (Lbucket : ℕ)
    (hcover : 1 ≤ dyadicScale (jointProfileBeta tau) Lbucket)
    (htop : dyadicScale (jointProfileBeta tau) Lbucket < 2) :
    ∃ n0 : ℕ, ∀ (G : WeightedMultigraph.{u}) (n B : ℕ),
      n0 ≤ n → (hB : 0 < B) → (hn : 0 < n) →
      (hlocal : G.LocallyPacksInto n) →
      (hfloor : G.FloorBundleAtMostOneTiny D T) →
      (hKlower : subtwoKappa * n ≤ B * k) →
      (hKupper : B * k ≤ 4 * n) →
      (heven : Even (B * k)) → (hfour : 4 ≤ B * k) →
      (baseColor : (G.subtwoFloorQuotient n).E → Fin (B * k)) →
      (hproper : (G.subtwoFloorQuotient n).IsProperOn
        (G.subtwoFloorQuotientEdges n) baseColor) →
      let C := G.subtwoFloorPhysicalColoredPacketBase
        (Nat.mul_pos hB hk) n baseColor hproper
      let edgeLabel := G.subtwoQuotientResidualEdgeLabel
        (G.subtwoFloorBlock n)
        (G.subtwoFloorBlock_fiber_card_le_five hn hlocal) C
      ∃ (C' : (G.subtwoQuotient (G.subtwoFloorBlock n)).GeneralColoredPacketBase (B*k))
        (x : C.residualGraph.E → Fin (B*k) → ℝ)
        (mixed : C.quotientHybridGraph.E → Fin (B*k)),
      ∃ (hmixed : C.quotientHybridGraph.IsProperOn
          C.quotientHybridPacketEdges mixed)
        (qLaw : ∀ v : C.residualGraph.V, Fin (B*k) →
          Finset (C.residualGraph.StarEdge v) → ℝ)
        (F : Finset C.residualGraph.E)
        (color : C.residualGraph.E → Fin (B*k))
        (selectedLabel : C.residualGraph.V → Fin (B*k) → Option (Fin 6)),
        C' = C.quotientRecoloredBase mixed hmixed ∧
        C'.fullEdges = C.fullEdges ∧
        C'.residualEdges = C.residualEdges ∧
        (∀ e, ∑ c, x e c ≤ 1) ∧
        (∀ v c l, subsetLabelMass (edgeLabel v) (qLaw v c) l ≤
          (∑ e : {e : C.residualGraph.StarEdge v //
              e.1 ∈ C.quotientFiniteEdges T},
            if edgeLabel v e.1 = l then
              x e.1.1 c /
                (finiteClassSize (C.quotientThresholdClass T (by omega) e.1.1) : ℝ)
            else 0) +
          (∑ e : {e : C.residualGraph.StarEdge v //
              e.1 ∉ C.quotientFiniteEdges T},
            if edgeLabel v e.1 = l then
              C.residualGraph.weight e.1.1 * x e.1.1 c else 0) /
              (1 - (1 : ℝ) / T) +
          (T+1 : ℝ) * (100 / n)) ∧
        C.residualGraph.IsFeasibleOn F color ∧
        (∀ e ∈ F, 0 < x e (color e)) ∧
        (∀ e ∈ F,
          color e ∈ (G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
            C'.fullEdges C'.baseColor (C.residualGraph.fst e) ∧
          color e ∈ (G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
            C'.fullEdges C'.baseColor (C.residualGraph.snd e)) ∧
        (∀ e ∈ F, ∀ v (hinc : C.residualGraph.Inc v e),
          selectedLabel v (color e) = some (edgeLabel v ⟨e, hinc⟩)) ∧
        (∀ v label,
          ((Finset.univ.filter (fun c : Fin (B*k) ↦
            selectedLabel v c = some label)).card : ℝ) <
          (∑ c, subsetLabelMass (edgeLabel v) (qLaw v c) label) +
          ((B : ℝ) * k) * tau + eta * (4*n)) ∧
        (∀ v,
          (∑ e ∈ Finset.univ \ F,
            if C.residualGraph.Inc v e then C.residualGraph.weight e else 0) ≤
          traceEps * (4*n) +
          (((Lbucket+1) *
            (dyadicSimpleEndpointBlockScale 1 (dyadicSimpleRoot (4*n))-1) : ℕ) : ℝ) +
          (4 / (1-tau/4)+1) *
            ((4*tau+eps+t+
              ((4:ℝ)/k) *
                (mixedCandidateOrientedScale (Label := Fin 6)
                  (β := jointProfileBeta tau) (qstep := jointProfileQ tau)
                  (r := jointProfileR tau) (jointProfileRho tau)
                  (jointProfileS tau) (jointProfileOmega tau) 400 *
                  (jointProfileRho tau * jointProfileS tau)) /
                  (4*t)+eta) * (4*n)) +
          8*(1+(dyadicSimpleReserveScale (dyadicSimpleRoot (4*n)):ℝ)) +
          2*jointProfileBeta tau) := by
  classical
  let mult := 25*((D+1)*(((T+1)^(D+1)*T+T)+1))
  have hmult : 0 < mult := by dsimp [mult]; positivity
  obtain ⟨Nprop, hprop⟩ :=
    WeightedMultigraph.exists_subtwoFloorPhysicalProposal_fixedScale
      T D hT eps heps0 heps1
  obtain ⟨Ndec, hdec⟩ :=
    WeightedMultigraph.mixedGraph_eventually_compactPhysicalDecoder
      (Label := Fin 6) (k := k) (mult := mult) (Lbucket := Lbucket)
      (tau := tau) (C0 := 400) (t := t) (eta := eta)
      (epsMix := eps) (alpha := alpha) (delta := delta)
      (traceEps := traceEps)
      hk hmult htau0 htau1 (by norm_num) ht heta heps0.le
      hcover htop halpha halphaSmall halphaDelta hdelta0 hdelta1
      hdeltaHalf htrace0 htrace1
  refine ⟨max Nprop (max Ndec (60000*(T+1))), ?_⟩
  intro G n B hn0 hB hn hlocal hfloor hKlower hKupper heven hfour
    baseColor hproper
  dsimp only
  let C := G.subtwoFloorPhysicalColoredPacketBase
    (Nat.mul_pos hB hk) n baseColor hproper
  let edgeLabel := G.subtwoQuotientResidualEdgeLabel
    (G.subtwoFloorBlock n)
    (G.subtwoFloorBlock_fiber_card_le_five hn hlocal) C
  have hKupperR : ((B*k : ℕ) : ℝ) ≤ 4*n := by exact_mod_cast hKupper
  have hKlowerR : subtwoKappa * n ≤ ((B*k : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul] using hKlower
  have hNprop : Nprop ≤ 4*n := by omega
  have hnlarge : 60000*(T+1) ≤ n := by omega
  obtain ⟨C', x, mixed, hmixed, hC', hfull, hresidual,
    hx, hxsum, hrow, hsupport, hdeficit⟩ :=
    hprop G n (B*k) (Nat.mul_pos hB hk) hn hlocal hfloor
      hKlowerR hKupperR heven hfour baseColor hproper hNprop hnlarge
  have hs := jointProfile_parameters htau0 htau1
  rcases hs with ⟨hs0, hβ, hq0, hr0, _, _, hleft, _, _, _, _⟩
  have hs1 : jointProfileS tau ≤ 1 := by nlinarith
  obtain ⟨qLaw, R, hq0', hqsum, _hfeas, hqmarg, hqsingle,
    hlabel, _hlarge, _htiny, _hidentity⟩ :=
    C.exists_quotientThresholdSingleLabelLawAndRealizations
      T n hT hn edgeLabel x (fun e c => (hx e c).1)
      (fun e c => (hx e c).2) hrow
      hs0.le hs1 hβ
      hq0 hr0
  let xp : C.residualGraph.E → (Fin B × Fin k) → ℝ :=
    C.residualGraph.actualBlockProposal x
  let qp : ∀ v, (Fin B × Fin k) →
      Finset (C.residualGraph.StarEdge v) → ℝ :=
    C.residualGraph.actualBlockLaw qLaw
  let Rp : ∀ v c label,
      C.residualGraph.BoundedProfileRealization
        (C.residualGraph.conditionalEndpointProposal
          (edgeLabel v) (fun e => xp e.1 c) (qp v c) label)
        (jointProfileS tau) (jointProfileBeta tau)
          (jointProfileQ tau) (jointProfileR tau)
          hβ hr0 :=
    fun v c label => R v (finProdFinEquiv c) label
  have hNdec : Ndec ≤ 4*n := by omega
  have hstar : ∀ v, C.residualGraph.starWeight v ≤ 4*n := by
    intro v
    exact G.subtwoFloorPhysical_residualStarWeight_le_four
      T hT (Nat.mul_pos hB hk) hn hlocal hKlowerR hKupperR
      baseColor hproper v
  have hpair : C.residualGraph.PairMultiplicityAtMost mult :=
    G.subtwoFloorPhysicalColoredPacketBase_residualMultiplicity_of_oneTiny
      D T (Nat.mul_pos hB hk) hn hlocal hfloor baseColor hproper
  have hpaletteDec : B*k ≤ 4*(4*n) := by omega
  obtain ⟨F, color, selectedLabel, hfeasible, hpos,
    hselected, hcount, hloss⟩ :=
    hdec (4*n) B hNdec hpaletteDec C.residualGraph xp edgeLabel qp
      hβ hr0 Rp hpair hB
      (fun v c S => hq0' v (finProdFinEquiv c) S)
      (fun v c f => hqmarg v (finProdFinEquiv c) f)
      (fun v c S hne hempty => hqsingle v (finProdFinEquiv c) S hne hempty)
      (fun v c => hqsum v (finProdFinEquiv c))
      (fun e c => (hx e (finProdFinEquiv c)).1)
      (by intro e c; dsimp [xp, WeightedMultigraph.actualBlockProposal]
          have h := (hx e (finProdFinEquiv c)).2
          have hnR : (0:ℝ)<n := by exact_mod_cast hn
          have heq : (100:ℝ)/n = 400/(4*(n:ℝ)) := by field_simp; ring
          simpa only [Nat.cast_mul, Nat.cast_ofNat, heq] using h)
      (by intro e
          change (∑ c, C.residualGraph.actualBlockProposal x e c) ≤ 1
          rw [C.residualGraph.actualBlockProposal_sum]
          exact hxsum e)
      (by intro v
          have hd : C.residualGraph.proposalDeficit
              (fun e c => xp e (finProdFinEquiv.symm c)) v =
              C.residualGraph.proposalDeficit x v := by
            congr 1
            funext e c
            change x e (finProdFinEquiv (finProdFinEquiv.symm c)) = x e c
            rw [Equiv.apply_symm_apply]
          rw [hd]
          have hv := hdeficit v
          norm_num [Nat.cast_mul] at *
          nlinarith)
      (by intro v
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hstar v)
  refine ⟨C', x, mixed, hmixed, qLaw, F, color, selectedLabel,
    hC', hfull, hresidual, hxsum, hlabel, hfeasible, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    have hp := hpos e he
    change 0 < x e (finProdFinEquiv (finProdFinEquiv.symm (color e))) at hp
    simpa only [Equiv.apply_symm_apply] using hp
  · intro e he
    exact hsupport e (color e) (by
      have hp := hpos e he
      change 0 < x e (finProdFinEquiv (finProdFinEquiv.symm (color e))) at hp
      simpa only [Equiv.apply_symm_apply] using hp)
  · exact hselected
  · intro v label
    have heq :
        (∑ c : Fin B × Fin k,
          subsetLabelMass (edgeLabel v) (qp v c) label) =
        (∑ c : Fin (B*k),
          subsetLabelMass (edgeLabel v) (qLaw v c) label) := by
      simpa only [qp, WeightedMultigraph.actualBlockLaw] using
        (Equiv.sum_comp finProdFinEquiv
          (fun c : Fin (B*k) =>
            subsetLabelMass (edgeLabel v) (qLaw v c) label))
    have hc := hcount v label
    rw [heq] at hc
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hc
  · intro v
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hloss v

end
end WeightedEdgeColoring.WeightedMultigraph
