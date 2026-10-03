import WeightedEdgeColoring.SubtwoMixedGraphBlockUniformPhysicalWord
import WeightedEdgeColoring.SubtwoMixedGraphFeasibleRelativeDecoderSupport
import WeightedEdgeColoring.SubtwoMixedGraphBlockResidualPhysical

/-! Convert a selected physical mixed word and the support-sensitive dyadic
decoder into a genuine partial coloring with a single residual bound. -/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {Color Label : Type*} [Fintype Color] [DecidableEq Color]
  [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → Color → ℝ)
variable (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
variable (qLaw : ∀ v : G.V, Color → Finset (G.StarEdge v) → ℝ)
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : ∀ v c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel v)
      (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
    s β qstep r hβ hr)

theorem exists_feasiblePartialColoring_of_selectedMixedWord
    {n N reserve C E S0 steps L K lambda mult : ℕ}
    {rho omega C0 extraGamma bound alpha gamma delta
      traceEps residualRate ratio scale deviation : ℝ}
    (hColor : 0 < Fintype.card Color)
    (hmult : G.PairMultiplicityAtMost mult)
    (hn : 0 < n) (hN : 0 < N)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class)
    (hstar : ∀ v, G.starWeight v ≤ n)
    (hcapacity : ∀ v c place,
      G.selectedMixedCandidateCapacityLoad
        proposal edgeLabel qLaw R rho omega choice c
          (Sum.inl (G.selectedMixedLargeCandidateRow
            proposal edgeLabel qLaw R choice v c place)) < bound)
    (hordinaryCap : (N : ℝ) * bound ≤ S0)
    (hreserve : 0 < reserve)
    (hextraGamma0 : 0 ≤ extraGamma)
    (hextraGamma1 : extraGamma < 1)
    (hextraCap : (1 - extraGamma) * N ≤ S0)
    (hordinaryCodegree : (N : ℝ) *
      ((explicitLargeSlotBound β qstep r : ℝ) *
        mixedGraphCandidateCapacityScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0 /
          (n : ℝ)) ≤ lambda)
    (hordinaryPair : mixedGraphCandidateCapacityScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0 / n ≤
        1 / (reserve : ℝ))
    (hextraCodegree : (N : ℝ) / reserve ≤ lambda)
    (hpairCodegree : (mult : ℝ) * N / reserve ≤ lambda)
    (hCN : C ≤ N) (hNC : 0 < N - C)
    (hE : 2 * ((n : ℝ) / β / (1 - extraGamma) +
      1 + reserve) ≤ E)
    (hchoiceCap : Fintype.card Color * explicitLargeSlotBound β qstep r *
      explicitLargeSlotBound β qstep r + E ≤ C)
    (numeric : MixedMaskedClosedScalars β alpha gamma delta
      N C S0 lambda L K steps)
    (hscale : 0 < scale)
    (hr1 : r ≤ 1) (hrate1 : rho / (1 - omega) ≤ 1)
    (hmargin : scale / (n : ℝ) * deviation + 2 * β ≤
      (1 - rho / (1 - omega)) * r)
    (hRelative : ∀ v c,
      G.selectedMixedNormalizedTinyReservoirLoad
        proposal edgeLabel qLaw R rho omega choice v c <
      rho / (1 - omega) *
        G.selectedMixedConcreteReservoirSize
          proposal edgeLabel qLaw R choice v c +
      scale / (n : ℝ) * deviation)
    (upper : Class → ℝ) (hupper0 : ∀ h, 0 ≤ upper h)
    (hweightUpper : ∀ e, G.weight e ≤ upper (bucket e))
    (hratioUpper : ∀ e,
      0 < G.selectedMixedLargeResidual
        proposal edgeLabel qLaw R rho omega choice e →
      upper (bucket e) ≤ ratio * G.weight e)
    (hratio0 : 0 ≤ ratio)
    (hupperSum : (∑ h, upper h) ≤ 4)
    (hResidual : ∀ v,
      G.weightedResidualStar
        (G.selectedMixedResidualOptionMass
          proposal edgeLabel qLaw R rho omega choice) v ≤
        residualRate * n)
    (htrace : (1 - (1 - delta) *
      variableSlackA alpha gamma lambda / 8) ^ steps ≤ traceEps) :
    ∃ (colored : Finset G.E)
      (color : G.E → Fin (Fintype.card Color)),
      G.IsFeasibleOn colored color ∧
      ∀ v,
        (∑ e ∈ Finset.univ \ colored,
          if G.Inc v e then G.weight e else 0) ≤
        traceEps * n +
          (((L + 1) * (K - 1) : ℕ) : ℝ) +
          (2 * ratio / (1 - extraGamma) + 1) *
            (residualRate * n) +
          8 * (1 + (reserve : ℝ)) + 2 * β := by
  classical
  obtain ⟨M, hM, decision, hfeasible, hbound⟩ :=
    G.exists_selectedMixedFeasibleFullDecoder_of_relativeScalars_support
      proposal edgeLabel qLaw R hColor hmult hn hN
      hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
      homega0 homega1 hrho hC0 hproposal0 hproposal
      choice bucket hstar hcapacity hordinaryCap hreserve
      hextraGamma0 hextraGamma1 hextraCap hordinaryCodegree
      hordinaryPair hextraCodegree hpairCodegree hCN hNC hE
      hchoiceCap numeric scale deviation ratio hscale hr1 hrate1
      hmargin hRelative upper hupper0 hweightUpper hratioUpper
  let residual := G.selectedMixedLargeResidual
    proposal edgeLabel qLaw R rho omega choice
  let T := G.selectedMixedTinyEdges (β := β)
  let x := G.selectedMixedNormalizedLargeOptionMass
    proposal edgeLabel qLaw R rho omega choice
  let O := G.selectedDyadicOrdinaryBaseOptionsAny
    (explicitLargeSlotBound β qstep r) N bucket extraGamma reserve
      residual x M
  let OFin := O.map
    (OrdinarySlotChoice.colorEquiv (Fintype.equivFin Color)).toEmbedding
  let hO := G.selectedDyadicOrdinaryBaseOptionsAny_isPartialMatching
    (explicitLargeSlotBound β qstep r) N bucket extraGamma reserve
      residual x M hM
  let hOFin := ordinarySlotChoice_colorEquiv_isPartialMatching
    G.fst G.snd (explicitLargeSlotBound β qstep r)
    (Fintype.equivFin Color) O hO
  let colored := G.ordinarySelectedEdges OFin ∪
    G.tinyDecisionColoredEdges T decision
  let color := G.ordinaryTinyJointColor hColor OFin hOFin T decision
  refine ⟨colored, color, hfeasible, ?_⟩
  intro v
  have hlarge := G.weightedSelectedMixedLargeResidual_le_fullStar
    proposal edgeLabel qLaw R rho omega choice v
  have htiny := G.tinyResidualLossLoad_selectedMixed_le_fullStar
    proposal edgeLabel qLaw R rho omega choice v
  have hdenom : 0 < 1 - extraGamma := by linarith
  have hrate : 0 ≤ 2 * ratio / (1 - extraGamma) := by positivity
  have hlarge' : 2 * ratio *
      G.weightedResidualStar residual v / (1 - extraGamma) ≤
      (2 * ratio / (1 - extraGamma)) * (residualRate * n) := by
    have hmul := mul_le_mul_of_nonneg_left
      (hlarge.trans (hResidual v)) (by positivity : (0 : ℝ) ≤ 2 * ratio)
    apply (div_le_iff₀ hdenom).2
    calc
      2 * ratio * G.weightedResidualStar residual v ≤
          2 * ratio * (residualRate * n) := hmul
      _ = ((2 * ratio / (1 - extraGamma)) *
          (residualRate * n)) * (1 - extraGamma) := by
        field_simp
        <;> ring
  have htrace' := mul_le_mul_of_nonneg_right htrace
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hupper' := mul_le_mul_of_nonneg_left hupperSum
    (by positivity : (0 : ℝ) ≤ 2 * (1 + (reserve : ℝ)))
  have hv := hbound v
  dsimp only [colored, color] at hv ⊢
  nlinarith [htiny.trans (hResidual v)]

end WeightedMultigraph

end
end WeightedEdgeColoring
