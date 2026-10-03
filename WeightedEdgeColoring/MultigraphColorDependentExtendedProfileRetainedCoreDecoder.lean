import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileRetainedTinyRounding
import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileStateSafety
import WeightedEdgeColoring.MultigraphExtendedProfileSelectedJointLoad
import WeightedEdgeColoring.BoundedMultiplicityLargeEdgeRestriction

/-!
# Combined decoder on the retained proposal core

A restricted ordinary matching handles retained profile-large edges.  The
unconditional tiny decision handles retained profile-tiny edges.  This file
unites them into one feasible, support-preserving partial coloring and
keeps the two residual contributions explicit.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k K : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- The retained large and retained tiny sets partition the full
high-proposal-mass core. -/
theorem retainedMacroscopic_union_retainedColorDependentTiny
    (gamma : ℝ) :
    G.retainedMacroscopicEdges proposal gamma β ∪
        G.retainedColorDependentTinyEdges proposal gamma β =
      Finset.univ \ G.lowProposalMassEdges proposal gamma := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_union.mp he with heMacro | heTiny
    · have hhigh :=
        (G.mem_retainedMacroscopicEdges proposal gamma β e).mp heMacro |>.1
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, ?_⟩
      intro heLow
      exact (not_lt_of_ge hhigh)
        ((G.mem_lowProposalMassEdges proposal gamma e).mp heLow)
    · have hhigh :=
        (G.mem_retainedColorDependentTinyEdges proposal gamma β e).mp heTiny |>.1
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, ?_⟩
      intro heLow
      exact (not_lt_of_ge hhigh)
        ((G.mem_lowProposalMassEdges proposal gamma e).mp heLow)
  · intro he
    have hnotLow := (Finset.mem_sdiff.mp he).2
    have hhigh : 1 - gamma ≤ G.proposalMass proposal e := by
      apply le_of_not_gt
      intro hlow
      exact hnotLow ((G.mem_lowProposalMassEdges proposal gamma e).mpr hlow)
    by_cases hlarge : β ≤ G.weight e
    · exact Finset.mem_union_left _
        ((G.mem_retainedMacroscopicEdges proposal gamma β e).mpr
          ⟨hhigh, hlarge⟩)
    · exact Finset.mem_union_right _
        ((G.mem_retainedColorDependentTinyEdges proposal gamma β e).mpr
          ⟨hhigh, lt_of_not_ge hlarge⟩)

/-- Direct combined decoder.  The ordinary matching hypotheses are exactly
what the restricted large-job nibble supplies: selected edges lie in the
retained large set, use positive proposal support, and their integral row
load is bounded by the concrete selected slot sizes. -/
theorem exists_retainedColorDependentCore_partialColoring
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hB : 0 < B) (hk : 0 < k)
    (gamma a delta largeLoss : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (herror : delta + 2 * β ≤ (1 - a) * r)
    (selected : G.ColorDependentSelectedStates proposal R)
    (M : Finset (OrdinarySlotChoice G.E (Fin (B * k)) K))
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (hlargeSubset : G.ordinarySelectedEdges M ⊆ G.largeEdgeJobs β)
    (hlargeSupport : ∀ e ∈ G.ordinarySelectedEdges M,
      0 < proposal e (finProdFinEquiv.symm
        (G.extendSelectedOrdinaryColor (Nat.mul_pos hB hk) M hM e)))
    (hlargeLoad : ∀ v c,
      G.selectedOrdinaryIntegralColorLoad M hM v (finProdFinEquiv c) ≤
        ∑ i, G.colorDependentExtendedProfileConcreteSlotSize R v c
          (selected v c.1 c.2) i)
    (htinyFractional : ∀ v c,
      G.selectedColorDependentNormalizedTinyReservoirLoad
          proposal R rho omega selected v c ≤
        a * G.colorDependentExtendedProfileReservoirSize
          R v c (selected v c.1 c.2) + delta)
    (hlargeLoss : ∀ v,
      (∑ e ∈ G.retainedMacroscopicEdges proposal gamma β \
          G.ordinarySelectedEdges M,
        if G.Inc v e then G.weight e else 0) ≤ largeLoss) :
    ∃ (P : Finset G.E) (color : G.E → Fin (B * k)),
      G.IsFeasibleOn P color ∧
      (∀ e ∈ P, 0 < proposal e (finProdFinEquiv.symm (color e))) ∧
      ∀ v,
        (∑ e ∈ (Finset.univ \ G.lowProposalMassEdges proposal gamma) \ P,
          if G.Inc v e then G.weight e else 0) ≤
        largeLoss +
          G.weightedResidualStar
            (G.selectedColorDependentRetainedCoreResidual proposal R gamma
              rho omega
              (G.encodedColorDependentSelectedBlock proposal R selected)) v +
          2 * β := by
  let T := G.retainedColorDependentTinyEdges proposal gamma β
  obtain ⟨decision, htinySupport, _htinyResidual, htinyLoad, htinyLoss⟩ :=
    G.exists_retainedColorDependentTinyDecision proposal R
      hs hq hr0 hleft homega0 homega1 hrho hproposal0 gamma selected
  have hdisj : Disjoint (G.ordinarySelectedEdges M) T := by
    rw [Finset.disjoint_left]
    intro e heM heT
    have heLarge := G.mem_largeEdgeJobs.mp (hlargeSubset heM)
    have heTiny := (G.mem_retainedColorDependentTinyEdges proposal gamma β e).mp
      heT |>.2
    exact (not_lt_of_ge heLarge) heTiny
  have hjointLoad : ∀ v d,
      G.selectedOrdinaryIntegralColorLoad M hM v d +
        G.tinyResidualIntegralColorLoad decision v d ≤ 1 := by
    intro v d
    let c := finProdFinEquiv.symm d
    have hc : finProdFinEquiv c = d := finProdFinEquiv.apply_symm_apply d
    rw [← hc]
    by_cases hex : ∃ e, G.Inc v e.1 ∧ decision e = some (finProdFinEquiv c)
    · rcases hex with ⟨e, hinc, hdecision⟩
      have hsupp := htinySupport e (finProdFinEquiv c) hdecision
      have hsupp' :
          0 < G.colorDependentExtendedProfileReservoirSize R
              (G.fst e.1) c
              (selected (G.fst e.1) c.1 c.2) ∧
            0 < G.colorDependentExtendedProfileReservoirSize R
              (G.snd e.1) c
              (selected (G.snd e.1) c.1 c.2) := by
        have hpair : finProdFinEquiv.symm (finProdFinEquiv c) = c :=
          finProdFinEquiv.symm_apply_apply c
        rw [hpair] at hsupp
        exact hsupp.2
      have hresPos : 0 < G.colorDependentExtendedProfileReservoirSize
          R v c (selected v c.1 c.2) := by
        rcases hinc with hfst | hsnd
        · subst v
          exact hsupp'.1
        · subst v
          exact hsupp'.2
      have hresGe : r ≤ G.colorDependentExtendedProfileReservoirSize
          R v c (selected v c.1 c.2) :=
        G.colorDependentExtendedProfileReservoirSize_ge_r_of_pos
          R hr1 v c _ hresPos
      have hcoef : 0 ≤ 1 - a := sub_nonneg.mpr ha1
      have hslack : delta + 2 * β ≤
          (1 - a) * G.colorDependentExtendedProfileReservoirSize
            R v c (selected v c.1 c.2) :=
        herror.trans (mul_le_mul_of_nonneg_left hresGe hcoef)
      have hsafe :=
        G.sum_colorDependentExtendedProfileConcreteSlotSize_add_reservoir_le_one
          R v c (selected v c.1 c.2)
      have htiny := (htinyLoad v c).trans
        (add_le_add (htinyFractional v c) le_rfl)
      nlinarith [hlargeLoad v c]
    · have htinyZero :
          G.tinyResidualIntegralColorLoad decision v (finProdFinEquiv c) = 0 := by
        unfold tinyResidualIntegralColorLoad
        apply Finset.sum_eq_zero
        intro e _he
        have hnot : ¬(G.Inc v e.1 ∧
            decision e = some (finProdFinEquiv c)) := fun h ↦ hex ⟨e, h⟩
        simp [hnot]
      rw [htinyZero, add_zero]
      exact (hlargeLoad v c).trans
        ((le_add_of_nonneg_right
          (G.colorDependentExtendedProfileReservoirSize_nonneg
            R v c (selected v c.1 c.2))).trans
          (G.sum_colorDependentExtendedProfileConcreteSlotSize_add_reservoir_le_one
            R v c (selected v c.1 c.2)))
  let P := G.ordinarySelectedEdges M ∪ G.tinyDecisionColoredEdges T decision
  let color := G.ordinaryTinyJointColor (Nat.mul_pos hB hk) M hM T decision
  have hfeasible : G.IsFeasibleOn P color := by
    exact G.ordinaryTinyJoint_isFeasibleOn_of_load_le_one
      (Nat.mul_pos hB hk) M hM T decision hdisj hjointLoad
  have hsupport : ∀ e ∈ P,
      0 < proposal e (finProdFinEquiv.symm (color e)) := by
    intro e heP
    rcases Finset.mem_union.mp heP with heM | heT
    · simpa [color, ordinaryTinyJointColor, extendSelectedOrdinaryColor,
          heM] using hlargeSupport e heM
    · have heTbase := (Finset.mem_filter.mp heT).1
      have heMnot : e ∉ G.ordinarySelectedEdges M := fun heM ↦
        Finset.disjoint_left.mp hdisj heM heTbase
      have hsome : ∃ d, G.tinyDecisionAt T decision e = some d := by
        have hne := (Finset.mem_filter.mp heT).2
        cases h : G.tinyDecisionAt T decision e with
        | none => exact False.elim (hne h)
        | some d => exact ⟨d, rfl⟩
      rcases hsome with ⟨d, hd⟩
      have hdecision : decision ⟨e, heTbase⟩ = some d := by
        simpa [G.tinyDecisionAt_of_mem T decision heTbase] using hd
      have hp := (htinySupport ⟨e, heTbase⟩ d hdecision).1
      simpa [color, ordinaryTinyJointColor, heMnot, hd] using hp
  refine ⟨P, color, hfeasible, hsupport, ?_⟩
  intro v
  let H := Finset.univ \ G.lowProposalMassEdges proposal gamma
  let A := G.retainedMacroscopicEdges proposal gamma β \
    G.ordinarySelectedEdges M
  let U := T \ G.tinyDecisionColoredEdges T decision
  have hdecomp : H \ P = A ∪ U := by
    ext e
    change
      e ∈ (Finset.univ \ G.lowProposalMassEdges proposal gamma) \
          (G.ordinarySelectedEdges M ∪ G.tinyDecisionColoredEdges T decision) ↔
        e ∈ (G.retainedMacroscopicEdges proposal gamma β \
            G.ordinarySelectedEdges M) ∪
          (T \ G.tinyDecisionColoredEdges T decision)
    constructor
    · intro he
      have heOutside := Finset.mem_sdiff.mp he
      have heHighCore := Finset.mem_sdiff.mp heOutside.1
      have hnotLow := heHighCore.2
      have hnotSelected : e ∉ G.ordinarySelectedEdges M := by
        intro heSelected
        exact heOutside.2 (Finset.mem_union_left _ heSelected)
      have hnotColored : e ∉ G.tinyDecisionColoredEdges T decision := by
        intro heColored
        exact heOutside.2 (Finset.mem_union_right _ heColored)
      have hhigh : 1 - gamma ≤ G.proposalMass proposal e := by
        apply le_of_not_gt
        intro hlow
        exact hnotLow
          ((G.mem_lowProposalMassEdges proposal gamma e).mpr hlow)
      by_cases hlarge : β ≤ G.weight e
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
          ⟨(G.mem_retainedMacroscopicEdges proposal gamma β e).mpr
              ⟨hhigh, hlarge⟩,
            hnotSelected⟩)
      · have htiny : G.weight e < β := lt_of_not_ge hlarge
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨(G.mem_retainedColorDependentTinyEdges proposal gamma β e).mpr
              ⟨hhigh, htiny⟩,
            hnotColored⟩)
    · intro he
      rcases Finset.mem_union.mp he with heA | heU
      · have heA' := Finset.mem_sdiff.mp heA
        have heMacro :=
          (G.mem_retainedMacroscopicEdges proposal gamma β e).mp heA'.1
        have hnotLow : e ∉ G.lowProposalMassEdges proposal gamma := by
          intro heLow
          exact (not_lt_of_ge heMacro.1)
            ((G.mem_lowProposalMassEdges proposal gamma e).mp heLow)
        refine Finset.mem_sdiff.mpr
          ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, hnotLow⟩, ?_⟩
        intro heP
        rcases Finset.mem_union.mp heP with heSelected | heColored
        · exact heA'.2 heSelected
        · have heT : e ∈ T := (Finset.mem_filter.mp heColored).1
          have htiny :=
            (G.mem_retainedColorDependentTinyEdges proposal gamma β e).mp heT |>.2
          exact (not_lt_of_ge heMacro.2) htiny
      · have heU' := Finset.mem_sdiff.mp heU
        have heTiny :=
          (G.mem_retainedColorDependentTinyEdges proposal gamma β e).mp heU'.1
        have hnotLow : e ∉ G.lowProposalMassEdges proposal gamma := by
          intro heLow
          exact (not_lt_of_ge heTiny.1)
            ((G.mem_lowProposalMassEdges proposal gamma e).mp heLow)
        refine Finset.mem_sdiff.mpr
          ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, hnotLow⟩, ?_⟩
        intro heP
        rcases Finset.mem_union.mp heP with heSelected | heColored
        · have hlarge := G.mem_largeEdgeJobs.mp (hlargeSubset heSelected)
          exact (not_lt_of_ge hlarge) heTiny.2
        · exact heU'.2 heColored
  have hAU : Disjoint A U := by
    rw [Finset.disjoint_left]
    intro e heA heU
    have heA' : e ∈ G.retainedMacroscopicEdges proposal gamma β \
        G.ordinarySelectedEdges M := by
      simpa [A] using heA
    have heU' : e ∈ T \ G.tinyDecisionColoredEdges T decision := by
      simpa [U] using heU
    have heAdata := Finset.mem_sdiff.mp heA'
    have heUdata := Finset.mem_sdiff.mp heU'
    have hlarge : β ≤ G.weight e :=
      (G.mem_retainedMacroscopicEdges proposal gamma β e).mp heAdata.1 |>.2
    have htiny : G.weight e < β :=
      (G.mem_retainedColorDependentTinyEdges proposal gamma β e).mp heUdata.1 |>.2
    exact (not_lt_of_ge hlarge) htiny
  rw [hdecomp, Finset.sum_union hAU]
  have hUloss :
      (∑ e ∈ U, if G.Inc v e then G.weight e else 0) =
        G.tinyResidualIntegralLossLoad decision v := by
    symm
    change G.tinyResidualIntegralLossLoad decision v =
      ∑ e ∈ T \ G.tinyDecisionColoredEdges T decision,
        if G.Inc v e then G.weight e else 0
    unfold tinyResidualIntegralLossLoad tinyDecisionColoredEdges
    rw [show T \ T.filter
        (fun e ↦ G.tinyDecisionAt T decision e ≠ none) =
        T.filter (fun e ↦ G.tinyDecisionAt T decision e = none) by
          ext e
          simp only [Finset.mem_sdiff, Finset.mem_filter]
          constructor
          · rintro ⟨heT, hnotColored⟩
            refine ⟨heT, ?_⟩
            by_contra hne
            exact hnotColored ⟨heT, hne⟩
          · rintro ⟨heT, heq⟩
            refine ⟨heT, ?_⟩
            rintro ⟨_, hne⟩
            exact hne heq]
    rw [Finset.sum_filter]
    rw [Finset.sum_subtype (p := fun e : G.E ↦ e ∈ T) T
      (by intro e; simp)]
    apply Finset.sum_congr rfl
    intro e _he
    rw [G.tinyDecisionAt_of_mem T decision e.2]
    by_cases hinc : G.Inc v e.1
    · cases hdecision : decision e <;> simp [hinc, hdecision]
    · simp [hinc]
  rw [hUloss]
  have htinyResidualBound :
      G.tinyResidualLossLoad
          (G.retainedColorDependentTinyEdges proposal gamma β)
          (fun e ↦ G.selectedColorDependentResidualOptionMass
            proposal R rho omega
              (G.encodedColorDependentSelectedBlock proposal R selected) e.1) v ≤
        G.weightedResidualStar
          (G.selectedColorDependentRetainedCoreResidual proposal R gamma
            rho omega
            (G.encodedColorDependentSelectedBlock proposal R selected)) v :=
    G.tinyResidualLossLoad_retainedColorDependentTiny_le
      proposal R gamma rho omega
        (G.encodedColorDependentSelectedBlock proposal R selected) v
  have htinyIntegralBound :
      G.tinyResidualIntegralLossLoad decision v ≤
        G.weightedResidualStar
            (G.selectedColorDependentRetainedCoreResidual proposal R gamma
              rho omega
              (G.encodedColorDependentSelectedBlock proposal R selected)) v +
          2 * β :=
    (htinyLoss v).trans (add_le_add htinyResidualBound le_rfl)
  calc
    (∑ e ∈ A, if G.Inc v e then G.weight e else 0) +
          G.tinyResidualIntegralLossLoad decision v ≤
        largeLoss +
          (G.weightedResidualStar
            (G.selectedColorDependentRetainedCoreResidual proposal R gamma
              rho omega
              (G.encodedColorDependentSelectedBlock proposal R selected)) v +
            2 * β) :=
      add_le_add (hlargeLoss v) htinyIntegralBound
    _ = largeLoss +
          G.weightedResidualStar
            (G.selectedColorDependentRetainedCoreResidual proposal R gamma
              rho omega
              (G.encodedColorDependentSelectedBlock proposal R selected)) v +
          2 * β := by ring

/-- The combined decoder with the retained-core clipping term discharged by
the selected block's quadratic estimate.  This is the form consumed by the
exact-multiple retained-core rounding theorem: the only remaining loss from
the macroscopic matching is `largeLoss`. -/
theorem exists_retainedColorDependentCore_partialColoring_of_quadraticError
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hB : 0 < B) (hk : 0 < k)
    (hmass : ∀ e, G.proposalMass proposal e ≤ 1)
    (gamma a delta largeLoss sigma targetLoss : ℝ)
    (hgamma0 : 0 ≤ gamma) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hrhos0 : 0 ≤ rho * s) (hrhos1 : rho * s ≤ 1)
    (hsigma0 : 0 ≤ sigma)
    (herror : delta + 2 * β ≤ (1 - a) * r)
    (selected : G.ColorDependentSelectedStates proposal R)
    (hquad : ∀ v,
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedColorDependentAllOptionMass proposal R rho omega
            (G.encodedColorDependentSelectedBlock proposal R selected) e.1 -
          G.colorDependentTotalTarget proposal rho s e.1) ^ 2) ≤ sigma)
    (M : Finset (OrdinarySlotChoice G.E (Fin (B * k)) K))
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (hlargeSubset : G.ordinarySelectedEdges M ⊆ G.largeEdgeJobs β)
    (hlargeSupport : ∀ e ∈ G.ordinarySelectedEdges M,
      0 < proposal e (finProdFinEquiv.symm
        (G.extendSelectedOrdinaryColor (Nat.mul_pos hB hk) M hM e)))
    (hlargeLoad : ∀ v c,
      G.selectedOrdinaryIntegralColorLoad M hM v (finProdFinEquiv c) ≤
        ∑ i, G.colorDependentExtendedProfileConcreteSlotSize R v c
          (selected v c.1 c.2) i)
    (htinyFractional : ∀ v c,
      G.selectedColorDependentNormalizedTinyReservoirLoad
          proposal R rho omega selected v c ≤
        a * G.colorDependentExtendedProfileReservoirSize
          R v c (selected v c.1 c.2) + delta)
    (hlargeLoss : ∀ v,
      (∑ e ∈ G.retainedMacroscopicEdges proposal gamma β \
          G.ordinarySelectedEdges M,
        if G.Inc v e then G.weight e else 0) ≤ largeLoss)
    (hbudget : ∀ v,
      largeLoss +
          ((1 - rho * s * (1 - gamma)) * G.starWeight v +
            Real.sqrt (G.starWeight v * sigma)) +
        2 * β ≤ targetLoss) :
    ∃ (P : Finset G.E) (color : G.E → Fin (B * k)),
      G.IsFeasibleOn P color ∧
      (∀ e ∈ P, 0 < proposal e (finProdFinEquiv.symm (color e))) ∧
      ∀ v,
        (∑ e ∈ (Finset.univ \ G.lowProposalMassEdges proposal gamma) \ P,
          if G.Inc v e then G.weight e else 0) ≤ targetLoss := by
  obtain ⟨P, color, hfeasible, hsupport, hloss⟩ :=
    G.exists_retainedColorDependentCore_partialColoring proposal R
      hs hq hr0 hr1 hleft homega0 homega1 hrho hproposal0 hB hk
      gamma a delta largeLoss ha0 ha1 herror selected M hM
      hlargeSubset hlargeSupport hlargeLoad htinyFractional hlargeLoss
  refine ⟨P, color, hfeasible, hsupport, ?_⟩
  intro v
  refine (hloss v).trans ?_
  have hres :=
    G.weightedResidualStar_selectedColorDependentRetainedCore_le_sqrt
      proposal R gamma rho omega hgamma0 hrhos0 hrhos1 hmass
      (G.encodedColorDependentSelectedBlock proposal R selected)
      v sigma hsigma0 (hquad v)
  nlinarith [hbudget v, hres]

end WeightedMultigraph

end

end WeightedEdgeColoring
